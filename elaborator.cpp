#include "elaborator.hpp"

#include "printer.hpp"

#include <iostream>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace {

// One local binder in the elaborator's context. Tracks the user-visible
// name and the kernel type. Used both to compute de Bruijn indices for
// name lookup and to construct a kernel Context for inferType calls
// during `=` desugaring and `congruenceOf(...)` elaboration.
//
// `value` is non-null for let-style binders (surface `let X := V`). It
// flows through to ContextEntry.value when the elaborator builds an
// opened Context for kernel calls — so isDefinitionallyEqual can ζ
// the let-name during equality checks. The auto-prover separately
// uses it to ζ-unfold at the closed-term level for structural
// matchers (lemma index, hypothesis match).
struct LocalBinder {
    std::string name;
    ExpressionPointer type;
    ExpressionPointer value = nullptr;
};

// Returns the FreeVariable name used when opening / closing the binder
// at `localBinders[index]` (Internal origin). Wildcards (`_`) get a
// position-dependent suffix so multiple `_` binders in the same stack
// don't collapse to the same FreeVariable. Every site that opens an
// Internal-origin FV for a local binder OR constructs a Context entry
// for one MUST go through this helper — otherwise opens and closes get
// out of sync (`closeBinder` searches by literal name) and inferType
// fails to find type info for the FV in its context. The user-visible
// binder name in `localBinders[i].name` stays unchanged; only the FV
// naming is rewritten here.
inline std::string openingNameFor(
    const std::vector<LocalBinder>& localBinders, size_t index) {
    const std::string& original = localBinders[index].name;
    if (original == "_") {
        return "_wildcard_" + std::to_string(index);
    }
    // Disambiguate against earlier binders with the same name —
    // FreeVariables are identified by (name, origin), so two binders
    // sharing a name would collide as a single FV, breaking
    // substitution and unification. The inner binder (higher index)
    // shadows the outer in the user's view, so it's the inner that
    // gets the unique suffix.
    for (size_t earlier = 0; earlier < index; ++earlier) {
        if (localBinders[earlier].name == original) {
            return original + "_shadow_" + std::to_string(index);
        }
    }
    return original;
}

// Spine-head hash used to bucket rewrite lemmas in the calc auto-prover's
// lemma index (Phase 3). We walk the Application spine to its head and
// hash just that head's identifying tag (Constant name, or a leaf-shape
// tag for anything else). Two terms whose spines share the same head
// land in the same bucket — e.g. `(a+b)+c`, `a+b`, and `a+0` all bucket
// under `Natural.add` along with every other lemma whose LHS is rooted
// at that operator. The subsequent first-order matcher resolves the
// (small) bucket, and the kernel rechecks whatever proof term we emit.
//
// Coarse on purpose: argument shape can't be part of the bucket key
// because lemma binders match arbitrary subtrees, and the hash of a
// `BoundVariable` placeholder can't agree with the hash of an
// arbitrary concrete subterm at the same slot. Discrimination trees
// solve this by branching at wildcard slots; head-only buckets get
// most of the speedup at a fraction of the implementation cost.
inline uint64_t spineHash(ExpressionPointer expression) {
    constexpr uint64_t kTagWildcard = 0xfeULL;
    ExpressionPointer head = expression;
    while (auto* application =
               std::get_if<Application>(&head->node)) {
        head = application->function;
    }
    uint64_t h = subtree_hash::kSeed;
    if (auto* constant = std::get_if<Constant>(&head->node)) {
        h = subtree_hash::mix(h, subtree_hash::kTagConstant);
        h = subtree_hash::mix(h,
            subtree_hash::hashString(constant->name));
        return h;
    }
    if (std::holds_alternative<Pi>(head->node)) {
        return subtree_hash::mix(h, subtree_hash::kTagPi);
    }
    if (std::holds_alternative<Lambda>(head->node)) {
        return subtree_hash::mix(h, subtree_hash::kTagLambda);
    }
    if (std::holds_alternative<Let>(head->node)) {
        return subtree_hash::mix(h, subtree_hash::kTagLet);
    }
    // BoundVariable / FreeVariable / Sort heads share one wildcard
    // bucket: it's only consulted when the diff position itself is a
    // bare leaf (rare), which is also exactly when reverse-direction
    // identity lemmas need to fire.
    return subtree_hash::mix(h, kTagWildcard);
}

class Elaborator {
public:
    Elaborator(Environment& environment,
               std::vector<std::string>& importedModules)
        : environment_(environment),
          importedModules_(importedModules) {}

    // When true, every `by <proof>` annotation on a calc step is
    // also tried with the auto-prover; if the auto-prover closes the
    // step on its own, a warning fires. Drives the
    // `--check-redundant-by` CLI flag.
    void setReportRedundantBy(bool flag) { reportRedundantBy_ = flag; }

    // When true, after elaborating a calc chain, check each internal
    // step's endpoint to see whether the auto-prover could close the
    // combined step (prev-prev → next) without going through it. If
    // yes, emit a warning so the user can remove the redundant
    // intermediate. Off by default — the per-step auto-prover
    // attempts are expensive on long chains. Drives the
    // `--check-redundant-calc-steps` CLI flag.
    void setReportRedundantCalcSteps(bool flag) {
        reportRedundantCalcSteps_ = flag;
    }

    void runModule(const SurfaceModule& module) {
        moduleName_ = module.moduleName;
        // Seed the rewrite-lemma index from theorems loaded via .mathv
        // dependencies. New theorems added during this module's
        // elaboration get registered incrementally in
        // elaborateDefinition / elaboratePatternMatchDefinition.
        seedAlgebraicRegistryFromEnvironment();
        for (const auto& statement : module.statements) {
            elaborateTopStatement(statement);
        }
    }

    // Walk the pre-loaded environment and run shape detection on
    // every Definition's declared type. We restrict to Definitions
    // (not Axioms) since theorems serialise as Definitions with a
    // proof body.
    void seedAlgebraicRegistryFromEnvironment() {
        for (const auto& entry : environment_.declarations) {
            const std::string& name = entry.first;
            const auto& declaration = entry.second;
            if (auto* def = std::get_if<Definition>(&declaration)) {
                registerAlgebraicShape(name, def->type);
            }
        }
    }

    ExpressionPointer runExpression(const SurfaceExpression& expression) {
        return elaborateExpression(expression, {});
    }

private:
    // -------- diagnostic context stack --------
    //
    // The elaborator keeps a stack of "while doing X at line Y" frames
    // as it descends. Errors prepend the stack so the user sees a
    // breadcrumb trail from the surface position to the failure. The
    // Frame guard is RAII: construct to push, destruct to pop. Push
    // before any non-trivial elaboration step; the destructor will run
    // even on exception unwinding, so we don't need explicit pops.

    // Each context frame records what the elaborator was doing AND, when
    // the caller can supply them, the proof context (local binders) and
    // the goal (expected type) at the point the frame was pushed.
    // Errors dump both alongside the breadcrumb so the user sees both
    // "where" and "what was being proved" at every level of the stack.
    struct FrameSnapshot {
        std::string description;
        std::vector<LocalBinder> contextSnapshot;  // copy at push time
        ExpressionPointer expectedType;             // may be null
        int line = 0;                                // 0 = unknown
        int column = 0;                              // 0 = unknown
    };

    struct Frame {
        Elaborator& elaborator;
        Frame(Elaborator& target, std::string description)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description), {}, nullptr,
                               0, 0});
        }
        Frame(Elaborator& target, std::string description,
              const std::vector<LocalBinder>& localBinders,
              ExpressionPointer expectedType)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description),
                               localBinders, expectedType, 0, 0});
        }
        Frame(Elaborator& target, std::string description,
              const std::vector<LocalBinder>& localBinders,
              ExpressionPointer expectedType,
              int line, int column)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(
                FrameSnapshot{std::move(description),
                               localBinders, expectedType,
                               line, column});
        }
        ~Frame() { elaborator.contextFrames_.pop_back(); }
        Frame(const Frame&) = delete;
        Frame& operator=(const Frame&) = delete;
    };

    // Recursively reduces beta-redexes in an expression for display.
    // Unlike `weakHeadNormalForm`, this does NOT unfold Definition
    // applications — those produce huge expanded forms in errors
    // ("Natural.multiply 3 4" stays as written rather than expanding
    // into the Natural_recursor chain). We only reduce
    // `App(Lambda(x, T, body), arg)` patterns at any depth.
    ExpressionPointer betaNormalizeForDisplay(
        ExpressionPointer expression) const {
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                betaNormalizeForDisplay(pi->domain),
                betaNormalizeForDisplay(pi->codomain));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                betaNormalizeForDisplay(lambda->domain),
                betaNormalizeForDisplay(lambda->body));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer fn = betaNormalizeForDisplay(
                application->function);
            ExpressionPointer arg = betaNormalizeForDisplay(
                application->argument);
            if (auto* lambda = std::get_if<Lambda>(&fn->node)) {
                ExpressionPointer reduced = substitute(
                    lambda->body, 0, arg);
                return betaNormalizeForDisplay(reduced);
            }
            return makeApplication(fn, arg);
        }
        return expression;
    }

    std::string prettyPrintForDisplay(
        ExpressionPointer expression) const {
        std::string raw =
            prettyPrint(betaNormalizeForDisplay(expression));
        // The printer prefixes Internal-origin FreeVariables with '@'
        // so that any leak into user output is visible. In error
        // messages we deliberately open binders into named FreeVars,
        // so the `@` markers are noise; strip them.
        std::string stripped;
        stripped.reserve(raw.size());
        for (char character : raw) {
            if (character != '@') stripped.push_back(character);
        }
        return stripped;
    }

    // Pretty-print an expression that lives in a local-binder scope.
    // Opens each binder as a named FreeVariable so the printer shows
    // the user's name rather than a bare `<bound k>` index. `count`
    // optionally limits how many binders are visible (useful when
    // printing the type of binder `i`, which references only the
    // first `i` binders).
    std::string prettyPrintInLocalScope(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders,
        size_t count) const {
        // Open with User-origin so the printer doesn't mark the
        // resulting FreeVariables with `@` (which is reserved for
        // signalling that an Internal-origin variable leaked).
        // Beta-normalise too so the printed form has no left-over
        // redexes (motive applications, etc.).
        ExpressionPointer opened = expression;
        for (size_t i = count; i > 0; --i) {
            opened = openBinder(opened, localBinders[i - 1].name,
                                 FreeVariableOrigin::User);
        }
        return prettyPrint(betaNormalizeForDisplay(opened));
    }
    std::string prettyPrintInLocalScope(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders) const {
        return prettyPrintInLocalScope(expression, localBinders,
                                         localBinders.size());
    }

    // Const version of openOverLocalBinders (the existing one in this
    // class is non-const because it shares the helper used during
    // mutating elaboration).
    ExpressionPointer openOverLocalBinders(
        ExpressionPointer term,
        const std::vector<LocalBinder>& localBinders,
        size_t count) const {
        for (size_t i = count; i > 0; --i) {
            term = openBinder(term,
                              openingNameFor(localBinders, i - 1),
                              FreeVariableOrigin::Internal);
        }
        return term;
    }

    std::string formatErrorWithContext(const std::string& message) const {
        if (contextFrames_.empty()) return message;
        std::string result;
        // Most-recent frame first (innermost work), then progressively
        // outer frames. Each frame on its own line indented under the
        // last so the breadcrumb reads top-to-bottom from outer cause
        // to inner failure. For frames carrying a context snapshot
        // and/or a goal, dump those one indent deeper.
        for (auto iterator = contextFrames_.rbegin();
             iterator != contextFrames_.rend(); ++iterator) {
            result += iterator->description;
            result += "\n";
            // Context dump (suppressed when the snapshot is empty —
            // top-level frames before any binder is pushed don't add
            // anything by saying "(no binders)").
            if (!iterator->contextSnapshot.empty()) {
                result += "    context:\n";
                for (size_t i = 0;
                     i < iterator->contextSnapshot.size(); ++i) {
                    const auto& binder = iterator->contextSnapshot[i];
                    // Type may reference earlier binders (de Bruijn);
                    // open those names so the printout reads as the
                    // user wrote them.
                    std::string printedType;
                    try {
                        printedType = prettyPrintInLocalScope(
                            binder.type, iterator->contextSnapshot, i);
                    } catch (...) {
                        // Pretty-printing must never amplify the
                        // primary error. Fall back to a marker.
                        printedType = "<un-printable>";
                    }
                    result += "      " + binder.name + " : "
                            + printedType + "\n";
                }
            }
            // Goal dump (only when supplied — most internal frames
            // don't have a meaningful local goal to report).
            if (iterator->expectedType) {
                std::string printedGoal;
                try {
                    printedGoal = prettyPrintInLocalScope(
                        iterator->expectedType,
                        iterator->contextSnapshot);
                } catch (...) {
                    printedGoal = "<un-printable>";
                }
                result += "    goal: " + printedGoal + "\n";
            }
            result += "  ";
        }
        result += message;
        return result;
    }

    [[noreturn]] void throwElaborate(const std::string& message) const {
        // Pick up the most recent (innermost) frame that has a known
        // source position; that's the best anchor for an editor to
        // highlight.
        int line = 0;
        int column = 0;
        for (auto iter = contextFrames_.rbegin();
             iter != contextFrames_.rend(); ++iter) {
            if (iter->line != 0) {
                line = iter->line;
                column = iter->column;
                break;
            }
        }
        throw ElaborateError(
            formatErrorWithContext(message), line, column);
    }

    // Wraps a kernel TypeError with the elaborator's context stack and
    // any pretty-printed types the kernel attached. Use in catch
    // blocks around kernel `inferType` / `isDefinitionallyEqual`
    // calls.
    [[noreturn]] void rethrowKernelError(const TypeError& error) const {
        std::string message = "kernel: ";
        message += error.what();
        if (error.expectedType) {
            message += "\n    expected type: ";
            message += prettyPrintForDisplay(error.expectedType);
        }
        if (error.actualType) {
            message += "\n    actual type:   ";
            message += prettyPrintForDisplay(error.actualType);
        }
        throw ElaborateError(formatErrorWithContext(message));
    }

    // -------- top-level statements --------

    void elaborateTopStatement(const SurfaceTopStatement& statement) {
        if (auto* import = std::get_if<SurfaceImportDeclaration>(&statement)) {
            importedModules_.push_back(import->moduleName);
            return;
        }
        if (std::get_if<SurfaceUsingDeclaration>(&statement)) {
            // No-op for v0: notation resolution not implemented yet. Modules
            // must use explicit qualified function calls.
            return;
        }
        if (auto* inductive = std::get_if<SurfaceInductiveDeclaration>(&statement)) {
            elaborateInductive(*inductive);
            return;
        }
        if (auto* axiom = std::get_if<SurfaceAxiomDeclaration>(&statement)) {
            elaborateAxiom(*axiom);
            return;
        }
        if (auto* definition = std::get_if<SurfaceDefinitionDeclaration>(&statement)) {
            elaborateDefinition(*definition);
            return;
        }
        if (auto* op = std::get_if<SurfaceOperatorDeclaration>(&statement)) {
            elaborateOperatorDeclaration(*op);
            return;
        }
        if (auto* ov = std::get_if<SurfaceOverloadDeclaration>(&statement)) {
            elaborateOverloadDeclaration(*ov);
            return;
        }
        if (auto* coercion =
                std::get_if<SurfaceCoercionDeclaration>(&statement)) {
            elaborateCoercionDeclaration(*coercion);
            return;
        }
        if (auto* convention =
                std::get_if<SurfaceConventionDeclaration>(&statement)) {
            elaborateConventionDeclaration(*convention);
            return;
        }
        throw ElaborateError("unhandled top-level statement variant");
    }

    // `convention p [q ...] : T [with H1 [, H2 ...]];` registers each
    // name (`p`, `q`, …) as a key in `conventionRegistry_`. The stored
    // value is the convention's binder shape: the carrier type and the
    // list of side-condition expressions (each referencing the names).
    // When `elaborateDefinition` later sees a free use of `p` in a
    // declaration's signature, it prepends an implicit binder for `p`
    // and one implicit binder per side-condition.
    void elaborateConventionDeclaration(
        const SurfaceConventionDeclaration& declaration) {
        ConventionEntry entry;
        entry.type = declaration.type;
        entry.propositions = declaration.propositions;
        // Each name shares the same type and propositions. The names
        // CO-DEPEND when a single declaration uses more than one of
        // them: if a theorem mentions both `p` and `q` from
        // `convention p q : Natural with Natural.is_prime(p)`, then the
        // primality binder only fires once (on `p`'s convention entry).
        // We register the same entry under each name; the prepending
        // logic deduplicates side-condition expressions by surface
        // syntax (close enough for v1).
        for (const auto& name : declaration.names) {
            if (conventionRegistry_.count(name) > 0) {
                throw ElaborateError(
                    "convention name '" + name
                    + "' is already registered");
            }
            conventionRegistry_[name] = entry;
        }
    }

    // Validate and register an `operator (sym) on (T1, T2) := F`
    // declaration. The function `F` must exist in scope and have type
    // `T1 → T2 → R` for some result type `R`. `T1` and `T2` must each
    // be the head Constant of a known type (axiomatic or via inductive/
    // definition), or the wildcard `_` when the slot's type is generic
    // (e.g. the LHS of `∈ : T → Set(T) → Prop` for any carrier T).
    // When a side is `_`, the head check is skipped — at dispatch time,
    // the lookup falls back to `(sym, _, RightType)` / `(sym, LeftType,
    // _)` / `(sym, _, _)` if no exact match is found.
    void elaborateOperatorDeclaration(
        const SurfaceOperatorDeclaration& declaration) {
        Frame frame(*this,
            "operator (" + declaration.operatorSymbol + ") on ("
            + declaration.leftTypeName + ", "
            + declaration.rightTypeName + ")");
        const Declaration* functionDecl =
            environment_.lookup(declaration.functionName);
        if (!functionDecl) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName + "' is not in scope");
        }
        // Pull the function's type and verify it's T1 → T2 → R. Peel
        // any leading implicit Pi binders first (declared via `{x : T}`)
        // so the validation sees the explicit operand slots. Wildcard
        // sides (`_`) match anything.
        ExpressionPointer functionType = declarationType(*functionDecl);
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, functionType);
        bool leftWildcard = (declaration.leftTypeName == "_");
        bool rightWildcard = (declaration.rightTypeName == "_");
        int declaredImplicitCount =
            environment_.implicitArgumentCount(declaration.functionName);
        for (int i = 0; i < declaredImplicitCount; ++i) {
            auto* implicitPi = std::get_if<Pi>(&cursor->node);
            if (!implicitPi) break;
            cursor = weakHeadNormalForm(
                environment_, implicitPi->codomain);
        }
        auto* leftPi = std::get_if<Pi>(&cursor->node);
        if (!leftPi) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + "' must take at least two arguments");
        }
        if (!leftWildcard
            && !typeHasHeadName(leftPi->domain, declaration.leftTypeName)) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + "' first parameter type does not have '"
                + declaration.leftTypeName + "' as its head");
        }
        ExpressionPointer afterLeft = weakHeadNormalForm(
            environment_, leftPi->codomain);
        auto* rightPi = std::get_if<Pi>(&afterLeft->node);
        if (!rightPi) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + "' must take at least two arguments");
        }
        if (!rightWildcard
            && !typeHasHeadName(rightPi->domain, declaration.rightTypeName)) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + "' second parameter type does not have '"
                + declaration.rightTypeName + "' as its head");
        }
        auto key = std::make_tuple(declaration.operatorSymbol,
                                     declaration.leftTypeName,
                                     declaration.rightTypeName);
        auto& slot = environment_.operatorRegistry[key];
        if (!slot.empty() && slot != declaration.functionName) {
            throwElaborate(
                "operator '" + declaration.operatorSymbol + "' on ("
                + declaration.leftTypeName + ", "
                + declaration.rightTypeName
                + ") is already registered to '" + slot + "'");
        }
        slot = declaration.functionName;
    }

    // Validate and register an `overload alias := F` declaration. The
    // function `F` must exist; the alias accumulates a list of fully-
    // qualified candidates that the elaborator picks among by argument-
    // type matching at call sites.
    void elaborateOverloadDeclaration(
        const SurfaceOverloadDeclaration& declaration) {
        Frame frame(*this,
            "overload '" + declaration.aliasName + "' := '"
            + declaration.functionName + "'");
        const Declaration* functionDecl =
            environment_.lookup(declaration.functionName);
        if (!functionDecl) {
            throwElaborate(
                "overload target '" + declaration.functionName
                + "' is not in scope");
        }
        // Disallow registering an alias whose name collides with an
        // existing declaration — that would be ambiguous at name lookup.
        if (environment_.lookup(declaration.aliasName) != nullptr) {
            throwElaborate(
                "overload alias '" + declaration.aliasName
                + "' collides with an existing declaration of the same "
                "name; pick a different alias");
        }
        auto& candidates =
            environment_.overloadAliases[declaration.aliasName];
        for (const auto& existing : candidates) {
            if (existing == declaration.functionName) {
                return;  // idempotent re-registration
            }
        }
        candidates.push_back(declaration.functionName);
    }

    // Validate and register a `coercion (S, T) := F` declaration.
    //
    // F must have type `S → T` (both head Constants). After validation
    // we add the direct edge and compute the transitive closure with
    // existing coercions; any registration whose closure step would
    // overwrite a different existing chain is rejected (diamond).
    void elaborateCoercionDeclaration(
        const SurfaceCoercionDeclaration& declaration) {
        Frame frame(*this,
            "coercion (" + declaration.sourceTypeName + ", "
            + declaration.targetTypeName + ")");
        if (declaration.sourceTypeName == declaration.targetTypeName) {
            throwElaborate(
                "coercion source and target must differ (got '"
                + declaration.sourceTypeName + "' on both sides)");
        }
        const Declaration* functionDecl =
            environment_.lookup(declaration.functionName);
        if (!functionDecl) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "' is not in scope");
        }
        // Verify F has type S → T (head Constants match).
        ExpressionPointer functionType = declarationType(*functionDecl);
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, functionType);
        auto* domainPi = std::get_if<Pi>(&cursor->node);
        if (!domainPi) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "' must take exactly one argument of type '"
                + declaration.sourceTypeName + "'");
        }
        if (!typeHasHeadName(domainPi->domain,
                              declaration.sourceTypeName)) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "': parameter type does not have '"
                + declaration.sourceTypeName + "' as its head");
        }
        if (!typeHasHeadName(domainPi->codomain,
                              declaration.targetTypeName)) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "': result type does not have '"
                + declaration.targetTypeName + "' as its head");
        }
        // Compute the transitive closure.
        // For each existing (X, S), add (X, T) = chain_XS + [F].
        // For each existing (T, Y), add (S, Y) = [F] + chain_TY.
        // For each combination, add (X, Y) = chain_XS + [F] + chain_TY.
        // Skip same-source-target entries; reject diamonds.
        using Key = std::tuple<std::string, std::string>;
        std::vector<std::pair<Key, std::vector<std::string>>> additions;
        std::vector<std::string> directChain{declaration.functionName};
        additions.push_back({Key{declaration.sourceTypeName,
                                    declaration.targetTypeName},
                              directChain});
        // Snapshot the existing entries so iteration isn't disturbed.
        std::vector<std::pair<Key, std::vector<std::string>>> snapshot(
            environment_.coercionRegistry.begin(),
            environment_.coercionRegistry.end());
        for (const auto& [key, chain] : snapshot) {
            const auto& [src, tgt] = key;
            // Extend the new direct edge with a suffix that starts at T.
            if (src == declaration.targetTypeName
                && tgt != declaration.sourceTypeName) {
                std::vector<std::string> combined = directChain;
                combined.insert(combined.end(),
                                 chain.begin(), chain.end());
                additions.push_back({Key{declaration.sourceTypeName, tgt},
                                      std::move(combined)});
            }
            // Prefix the new direct edge with a chain that ends at S.
            if (tgt == declaration.sourceTypeName
                && src != declaration.targetTypeName) {
                std::vector<std::string> combined = chain;
                combined.push_back(declaration.functionName);
                additions.push_back({Key{src, declaration.targetTypeName},
                                      std::move(combined)});
                // And the cross-combinations: (src → T → Y) for each
                // existing (T, Y).
                for (const auto& [key2, chain2] : snapshot) {
                    const auto& [src2, tgt2] = key2;
                    if (src2 != declaration.targetTypeName) continue;
                    if (src == tgt2) continue;  // skip A → ... → A
                    std::vector<std::string> three = chain;
                    three.push_back(declaration.functionName);
                    three.insert(three.end(),
                                  chain2.begin(), chain2.end());
                    additions.push_back({Key{src, tgt2},
                                          std::move(three)});
                }
            }
        }
        // Diamond check: for each new key, ensure it's not already
        // present (with any chain). If it is, the user has two distinct
        // paths from the same source to the same target — reject.
        for (const auto& [key, chain] : additions) {
            const auto& [src, tgt] = key;
            if (src == tgt) continue;
            auto existing = environment_.coercionRegistry.find(key);
            if (existing != environment_.coercionRegistry.end()) {
                if (existing->second != chain) {
                    throwElaborate(
                        "coercion diamond: registering ("
                        + declaration.sourceTypeName + ", "
                        + declaration.targetTypeName
                        + ") would create a second path from '"
                        + src + "' to '" + tgt + "'; the existing "
                        "chain is already in the registry");
                }
                // Same chain already there — skip.
                continue;
            }
        }
        for (auto& [key, chain] : additions) {
            const auto& [src, tgt] = key;
            if (src == tgt) continue;
            environment_.coercionRegistry[key] = std::move(chain);
        }
    }

    // Does `expressionType` have the given Constant name at its head?
    // Checks the *raw* head first (so a parameter declared as
    // `Rational` matches `Rational`, even though `Rational` δ-reduces
    // to `Quotient(...)`). Falls back to WHNF if the raw head isn't a
    // Constant. Used for validating operator-declaration signatures.
    bool typeHasHeadName(ExpressionPointer expressionType,
                           const std::string& expectedName) {
        ExpressionPointer cursor = expressionType;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            cursor = application->function;
        }
        if (auto* constant = std::get_if<Constant>(&cursor->node)) {
            if (constant->name == expectedName) return true;
        }
        // Fall back to WHNF — e.g., when the parameter type is itself a
        // computation that reduces to a Constant head.
        ExpressionPointer reduced = weakHeadNormalForm(
            environment_, expressionType);
        while (auto* application =
                   std::get_if<Application>(&reduced->node)) {
            reduced = weakHeadNormalForm(environment_,
                                          application->function);
        }
        auto* constant = std::get_if<Constant>(&reduced->node);
        return constant && constant->name == expectedName;
    }

    void elaborateAxiom(const SurfaceAxiomDeclaration& declaration) {
        Frame frame(*this, "axiom '" + declaration.name + "'");
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();
        ExpressionPointer type =
            elaborateExpression(*declaration.type, {});
        try {
            addAxiom(environment_, declaration.name,
                     finalUniverseParameters(declaration.universeParameters),
                     std::move(type));
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        // Axiom types are written as `(x : T) → U` or
        // `{x : T} → U` arrow chains in the surface syntax. Count the
        // leading implicit `{…}` binders in the SURFACE type and
        // register them so call-site implicit-argument inference can
        // fire — without this the kernel would see a fully-applied Pi
        // chain and there'd be nowhere to record which leading
        // arguments are meant to be inferred.
        int implicitCount =
            countLeadingImplicitArgumentNamesInType(declaration.type);
        if (implicitCount > 0) {
            environment_.implicitArgumentCounts[declaration.name] =
                implicitCount;
        }
        // Axioms are accepted without proof. The foundational ones live
        // in `library/axioms.math` (module name `axioms`) and are
        // silently approved; an axiom declared in any other module is
        // flagged so we never accidentally introduce a new unproved
        // assumption.
        if (moduleName_ != "axioms") {
            std::cerr << "warning: axiom '" << declaration.name
                      << "' admitted without proof\n";
        }
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

    // Walk a surface type expression's leading Pi-binders and count
    // names across the consecutive prefix of implicit binders. Stops
    // at the first explicit binder, the first non-Pi node, or end of
    // chain. Used by `elaborateAxiom` to register implicit-argument
    // counts so call-site inference can fire.
    int countLeadingImplicitArgumentNamesInType(
        SurfaceExpressionPointer typeExpression) {
        int count = 0;
        SurfaceExpressionPointer cursor = typeExpression;
        while (auto* pi = std::get_if<SurfacePiType>(&cursor->node)) {
            if (!pi->binder.isImplicit) break;
            count += static_cast<int>(pi->binder.names.size());
            cursor = pi->codomain;
        }
        return count;
    }

    // Like `referencesBoundBelowThreshold` but allows the abstraction
    // index `abstractIndex` — any Bound var equal to that index (after
    // depth adjustment) is treated as the variable we plan to abstract
    // over and so isn't counted as a capture. Other Bound vars below
    // threshold ARE counted as captures and force the caller to give up.
    bool referencesOtherBoundsBelowThreshold(
        ExpressionPointer expression,
        int threshold,
        int abstractIndex,
        int currentDepth = 0) {
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int effective =
                boundVariable->deBruijnIndex - currentDepth;
            if (effective < 0) return false;
            if (effective == abstractIndex) return false;
            return effective < threshold;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesOtherBoundsBelowThreshold(
                       pi->domain, threshold, abstractIndex,
                       currentDepth)
                || referencesOtherBoundsBelowThreshold(
                       pi->codomain, threshold, abstractIndex,
                       currentDepth + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return referencesOtherBoundsBelowThreshold(
                       lambda->domain, threshold, abstractIndex,
                       currentDepth)
                || referencesOtherBoundsBelowThreshold(
                       lambda->body, threshold, abstractIndex,
                       currentDepth + 1);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return referencesOtherBoundsBelowThreshold(
                       application->function, threshold, abstractIndex,
                       currentDepth)
                || referencesOtherBoundsBelowThreshold(
                       application->argument, threshold, abstractIndex,
                       currentDepth);
        }
        return false;
    }

    // Repeatedly abstracts over a sequence of BoundVariable indices.
    // `indices` is in outermost-to-innermost binder order — i.e.
    // indices[0] becomes the outer Lambda's binder and indices.back()
    // becomes the inner Lambda's binder. After each abstraction every
    // other outer reference shifts up by one, so the i-th abstraction
    // targets the original index shifted by i.
    ExpressionPointer abstractOverBoundVariables(
        ExpressionPointer expression,
        const std::vector<int>& indices) {
        ExpressionPointer result = expression;
        for (size_t i = 0; i < indices.size(); ++i) {
            int adjustedIndex =
                indices[i] + static_cast<int>(i);
            result = abstractOverBoundVariable(result, adjustedIndex);
        }
        return result;
    }

    // Rewrites `expression` so that BoundVariable(targetIndex) becomes
    // BoundVariable(0) at every depth, and every OTHER BoundVariable
    // that refers to outer scope is shifted up by one. Used to build
    // a motive that abstracts over a specific local-binder variable
    // (the scrutinee of a `cases` expression): the resulting term is
    // suitable as the body of a Lambda whose binder takes the
    // scrutinee's place at index 0.
    ExpressionPointer abstractOverBoundVariable(
        ExpressionPointer expression,
        int targetIndex,
        int currentDepth = 0) {
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int index = boundVariable->deBruijnIndex;
            int effective = index - currentDepth;
            if (effective == targetIndex) {
                return makeBoundVariable(currentDepth);
            }
            if (effective >= 0) {
                return makeBoundVariable(index + 1);
            }
            return expression;  // refers to a binder we've descended into
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                abstractOverBoundVariable(pi->domain, targetIndex,
                                            currentDepth),
                abstractOverBoundVariable(pi->codomain, targetIndex,
                                            currentDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                abstractOverBoundVariable(lambda->domain, targetIndex,
                                            currentDepth),
                abstractOverBoundVariable(lambda->body, targetIndex,
                                            currentDepth + 1));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                abstractOverBoundVariable(application->function,
                                            targetIndex, currentDepth),
                abstractOverBoundVariable(application->argument,
                                            targetIndex, currentDepth));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                abstractOverBoundVariable(let->type, targetIndex,
                                            currentDepth),
                abstractOverBoundVariable(let->value, targetIndex,
                                            currentDepth),
                abstractOverBoundVariable(let->body, targetIndex,
                                            currentDepth + 1));
        }
        return expression;
    }

    // Counts leading implicit binder names in a declaration's argument
    // list. Throws if `{x:T}` and `(y:U)` are interleaved (Phase 2.1
    // restricts implicit binders to a leading consecutive prefix). The
    // result is the total number of NAMES across the leading implicit
    // binders (so `{A B : Type}` counts as 2).
    int countLeadingImplicitArgumentNames(
        const SurfaceDefinitionDeclaration& declaration) {
        int count = 0;
        bool seenExplicit = false;
        for (const auto& binder : declaration.arguments) {
            if (binder.isImplicit) {
                if (seenExplicit) {
                    throw ElaborateError(
                        "declaration '" + declaration.name
                        + "': implicit binders '{x : T}' must precede "
                          "all explicit binders");
                }
                count += static_cast<int>(binder.names.size());
            } else {
                seenExplicit = true;
            }
        }
        return count;
    }

    // For each convention name registered in `conventionRegistry_`, check
    // whether it appears as a free identifier somewhere in `declaration`.
    // Collect a deterministic ordered list of "needed" conventions and
    // build implicit binders for each: one for the name itself, one for
    // each side-condition proposition. Returns a fresh
    // SurfaceDefinitionDeclaration with those binders prepended at the
    // front of `arguments`.
    SurfaceDefinitionDeclaration augmentDeclarationWithConventions(
        const SurfaceDefinitionDeclaration& declaration) {
        if (conventionRegistry_.empty()) return declaration;
        std::unordered_set<std::string> userBoundNames;
        for (const auto& binder : declaration.arguments) {
            for (const auto& name : binder.names) {
                userBoundNames.insert(name);
            }
        }
        // We preserve insertion order: a convention is added the first
        // time we see it mentioned. We walk binders' types, the
        // declaration type, the body (if any), and each case body.
        std::vector<std::string> orderedMentioned;
        std::unordered_set<std::string> mentionedSet;
        auto record = [&](const std::string& name) {
            if (userBoundNames.count(name) > 0) return;
            if (conventionRegistry_.count(name) == 0) return;
            if (mentionedSet.insert(name).second) {
                orderedMentioned.push_back(name);
            }
        };
        for (const auto& binder : declaration.arguments) {
            if (binder.type) collectMentionsInSurface(*binder.type, record);
        }
        if (declaration.type) {
            collectMentionsInSurface(*declaration.type, record);
        }
        if (declaration.body) {
            collectMentionsInSurface(*declaration.body, record);
        }
        for (const auto& clause : declaration.cases) {
            for (const auto& pattern : clause.patterns) {
                (void)pattern;
            }
            if (clause.body) collectMentionsInSurface(*clause.body, record);
        }
        if (orderedMentioned.empty()) return declaration;
        // Build prepended binders. For each mentioned convention, push
        // an implicit binder for the name itself, then one implicit
        // binder per side-condition proposition (with an auto-generated
        // anonymous name).
        SurfaceDefinitionDeclaration augmented = declaration;
        std::vector<SurfaceBinder> prepended;
        int propCounter = 0;
        for (const auto& name : orderedMentioned) {
            const auto& entry = conventionRegistry_[name];
            SurfaceBinder nameBinder;
            nameBinder.names = {name};
            nameBinder.type = entry.type;
            nameBinder.isImplicit = true;
            prepended.push_back(nameBinder);
            for (const auto& prop : entry.propositions) {
                SurfaceBinder propBinder;
                propBinder.names = {
                    prop.name.empty()
                        ? ("_convention_h"
                           + std::to_string(propCounter++))
                        : prop.name};
                propBinder.type = prop.proposition;
                propBinder.isImplicit = true;
                prepended.push_back(propBinder);
            }
        }
        augmented.arguments.insert(
            augmented.arguments.begin(),
            prepended.begin(), prepended.end());
        return augmented;
    }

    // Walk `expression` and call `record(name)` for every
    // SurfaceIdentifier reference. Pattern definitions and `cases`
    // clauses' patterns introduce locally-bound names; we don't
    // currently model that here (the predicate is "appears anywhere",
    // not "appears free"), but the augment caller filters out names
    // the user explicitly binds, which handles the most common
    // shadowing case.
    template <typename Recorder>
    void collectMentionsInSurface(const SurfaceExpression& expression,
                                    Recorder record) {
        if (auto* id = std::get_if<SurfaceIdentifier>(&expression.node)) {
            record(id->qualifiedName);
            return;
        }
        if (auto* app = std::get_if<SurfaceApplication>(&expression.node)) {
            collectMentionsInSurface(*app->function, record);
            for (const auto& arg : app->arguments) {
                if (arg.value) collectMentionsInSurface(*arg.value, record);
            }
            return;
        }
        if (auto* pi = std::get_if<SurfacePiType>(&expression.node)) {
            if (pi->binder.type) {
                collectMentionsInSurface(*pi->binder.type, record);
            }
            if (pi->codomain) collectMentionsInSurface(*pi->codomain, record);
            return;
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&expression.node)) {
            if (lambda->binder.type) {
                collectMentionsInSurface(*lambda->binder.type, record);
            }
            if (lambda->body) collectMentionsInSurface(*lambda->body, record);
            return;
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            if (let->type) collectMentionsInSurface(*let->type, record);
            if (let->value) collectMentionsInSurface(*let->value, record);
            if (let->body) collectMentionsInSurface(*let->body, record);
            return;
        }
        if (auto* asc =
                std::get_if<SurfaceAscription>(&expression.node)) {
            if (asc->expression) {
                collectMentionsInSurface(*asc->expression, record);
            }
            if (asc->type) collectMentionsInSurface(*asc->type, record);
            return;
        }
        if (auto* bin =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (bin->left) collectMentionsInSurface(*bin->left, record);
            if (bin->right) collectMentionsInSurface(*bin->right, record);
            return;
        }
        if (auto* un =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            if (un->operand) collectMentionsInSurface(*un->operand, record);
            return;
        }
        if (auto* tup =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            for (const auto& c : tup->components) {
                if (c) collectMentionsInSurface(*c, record);
            }
            return;
        }
        if (auto* cas = std::get_if<SurfaceCases>(&expression.node)) {
            if (cas->scrutinee) {
                collectMentionsInSurface(*cas->scrutinee, record);
            }
            for (const auto& clause : cas->clauses) {
                if (clause.body) {
                    collectMentionsInSurface(*clause.body, record);
                }
            }
            return;
        }
        // SurfaceNumericLiteral, SurfaceType, SurfaceProposition,
        // SurfaceSorry, SurfaceRing, calc, by_induction, and a handful
        // of other leaf/specialised nodes have no children we care
        // about for convention detection. We default to ignoring them
        // — at worst the convention doesn't fire for those forms.
    }

    // RAII guard that restores opacities flipped by `unfold X in …`
    // forms during a single definition / theorem's elaboration. The
    // guard runs after the body has been type-checked AND after
    // addDefinition completes (so the kernel's final check sees the
    // unfolded view); on exit it restores each affected definition
    // to its original opacity and truncates the pending-restores
    // list back to the pre-call size.
    struct OpacityRestoreScope {
        Elaborator& self;
        size_t startSize;
        explicit OpacityRestoreScope(Elaborator& s)
            : self(s),
              startSize(s.pendingOpacityRestores_.size()) {}
        ~OpacityRestoreScope() {
            bool anyRestored = false;
            while (self.pendingOpacityRestores_.size() > startSize) {
                const auto& entry =
                    self.pendingOpacityRestores_.back();
                auto it = self.environment_.declarations.find(
                    entry.first);
                if (it != self.environment_.declarations.end()) {
                    if (auto* def =
                            std::get_if<Definition>(&it->second)) {
                        def->opacity = entry.second;
                        anyRestored = true;
                    }
                }
                self.pendingOpacityRestores_.pop_back();
            }
            if (anyRestored) {
                // Reduction depends on opacity, and the kernel's WHNF /
                // isDefEq caches were populated during the just-finished
                // unfold scope under the now-stale transparent view.
                invalidateKernelCaches();
            }
        }
    };

    void elaborateDefinition(const SurfaceDefinitionDeclaration& origDecl) {
        OpacityRestoreScope opacityScope(*this);
        SurfaceDefinitionDeclaration augmented =
            augmentDeclarationWithConventions(origDecl);
        const SurfaceDefinitionDeclaration& declaration = augmented;
        if (!declaration.cases.empty()) {
            elaboratePatternMatchDefinition(declaration);
            return;
        }
        Frame frame(*this,
            (declaration.isTheorem ? "theorem '" : "definition '")
            + declaration.name + "'");
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();

        // Surface form has explicit (a : T) binders before the colon, plus
        // a return type after, plus a body. To register with the kernel:
        //   declared type = (a1 : T1) → (a2 : T2) → ... → returnType
        //   body          = fun (a1 : T1) (a2 : T2) ... => bodyExpression
        // We thread a local-binder list as we elaborate the type and body
        // in parallel, then wrap both with the appropriate Pi / Lambda.
        std::vector<LocalBinder> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            argumentBinders;
        for (const auto& binder : declaration.arguments) {
            ExpressionPointer argumentType =
                elaborateExpression(*binder.type, localBinders);
            for (const auto& name : binder.names) {
                argumentBinders.push_back({name, argumentType});
                localBinders.push_back({name, argumentType});
                if (&name != &binder.names.back()) {
                    argumentType = elaborateExpression(*binder.type,
                                                        localBinders);
                }
            }
        }
        ExpressionPointer returnType =
            elaborateExpression(*declaration.type, localBinders);
        ExpressionPointer bodyExpression;
        try {
            bodyExpression = elaborateExpression(*declaration.body,
                                                  localBinders,
                                                  returnType);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }

        // Diff-inference for non-calc equality coercion at theorem body
        // position: covers `theorem foo : succ(a) = succ(b) := eq` (no
        // explicit congruenceOf wrapper) when `eq : a = b`.
        bodyExpression = coerceToExpectedTypeViaDiff(
            localBinders, bodyExpression, returnType);
        checkRedundantCongruenceOfWrapper(
            declaration.body, localBinders, returnType,
            "theorem body");

        // Build the full declared type and body by wrapping in reverse.
        ExpressionPointer fullType = returnType;
        ExpressionPointer fullBody = bodyExpression;
        for (auto iterator = argumentBinders.rbegin();
             iterator != argumentBinders.rend(); ++iterator) {
            fullType = makePi(iterator->first, iterator->second, fullType);
            fullBody = makeLambda(iterator->first, iterator->second,
                                   fullBody);
        }

        // We are about to move fullType/fullBody into addDefinition. Keep
        // a copy of the type for post-registration algebraic-shape
        // detection.
        ExpressionPointer typeForDetection = fullType;
        try {
            addDefinition(environment_, declaration.name,
                          finalUniverseParameters(declaration.universeParameters),
                          std::move(fullType), std::move(fullBody),
                          declaration.opaque
                              ? Opacity::Opaque
                              : Opacity::Transparent);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        int implicitCount =
            countLeadingImplicitArgumentNames(declaration);
        if (implicitCount > 0) {
            environment_.implicitArgumentCounts[declaration.name] =
                implicitCount;
        }
        if (declaration.isTheorem) {
            registerAlgebraicShape(declaration.name, typeForDetection);
        }
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

    // -------- pattern-matching definitions --------
    //
    // A pattern-match definition like
    //
    //   definition Natural.add : Natural → Natural → Natural
    //     | zero,         m => m
    //     | successor(k), m => successor(Natural.add(k, m))
    //
    // is translated into a recursor call. For v1 the supported shape is:
    //   - All function arguments are listed in the type signature
    //     (Pi-chain). No `(arguments)` allowed before the colon.
    //   - The first argument is the scrutinee. Its type must be a bare
    //     inductive identifier with zero parameters (Natural, Boolean,
    //     enum-like types).
    //   - Other positions in each pattern row must be bare variable
    //     patterns (or `_`).
    //   - Every constructor must have exactly one matching case.
    //   - Recursive calls in case bodies must use the destructured
    //     argument of the case as their first argument (structural
    //     recursion).

    void elaboratePatternMatchDefinition(
        const SurfaceDefinitionDeclaration& declaration) {

        Frame frame(*this,
            (declaration.isTheorem ? "theorem '" : "definition '")
            + declaration.name + "' (pattern-match form)");
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();

        // Outer binders (pre-colon arguments like `(A B : Proposition)`)
        // become wrapper Pis around the type and wrapper Lambdas around
        // the body. Everything else — the scrutinee analysis, motive,
        // case lambdas, recursor application — happens inside that
        // outer-binder scope.
        std::vector<LocalBinder> outerBinderStack;
        std::vector<std::pair<std::string, ExpressionPointer>>
            outerBinders;
        for (const auto& binder : declaration.arguments) {
            ExpressionPointer outerBinderType =
                elaborateExpression(*binder.type, outerBinderStack);
            for (const auto& name : binder.names) {
                outerBinders.push_back({name, outerBinderType});
                outerBinderStack.push_back({name, outerBinderType});
                if (&name != &binder.names.back()) {
                    outerBinderType =
                        elaborateExpression(*binder.type, outerBinderStack);
                }
            }
        }
        int outerBinderCount = static_cast<int>(outerBinders.size());

        // Decompose the type into a list of (name, surface type) binders
        // plus a final return type. Anonymous Pis get synthesised names.
        struct SurfaceArgument {
            std::string name;
            SurfaceExpressionPointer type;
        };
        std::vector<SurfaceArgument> functionArguments;
        SurfaceExpressionPointer returnType = declaration.type;
        int syntheticIndex = 0;
        while (auto* piType =
                   std::get_if<SurfacePiType>(&returnType->node)) {
            if (piType->binder.names.empty()) {
                SurfaceArgument argument;
                argument.name =
                    "_argument" + std::to_string(syntheticIndex++);
                argument.type = piType->binder.type;
                functionArguments.push_back(argument);
            } else {
                for (const auto& name : piType->binder.names) {
                    SurfaceArgument argument;
                    argument.name = name;
                    argument.type = piType->binder.type;
                    functionArguments.push_back(argument);
                }
            }
            returnType = piType->codomain;
        }
        if (functionArguments.empty()) {
            throw ElaborateError(
                "pattern-match definition '" + declaration.name
                + "' must have at least one argument");
        }

        // Elaborate the kernel types for each function argument, and
        // the kernel return type. We need these for both type signature
        // and motive construction. The starting stack is the outer
        // binder stack, so function-argument types and the return type
        // can reference outer binders by name.
        const SurfaceArgument& scrutineeArgument = functionArguments[0];
        std::vector<LocalBinder> binderStack = outerBinderStack;
        std::vector<ExpressionPointer> argumentKernelTypes;
        for (const auto& argument : functionArguments) {
            ExpressionPointer argumentType =
                elaborateExpression(*argument.type, binderStack);
            argumentKernelTypes.push_back(argumentType);
            binderStack.push_back({argument.name, argumentType});
        }
        ExpressionPointer returnKernelType =
            elaborateExpression(*returnType, binderStack);

        // Analyse the elaborated (and weak-head-normalised) scrutinee
        // type to extract the inductive name, universe arguments, and
        // parameter/index values. Normalising lets a definition like
        // `Natural.divides(d, n)` unfold to its underlying inductive
        // (here `Exists(...)`) so we can pattern-match through it.
        std::string inductiveName;
        std::vector<LevelPointer> inductiveUniverseArguments;
        std::vector<ExpressionPointer> inductiveArguments;
        {
            ExpressionPointer cursor = weakHeadNormalForm(
                environment_, argumentKernelTypes[0]);
            while (auto* application =
                       std::get_if<Application>(&cursor->node)) {
                inductiveArguments.insert(inductiveArguments.begin(),
                                            application->argument);
                cursor = weakHeadNormalForm(
                    environment_, application->function);
            }
            auto* headConstant = std::get_if<Constant>(&cursor->node);
            if (!headConstant) {
                throw ElaborateError(
                    "pattern-match definition '" + declaration.name
                    + "': scrutinee type's head is not an inductive "
                    "constant after normalisation");
            }
            inductiveName = headConstant->name;
            inductiveUniverseArguments = headConstant->universeArguments;
        }
        const Declaration* inductiveLookup =
            environment_.lookup(inductiveName);
        if (!inductiveLookup) {
            throw ElaborateError("inductive '" + inductiveName
                                  + "' not found in environment");
        }
        const Inductive* inductive =
            std::get_if<Inductive>(inductiveLookup);
        if (!inductive) {
            throw ElaborateError("'" + inductiveName
                                  + "' is not an inductive type");
        }

        // Split into parameters (first numParameters) and indices (rest).
        // For indexed inductives, each index value MUST be a
        // BoundVariable referring to a distinct outer binder. This
        // restriction lets the motive simply re-bind those outer
        // names. More general index patterns (e.g. `Equality(A, zero, n)`)
        // require unification machinery we don't yet have.
        std::vector<ExpressionPointer> parameterValues(
            inductiveArguments.begin(),
            inductiveArguments.begin() + inductive->numParameters);
        std::vector<ExpressionPointer> indexValues(
            inductiveArguments.begin() + inductive->numParameters,
            inductiveArguments.end());
        std::vector<int> indexToOuterBinderPosition(indexValues.size());
        std::vector<bool> outerBinderIsIndex(outerBinderCount, false);
        for (size_t k = 0; k < indexValues.size(); ++k) {
            auto* boundVariable = std::get_if<BoundVariable>(
                &indexValues[k]->node);
            if (!boundVariable) {
                throw ElaborateError(
                    "pattern matching on indexed inductive '"
                    + inductiveName
                    + "': index " + std::to_string(k)
                    + " of the scrutinee must be a local variable name "
                    "(complex index expressions are not supported)");
            }
            int outerPosition = outerBinderCount - 1
                - boundVariable->deBruijnIndex;
            if (outerPosition < 0
                || outerPosition >= outerBinderCount) {
                throw ElaborateError(
                    "pattern matching on indexed inductive '"
                    + inductiveName
                    + "': index " + std::to_string(k)
                    + " must reference an outer binder of the "
                    "definition");
            }
            if (outerBinderIsIndex[outerPosition]) {
                throw ElaborateError(
                    "pattern matching on indexed inductive '"
                    + inductiveName
                    + "': the same outer binder is used as more than "
                    "one index");
            }
            outerBinderIsIndex[outerPosition] = true;
            indexToOuterBinderPosition[k] = outerPosition;
        }

        // Build the full type as a Pi chain over function arguments,
        // then wrap in another Pi chain for the outer binders.
        ExpressionPointer fullType = returnKernelType;
        for (int i = static_cast<int>(functionArguments.size()) - 1;
             i >= 0; --i) {
            fullType = makePi(functionArguments[i].name,
                              argumentKernelTypes[i],
                              std::move(fullType));
        }
        for (int i = outerBinderCount - 1; i >= 0; --i) {
            fullType = makePi(outerBinders[i].first,
                              outerBinders[i].second,
                              std::move(fullType));
        }

        // Build the motive in the kernel. For an inductive without
        // indices the motive is `Lambda scrutinee. Pi otherArgs.
        // returnType`. For an indexed inductive it is
        // `Lambda i_1 ... Lambda i_m. Lambda scrutinee. Pi otherArgs.
        // returnType`, where the m index lambdas "re-bind" the outer
        // binders that the scrutinee's index positions reference. The
        // user's surface returnType references those names directly;
        // we elaborate it under a binder stack where the motive's
        // index binders shadow the outer ones, so name resolution
        // picks the motive-bound copy.
        ExpressionPointer motive;
        ExpressionPointer scrutineeTypeInMotive;  // used below for type
        {
            std::vector<LocalBinder> motiveStack = outerBinderStack;
            // Append motive-bound index binders (in scrutinee order).
            // Each shares its name with the corresponding outer binder,
            // so user references to that name in the return type
            // resolve to the motive-bound version (shadowing the
            // outer one). The type is the outer binder's type, shifted
            // to account for any new binders that sit between the
            // outer binder's original position and the motive index
            // binder's current position.
            std::vector<ExpressionPointer> motiveIndexBinderTypes;
            std::vector<std::string> motiveIndexBinderNames;
            for (size_t k = 0; k < indexValues.size(); ++k) {
                int outerPosition = indexToOuterBinderPosition[k];
                int shiftAmount = static_cast<int>(motiveStack.size())
                    - outerPosition;
                ExpressionPointer indexBinderType = shift(
                    outerBinderStack[outerPosition].type, shiftAmount);
                motiveIndexBinderTypes.push_back(indexBinderType);
                motiveIndexBinderNames.push_back(
                    outerBinderStack[outerPosition].name);
                motiveStack.push_back(
                    {outerBinderStack[outerPosition].name,
                     indexBinderType});
            }
            // Re-elaborate the scrutinee's surface type in the new
            // motiveStack so that any references to outer index
            // binders resolve to the motive's index binders.
            scrutineeTypeInMotive = elaborateExpression(
                *functionArguments[0].type, motiveStack);
            motiveStack.push_back({scrutineeArgument.name,
                                    scrutineeTypeInMotive});
            std::vector<ExpressionPointer> otherArgumentKernelTypes;
            for (size_t i = 1; i < functionArguments.size(); ++i) {
                ExpressionPointer argumentType =
                    elaborateExpression(*functionArguments[i].type,
                                         motiveStack);
                otherArgumentKernelTypes.push_back(argumentType);
                motiveStack.push_back(
                    {functionArguments[i].name, argumentType});
            }
            ExpressionPointer motiveCodomain =
                elaborateExpression(*returnType, motiveStack);
            // Wrap with Pis for non-scrutinee function arguments.
            for (int i =
                     static_cast<int>(otherArgumentKernelTypes.size()) - 1;
                 i >= 0; --i) {
                motiveCodomain = makePi(functionArguments[i + 1].name,
                                         otherArgumentKernelTypes[i],
                                         std::move(motiveCodomain));
            }
            // Wrap with the scrutinee lambda.
            motiveCodomain = makeLambda(scrutineeArgument.name,
                                          scrutineeTypeInMotive,
                                          std::move(motiveCodomain));
            // Wrap with index lambdas, innermost (last) first.
            for (int k = static_cast<int>(indexValues.size()) - 1;
                 k >= 0; --k) {
                motiveCodomain =
                    makeLambda(motiveIndexBinderNames[k],
                                motiveIndexBinderTypes[k],
                                std::move(motiveCodomain));
            }
            motive = std::move(motiveCodomain);
        }

        // Determine the motive's universe level by asking the kernel
        // for its type (a Pi chain ending in a Sort). The motive may
        // reference outer binders, so we open those references into
        // Internal-origin FreeVariables and pass a matching Context
        // to inferType.
        LevelPointer motiveLevel;
        {
            // Context entries' types must themselves be in the opened
            // form — each binder's type may reference earlier outer
            // binders via Bound vars, and those need to become FreeVars
            // with matching Internal-origin names.
            Context outerBinderContext;
            for (size_t i = 0; i < outerBinderStack.size(); ++i) {
                ExpressionPointer openedType = openOverLocalBinders(
                    outerBinderStack[i].type, outerBinderStack, i);
                outerBinderContext.push_back(
                    {openingNameFor(outerBinderStack, i), openedType,
                     FreeVariableOrigin::Internal});
            }
            ExpressionPointer motiveType =
                inferType(environment_, outerBinderContext,
                           openOverLocalBinders(
                               motive, outerBinderStack,
                               outerBinderStack.size()));
            ExpressionPointer cursor = motiveType;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                cursor = pi->codomain;
            }
            auto* sortNode = std::get_if<Sort>(&cursor->node);
            if (!sortNode) {
                throw ElaborateError(
                    "internal: motive's type doesn't end in a Sort");
            }
            motiveLevel = sortNode->level;
        }

        // Build a case lambda for each constructor, in declared order.
        // For parameterised inductives, pass the parameter values so the
        // case lambda can strip the constructor's parameter Pis and
        // substitute the values into the remaining argument types.
        // The outer-binder stack lets the case body and any
        // non-scrutinee argument types reference outer binders.
        std::vector<ExpressionPointer> caseLambdas;
        for (const auto& constructorName : inductive->constructorNames) {
            caseLambdas.push_back(
                buildCaseLambda(declaration, constructorName,
                                inductiveName,
                                inductiveUniverseArguments, motive,
                                parameterValues,
                                outerBinderStack));
        }

        // Build the recursor call. The recursor's universe arguments
        // are the inductive's universe arguments followed (for large-
        // eliminating recursors) by the motive's universe level. For
        // restricted-elimination recursors (Proposition inductives that
        // aren't singletons), the motive is forced to Proposition and the
        // recursor takes no extra universe argument.
        std::string recursorName = inductiveName + "_recursor";
        const Declaration* recursorLookup =
            environment_.lookup(recursorName);
        if (!recursorLookup) {
            throw ElaborateError(
                "recursor '" + recursorName + "' not in environment");
        }
        const Recursor* recursorDeclaration =
            std::get_if<Recursor>(recursorLookup);
        if (!recursorDeclaration) {
            throw ElaborateError(
                "'" + recursorName + "' is not a recursor");
        }
        bool recursorHasMotiveLevel =
            recursorDeclaration->universeParameters.size()
            > inductive->universeParameters.size();
        std::vector<LevelPointer> recursorUniverseArguments =
            inductiveUniverseArguments;
        if (recursorHasMotiveLevel) {
            recursorUniverseArguments.push_back(motiveLevel);
        }
        ExpressionPointer recursorReference =
            makeConstant(std::move(recursorName),
                          std::move(recursorUniverseArguments));
        ExpressionPointer applied = std::move(recursorReference);
        // The recursor call lives inside the function-argument lambdas
        // (which we wrap below), which are themselves inside the
        // outer-binder lambdas. Parameter values, the motive, and case
        // lambdas were all built within the outer-binder scope, so any
        // BoundVariable references to outer binders inside them must
        // be bumped by `argumentCount` to account for the extra
        // function-argument lambdas above us. For closed sub-terms
        // (no outer binders in scope, or no references to them) the
        // shift is a no-op.
        int argumentCount = static_cast<int>(functionArguments.size());
        for (const auto& parameterValue : parameterValues) {
            applied = makeApplication(std::move(applied),
                                       shift(parameterValue, argumentCount));
        }
        applied = makeApplication(std::move(applied),
                                   shift(motive, argumentCount));
        for (auto& caseLambda : caseLambdas) {
            applied = makeApplication(
                std::move(applied),
                shift(std::move(caseLambda), argumentCount));
        }
        // For indexed inductives, apply the recursor to the index
        // values (in scrutinee order). They were extracted from the
        // scrutinee type as outer-binder BoundVariables; shift them
        // by argumentCount to account for the enclosing function-arg
        // lambdas we'll wrap with below.
        for (const auto& indexValue : indexValues) {
            applied = makeApplication(std::move(applied),
                                       shift(indexValue, argumentCount));
        }
        // The scrutinee. The function's arguments are bound (from
        // innermost outermost) at depths n-1, n-2, ..., 0 inside the
        // body lambda. The scrutinee is the FIRST function argument,
        // so its de Bruijn index when we're inside ALL function
        // argument binders is (n - 1) — counting from innermost
        // outward.
        applied = makeApplication(std::move(applied),
                                   makeBoundVariable(argumentCount - 1));
        // Then apply to all the other arguments (in declaration order,
        // from the second onward). At the point we apply argument i,
        // its de Bruijn index inside the body lambda is
        // (argumentCount - 1 - i).
        for (int i = 1; i < argumentCount; ++i) {
            applied = makeApplication(
                std::move(applied),
                makeBoundVariable(argumentCount - 1 - i));
        }

        // Wrap in lambdas over function arguments, then in lambdas
        // over the outer binders.
        ExpressionPointer fullBody = applied;
        for (int i = argumentCount - 1; i >= 0; --i) {
            fullBody = makeLambda(functionArguments[i].name,
                                   argumentKernelTypes[i],
                                   std::move(fullBody));
        }
        for (int i = outerBinderCount - 1; i >= 0; --i) {
            fullBody = makeLambda(outerBinders[i].first,
                                   outerBinders[i].second,
                                   std::move(fullBody));
        }

        ExpressionPointer typeForDetection = fullType;
        try {
            addDefinition(environment_, declaration.name,
                          finalUniverseParameters(declaration.universeParameters),
                          std::move(fullType), std::move(fullBody),
                          declaration.opaque
                              ? Opacity::Opaque
                              : Opacity::Transparent);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        int implicitCount =
            countLeadingImplicitArgumentNames(declaration);
        if (implicitCount > 0) {
            environment_.implicitArgumentCounts[declaration.name] =
                implicitCount;
        }
        if (declaration.isTheorem) {
            registerAlgebraicShape(declaration.name, typeForDetection);
        }

        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

    struct FunctionArgumentPair {
        std::string name;
        SurfaceExpressionPointer surfaceType;
    };

    // Builds the kernel Lambda for one case of a pattern-match definition.
    // For parameterised inductives, the caller supplies the parameter
    // values that the scrutinee is applied to; the case lambda strips
    // the constructor's parameter Pis and substitutes the values into
    // the remaining argument types, so the case lambda binds only the
    // non-parameter arguments.
    // The `outerBinderStack` is the context of outer (pre-colon) binders
    // around the entire pattern-match definition. Non-scrutinee
    // argument types and the case body are elaborated with those
    // outer binders in scope, so they can be referenced by name.
    ExpressionPointer buildCaseLambda(
        const SurfaceDefinitionDeclaration& declaration,
        const std::string& constructorName,
        const std::string& inductiveName,
        const std::vector<LevelPointer>& inductiveUniverseArguments,
        ExpressionPointer motive,
        const std::vector<ExpressionPointer>& parameterValues,
        const std::vector<LocalBinder>& outerBinderStack) {

        Frame frame(*this,
            "case for '" + constructorName + "' of '"
            + inductiveName + "'");

        // Find the case in the declaration matching this constructor.
        const SurfacePatternCase* matchedCase = nullptr;
        for (const auto& caseDeclaration : declaration.cases) {
            const SurfacePattern& firstPattern = *caseDeclaration.patterns.front();
            std::string seenName;
            if (auto* constructorPattern =
                    std::get_if<SurfacePatternConstructor>(
                        &firstPattern.node)) {
                seenName = constructorPattern->constructorName;
            } else if (auto* bareName =
                           std::get_if<SurfacePatternBareName>(
                               &firstPattern.node)) {
                seenName = bareName->name;
            }
            if (seenName == constructorName) {
                matchedCase = &caseDeclaration;
                break;
            }
        }
        if (!matchedCase) {
            throw ElaborateError(
                "missing pattern case for constructor '" + constructorName
                + "' in definition '" + declaration.name + "'");
        }

        // Non-bare patterns in non-scrutinee positions are handled below
        // (after the lambda binders are built) by emitting a chain of
        // inner recursor applications via `buildBodyForCase`. Each such
        // inner recursor uses a motive that abstracts both its scrutinee
        // and all later-bound function-arg binders, so dependent types
        // (e.g. an equality hypothesis whose type mentions the scrutinee)
        // refine correctly under the destructure.

        // Extract the destructured argument names from the pattern.
        std::vector<std::string> destructuredNames;
        const SurfacePattern& firstPattern = *matchedCase->patterns.front();
        if (auto* constructorPattern =
                std::get_if<SurfacePatternConstructor>(&firstPattern.node)) {
            for (const auto& subPattern : constructorPattern->arguments) {
                auto* bareName = std::get_if<SurfacePatternBareName>(
                    &subPattern->node);
                if (!bareName) {
                    throw ElaborateError(
                        "nested patterns are not supported in v1");
                }
                destructuredNames.push_back(bareName->name);
            }
        }

        // Get constructor info from the environment.
        const Declaration* constructorLookup =
            environment_.lookup(constructorName);
        const Constructor* constructor =
            std::get_if<Constructor>(constructorLookup);
        if (!constructor) {
            throw ElaborateError(
                "constructor lookup failed for '" + constructorName + "'");
        }
        // Decompose constructor type into per-argument Pis. For a non-
        // parameterised inductive, the constructor's type is exactly
        // a Pi chain over its arguments ending in the inductive type.
        struct ConstructorArgument {
            std::string defaultName;
            ExpressionPointer type;
            bool isRecursive;
        };
        std::vector<ConstructorArgument> constructorArguments;
        // Pre-compute the per-arg `isRecursive` flag from the ORIGINAL
        // (un-substituted) constructor type. Doing this after parameter
        // substitution gives false positives when a parameter value
        // happens to have the inductive's name as its head — e.g.
        // matching on a scrutinee of type `And(A, And(B, C))` would
        // make And.introduction's second arg appear recursive purely
        // because the substituted second parameter is itself an `And`.
        // In the original type, that arg's head is the parameter
        // variable (a BoundVariable), which is unambiguous.
        std::vector<bool> argumentIsRecursiveOriginal;
        {
            ExpressionPointer originalCursor = constructor->type;
            for (size_t p = 0; p < parameterValues.size(); ++p) {
                auto* pi =
                    std::get_if<Pi>(&originalCursor->node);
                if (!pi) break;
                originalCursor = pi->codomain;
            }
            while (auto* pi =
                       std::get_if<Pi>(&originalCursor->node)) {
                ExpressionPointer typeHead = pi->domain;
                while (auto* application =
                           std::get_if<Application>(&typeHead->node)) {
                    typeHead = application->function;
                }
                auto* constant =
                    std::get_if<Constant>(&typeHead->node);
                argumentIsRecursiveOriginal.push_back(
                    constant && constant->name == inductiveName);
                originalCursor = pi->codomain;
            }
        }
        // The constructor's specific index values (one per index of the
        // inductive). Extracted from the result type after stripping
        // all parameter and value-arg Pis. References here may be to:
        //   - Value-arg BoundVariables (Bound(0..nonParamArgs-1)) bound
        //     by the constructor's own value-arg Pis, OR
        //   - Outer-binder references coming from the substituted
        //     parameter values.
        std::vector<ExpressionPointer> constructorIndexValuesRaw;
        {
            // Apply the parameter values to the constructor's type via
            // beta reduction — peel one parameter Pi, substitute its
            // value, repeat. (Peeling all Pis first and then substituting
            // all values in sequence is incorrect when the values
            // themselves reference outer binders: each later substitute
            // walks the partially-substituted cursor and collides with
            // BoundVariables introduced by the earlier substitutes.)
            ExpressionPointer cursor = constructor->type;
            for (size_t i = 0; i < parameterValues.size(); ++i) {
                auto* pi = std::get_if<Pi>(&cursor->node);
                if (!pi) {
                    throw ElaborateError(
                        "internal: constructor '" + constructorName
                        + "' has fewer parameter Pis than expected");
                }
                cursor = substitute(pi->codomain, 0, parameterValues[i]);
            }
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                ConstructorArgument constructorArgument;
                constructorArgument.defaultName = pi->displayHint;
                constructorArgument.type = pi->domain;
                // Use the recursive-flag computed from the ORIGINAL
                // constructor type (above). Falling back to checking
                // the post-substitution head would mistake parameter
                // values whose head is the inductive (e.g. `And(B, C)`
                // substituted into And.introduction's `b : B` slot)
                // for genuine recursive arguments.
                size_t index = constructorArguments.size();
                constructorArgument.isRecursive =
                    (index < argumentIsRecursiveOriginal.size())
                    && argumentIsRecursiveOriginal[index];
                constructorArguments.push_back(constructorArgument);
                cursor = pi->codomain;
            }
            // Now cursor is the constructor's result type:
            // Inductive(parameterValues..., constructorIndexValues...).
            // Peel the application chain and split.
            std::vector<ExpressionPointer> inductiveArguments;
            ExpressionPointer resultCursor = cursor;
            while (auto* application =
                       std::get_if<Application>(&resultCursor->node)) {
                inductiveArguments.insert(inductiveArguments.begin(),
                                            application->argument);
                resultCursor = application->function;
            }
            for (size_t k = parameterValues.size();
                 k < inductiveArguments.size(); ++k) {
                constructorIndexValuesRaw.push_back(
                    inductiveArguments[k]);
            }
        }
        // The user may supply N names (value args only — IHs get
        // auto-generated `_inductionHypothesisFor_<name>` names) or
        // N + recursiveCount names (value args followed by explicit
        // IH names, in declaration order of the recursive args).
        size_t recursiveCount = 0;
        for (const auto& constructorArgument : constructorArguments) {
            if (constructorArgument.isRecursive) ++recursiveCount;
        }
        size_t minNames = constructorArguments.size();
        size_t maxNames = constructorArguments.size() + recursiveCount;
        if (destructuredNames.size() < minNames
            || destructuredNames.size() > maxNames) {
            throw ElaborateError(
                "pattern for '" + constructorName + "' binds "
                + std::to_string(destructuredNames.size())
                + " name(s) but the constructor takes "
                + std::to_string(constructorArguments.size())
                + " value argument(s)"
                + (recursiveCount > 0
                       ? " plus an optional "
                         + std::to_string(recursiveCount)
                         + " induction-hypothesis name(s)"
                       : ""));
        }
        bool userProvidedHypothesisNames =
            destructuredNames.size() == maxNames;
        size_t nextHypothesisIndex = constructorArguments.size();

        // The case lambda's binders, in order:
        //   For each constructor argument i:
        //     - destructuredNames[i] : constructorArguments[i].type
        //     - if recursive, an induction hypothesis
        //       "_inductionHypothesisFor_<name>" of type
        //       motive(argument_i)
        //   Then the remaining function arguments (in order), using
        //   names from matchedCase->patterns[1..n-1] (must be
        //   bare-name patterns).
        std::vector<LocalBinder> lambdaBinders;
        std::map<std::string, std::string> recursiveArgToHypothesis;
        // Position of each destructured constructor argument inside
        // lambdaBinders (the loop interleaves induction hypotheses for
        // recursive args, so positions aren't 0,1,2,...).
        std::vector<size_t> destructuredArgumentPositions;
        // The motive needs to be referenced when constructing rec-hypothesis
        // types. It currently has no free variables (it was elaborated in
        // an empty stack). Each time we use it under N additional binders,
        // we need to shift by N to keep de Bruijn indices valid.
        int binderDepth = 0;  // counter of binders we're adding
        for (size_t i = 0; i < constructorArguments.size(); ++i) {
            const auto& constructorArgument = constructorArguments[i];
            const std::string& destructuredName = destructuredNames[i];
            // The constructor's type Pis use BoundVariables that reference
            // previously-bound constructor arguments. We must shift
            // the type
            // by (binderDepth - i) to account for our current binder count
            // — i is the number of OTHER constructor arguments already
            // in the lambda binder list (each constructor argument adds
            // 1, each induction hypothesis adds 1). For a non-recursive
            // constructor like zero, this loop runs zero times. For
            // successor, just one constructor argument (and its
            // induction hypothesis).
            // Within one constructor, the kernel-emitted types reference
            // earlier constructor arguments via Bound(i - 1 - j).
            // After shifting by
            // (binderDepth - i), the types match our actual lambda depth.
            ExpressionPointer constructorArgumentType =
                shift(constructorArgument.type, binderDepth - static_cast<int>(i));
            destructuredArgumentPositions.push_back(lambdaBinders.size());
            lambdaBinders.push_back({destructuredName, constructorArgumentType});
            binderDepth++;
            if (constructorArgument.isRecursive) {
                // Recursive hypothesis: type = motive(<indices>,
                // <this destructured>). For non-indexed inductives the
                // index list is empty and the motive takes a single
                // argument (the scrutinee). For indexed ones (e.g.
                // LessOrEqual.step's recursive proof argument has type
                // LessOrEqual(smaller, larger)), we must extract those
                // indices from the value-arg's type and feed them to
                // the motive in order.
                ExpressionPointer shiftedMotive = shift(motive, binderDepth);
                ExpressionPointer recursionHypothesisType = shiftedMotive;
                // Peel the constructor-argument type (now in our
                // lambdaBinder scope, since constructorArgumentType is
                // shifted) to extract its arguments. The first
                // `numParameters` are parameter values; the rest are
                // index values.
                ExpressionPointer typeCursor =
                    shift(constructorArgumentType, 1);
                std::vector<ExpressionPointer> recursiveTypeArguments;
                while (auto* application =
                           std::get_if<Application>(&typeCursor->node)) {
                    recursiveTypeArguments.insert(
                        recursiveTypeArguments.begin(),
                        application->argument);
                    typeCursor = application->function;
                }
                for (size_t k = parameterValues.size();
                     k < recursiveTypeArguments.size(); ++k) {
                    recursionHypothesisType = makeApplication(
                        recursionHypothesisType,
                        recursiveTypeArguments[k]);
                }
                recursionHypothesisType =
                    makeApplication(recursionHypothesisType,
                                    makeBoundVariable(0));
                // ^ Bound(0) is the most-recently-bound name, which is
                // the constructor argument we just added
                // (destructuredName).
                std::string hypothesisName;
                if (userProvidedHypothesisNames) {
                    hypothesisName =
                        destructuredNames[nextHypothesisIndex++];
                } else {
                    hypothesisName =
                        "_inductionHypothesisFor_" + destructuredName;
                }
                lambdaBinders.push_back({hypothesisName,
                                          recursionHypothesisType});
                recursiveArgToHypothesis[destructuredName] = hypothesisName;
                binderDepth++;
            }
        }

        // Compute the motive applied to (constructorIndexValues..., Ctor
        // app), beta-reduced. The result is a Pi chain over the
        // non-scrutinee function arguments, ending in the body's
        // expected type. We then peel one Pi per non-scrutinee pattern
        // position to obtain each function argument's substituted
        // binder type — naturally substituted because the motive
        // abstracted them.
        ExpressionPointer motiveAtCase;
        {
            int totalBinderDepth = static_cast<int>(lambdaBinders.size());
            int constructorValueArgCount =
                static_cast<int>(constructorArguments.size());
            motiveAtCase = shift(motive, totalBinderDepth);
            // Apply to the constructor's specific index values. These
            // may reference value-arg BoundVariables (Bound(0..n-1))
            // and outer binders via parameter-value lifts. Shift by
            // (totalBinderDepth - constructorValueArgCount) to map
            // them to body coordinates — relies on the value args
            // sitting contiguously at the bottom of lambdaBinders
            // (i.e. no induction hypotheses interspersed between
            // them). See limitation note in commit message.
            for (const auto& indexValue : constructorIndexValuesRaw) {
                motiveAtCase = makeApplication(
                    motiveAtCase,
                    shift(indexValue,
                           totalBinderDepth
                           - constructorValueArgCount));
            }
            // Apply to the constructor application of (params,
            // destructured-values).
            ExpressionPointer constructorApplication =
                makeConstant(constructorName,
                              inductiveUniverseArguments);
            for (const auto& parameterValue : parameterValues) {
                constructorApplication = makeApplication(
                    constructorApplication,
                    shift(parameterValue, totalBinderDepth));
            }
            for (size_t i = 0; i < destructuredArgumentPositions.size();
                 ++i) {
                int deBruijnIndex = totalBinderDepth - 1
                    - static_cast<int>(
                        destructuredArgumentPositions[i]);
                constructorApplication = makeApplication(
                    constructorApplication,
                    makeBoundVariable(deBruijnIndex));
            }
            motiveAtCase = makeApplication(
                std::move(motiveAtCase),
                std::move(constructorApplication));
            motiveAtCase = weakHeadNormalForm(
                environment_, motiveAtCase);
        }

        // Peel one Pi per non-scrutinee pattern position. The Pi's
        // domain is the case-binder type (already with the scrutinee
        // replaced and earlier non-scrutinee args properly indexed,
        // courtesy of the motive's beta reduction). The codomain
        // descends inside the binder we just bound — so references
        // to it as `Bound(0)` line up with our growing lambdaBinders.
        // Non-bare patterns at these positions get a synthetic binder
        // name here; `buildBodyForCase` (below) then emits a nested
        // recursor that destructures them with a properly-abstracting
        // motive (so dependent later-arg types refine correctly).
        std::vector<size_t> otherFunctionArgumentPositions;
        for (size_t i = 1; i < matchedCase->patterns.size(); ++i) {
            const SurfacePattern& pattern = *matchedCase->patterns[i];
            auto* pi = std::get_if<Pi>(&motiveAtCase->node);
            if (!pi) {
                throw ElaborateError(
                    "pattern case for '" + constructorName + "' has too "
                    "many positions for the function signature");
            }
            std::string positionName;
            if (auto* bareName = std::get_if<SurfacePatternBareName>(
                    &pattern.node)) {
                positionName = bareName->name;
            } else if (std::get_if<SurfacePatternConstructor>(
                           &pattern.node)) {
                positionName =
                    "_innerScrutinee_" + std::to_string(i);
            } else {
                throw ElaborateError(
                    "non-scrutinee pattern positions must be variable "
                    "or constructor patterns");
            }
            otherFunctionArgumentPositions.push_back(lambdaBinders.size());
            lambdaBinders.push_back({positionName, pi->domain});
            motiveAtCase = pi->codomain;
            binderDepth++;
        }

        // The expected body type is what's left of the motive after
        // all the non-scrutinee Pi peels.
        ExpressionPointer expectedBodyType = motiveAtCase;

        // Elaborate the body with all binders in scope (outer + case).
        std::vector<LocalBinder> bodyStack = outerBinderStack;
        for (const auto& binder : lambdaBinders) {
            bodyStack.push_back({binder.name, binder.type});
        }

        // If any non-scrutinee position has a constructor pattern,
        // `buildBodyForCase` emits a chain of inner recursor calls
        // whose motives properly abstract later-bound dependent args.
        // Otherwise it's a thin wrapper around elaborateExpression.
        std::vector<size_t> positionToBinderIndex =
            otherFunctionArgumentPositions;
        ExpressionPointer bodyKernel = buildBodyForCase(
            *matchedCase,
            /*patternIndex=*/1,
            positionToBinderIndex,
            lambdaBinders,
            bodyStack,
            expectedBodyType,
            static_cast<int>(outerBinderStack.size()),
            recursiveArgToHypothesis,
            declaration.name);

        // Early type-check: verify the body's inferred type matches
        // the expected one. This catches a mismatch HERE — with the
        // case-for-`Constructor` frame still on the stack — rather
        // than letting it bubble up to the final recursor application
        // where attribution to the specific case is lost.
        try {
            ExpressionPointer bodyTypeOpened = inferTypeInLocalContext(
                bodyStack, bodyKernel);
            ExpressionPointer expectedOpened = openOverLocalBinders(
                expectedBodyType, bodyStack, bodyStack.size());
            Context bodyContext = buildContextFromLocalBinders(bodyStack);
            if (!isDefinitionallyEqual(environment_, bodyContext,
                                        bodyTypeOpened, expectedOpened)) {
                // Pass the OPENED types so the display path doesn't
                // emit `<bound N>` indices — the body-stack binders
                // now exist in the types as named FreeVariables.
                TypeError error("case body's type does not match the "
                                 "expected return type for this branch");
                error.expectedType = expectedOpened;
                error.actualType = bodyTypeOpened;
                rethrowKernelError(error);
            }
        } catch (const TypeError& kernelError) {
            // Wrap any other kernel error from inferType above.
            if (kernelError.expectedType
                || kernelError.actualType) {
                rethrowKernelError(kernelError);
            }
            TypeError reraised = kernelError;
            rethrowKernelError(reraised);
        }

        // Wrap in lambdas in reverse order.
        ExpressionPointer caseLambda = bodyKernel;
        for (auto iterator = lambdaBinders.rbegin();
             iterator != lambdaBinders.rend(); ++iterator) {
            caseLambda = makeLambda(iterator->name, iterator->type,
                                     std::move(caseLambda));
        }
        return caseLambda;
    }

    // Builds the body for one outer case of a pattern-match definition,
    // walking the user's pattern positions from `patternIndex` onwards.
    //
    //   * Bare-name positions are already regular case-lambda binders;
    //     we just skip past them.
    //   * Constructor patterns at non-scrutinee positions need to be
    //     destructured AND have all later-bound function-arg types
    //     refined under the destructure. We do this by emitting an
    //     inner recursor on that position, with a motive that abstracts
    //     both the position's variable AND all later position variables.
    //     The recursor's case lambda binds the constructor's value args
    //     plus a fresh re-binding of each later position (with refined
    //     types), and recursively calls back into this function for the
    //     next position.
    //
    // V1 restrictions for inner constructor patterns: the inner inductive
    // must be non-parameterised, non-indexed, single-constructor, and
    // non-recursive. (Real call sites — `IntegerRepresentative.make` —
    // satisfy all four; multi-constructor inner patterns would need
    // cross-row coverage analysis that isn't yet wired up.)
    ExpressionPointer buildBodyForCase(
        const SurfacePatternCase& matchedCase,
        size_t patternIndex,
        std::vector<size_t> positionToBinderIndex,
        std::vector<LocalBinder> currentLambdaBinders,
        std::vector<LocalBinder> bodyStack,
        ExpressionPointer expectedType,
        int outerBinderCount,
        const std::map<std::string, std::string>&
            recursiveArgToHypothesis,
        const std::string& declarationName) {

        size_t numPatterns = matchedCase.patterns.size();
        size_t nextCtorPos = numPatterns;
        for (size_t i = patternIndex; i < numPatterns; ++i) {
            if (std::get_if<SurfacePatternConstructor>(
                    &matchedCase.patterns[i]->node)) {
                nextCtorPos = i;
                break;
            }
        }
        if (nextCtorPos == numPatterns) {
            // No remaining inner-constructor patterns — elaborate the
            // user body with the current expected type. Rewriting
            // recursive calls happens here (not at intermediate
            // recursor levels) because the user body is what mentions
            // recursive calls by name.
            SurfaceExpressionPointer rewrittenBody = rewriteRecursiveCalls(
                matchedCase.body, declarationName,
                recursiveArgToHypothesis, outerBinderCount);
            ExpressionPointer caseBody = elaborateExpression(
                *rewrittenBody, bodyStack, expectedType);
            caseBody = coerceToExpectedTypeViaDiff(
                bodyStack, caseBody, expectedType);
            checkRedundantCongruenceOfWrapper(
                rewrittenBody, bodyStack, expectedType,
                "pattern-match case body");
            return caseBody;
        }

        const auto& ctorPattern =
            std::get<SurfacePatternConstructor>(
                matchedCase.patterns[nextCtorPos]->node);
        size_t relativeIndex = nextCtorPos - patternIndex;
        size_t scrutineeBinderIdx =
            positionToBinderIndex[relativeIndex];

        int currentBinderCount =
            static_cast<int>(currentLambdaBinders.size());
        int scrutineeDB =
            currentBinderCount - 1
            - static_cast<int>(scrutineeBinderIdx);

        // Collect de Bruijn indices and original-type snapshots for
        // each position strictly after `nextCtorPos`. These get
        // abstracted into the motive, re-bound (with refined types)
        // inside the case lambda, and then applied as arguments to
        // the inner recursor.
        std::vector<int> laterDBs;
        std::vector<ExpressionPointer> laterTypesBs;
        std::vector<std::string> laterNames;
        for (size_t k = relativeIndex + 1;
             k < positionToBinderIndex.size(); ++k) {
            size_t binderIdx = positionToBinderIndex[k];
            int dbjn = currentBinderCount - 1
                     - static_cast<int>(binderIdx);
            laterDBs.push_back(dbjn);
            ExpressionPointer t = shift(
                currentLambdaBinders[binderIdx].type,
                currentBinderCount - static_cast<int>(binderIdx));
            laterTypesBs.push_back(t);
            laterNames.push_back(
                currentLambdaBinders[binderIdx].name);
        }

        // Scrutinee type, shifted from its insertion scope to
        // bodyStack scope.
        ExpressionPointer scrutineeTypeBs = shift(
            currentLambdaBinders[scrutineeBinderIdx].type,
            currentBinderCount
                - static_cast<int>(scrutineeBinderIdx));

        // Resolve the inner inductive and verify v1 restrictions.
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, scrutineeTypeBs);
        std::vector<ExpressionPointer> inductiveArgs;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            inductiveArgs.insert(inductiveArgs.begin(),
                                  application->argument);
            cursor = weakHeadNormalForm(
                environment_, application->function);
        }
        auto* indConstant = std::get_if<Constant>(&cursor->node);
        if (!indConstant) {
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos)
                + ": scrutinee type's head is not an inductive "
                "constant");
        }
        const std::string& innerInductiveName = indConstant->name;
        const Declaration* innerInductiveDecl =
            environment_.lookup(innerInductiveName);
        const Inductive* innerInductive = innerInductiveDecl
            ? std::get_if<Inductive>(innerInductiveDecl) : nullptr;
        if (!innerInductive) {
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos) + ": '"
                + innerInductiveName + "' is not an inductive type");
        }
        if (static_cast<int>(inductiveArgs.size())
                != innerInductive->numParameters) {
            // We extract parameter values from `inductiveArgs` (the
            // applications walked off the scrutinee's type head). Any
            // extras would be index values; v1 doesn't yet support
            // indexed inner inductives.
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos) + ": inductive '"
                + innerInductiveName
                + "' is indexed; v1 supports only non-indexed inner "
                "inductives");
        }
        std::vector<ExpressionPointer> innerParameterValues(
            inductiveArgs.begin(),
            inductiveArgs.begin() + innerInductive->numParameters);
        if (innerInductive->constructorNames.size() != 1) {
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos) + ": inductive '"
                + innerInductiveName + "' has "
                + std::to_string(
                    innerInductive->constructorNames.size())
                + " constructors; v1 supports inner constructor "
                "patterns only on single-constructor inductives");
        }
        const std::string& expectedCtorName =
            innerInductive->constructorNames[0];
        if (ctorPattern.constructorName != expectedCtorName) {
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos)
                + ": expected constructor '" + expectedCtorName
                + "' (the only constructor of '"
                + innerInductiveName + "'), got '"
                + ctorPattern.constructorName + "'");
        }

        // Constructor info — extract value-arg types and verify
        // non-recursiveness.
        const Declaration* ctorDecl =
            environment_.lookup(expectedCtorName);
        const Constructor* ctorInfo = ctorDecl
            ? std::get_if<Constructor>(ctorDecl) : nullptr;
        if (!ctorInfo) {
            throw ElaborateError(
                "constructor lookup failed for '"
                + expectedCtorName + "'");
        }
        std::vector<ExpressionPointer> ctorArgTypes;
        {
            // Peel parameter Pis one at a time, substituting each
            // parameter value into the codomain (same pattern as the
            // outer-case decomposition). This keeps types of value
            // args coherent when parameter values reference other
            // local binders.
            ExpressionPointer ctorCursor = ctorInfo->type;
            for (const auto& paramValue : innerParameterValues) {
                auto* pi = std::get_if<Pi>(&ctorCursor->node);
                if (!pi) {
                    throw ElaborateError(
                        "internal: constructor '" + expectedCtorName
                        + "' has fewer parameter Pis than expected");
                }
                ctorCursor =
                    substitute(pi->codomain, 0, paramValue);
            }
            // The recursive-flag check below uses the ORIGINAL type's
            // value-arg heads — after parameter substitution, an arg
            // whose type happens to have the inductive as its head
            // (e.g. a parameter of type `T → T` substituted into an
            // arg slot) would look spuriously recursive.
            ExpressionPointer originalCursor = ctorInfo->type;
            for (size_t p = 0; p < innerParameterValues.size(); ++p) {
                auto* pi = std::get_if<Pi>(&originalCursor->node);
                if (!pi) break;
                originalCursor = pi->codomain;
            }
            while (auto* pi = std::get_if<Pi>(&ctorCursor->node)) {
                auto* originalPi =
                    std::get_if<Pi>(&originalCursor->node);
                if (originalPi) {
                    ExpressionPointer head = originalPi->domain;
                    while (auto* application =
                               std::get_if<Application>(&head->node)) {
                        head = application->function;
                    }
                    if (auto* c =
                            std::get_if<Constant>(&head->node)) {
                        if (c->name == innerInductiveName) {
                            throw ElaborateError(
                                "inner constructor pattern at "
                                "position "
                                + std::to_string(nextCtorPos)
                                + ": constructor '" + expectedCtorName
                                + "' is recursive; v1 supports inner "
                                "constructor patterns only on "
                                "non-recursive constructors");
                        }
                    }
                    originalCursor = originalPi->codomain;
                }
                ctorArgTypes.push_back(pi->domain);
                ctorCursor = pi->codomain;
            }
        }
        if (ctorPattern.arguments.size() != ctorArgTypes.size()) {
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos) + ": pattern binds "
                + std::to_string(ctorPattern.arguments.size())
                + " name(s) but constructor '" + expectedCtorName
                + "' takes " + std::to_string(ctorArgTypes.size())
                + " value argument(s)");
        }
        std::vector<std::string> ctorArgNames;
        for (const auto& argPat : ctorPattern.arguments) {
            auto* bareName = std::get_if<SurfacePatternBareName>(
                &argPat->node);
            if (!bareName) {
                throw ElaborateError(
                    "inner constructor pattern at position "
                    + std::to_string(nextCtorPos)
                    + ": nested patterns are not supported");
            }
            ctorArgNames.push_back(bareName->name);
        }

        // Build the motive's abstraction list (outermost-first):
        // scrutinee + all later positions.
        std::vector<int> abstractionList;
        abstractionList.push_back(scrutineeDB);
        for (int db : laterDBs) {
            abstractionList.push_back(db);
        }
        ExpressionPointer motiveBody = abstractOverBoundVariables(
            expectedType, abstractionList);

        // Wrap the motive body in Pis (for later positions, innermost
        // first) and finally an outer Lambda for the scrutinee. Each
        // Pi's domain is the corresponding position's type, abstracted
        // over the binders already in place above this Pi.
        ExpressionPointer motiveChainBody = motiveBody;
        int laterCount = static_cast<int>(laterTypesBs.size());
        for (int k = laterCount; k >= 1; --k) {
            std::vector<int> subAbstraction(
                abstractionList.begin(),
                abstractionList.begin() + k);
            ExpressionPointer pInDomain = abstractOverBoundVariables(
                laterTypesBs[k - 1], subAbstraction);
            motiveChainBody = makePi(laterNames[k - 1],
                                       pInDomain, motiveChainBody);
        }
        std::string scrutineeName =
            currentLambdaBinders[scrutineeBinderIdx].name;
        ExpressionPointer motive = makeLambda(
            scrutineeName, scrutineeTypeBs, motiveChainBody);

        // Determine the motive's universe level (needed if the inner
        // recursor takes a motive-level universe argument).
        LevelPointer motiveLevel;
        {
            Context openedContext;
            for (size_t i = 0; i < bodyStack.size(); ++i) {
                ExpressionPointer openedType = openOverLocalBinders(
                    bodyStack[i].type, bodyStack, i);
                openedContext.push_back(
                    {openingNameFor(bodyStack, i), openedType,
                     FreeVariableOrigin::Internal});
            }
            ExpressionPointer motiveType =
                inferType(environment_, openedContext,
                           openOverLocalBinders(
                               motive, bodyStack, bodyStack.size()));
            ExpressionPointer motiveCursor = motiveType;
            while (auto* pi = std::get_if<Pi>(&motiveCursor->node)) {
                motiveCursor = pi->codomain;
            }
            auto* sortNode =
                std::get_if<Sort>(&motiveCursor->node);
            if (!sortNode) {
                throw ElaborateError(
                    "internal: inner-recursor motive's type doesn't "
                    "end in a Sort");
            }
            motiveLevel = sortNode->level;
        }

        std::string recursorName =
            innerInductiveName + "_recursor";
        const Declaration* recursorDecl =
            environment_.lookup(recursorName);
        const Recursor* recursorInfo = recursorDecl
            ? std::get_if<Recursor>(recursorDecl) : nullptr;
        if (!recursorInfo) {
            throw ElaborateError(
                "recursor '" + recursorName + "' not in environment");
        }
        bool recursorHasMotiveLevel =
            recursorInfo->universeParameters.size()
            > innerInductive->universeParameters.size();
        std::vector<LevelPointer> recursorUniverseArguments =
            indConstant->universeArguments;
        if (recursorHasMotiveLevel) {
            recursorUniverseArguments.push_back(motiveLevel);
        }

        // Build the case lambda. Step 1: bind the constructor's value
        // args; step 2: derive the post-beta motive type and peel its
        // Pi chain to bind the re-bound later positions; step 3:
        // recurse for the body inside that scope.
        std::vector<LocalBinder> caseLambdaBinders;
        std::vector<LocalBinder> caseBodyStack = bodyStack;
        for (size_t k = 0; k < ctorArgTypes.size(); ++k) {
            caseLambdaBinders.push_back(
                {ctorArgNames[k], ctorArgTypes[k]});
            caseBodyStack.push_back(
                {ctorArgNames[k], ctorArgTypes[k]});
        }
        // ctor_app : the constructor applied to (parameters, then
        // its just-bound value args), in caseBodyStack scope. Parameter
        // values lived in bodyStack scope; shift by ctorArgTypes.size()
        // to put them in caseBodyStack scope (which has the ctor-arg
        // binders above bodyStack).
        ExpressionPointer ctorApp = makeConstant(
            expectedCtorName, indConstant->universeArguments);
        for (const auto& paramValue : innerParameterValues) {
            ctorApp = makeApplication(
                ctorApp,
                shift(paramValue,
                       static_cast<int>(ctorArgTypes.size())));
        }
        for (size_t k = 0; k < ctorArgTypes.size(); ++k) {
            int ctorArgDB =
                static_cast<int>(ctorArgTypes.size()) - 1
                - static_cast<int>(k);
            ctorApp = makeApplication(
                ctorApp, makeBoundVariable(ctorArgDB));
        }
        // Beta-reduce motive(ctor_app). The motive's body lives in
        // scope [bodyStack..., L_p] (its Lambda binder); shift by
        // ctorArgTypes.size() with cutoff 1 so bodyStack refs move
        // into caseBodyStack but L_p (Bound 0) stays as the
        // substitution target.
        ExpressionPointer shiftedMotiveBody = shift(
            motiveChainBody,
            static_cast<int>(ctorArgTypes.size()),
            /*cutoff=*/1);
        ExpressionPointer caseBodyType =
            substitute(shiftedMotiveBody, 0, ctorApp);

        std::vector<size_t> newPositionToBinderIndex;
        for (size_t k = 0; k < laterTypesBs.size(); ++k) {
            auto* pi = std::get_if<Pi>(&caseBodyType->node);
            if (!pi) {
                throw ElaborateError(
                    "internal: inner-recursor case body type is "
                    "missing a Pi for position "
                    + std::to_string(nextCtorPos + 1 + k));
            }
            newPositionToBinderIndex.push_back(
                caseLambdaBinders.size());
            caseLambdaBinders.push_back(
                {laterNames[k], pi->domain});
            caseBodyStack.push_back(
                {laterNames[k], pi->domain});
            caseBodyType = pi->codomain;
        }

        ExpressionPointer innerBody = buildBodyForCase(
            matchedCase,
            nextCtorPos + 1,
            newPositionToBinderIndex,
            caseLambdaBinders,
            caseBodyStack,
            caseBodyType,
            outerBinderCount,
            recursiveArgToHypothesis,
            declarationName);

        ExpressionPointer caseLambdaExpr = innerBody;
        for (auto it = caseLambdaBinders.rbegin();
             it != caseLambdaBinders.rend(); ++it) {
            caseLambdaExpr = makeLambda(
                it->name, it->type, std::move(caseLambdaExpr));
        }

        // Inner recursor application: parameters, motive, case
        // lambda, scrutinee ref, then later position refs (which
        // "unpack" the motive's Pi chain back into the expectedType).
        ExpressionPointer applied = makeConstant(
            recursorName, recursorUniverseArguments);
        for (const auto& paramValue : innerParameterValues) {
            applied = makeApplication(applied, paramValue);
        }
        applied = makeApplication(applied, motive);
        applied = makeApplication(applied, caseLambdaExpr);
        applied = makeApplication(applied,
                                   makeBoundVariable(scrutineeDB));
        for (int db : laterDBs) {
            applied = makeApplication(applied,
                                       makeBoundVariable(db));
        }
        return applied;
    }

    // Walks a surface expression and replaces calls of the form
    // `thisDeclName(<outerBinders>..., <destructuredName>, ...rest)`
    // with `<recursionHypothesis>(...rest)`, where the mapping
    // `destructuredName → recursionHypothesis` is determined by the
    // case currently being translated. `outerBinderCount` is the
    // number of pre-colon arguments the user must repeat in every
    // recursive call before the scrutinee. Non-recursive calls (or
    // recursive calls on something other than a destructured variable
    // at the right position) are left alone — the kernel will reject
    // them as ill-typed if structural recursion was actually required.
    SurfaceExpressionPointer rewriteRecursiveCalls(
        SurfaceExpressionPointer expression,
        const std::string& thisDeclName,
        const std::map<std::string, std::string>&
            recursiveArgToHypothesis,
        int outerBinderCount) {

        const SurfaceExpression& node = *expression;
        if (auto* application =
                std::get_if<SurfaceApplication>(&node.node)) {
            // Recurse into function and arguments first.
            auto rewrittenFunction = rewriteRecursiveCalls(
                application->function, thisDeclName,
                recursiveArgToHypothesis, outerBinderCount);
            std::vector<SurfaceArgument> rewrittenArguments;
            for (const auto& argument : application->arguments) {
                SurfaceArgument rewritten;
                rewritten.name = argument.name;
                rewritten.value = rewriteRecursiveCalls(
                    argument.value, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount);
                rewrittenArguments.push_back(std::move(rewritten));
            }
            // Check if this is a recursive call we should rewrite.
            // The scrutinee sits at index `outerBinderCount` (after
            // the user has typed out the outer binders).
            auto* functionIdentifier = std::get_if<SurfaceIdentifier>(
                &application->function->node);
            if (functionIdentifier
                && functionIdentifier->qualifiedName == thisDeclName
                && functionIdentifier->universeArgs.empty()
                && static_cast<int>(rewrittenArguments.size())
                       > outerBinderCount) {
                auto* scrutineeArgumentIdentifier =
                    std::get_if<SurfaceIdentifier>(
                        &rewrittenArguments[outerBinderCount].value->node);
                if (scrutineeArgumentIdentifier
                    && scrutineeArgumentIdentifier->universeArgs.empty()) {
                    auto iterator = recursiveArgToHypothesis.find(
                        scrutineeArgumentIdentifier->qualifiedName);
                    if (iterator != recursiveArgToHypothesis.end()) {
                        // Replace head with the recursion hypothesis,
                        // dropping the outer-binder arguments and the
                        // scrutinee (the recursor handles them implicitly).
                        auto hypothesisIdentifier =
                            makeSurfaceIdentifier(iterator->second, {},
                                                   node.line, node.column);
                        std::vector<SurfaceArgument>
                            remainingArguments(
                                rewrittenArguments.begin()
                                    + outerBinderCount + 1,
                                rewrittenArguments.end());
                        if (remainingArguments.empty()) {
                            return hypothesisIdentifier;
                        }
                        return makeSurfaceApplication(
                            hypothesisIdentifier,
                            std::move(remainingArguments),
                            node.line, node.column);
                    }
                }
            }
            return makeSurfaceApplication(std::move(rewrittenFunction),
                                           std::move(rewrittenArguments),
                                           node.line, node.column);
        }
        if (auto* piType = std::get_if<SurfacePiType>(&node.node)) {
            return makeSurfacePiType(
                {piType->binder.names,
                 rewriteRecursiveCalls(piType->binder.type, thisDeclName,
                                        recursiveArgToHypothesis,
                                        outerBinderCount)},
                rewriteRecursiveCalls(piType->codomain, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&node.node)) {
            return makeSurfaceLambda(
                {lambda->binder.names,
                 rewriteRecursiveCalls(lambda->binder.type, thisDeclName,
                                        recursiveArgToHypothesis,
                                        outerBinderCount)},
                rewriteRecursiveCalls(lambda->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* let = std::get_if<SurfaceLet>(&node.node)) {
            return makeSurfaceLet(
                let->name,
                rewriteRecursiveCalls(let->type, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(let->value, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(let->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* ascription = std::get_if<SurfaceAscription>(&node.node)) {
            return makeSurfaceAscription(
                rewriteRecursiveCalls(ascription->expression,
                                       thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(ascription->type, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&node.node)) {
            return makeSurfaceBinaryOperation(
                binary->opSymbol,
                rewriteRecursiveCalls(binary->left, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(binary->right, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* unary = std::get_if<SurfaceUnaryOperation>(&node.node)) {
            return makeSurfaceUnaryOperation(
                unary->opSymbol,
                rewriteRecursiveCalls(unary->operand, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* cases = std::get_if<SurfaceCases>(&node.node)) {
            auto rewrittenScrutinee = rewriteRecursiveCalls(
                cases->scrutinee, thisDeclName,
                recursiveArgToHypothesis, outerBinderCount);
            std::vector<SurfaceCasesClause> rewrittenClauses;
            for (const auto& clause : cases->clauses) {
                SurfaceCasesClause rewrittenClause;
                rewrittenClause.pattern = clause.pattern;
                rewrittenClause.body = rewriteRecursiveCalls(
                    clause.body, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount);
                rewrittenClause.line = clause.line;
                rewrittenClause.column = clause.column;
                rewrittenClauses.push_back(std::move(rewrittenClause));
            }
            if (cases->equalityHypothesisName.empty()
                && cases->refiningNames.empty()) {
                return makeSurfaceCases(std::move(rewrittenScrutinee),
                                         std::move(rewrittenClauses),
                                         node.line, node.column);
            }
            return makeSurfaceCasesWithRefining(
                std::move(rewrittenScrutinee),
                std::move(rewrittenClauses),
                cases->equalityHypothesisName,
                cases->refiningNames,
                node.line, node.column);
        }
        if (auto* claim = std::get_if<SurfaceStructuredClaim>(&node.node)) {
            // Anonymous `claim T by V;` desugars to a SurfaceLet whose
            // value is this SurfaceStructuredClaim. Without recursing
            // through the claim's sub-expressions, a recursive call
            // sitting in `byHint` (or in `proposition` / an arm) would
            // survive untouched and trip the kernel's "undefined
            // constant: <thisDeclName>" check at elaboration time. See
            // QUIRK.md (claim-anonymous-self-recursion) for the
            // historical context.
            SurfaceExpressionPointer rewrittenProposition =
                claim->proposition
                    ? rewriteRecursiveCalls(claim->proposition,
                                             thisDeclName,
                                             recursiveArgToHypothesis,
                                             outerBinderCount)
                    : nullptr;
            SurfaceExpressionPointer rewrittenByHint =
                claim->byHint
                    ? rewriteRecursiveCalls(claim->byHint,
                                             thisDeclName,
                                             recursiveArgToHypothesis,
                                             outerBinderCount)
                    : nullptr;
            std::vector<SurfaceStructuredClaimArm> rewrittenArms;
            for (const auto& arm : claim->arms) {
                SurfaceStructuredClaimArm rewrittenArm;
                rewrittenArm.disjunctType = arm.disjunctType
                    ? rewriteRecursiveCalls(arm.disjunctType,
                                             thisDeclName,
                                             recursiveArgToHypothesis,
                                             outerBinderCount)
                    : nullptr;
                rewrittenArm.binderName = arm.binderName;
                rewrittenArm.body = arm.body
                    ? rewriteRecursiveCalls(arm.body, thisDeclName,
                                             recursiveArgToHypothesis,
                                             outerBinderCount)
                    : nullptr;
                rewrittenArm.line = arm.line;
                rewrittenArm.column = arm.column;
                rewrittenArms.push_back(std::move(rewrittenArm));
            }
            auto rewrittenNode = makeSurfaceStructuredClaim(
                std::move(rewrittenProposition),
                claim->label,
                std::move(rewrittenByHint),
                claim->byCases,
                std::move(rewrittenArms),
                node.line, node.column,
                claim->byInduction,
                claim->bySubstitution);
            return rewrittenNode;
        }
        if (auto* calc = std::get_if<SurfaceCalc>(&node.node)) {
            auto rewrittenInitial = rewriteRecursiveCalls(
                calc->initialExpression, thisDeclName,
                recursiveArgToHypothesis, outerBinderCount);
            std::vector<SurfaceCalcStep> rewrittenSteps;
            for (const auto& step : calc->steps) {
                SurfaceCalcStep rewrittenStep;
                rewrittenStep.relation = step.relation;
                rewrittenStep.nextExpression = rewriteRecursiveCalls(
                    step.nextExpression, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount);
                rewrittenStep.stepProof = rewriteRecursiveCalls(
                    step.stepProof, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount);
                rewrittenStep.line = step.line;
                rewrittenStep.column = step.column;
                rewrittenSteps.push_back(std::move(rewrittenStep));
            }
            return makeSurfaceCalc(std::move(rewrittenInitial),
                                    std::move(rewrittenSteps),
                                    node.line, node.column);
        }
        // Atomic forms (identifier, numeric literal, Type, Proposition,
        // hammer placeholder) carry no sub-expressions and are unchanged.
        return expression;
    }

    void elaborateInductive(const SurfaceInductiveDeclaration& declaration) {
        Frame frame(*this, "inductive '" + declaration.name + "'");
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();

        // Build the kind: parameter Pis wrapped around the surface kind.
        std::vector<LocalBinder> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            parameterBinders;
        for (const auto& binder : declaration.parameters) {
            ExpressionPointer parameterType =
                elaborateExpression(*binder.type, localBinders);
            for (const auto& name : binder.names) {
                parameterBinders.push_back({name, parameterType});
                localBinders.push_back({name, parameterType});
                if (&name != &binder.names.back()) {
                    parameterType = elaborateExpression(*binder.type,
                                                         localBinders);
                }
            }
        }
        ExpressionPointer kindBody =
            elaborateExpression(*declaration.kind, localBinders);

        ExpressionPointer fullKind = kindBody;
        for (auto iterator = parameterBinders.rbegin();
             iterator != parameterBinders.rend(); ++iterator) {
            fullKind = makePi(iterator->first, iterator->second, fullKind);
        }

        // Constructors. Each constructor's type may reference the
        // inductive being declared and the parameters; we elaborate in
        // the parameter-extended context already built for the kind,
        // then wrap with parameter Pis using the same kernel types we
        // computed for the kind. Reusing the kind's localBinders /
        // parameterBinders avoids re-elaborating parameter types (which
        // would create fresh universe metavariables and decouple the
        // constructors' references to the parameters from the kind's).
        std::vector<ConstructorSpec> kernelConstructors;
        for (const auto& constructorSpec : declaration.constructors) {
            ExpressionPointer constructorBody =
                elaborateExpression(*constructorSpec.type, localBinders);
            ExpressionPointer fullConstructorType = constructorBody;
            for (auto iterator = parameterBinders.rbegin();
                 iterator != parameterBinders.rend(); ++iterator) {
                fullConstructorType = makePi(iterator->first,
                                              iterator->second,
                                              fullConstructorType);
            }
            kernelConstructors.push_back({constructorSpec.name,
                                           fullConstructorType});
        }

        int numParameters = 0;
        for (const auto& binder : declaration.parameters) {
            numParameters += static_cast<int>(binder.names.size());
        }
        try {
            addInductive(environment_, declaration.name,
                         finalUniverseParameters(declaration.universeParameters),
                         fullKind, numParameters,
                         std::move(kernelConstructors));
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }

        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

    // -------- expression elaboration --------

    // Convert a list of SurfaceArguments (possibly with names) into a
    // positional list of SurfaceExpressionPointers, reordering named
    // arguments against the function's parameter-binder names. The
    // result is what the rest of the application-dispatch logic
    // expects (a positional vector).
    //
    // Rules:
    //   * If no argument has a name, return the values unchanged.
    //   * If any argument has a name, look up the function head's
    //     declaration in the environment and walk its kernel-Pi-chain
    //     `displayHint`s. The displayHints — minus the implicit-arg
    //     prefix the user's positional count implies — are the
    //     parameter names users can reference.
    //   * Positional arguments and named arguments may be mixed:
    //     positional arguments fill slots in order, named arguments
    //     take their named slot. Duplicate assignments are an error.
    //
    // On any inability to find the parameter names (head isn't a
    // direct identifier, declaration not in env, anonymous binders),
    // mixed positional+named falls back to positional-only by
    // requiring all arguments to be positional.
    std::vector<SurfaceExpressionPointer> reorderArgumentsForCall(
        const std::vector<SurfaceArgument>& arguments,
        SurfaceExpressionPointer functionSurface,
        int line) {
        // Fast path: all positional. Just unwrap.
        bool anyNamed = false;
        for (const auto& a : arguments) {
            if (!a.name.empty()) { anyNamed = true; break; }
        }
        if (!anyNamed) {
            std::vector<SurfaceExpressionPointer> result;
            result.reserve(arguments.size());
            for (const auto& a : arguments) result.push_back(a.value);
            return result;
        }
        // Named-argument resolution. Look up the function's parameter
        // names by walking the kernel type's Pi chain.
        auto* headIdentifier = std::get_if<SurfaceIdentifier>(
            &functionSurface->node);
        if (!headIdentifier) {
            throwElaborate(
                "named arguments require a direct identifier as the "
                "function head (got a more complex expression at line "
                + std::to_string(line) + ")");
        }
        const Declaration* declaration =
            environment_.lookup(headIdentifier->qualifiedName);
        if (!declaration) {
            throwElaborate(
                "named arguments: function '"
                + headIdentifier->qualifiedName
                + "' is not in scope");
        }
        ExpressionPointer kernelType = declarationType(*declaration);
        std::vector<std::string> parameterNames;
        {
            ExpressionPointer cursor = kernelType;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                parameterNames.push_back(pi->displayHint);
                cursor = pi->codomain;
            }
        }
        // Determine the "user-facing" parameter window. If the
        // function has registered implicit-argument count K, skip the
        // first K parameters. The remaining parameters' names are what
        // the user can reference.
        int implicitCount = environment_.implicitArgumentCount(
            headIdentifier->qualifiedName);
        if (implicitCount > static_cast<int>(parameterNames.size())) {
            implicitCount =
                static_cast<int>(parameterNames.size());
        }
        std::vector<std::string> userParamNames(
            parameterNames.begin() + implicitCount,
            parameterNames.end());
        size_t argCount = arguments.size();
        if (argCount > userParamNames.size()) {
            throwElaborate(
                "named arguments: function '"
                + headIdentifier->qualifiedName
                + "' has "
                + std::to_string(userParamNames.size())
                + " user-facing parameters but call supplies "
                + std::to_string(argCount));
        }
        // Two windows to try: the PREFIX [0..argCount) and the SUFFIX
        // [size-argCount..size). Prefix wins for fully-applied calls
        // and for explicit-parameter calls; suffix wins for desugared
        // calls (Quotient.sound, Quotient.mk, etc.) where the user
        // supplies only the trailing explicit parameters. Pick the
        // window that accepts every named argument; if both, prefix
        // wins as the more general default.
        std::vector<std::string> namesSupplied;
        for (const auto& a : arguments) {
            if (!a.name.empty()) namesSupplied.push_back(a.name);
        }
        auto windowAccepts =
            [&](size_t windowStart) -> bool {
                for (const auto& name : namesSupplied) {
                    bool found = false;
                    for (size_t i = 0; i < argCount; ++i) {
                        if (userParamNames[windowStart + i] == name) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) return false;
                }
                return true;
            };
        size_t windowStart = 0;
        bool prefixAccepts = windowAccepts(0);
        size_t suffixStart = userParamNames.size() - argCount;
        bool suffixAccepts =
            (suffixStart != 0) && windowAccepts(suffixStart);
        if (prefixAccepts) {
            windowStart = 0;
        } else if (suffixAccepts) {
            windowStart = suffixStart;
        } else {
            throwElaborate(
                "named arguments: no window of '"
                + headIdentifier->qualifiedName
                + "'s parameters matches the supplied names");
        }
        std::vector<SurfaceExpressionPointer> slots(
            argCount, SurfaceExpressionPointer{});
        std::vector<bool> slotFilled(argCount, false);
        // First pass: place named arguments.
        for (const auto& a : arguments) {
            if (a.name.empty()) continue;
            int paramIndex = -1;
            for (size_t i = 0; i < argCount; ++i) {
                if (userParamNames[windowStart + i] == a.name) {
                    paramIndex = static_cast<int>(i);
                    break;
                }
            }
            if (paramIndex < 0) {
                throwElaborate(
                    "named arguments: '"
                    + headIdentifier->qualifiedName
                    + "' has no parameter named '"
                    + a.name + "' in the resolved window");
            }
            if (slotFilled[paramIndex]) {
                throwElaborate(
                    "named arguments: parameter '"
                    + a.name + "' assigned twice");
            }
            slots[paramIndex] = a.value;
            slotFilled[paramIndex] = true;
        }
        // Second pass: positional arguments into the next unfilled
        // slot, in source order.
        size_t nextSlot = 0;
        for (const auto& a : arguments) {
            if (!a.name.empty()) continue;
            while (nextSlot < argCount && slotFilled[nextSlot]) {
                ++nextSlot;
            }
            if (nextSlot >= argCount) {
                throwElaborate(
                    "named arguments: too many positional arguments "
                    "after named-argument assignments");
            }
            slots[nextSlot] = a.value;
            slotFilled[nextSlot] = true;
            ++nextSlot;
        }
        return slots;
    }

    // RAII guard pushing an expected type onto goalStack_ at entry
    // and popping it on exit. Used by elaborateExpression so the
    // `goal` keyword can resolve to the most-recent active expected
    // type without each caller having to thread it through.
    struct GoalScope {
        std::vector<ExpressionPointer>& stack;
        bool pushed;
        GoalScope(std::vector<ExpressionPointer>& s,
                  ExpressionPointer expectedType)
            : stack(s), pushed(false) {
            if (expectedType) {
                stack.push_back(expectedType);
                pushed = true;
            }
        }
        ~GoalScope() {
            if (pushed) stack.pop_back();
        }
    };

    ExpressionPointer elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType = nullptr) {

        GoalScope goalScope(goalStack_, expectedType);

        // `goal` — refers to the elaborator's current expected type.
        // Resolves to the most-recent push on goalStack_. Note: a
        // bare `goal` here uses the OUTER expected type (the one
        // active when this elaborateExpression was called) rather
        // than the one just pushed for this call, because we want
        // the value of the surrounding goal, not the type of the
        // SurfaceGoal node itself.
        if (std::holds_alternative<SurfaceGoal>(expression.node)) {
            // Walk past the just-pushed frame (if any) to find the
            // surrounding goal.
            int top = static_cast<int>(goalStack_.size()) - 1;
            if (goalScope.pushed) top -= 1;
            if (top < 0) {
                throwElaborate(
                    "`goal` used where no expected type is "
                    "available — this position doesn't propagate "
                    "a goal from any enclosing context");
            }
            return goalStack_[top];
        }

        if (auto* unfold =
                std::get_if<SurfaceUnfold>(&expression.node)) {
            // Flip each named definition's opacity from Opaque to
            // Transparent and DEFER the restore until the enclosing
            // theorem / definition finishes (so the kernel's final
            // typecheck inside `addDefinition` also sees the unfolded
            // view). Names that don't refer to definitions are a
            // user error; fail loudly.
            for (const std::string& name : unfold->names) {
                auto it = environment_.declarations.find(name);
                if (it == environment_.declarations.end()) {
                    throwElaborate(
                        "unfold: no declaration named `" + name + "`");
                }
                auto* def = std::get_if<Definition>(&it->second);
                if (!def) {
                    throwElaborate(
                        "unfold: `" + name + "` is not a definition "
                        "(unfolding only applies to definitions; "
                        "axioms / inductives have no body)");
                }
                pendingOpacityRestores_.push_back(
                    {name, def->opacity});
                def->opacity = Opacity::Transparent;
            }
            // Reduction depends on opacity, and the kernel's WHNF /
            // isDefEq caches don't track that — drop them so a stale
            // TRUE result computed under opaque opacity doesn't fool
            // the body's equality checks under the new transparent
            // view (or vice versa on the restore).
            invalidateKernelCaches();
            return elaborateExpression(
                *unfold->body, localBinders, expectedType);
        }

        if (auto* identifier =
                std::get_if<SurfaceIdentifier>(&expression.node)) {
            // Special case: bare `reflexivity` with an expected
            // equality type closes the step by inferring the
            // argument. Reads as "by reflexivity" in math.
            if (identifier->qualifiedName == "reflexivity"
                && identifier->universeArgs.empty()
                && expectedType) {
                ExpressionPointer expectedOpened = openOverLocalBinders(
                    expectedType, localBinders, localBinders.size());
                ExpressionPointer expectedWhnf = weakHeadNormalForm(
                    environment_, expectedOpened);
                EqualityComponents goalComps;
                try {
                    goalComps = extractEqualityComponents(
                        expectedWhnf, "bare reflexivity",
                        expression.line);
                } catch (const ElaborateError&) {
                    return elaborateIdentifier(
                        *identifier, localBinders,
                        expression.line, expression.column);
                }
                // Build reflexivity.{u}(carrier, leftEndpoint). The
                // kernel checks left and right are def-equal.
                ExpressionPointer call = makeConstant(
                    "reflexivity",
                    {goalComps.carrierUniverseLevel});
                ExpressionPointer carrier = closeOverLocalBinders(
                    goalComps.carrierType, localBinders,
                    localBinders.size());
                ExpressionPointer leftEndpoint = closeOverLocalBinders(
                    goalComps.leftEndpoint, localBinders,
                    localBinders.size());
                call = makeApplication(
                    std::move(call), std::move(carrier));
                call = makeApplication(
                    std::move(call), std::move(leftEndpoint));
                return call;
            }
            return elaborateIdentifier(*identifier, localBinders,
                                        expression.line, expression.column);
        }
        if (auto* numeric =
                std::get_if<SurfaceNumericLiteral>(&expression.node)) {
            return elaborateNumericLiteral(*numeric, expression.line,
                                            expression.column);
        }
        if (auto* application =
                std::get_if<SurfaceApplication>(&expression.node)) {
            // A small family of identifier names is special-cased to
            // infer their typically-explicit arguments from the user-
            // supplied positional arguments.
            auto* headIdentifier = std::get_if<SurfaceIdentifier>(
                &application->function->node);
            // Reorder named arguments into positional order. If no
            // named arguments are present, the result is just the
            // positional values in their original order. After this
            // point, all downstream dispatch logic sees a uniform
            // positional argument list (`positionalArguments`).
            std::vector<SurfaceExpressionPointer> positionalArguments =
                reorderArgumentsForCall(
                    application->arguments,
                    application->function,
                    expression.line);
            if (headIdentifier && headIdentifier->universeArgs.empty()) {
                const std::string& name = headIdentifier->qualifiedName;
                size_t argumentCount = positionalArguments.size();
                if (name == "congruenceOf" && argumentCount == 2) {
                    return desugarCongruenceOf(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "reflexivity" && argumentCount == 1) {
                    return desugarReflexivity(
                        positionalArguments[0],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "Equality.symmetry" && argumentCount == 1) {
                    return desugarEqualitySymmetry(
                        positionalArguments[0],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "Equality.transitivity"
                    && argumentCount == 2) {
                    return desugarEqualityTransitivity(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "rewrite" && argumentCount == 1) {
                    return desugarRewrite(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "rewrite" && argumentCount == 2) {
                    return desugarRewriteTerm(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "simplify" && argumentCount >= 1) {
                    return desugarSimplify(
                        positionalArguments,
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "absurd" && argumentCount == 1) {
                    return desugarAbsurd(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                // Quotient operations with implicit `T, R` inference.
                // Each user-facing form takes the explicit value args
                // only; the carrier and equivalence are recovered from
                // those args' types via a small custom desugar (the
                // standard implicit-argument machinery doesn't play
                // well with the combined universe-polymorphism +
                // implicit-binder case for axioms).
                if (name == "Quotient.mk" && argumentCount == 1) {
                    return desugarQuotientMk(
                        positionalArguments[0],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.sound" && argumentCount == 3) {
                    return desugarQuotientSound(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.lift" && argumentCount == 3) {
                    return desugarQuotientLift(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Exists.eliminate" && argumentCount == 2) {
                    return desugarExistsEliminate(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "And.eliminate" && argumentCount == 2) {
                    return desugarAndEliminate(
                        positionalArguments[0],
                        positionalArguments[1],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Or.eliminate" && argumentCount == 3) {
                    return desugarOrEliminate(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.induct" && argumentCount == 3) {
                    return desugarQuotientInduct(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.induct_two" && argumentCount == 4) {
                    return desugarQuotientInductTwo(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        positionalArguments[3],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                if (name == "Quotient.induct_three" && argumentCount == 5) {
                    return desugarQuotientInductThree(
                        positionalArguments[0],
                        positionalArguments[1],
                        positionalArguments[2],
                        positionalArguments[3],
                        positionalArguments[4],
                        localBinders, expectedType,
                        expression.line, expression.column);
                }
                // Function-name overload resolution. When the head is
                // registered as an overload alias (via `overload alias
                // := F;`) and is not itself a regular declaration,
                // elaborate the arguments to infer their types, then
                // pick the unique candidate whose parameter-type
                // sequence matches.
                if (environment_.lookup(name) == nullptr) {
                    const std::vector<std::string>* candidates =
                        environment_.lookupOverloads(name);
                    if (candidates) {
                        return resolveOverloadedCall(
                            name, *candidates,
                            positionalArguments,
                            localBinders, expectedType,
                            expression.line, expression.column);
                    }
                }
                // Constructor parameter inference: if the head is a
                // constructor of a parameterised inductive and the user
                // supplied only the non-parameter arguments, infer the
                // parameter values from the value-argument types and
                // (when available) the expectedType.
                bool isCurrentDeclaration =
                    !currentDeclarationName_.empty()
                    && currentDeclarationName_ == name;
                const Declaration* environmentDeclaration =
                    environment_.lookup(name);
                if (!isCurrentDeclaration && environmentDeclaration) {
                    if (auto* constructor =
                            std::get_if<Constructor>(
                                environmentDeclaration)) {
                        const Declaration* inductiveLookup =
                            environment_.lookup(constructor->inductiveName);
                        const Inductive* inductive = inductiveLookup
                            ? std::get_if<Inductive>(inductiveLookup)
                            : nullptr;
                        if (inductive && inductive->numParameters > 0) {
                            int totalPiCount =
                                countLeadingPis(constructor->type);
                            int valueArgumentCount =
                                totalPiCount - inductive->numParameters;
                            if (static_cast<int>(argumentCount)
                                == valueArgumentCount) {
                                std::vector<LevelPointer> universeArguments =
                                    universeArgumentsForConstructorCall(
                                        *constructor, *inductive,
                                        expectedType);
                                return elaborateConstructorCallInferringParameters(
                                    *constructor, *inductive,
                                    positionalArguments,
                                    universeArguments, localBinders,
                                    expectedType, expression.line);
                            }
                        }
                    }
                }
                // Leading-argument inference for under-applied calls to
                // an Axiom or Definition (Theorem). When the user
                // supplies STRICTLY FEWER value arguments than the
                // declaration's total Pi count and an expectedType is
                // available, try to fill in the missing leading args
                // by backward-forward unification — the same machinery
                // constructor parameter inference uses.
                //
                // Engages only when:
                //   * argumentCount is between 1 and totalPiCount-1,
                //   * expectedType is non-null,
                //   * the declaration has no universe parameters OR
                //     the user supplied an explicit `.{...}` list of
                //     the right arity.
                // If inference cannot resolve every leading metavariable
                // we fall through to the partial-application path so the
                // user can still partially apply explicitly.
                if (!isCurrentDeclaration
                    && environmentDeclaration
                    && expectedType
                    && argumentCount > 0) {
                    ExpressionPointer declarationKernelType;
                    const std::vector<std::string>* declarationUniverseParams
                        = nullptr;
                    if (auto* axiom =
                            std::get_if<Axiom>(environmentDeclaration)) {
                        declarationKernelType = axiom->type;
                        declarationUniverseParams = &axiom->universeParameters;
                    } else if (auto* definition =
                                   std::get_if<Definition>(
                                       environmentDeclaration)) {
                        declarationKernelType = definition->type;
                        declarationUniverseParams =
                            &definition->universeParameters;
                    }
                    if (declarationKernelType) {
                        int totalPiCount =
                            countLeadingPis(declarationKernelType);
                        int declaredImplicitCount =
                            environment_.implicitArgumentCount(name);
                        // Two engagement modes:
                        //   (a) Declaration uses `{x : T}` implicit
                        //       binders. The user provides exactly the
                        //       explicit-arg count and we infer the
                        //       declared implicit prefix.
                        //   (b) Declaration has no implicit binders.
                        //       Fall back to arity-based inference:
                        //       under-applied calls infer the missing
                        //       leading args.
                        int numLeadingToInfer = 0;
                        if (declaredImplicitCount > 0) {
                            if (static_cast<int>(argumentCount)
                                == totalPiCount - declaredImplicitCount) {
                                numLeadingToInfer = declaredImplicitCount;
                            }
                        } else {
                            numLeadingToInfer =
                                totalPiCount
                                - static_cast<int>(argumentCount);
                        }
                        bool universesProvided =
                            declarationUniverseParams->empty()
                            || (headIdentifier->universeArgs.size()
                                == declarationUniverseParams->size());
                        bool explicitImplicitMode =
                            declaredImplicitCount > 0;
                        // Gate: in explicit-implicit mode we can infer
                        // universe args from value args (with skip), so
                        // we proceed even without `universesProvided`.
                        // In arity-based mode we keep the original gate
                        // to avoid changing behavior for under-applied
                        // polymorphic calls — Stage 2 handles those.
                        bool gateOk = explicitImplicitMode
                                      || universesProvided;
                        if (numLeadingToInfer > 0 && gateOk) {
                            // When the declaration uses explicit
                            // `{x : T}` binders, the user has
                            // committed to inference — any failure is
                            // a real error. When inference is engaged
                            // only via arity-based heuristics (the
                            // declaration has no implicit markers),
                            // we fall back to partial application so
                            // intentional under-application still
                            // works.
                            auto runInference = [&]() {
                                std::vector<LevelPointer> universeArguments;
                                if (!headIdentifier->universeArgs.empty()) {
                                    for (const auto& level :
                                         headIdentifier->universeArgs) {
                                        universeArguments.push_back(
                                            elaborateLevel(*level));
                                    }
                                } else if (!declarationUniverseParams
                                               ->empty()) {
                                    // No user-supplied `.{...}`, but the
                                    // declaration is universe-polymorphic.
                                    // Infer universes from the trailing
                                    // value args' types (skipping the
                                    // leading implicit binders the user
                                    // also didn't pass).
                                    std::vector<ExpressionPointer>
                                        valueArgsForUniverseInference;
                                    for (const auto& argumentSurface :
                                         positionalArguments) {
                                        try {
                                            valueArgsForUniverseInference
                                                .push_back(
                                                    elaborateExpression(
                                                        *argumentSurface,
                                                        localBinders));
                                        } catch (const ElaborateError&) {
                                            valueArgsForUniverseInference
                                                .push_back(nullptr);
                                        }
                                    }
                                    universeArguments =
                                        inferUniverseArguments(
                                            *environmentDeclaration,
                                            valueArgsForUniverseInference,
                                            localBinders,
                                            numLeadingToInfer);
                                }
                                ExpressionPointer instantiated =
                                    substituteUniverseLevels(
                                        declarationKernelType,
                                        *declarationUniverseParams,
                                        universeArguments);
                                CallInferenceResult inferred =
                                    inferLeadingArguments(
                                        name, instantiated,
                                        numLeadingToInfer,
                                        positionalArguments,
                                        localBinders, expectedType,
                                        "_callLeadingArgument_",
                                        expression.line);
                                ExpressionPointer head = makeConstant(
                                    name, universeArguments);
                                for (auto& leadingValue :
                                     inferred.leadingValues) {
                                    head = makeApplication(
                                        std::move(head),
                                        std::move(leadingValue));
                                }
                                for (auto& trailingValue :
                                     inferred.trailingValues) {
                                    head = makeApplication(
                                        std::move(head),
                                        std::move(trailingValue));
                                }
                                return head;
                            };
                            if (explicitImplicitMode) {
                                return runInference();
                            }
                            try {
                                return runInference();
                            } catch (const ElaborateError&) {
                                // Inference failed in arity-based
                                // mode — fall through to partial
                                // application.
                            }
                        }
                    }
                }
                // Stage 2 universe inference: if the head is a polymorphic
                // constant called without explicit `.{...}`, infer the
                // universe arguments by unifying the value arguments'
                // types against the declaration's parameter types.
                if (!isCurrentDeclaration
                    && environmentDeclaration
                    && universeParameterCount(*environmentDeclaration) > 0) {
                    std::vector<ExpressionPointer> valueArguments;
                    for (const auto& argumentSurface :
                         positionalArguments) {
                        valueArguments.push_back(elaborateExpression(
                            *argumentSurface, localBinders));
                    }
                    std::vector<LevelPointer> inferredUniverseArguments =
                        inferUniverseArguments(*environmentDeclaration,
                                                 valueArguments,
                                                 localBinders);
                    ExpressionPointer head = makeConstant(
                        name, inferredUniverseArguments);
                    for (auto& valueArgument : valueArguments) {
                        head = makeApplication(std::move(head),
                                                std::move(valueArgument));
                    }
                    return head;
                }
            }
            ExpressionPointer head =
                elaborateExpression(*application->function, localBinders);
            // Propagate the expected argument type to each argument
            // elaboration by walking the head's type. Lets constructor
            // parameter inference inside lambda-shaped arguments see
            // the right expected type (e.g. for the handler functions
            // passed to Or.eliminate / Exists.eliminate).
            ExpressionPointer headType;
            try {
                headType = weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(localBinders, head));
            } catch (...) {
                headType = nullptr;
            }
            for (const auto& argument : positionalArguments) {
                ExpressionPointer argumentExpectedType;
                if (headType) {
                    if (auto* pi =
                            std::get_if<Pi>(&headType->node)) {
                        argumentExpectedType = pi->domain;
                    }
                }
                ExpressionPointer argumentTerm =
                    elaborateExpression(*argument, localBinders,
                                         argumentExpectedType);
                // Diff-wrap and redundancy check on the argument too —
                // catches `f(congruenceOf(λ, P))` where bare `f(P)`
                // would work (e.g. `rewrite(congruenceOf(...), term)`
                // when the inner lemma alone has the equality shape
                // that diff inference can fit to `rewrite`'s expected
                // first-arg type).
                if (argumentExpectedType) {
                    argumentTerm = coerceToExpectedTypeViaDiff(
                        localBinders, argumentTerm,
                        argumentExpectedType);
                    checkRedundantCongruenceOfWrapper(
                        argument, localBinders, argumentExpectedType,
                        "function-call argument");
                }
                if (headType) {
                    if (auto* pi =
                            std::get_if<Pi>(&headType->node)) {
                        headType = weakHeadNormalForm(environment_,
                            substitute(pi->codomain, 0, argumentTerm));
                    } else {
                        headType = nullptr;
                    }
                }
                head = makeApplication(std::move(head),
                                        std::move(argumentTerm));
            }
            return head;
        }
        if (auto* piType = std::get_if<SurfacePiType>(&expression.node)) {
            return elaboratePiType(*piType, localBinders);
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&expression.node)) {
            return elaborateLambda(*lambda, localBinders, expectedType);
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            ExpressionPointer letType =
                elaborateExpression(*let->type, localBinders);
            // Pass the declared type as the expected type for the value
            // so bidirectional elaborators (cases, anonymous tuples,
            // hammer, calc) can use it — without this, `let h : T := ?;`
            // can't trigger the hammer's reflexivity-match etc.
            ExpressionPointer letValue =
                elaborateExpression(*let->value, localBinders, letType);
            // Diff-inference for non-calc equality coercion: covers
            // `claim X : succ(a) = succ(b) by eq` (desugars to a
            // SurfaceLet) without an explicit congruenceOf wrapper.
            letValue = coerceToExpectedTypeViaDiff(
                localBinders, letValue, letType);
            checkRedundantCongruenceOfWrapper(
                let->value, localBinders, letType,
                "let value");
            std::vector<LocalBinder> extended = localBinders;
            // Capture the value on the LocalBinder so downstream
            // openedContext builders can mark it as let-bound (enabling
            // ζ-reduction in isDefinitionallyEqual on the FreeVariable),
            // and so the auto-prover's structural matchers can ζ-unfold
            // when matching on the closed term.
            extended.push_back({let->name, letType, letValue});
            // Propagate expectedType to body (shifted for new binder).
            ExpressionPointer bodyExpectedType =
                expectedType ? shift(expectedType, 1) : nullptr;
            ExpressionPointer letBody =
                elaborateExpression(*let->body, extended,
                                     bodyExpectedType);
            // Surface-text unused-name check on every named SurfaceLet
            // (covers `let X := V;`, legacy `claim X : T by V;`, and
            // `calc … as X;` desugaring). The kernel-level BV(0) check
            // is too lenient here: a downstream auto-prover call that
            // consumes the binding by type-match registers as BV(0)
            // referenced, even though the user never typed X — in
            // which case the anonymous form would behave identically
            // and the name is dead weight. Surface-text catches that.
            // Anonymous synthesised names (prefix `_`) are skipped by
            // warnIfSurfaceNameUnused itself.
            if (let->body) {
                if (let->fromCalcAsBinding) {
                    // Specialised message: the fix is to drop the
                    // `as NAME` postfix, not the calc itself.
                    if (reportRedundantBy_
                        && !let->name.empty()
                        && let->name[0] != '_'
                        && !surfaceMentionsName(
                            *let->body, let->name)) {
                        std::cerr << "warning: " << moduleName_
                            << ":" << expression.line
                            << ":" << expression.column
                            << ": `calc ... as " << let->name
                            << "` is never textually referenced —"
                               " drop the `as " << let->name
                            << "` to use the anonymous `calc ...;`"
                               " form (downstream calc steps still"
                               " find this equation by type-match)\n";
                    }
                } else if (reportRedundantBy_
                           && !let->name.empty()
                           && let->name[0] != '_'
                           && !surfaceMentionsName(
                               *let->body, let->name)) {
                    // `let X := V;` / `claim X : T by V;` whose name
                    // is never typed in the body. Three ways to fix:
                    //   1. Drop the binding entirely (the value/claim
                    //      is dead — nothing in scope after needs it).
                    //   2. If the auto-prover is consuming it by type-
                    //      match, switch to the anonymous form
                    //      (`claim T by V;`) — same effect, no name.
                    //   3. If the claim is documentation only (for the
                    //      reader's benefit, not the kernel's), switch
                    //      to `note T;` — the auto-prover still has to
                    //      close it, but the intent is clearly
                    //      "observe that …" rather than "introduce a
                    //      named hypothesis."
                    std::cerr << "warning: " << moduleName_
                        << ":" << expression.line
                        << ":" << expression.column
                        << ": unused name `" << let->name
                        << "` introduced by let / claim binding —"
                           " drop it, or switch to anonymous form"
                           " (`claim T by V;`) if the auto-prover"
                           " consumes it, or to `note T;` if it's"
                           " for the reader\n";
                }
            }
            return makeLet(let->name, std::move(letType),
                           std::move(letValue), std::move(letBody));
        }
        if (auto* ascription =
                std::get_if<SurfaceAscription>(&expression.node)) {
            // Pass the ascribed type as the expected type so bidirectional
            // elaborators (cases, anonymous tuples, hammer, calc) can
            // use it.
            ExpressionPointer ascribedType =
                elaborateExpression(*ascription->type, localBinders);
            // Carrier-identity shortcut: `(0 : T)` / `(1 : T)` where T
            // is a known constant with `T.zero` / `T.one` declared
            // emit the carrier's named identity directly. Without
            // this, the ascription would coerce a Natural literal into
            // T, producing a chain like
            // `Integer.to_rational(Natural.to_integer(zero))` — equal
            // to `T.zero` definitionally but opaque to `ring` (and to
            // any structural-search auto-prover) because the surface
            // shape is no longer the literal `T.zero`. Only fires when
            // the ascribed expression is a BARE numeric literal (not a
            // sub-expression like `1 + d`), so existing
            // `((1 + d) : Integer)` style ascriptions keep their
            // Natural-then-coerce semantics.
            if (auto* numeric = std::get_if<SurfaceNumericLiteral>(
                    &ascription->expression->node)) {
                int value = std::stoi(numeric->digits);
                if (value == 0 || value == 1) {
                    ExpressionPointer cursor = ascribedType;
                    while (auto* application =
                               std::get_if<Application>(&cursor->node)) {
                        cursor = application->function;
                    }
                    if (auto* head =
                            std::get_if<Constant>(&cursor->node)) {
                        std::string constantName = head->name
                            + (value == 0 ? ".zero" : ".one");
                        if (environment_.lookup(constantName)
                            != nullptr) {
                            return makeConstant(constantName);
                        }
                    }
                }
            }
            ExpressionPointer inner =
                elaborateExpression(*ascription->expression,
                                     localBinders, ascribedType);

            // Ascription doubles as a coercion: if `inner`'s inferred
            // type doesn't match the ascribed type but a registered
            // coercion chain bridges them, compose the chain and
            // apply it. The registry is populated by `coercion (S, T)
            // := F;` declarations and transitively closed at
            // registration time, so direct and multi-hop coercions
            // alike are a single lookup here.
            //
            // When no coercion fires, fall through to returning
            // `inner` directly; any type mismatch surfaces at the
            // eventual use site, exactly as it did before.
            if (!environment_.coercionRegistry.empty()) {
                try {
                    ExpressionPointer innerTypeOpened =
                        inferTypeInLocalContext(localBinders, inner);
                    ExpressionPointer ascribedTypeOpened =
                        openOverLocalBinders(ascribedType, localBinders,
                                              localBinders.size());
                    Context coercionContext =
                        buildContextFromLocalBinders(localBinders);
                    if (isDefinitionallyEqual(environment_, coercionContext,
                                                innerTypeOpened,
                                                ascribedTypeOpened)) {
                        return inner;
                    }
                    // Search registry for a chain from inner's head
                    // type to the ascribed head type. We match by raw
                    // head Constant name (without delta-reducing the
                    // type): the registry is keyed on the source-level
                    // type name, e.g. `Integer`, not the unfolded
                    // `Quotient(...)`.
                    auto headName =
                        [&](ExpressionPointer type) -> std::string {
                            ExpressionPointer cursor = type;
                            // Peel applications to find the head.
                            while (true) {
                                if (auto* app =
                                        std::get_if<Application>(
                                            &cursor->node)) {
                                    cursor = app->function;
                                    continue;
                                }
                                break;
                            }
                            if (auto* c =
                                    std::get_if<Constant>(&cursor->node)) {
                                return c->name;
                            }
                            return std::string{};
                        };
                    std::string innerHead = headName(innerTypeOpened);
                    std::string ascribedHead = headName(ascribedTypeOpened);
                    if (!innerHead.empty() && !ascribedHead.empty()) {
                        auto entry = environment_.coercionRegistry.find(
                            std::make_tuple(innerHead, ascribedHead));
                        if (entry != environment_.coercionRegistry.end()) {
                            ExpressionPointer call = std::move(inner);
                            for (const auto& funcName : entry->second) {
                                call = makeApplication(
                                    makeConstant(funcName),
                                    std::move(call));
                            }
                            return call;
                        }
                    }
                } catch (const TypeError&) {
                    // Inner expression's type couldn't be inferred —
                    // fall back to the no-coercion path.
                }
            }
            return inner;
        }
        if (auto* typeExpression =
                std::get_if<SurfaceType>(&expression.node)) {
            LevelPointer level = elaborateLevel(*typeExpression->level);
            return makeType(std::move(level));
        }
        if (std::get_if<SurfaceProposition>(&expression.node)) {
            return makeProposition();
        }
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (binary->opSymbol == "=") {
                // Desugar `a = b` to `Equality.{u}(typeOfA, a, b)`.
                // The inferred type may contain Internal-origin FreeVars
                // introduced by our opening; close them back so the
                // resulting term is valid in the original context.
                ExpressionPointer leftKernel =
                    elaborateExpression(*binary->left, localBinders);
                ExpressionPointer leftTypeOpen =
                    inferTypeInLocalContext(localBinders, leftKernel);
                ExpressionPointer leftType = closeOverLocalBinders(
                    leftTypeOpen, localBinders, localBinders.size());
                // Pass leftType as expected type for the right side.
                // This lets `Quotient.mk(rep2)` (implicit T, R) back-
                // infer R from the carrier when the left side fixes it.
                ExpressionPointer rightKernel =
                    elaborateExpression(*binary->right, localBinders,
                                          leftType);
                LevelPointer universeLevel =
                    typeUniverseOf(localBinders, leftKernel);
                ExpressionPointer equalityReference =
                    makeConstant("Equality", {universeLevel});
                ExpressionPointer applied = makeApplication(
                    std::move(equalityReference), std::move(leftType));
                applied = makeApplication(std::move(applied),
                                           std::move(leftKernel));
                applied = makeApplication(std::move(applied),
                                           std::move(rightKernel));
                return applied;
            }
            // Negated relations: `a ≠ b` → `Not(a = b)`,
            // `a ≰ b` → `Not(a ≤ b)`, `a ∤ b` → `Not(a ∣ b)`. We
            // build the surface call to the positive relation and
            // recursively elaborate inside a `Not`.
            const std::string& sym = binary->opSymbol;
            const char* positive = nullptr;
            if (sym == "≠") positive = "=";
            else if (sym == "≰") positive = "≤";
            else if (sym == "∤") positive = "∣";
            if (positive) {
                if (environment_.lookup("Not") == nullptr) {
                    throw ElaborateError(
                        "operator '" + sym + "' requires `Not` in scope "
                        "(import Logic.basics) at line "
                        + std::to_string(expression.line));
                }
                SurfaceExpressionPointer positiveSurface =
                    makeSurfaceBinaryOperation(
                        positive, binary->left, binary->right,
                        expression.line, expression.column);
                ExpressionPointer positiveKernel =
                    elaborateExpression(*positiveSurface, localBinders);
                ExpressionPointer notCall = makeConstant("Not");
                return makeApplication(std::move(notCall),
                                        std::move(positiveKernel));
            }
            return desugarArithmeticOperator(
                binary->opSymbol, *binary->left, *binary->right,
                localBinders, expectedType, expression.line);
        }
        if (auto* unary =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            if (unary->opSymbol == "¬") {
                if (environment_.lookup("Not") == nullptr) {
                    throw ElaborateError(
                        "unary operator '¬' requires `Not` in scope "
                        "(import Logic.basics) at line "
                        + std::to_string(expression.line));
                }
                ExpressionPointer operandKernel =
                    elaborateExpression(*unary->operand, localBinders);
                ExpressionPointer call = makeConstant("Not");
                return makeApplication(std::move(call),
                                        std::move(operandKernel));
            }
            if (unary->opSymbol == "-") {
                // Dispatch unary `-` based on the operand's head type:
                // Integer.negate / Rational.negate / etc. If the raw
                // head type doesn't have a `.negate`, try operand-type
                // names from the binary `-` registry whose definition
                // δ-reduces to the operand's actual type — same fallback
                // as the binary operator dispatch.
                //
                // Propagate the outer expected type to the operand
                // when it has a Constant head — `-` is type-preserving
                // for numeric carriers, so short-form `Quotient.mk(rep)`
                // can fire under it.
                ExpressionPointer operandExpectedType = nullptr;
                if (expectedType
                    && std::holds_alternative<Constant>(
                            expectedType->node)) {
                    operandExpectedType = expectedType;
                }
                ExpressionPointer operandKernel =
                    elaborateExpression(*unary->operand, localBinders,
                                         operandExpectedType);
                ExpressionPointer operandType =
                    inferTypeInLocalContext(localBinders, operandKernel);
                std::string operandTypeName =
                    headConstantName(operandType);
                std::string negateFunction;
                if (!operandTypeName.empty()
                    && environment_.lookup(operandTypeName + ".negate")
                       != nullptr) {
                    negateFunction = operandTypeName + ".negate";
                } else {
                    // Fallback: search definitions whose body δ-reduces
                    // to the operand's WHNF. For each such T, check if
                    // `<T>.negate` exists; if so, dispatch there. Catches
                    // operands whose raw head is `Quotient(...)` but
                    // whose intended type alias (e.g. `Integer`) has a
                    // `.negate`.
                    ExpressionPointer operandWHNF = weakHeadNormalForm(
                        environment_, operandType);
                    for (const auto& [name, declaration]
                         : environment_.declarations) {
                        auto* def =
                            std::get_if<Definition>(&declaration);
                        if (!def) continue;
                        ExpressionPointer bodyWHNF = weakHeadNormalForm(
                            environment_, def->body);
                        if (structurallyEqual(bodyWHNF, operandWHNF)) {
                            if (environment_.lookup(name + ".negate")
                                != nullptr) {
                                negateFunction = name + ".negate";
                                break;
                            }
                        }
                    }
                }
                if (negateFunction.empty()) {
                    throw ElaborateError(
                        "unary operator '-' on type '"
                        + operandTypeName
                        + "': no `<T>.negate` in scope (line "
                        + std::to_string(expression.line) + ")");
                }
                ExpressionPointer call = makeConstant(negateFunction);
                return makeApplication(std::move(call),
                                        std::move(operandKernel));
            }
            throw ElaborateError(
                "unary operator '" + unary->opSymbol + "' is not yet "
                "supported by the elaborator");
        }
        if (auto* tuple =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            return elaborateAnonymousTuple(*tuple, localBinders, expectedType,
                                            expression.line, expression.column);
        }
        if (auto* cases =
                std::get_if<SurfaceCases>(&expression.node)) {
            return elaborateCasesExpression(*cases, localBinders, expectedType,
                                             expression.line, expression.column);
        }
        if (std::get_if<SurfaceSorry>(&expression.node)) {
            return elaborateSorry(localBinders, expectedType,
                                   expression.line, expression.column);
        }
        if (auto* decide = std::get_if<SurfaceDecide>(&expression.node)) {
            return elaborateDecideExpression(
                *decide, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* note = std::get_if<SurfaceNote>(&expression.node)) {
            return elaborateNoteExpression(
                *note, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (std::get_if<SurfaceRing>(&expression.node)) {
            return elaborateRing(localBinders, expectedType,
                                  expression.line, expression.column);
        }
        if (auto* fieldTactic =
                std::get_if<SurfaceField>(&expression.node)) {
            return elaborateField(*fieldTactic, localBinders, expectedType,
                                   expression.line, expression.column);
        }
        if (auto* calc = std::get_if<SurfaceCalc>(&expression.node)) {
            return elaborateCalc(*calc, localBinders, expectedType,
                                  expression.line, expression.column);
        }
        if (auto* byInductionUsing =
                std::get_if<SurfaceByInductionUsing>(&expression.node)) {
            return elaborateByInductionUsing(
                *byInductionUsing, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* claim =
                std::get_if<SurfaceStructuredClaim>(&expression.node)) {
            return elaborateStructuredClaim(
                *claim, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* given =
                std::get_if<SurfaceGiven>(&expression.node)) {
            return elaborateGiven(
                *given, localBinders,
                expression.line, expression.column);
        }
        if (auto* choose =
                std::get_if<SurfaceChoose>(&expression.node)) {
            return elaborateChoose(
                *choose, localBinders, expectedType,
                expression.line, expression.column);
        }
        if (auto* strongInduction =
                std::get_if<SurfaceByStrongInduction>(&expression.node)) {
            return elaborateByStrongInduction(
                *strongInduction, localBinders, expectedType,
                expression.line, expression.column);
        }
        throw ElaborateError("unhandled surface expression variant");
    }

    // `by_strong_induction on E with subject, ih { body }` —
    // single-step strong induction. Extract the scrutinee's carrier
    // type, build `<CarrierTypeName>.strong_induction` as the
    // induction lemma, and dispatch to elaborateByInductionUsing.
    //
    // Carrier extraction: WHNF the scrutinee's type, peel
    // Application heads, expect a Constant at the spine. The
    // strong-induction lemma must live in the module that defines
    // the type and be named `<TypeName>.strong_induction`.
    ExpressionPointer elaborateByStrongInduction(
        const SurfaceByStrongInduction& form,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "by_strong_induction at line " + std::to_string(line));
        // First-pass scrutinee elaboration just to learn the type.
        // elaborateByInductionUsing will re-elaborate.
        ExpressionPointer scrutineeKernel = elaborateExpression(
            *form.scrutinee, localBinders);
        ExpressionPointer scrutineeTypeOpened = inferTypeInLocalContext(
            localBinders, scrutineeKernel);
        ExpressionPointer scrutineeTypeWhnf = weakHeadNormalForm(
            environment_, scrutineeTypeOpened);
        // Peel Application heads to find the spine constant.
        ExpressionPointer spineHead = scrutineeTypeWhnf;
        while (auto* app = std::get_if<Application>(&spineHead->node)) {
            spineHead = app->function;
        }
        auto* headConstant = std::get_if<Constant>(&spineHead->node);
        if (!headConstant) {
            throwElaborate(
                "by_strong_induction: scrutinee's type has no "
                "named carrier (head must be a constant like "
                "`Natural` or `Integer`)");
        }
        std::string lemmaName =
            headConstant->name + ".strong_induction";
        if (!environment_.lookup(lemmaName)) {
            throwElaborate(
                "by_strong_induction: no `" + lemmaName
                + "` in scope (expected the strong-induction "
                  "principle for carrier `" + headConstant->name
                + "` to be defined under that name; import the "
                  "module that provides it)");
        }
        // Build a SurfaceByInductionUsing wrapping the resolved
        // lemma name, then dispatch to existing logic.
        SurfaceExpressionPointer lemmaSurface = makeSurfaceIdentifier(
            std::move(lemmaName), {}, line, column);
        SurfaceByInductionUsing wrapped{
            form.scrutinee,
            std::move(lemmaSurface),
            form.subjectName,
            form.ihName,
            form.body};
        return elaborateByInductionUsing(
            wrapped, localBinders, expectedType, line, column);
    }

    // `choose <name> such that <predicate>;` — Exists-elim via scope
    // lookup. Scans local binders last-first for a hypothesis whose
    // type WHNFs to `Exists(T, motive)`; the most-recent match wins.
    // Desugars to a `cases ⟨<name>, _choice_pred_…⟩ => <body>` over
    // that hypothesis.
    //
    // v1: the user's predicate is documentation, not a search key —
    // if the most-recent Exists doesn't match what the user intended,
    // the body will fail to elaborate when it tries to use the
    // destructured predicate hypothesis. Predicate-shape filtering
    // is a planned follow-up.
    ExpressionPointer elaborateChoose(
        const SurfaceChoose& choose,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "choose " + choose.name + " at line "
            + std::to_string(line));
        int N = static_cast<int>(localBinders.size());
        int matchedIndex = -1;
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ExpressionPointer binderTypeInScope =
                liftBoundVariables(localBinders[b].type, lift, 0);
            ExpressionPointer binderTypeOpen = openOverLocalBinders(
                binderTypeInScope, localBinders, N);
            ExpressionPointer whnf = weakHeadNormalForm(
                environment_, binderTypeOpen);
            // Exists(T, motive) is App(App(Const "Exists"), T, motive).
            auto* outerApp = std::get_if<Application>(&whnf->node);
            if (!outerApp) continue;
            auto* innerApp = std::get_if<Application>(
                &outerApp->function->node);
            if (!innerApp) continue;
            auto* head = std::get_if<Constant>(
                &innerApp->function->node);
            if (!head || head->name != "Exists") continue;
            matchedIndex = b;
            break;
        }
        if (matchedIndex == -1) {
            throwElaborate(
                "choose " + choose.name + " such that <pred>: "
                "no in-scope hypothesis has type Exists(_, _). "
                "Prepend `claim Exists(...) by …;` to bring one "
                "into scope, or use `obtain ⟨…⟩ from …;` with an "
                "explicit source.");
        }
        // Unused-name warning: `choose N such that P(N);` then a
        // body that never mentions N is dead weight. Check at the
        // surface level (we destructure-and-elaborate below; the
        // post-elaboration body is wrapped in two Lambdas, making
        // a kernel BV check awkward to phrase here). Suppress if the
        // body contains an auto-prover-using construct (structured
        // claim, contradiction): the predicate hypothesis `P(N)` is
        // in scope and the auto-prover may consult it without N
        // appearing in surface syntax — using N transitively through
        // the predicate's type.
        if (choose.body
            && !surfaceContainsAutoProverInvocation(*choose.body)) {
            warnIfSurfaceNameUnused(
                choose.name, *choose.body, line, column,
                "`choose ... such that`");
        }
        // Build a SurfaceCases destructuring the matched hypothesis.
        SurfaceExpressionPointer scrutinee = makeSurfaceIdentifier(
            localBinders[matchedIndex].name, {}, line, column);
        std::string predHypName =
            "_choice_pred_" + std::to_string(line) + "_"
            + std::to_string(column);
        std::vector<SurfacePatternPointer> patternComponents;
        patternComponents.push_back(
            makeSurfacePatternBareName(
                choose.name, line, column));
        patternComponents.push_back(
            makeSurfacePatternBareName(
                std::move(predHypName), line, column));
        SurfacePatternPointer tuplePattern = makeSurfacePatternTuple(
            std::move(patternComponents), line, column);
        SurfaceCasesClause clause;
        clause.pattern = std::move(tuplePattern);
        clause.body = choose.body;
        clause.line = line;
        clause.column = column;
        std::vector<SurfaceCasesClause> clauses;
        clauses.push_back(std::move(clause));
        SurfaceExpressionPointer casesExpression = makeSurfaceCases(
            std::move(scrutinee), std::move(clauses), line, column);
        return elaborateExpression(
            *casesExpression, localBinders, expectedType);
    }

    // `by_induction on E using L with subject, ih { body }`:
    //   E    = local-variable scrutinee
    //   L    = induction lemma whose type is
    //              (motive : T → Sort u)
    //            → ((subject : T) → IH(subject) → motive subject)
    //            → (target : T) → motive target
    //   body = proves motive(subject), with subject and ih in scope
    //
    // Strategy: build the motive by abstracting expectedType over E,
    // apply the lemma to the motive (so the kernel substitutes it into
    // the remainder of the lemma's type), then decompose the
    // already-substituted type to extract the subject and ih binder
    // types. Then build the step lambda and finish the application.
    ExpressionPointer elaborateByInductionUsing(
        const SurfaceByInductionUsing& form,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "by_induction-using at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "by_induction needs an expected type from context");
        }
        ExpressionPointer scrutineeKernel = elaborateExpression(
            *form.scrutinee, localBinders);
        auto* boundVariable =
            std::get_if<BoundVariable>(&scrutineeKernel->node);
        if (!boundVariable
            || boundVariable->deBruijnIndex < 0
            || boundVariable->deBruijnIndex
                   >= static_cast<int>(localBinders.size())) {
            throwElaborate(
                "by_induction's scrutinee must be a local-binder "
                "variable (a parameter or let-binding name)");
        }
        int scrutineeDeBruijn = boundVariable->deBruijnIndex;
        int scrutineeArrayIndex =
            static_cast<int>(localBinders.size()) - 1
            - scrutineeDeBruijn;
        ExpressionPointer scrutineeType =
            localBinders[scrutineeArrayIndex].type;
        ExpressionPointer lemmaKernel = elaborateExpression(
            *form.inductionLemma, localBinders);

        // Build motive: Lambda(subjectName, T, expectedType[E := Bound 0]).
        ExpressionPointer motiveBody =
            abstractOverBoundVariables(expectedType, {scrutineeDeBruijn});
        ExpressionPointer motive = makeLambda(
            form.subjectName, scrutineeType, motiveBody);

        // Apply the motive to the lemma. The kernel computes the
        // remaining-arguments type, with motive already substituted.
        ExpressionPointer lemmaAppliedToMotive =
            makeApplication(lemmaKernel, motive);
        ExpressionPointer remainingType = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, lemmaAppliedToMotive));
        // remainingType should be:
        //   (step : (subject : T) → IH(subject) → motive(subject))
        //   → (target : T) → motive(target)
        auto* stepPi = std::get_if<Pi>(&remainingType->node);
        if (!stepPi) {
            throwElaborate(
                "induction lemma has no step argument after the motive");
        }
        ExpressionPointer stepType = weakHeadNormalForm(
            environment_, stepPi->domain);
        // stepType = (subject : T) → IH(subject) → motive(subject) —
        // all in OUR context now (motive is concrete, not bound).
        auto* stepSubjectPi = std::get_if<Pi>(&stepType->node);
        if (!stepSubjectPi) {
            throwElaborate(
                "induction lemma's step must begin with a subject "
                "argument (Pi)");
        }
        ExpressionPointer afterSubject = weakHeadNormalForm(
            environment_, stepSubjectPi->codomain);
        auto* stepIhPi = std::get_if<Pi>(&afterSubject->node);
        if (!stepIhPi) {
            throwElaborate(
                "induction lemma's step must have an ih argument after "
                "the subject");
        }
        ExpressionPointer ihTypeAfterSubject = stepIhPi->domain;
        // ihTypeAfterSubject is in a context with subject at Bound(0)
        // and our outer binders shifted by 1.

        // Build the step lambda. Body's local-binder context:
        // localBinders ++ [(subject, T), (ih, IH_in_body_context)].
        // In stepBinders, subject is Bound(1) and ih is Bound(0); the
        // outer binders are shifted accordingly.
        std::vector<LocalBinder> stepBinders = localBinders;
        stepBinders.push_back({form.subjectName, scrutineeType});
        stepBinders.push_back({form.ihName, ihTypeAfterSubject});
        // Body's expected type: motive(subject). motiveBody has
        // Bound(0) for "abstract subject"; we want Bound(1) (subject
        // in step body's context).
        ExpressionPointer bodyExpectedType = shift(motiveBody, 1);
        ExpressionPointer bodyKernel = elaborateExpression(
            *form.body, stepBinders, bodyExpectedType);
        ExpressionPointer ihLambda = makeLambda(
            form.ihName, ihTypeAfterSubject, bodyKernel);
        ExpressionPointer step = makeLambda(
            form.subjectName, scrutineeType, ihLambda);

        // Final: lemmaAppliedToMotive(step)(scrutinee).
        ExpressionPointer application =
            makeApplication(lemmaAppliedToMotive, std::move(step));
        application = makeApplication(std::move(application),
                                       std::move(scrutineeKernel));
        (void)column;
        return application;
    }

    // Step 2 of the structured-proof feature. Elaborates
    // `claim P [by Hint]` (and the bare-claim trailing form, where
    // the goal is the surrounding expectedType). Auto-fills the
    // hint's arguments by unifying its conclusion with the goal and
    // looking up any leftover binder values in local hypotheses.
    //
    // Limitations of v1:
    // - Disjunctive arms aren't elaborated yet (Step 4).
    // - `claim P` without `by` isn't elaborated yet (Step 5).
    // - Inter-slot dependencies: each slot's domain may reference
    //   outer slots that are bound by unification. Slots not bound
    //   by unification must be findable in local hypotheses by
    //   structural-type match.
    ExpressionPointer elaborateStructuredClaim(
        const SurfaceStructuredClaim& claim,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "claim at line " + std::to_string(line));

        if (claim.byCases) {
            return elaborateClaimByCases(
                claim, localBinders, expectedType, line);
        }

        // Resolve the goal proposition.
        ExpressionPointer goalClosed;
        if (claim.proposition) {
            goalClosed = elaborateExpression(
                *claim.proposition, localBinders);
        } else if (expectedType) {
            goalClosed = expectedType;
        } else {
            throwElaborate(
                "bare `claim` needs an expected type from context "
                "(none available — wrap the claim in `(claim : T)` "
                "or provide a proposition: `claim P [by Hint]`)");
        }

        if (!claim.byHint && !claim.bySubstitution) {
            return autoProveClaim(
                goalClosed, localBinders, line);
        }

        // `claim P by substitution` (no eq supplied) — call the
        // equality bridge directly. `claim P by substituting <eq>`
        // — narrow the bridge to the supplied equality (passed via
        // byHint).
        if (claim.bySubstitution) {
            return elaborateClaimBySubstitution(
                claim, goalClosed, localBinders, line);
        }

        // `claim P by induction on E …` — the byHint is the
        // SurfaceCases / SurfaceCasesWithRefining the parser
        // packaged from the `induction on E { case … }` tail.
        // Elaborate it with the resolved goal as the expected
        // type so the cases-block motive abstracts over E. No
        // autoFillHintForClaim pass: the cases form produces a
        // term of exactly the goal type when the arms cover the
        // constructors.
        if (claim.byInduction) {
            return elaborateExpression(
                *claim.byHint, localBinders, goalClosed);
        }

        // When the byHint is syntactically a lambda or a block (i.e.
        // a SurfaceLambda or a SurfaceLet chain), elaborate it WITH
        // the resolved goal as the expected type. Both shapes have
        // an inner expression — the lambda's body, the block's tail
        // — that may itself need an expected type to elaborate
        // (e.g. a nested bare `claim by cases`, which motive-
        // abstracts over its expected type). Without the propagation
        // the inner form has nothing to abstract over and errors.
        //
        // Other byHint shapes (applications, identifiers, etc.) keep
        // the no-expected-type path so `autoFillHintForClaim` can
        // peel a partial-application byHint's Pi chain and fill
        // missing args. Forcing expected type on a partial app would
        // make the kernel reject the Pi-typed result mid-elaboration,
        // before autoFillHintForClaim gets to bridge the gap.
        bool propagateExpectedTypeToHint =
            std::holds_alternative<SurfaceLambda>(claim.byHint->node)
            || std::holds_alternative<SurfaceLet>(claim.byHint->node);
        ExpressionPointer hintTerm = elaborateExpression(
            *claim.byHint, localBinders,
            propagateExpectedTypeToHint ? goalClosed : nullptr);
        // `inferTypeInLocalContext` returns an OPENED type;
        // `autoFillHintForClaim` expects closed form throughout
        // (matchAgainstPattern / instantiateLemmaBinders are
        // closed-form helpers).
        ExpressionPointer hintTypeOpened =
            inferTypeInLocalContext(localBinders, hintTerm);
        ExpressionPointer hintType = closeOverLocalBinders(
            hintTypeOpened, localBinders, localBinders.size());

        ExpressionPointer result = autoFillHintForClaim(
            hintTerm, hintType, goalClosed, localBinders, line);

        // `--check-redundant-by`: speculatively run the bare-`claim`
        // auto-prover on the same goal. If it would also discharge
        // the goal, warn that the hint is redundant.
        if (reportRedundantBy_) {
            ExpressionPointer autoAttempt;
            try {
                autoAttempt = autoProveClaim(
                    goalClosed, localBinders, line);
            } catch (const ElaborateError&) {
                autoAttempt = nullptr;
            } catch (const TypeError&) {
                autoAttempt = nullptr;
            }
            if (autoAttempt) {
                std::cerr << "warning: " << moduleName_
                    << ":" << line
                    << ": redundant `by` on `claim` — auto-prover"
                       " closes the goal without help\n";
            }
        }
        return result;
    }

    // Walks the Pi chain of `hintType`, unifies the conclusion with
    // `goalClosed`, fills remaining binders from local hypotheses,
    // and returns the resulting application of `hintTerm`. All
    // inputs and outputs are in closed-over-localBinders form.
    ExpressionPointer autoFillHintForClaim(
        ExpressionPointer hintTerm,
        ExpressionPointer hintType,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {

        // Reduce the goal so unification has a stable shape (the
        // goal can be the surrounding expectedType, which may carry
        // unreduced sugar like `LessOrEqual`-as-Constant).
        ExpressionPointer goalReduced = weakHeadNormalForm(
            environment_, goalClosed);
        ExpressionPointer hintTypeReduced = weakHeadNormalForm(
            environment_, hintType);

        // Fast path: hintType already matches the goal definitionally.
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer hintTypeOpened = openOverLocalBinders(
            hintType, localBinders, localBinders.size());
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        if (isSubtype(environment_, openedContext,
                      hintTypeOpened, goalOpened)) {
            return hintTerm;
        }

        // Peel Pi chain, collecting domains outermost-first and the
        // cursor at each peel depth.
        std::vector<ExpressionPointer> domainsOutermostFirst;
        std::vector<ExpressionPointer> cursorsAtDepth;
        cursorsAtDepth.push_back(hintTypeReduced);
        ExpressionPointer cursor = hintTypeReduced;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            domainsOutermostFirst.push_back(pi->domain);
            cursor = pi->codomain;
            cursorsAtDepth.push_back(cursor);
        }
        int totalBinders =
            static_cast<int>(domainsOutermostFirst.size());
        if (totalBinders == 0) {
            // No Pi's and not defeq: nothing more to try.
            throwElaborate(
                "the `by` hint's type doesn't match the goal "
                "(claimed `"
                + prettyPrintInLocalScope(goalClosed, localBinders)
                + "`, hint has type `"
                + prettyPrintInLocalScope(hintType, localBinders)
                + "`)");
        }

        // Try matching the goal at each peel depth, deepest first.
        // At depth k (0 ≤ k ≤ totalBinders) we've peeled k outermost
        // Pi's; the remaining cursor may still be a Pi (e.g., `Not(P)`
        // = `P → False` has an "extra" Pi past the explicit binders).
        // Bindings at depth k has size k; bindings[i] is the value
        // for BV(i) in cursorsAtDepth[k] (innermost peeled first).
        int matchedDepth = -1;
        std::vector<ExpressionPointer> bindings;
        for (int trialDepth = totalBinders;
             trialDepth >= 0 && matchedDepth == -1;
             --trialDepth) {
            std::vector<ExpressionPointer> trialReduced(trialDepth);
            if (matchAgainstPattern(
                    cursorsAtDepth[trialDepth], goalReduced,
                    trialDepth, trialReduced)) {
                matchedDepth = trialDepth;
                bindings = std::move(trialReduced);
                break;
            }
            std::vector<ExpressionPointer> trialUnreduced(trialDepth);
            if (matchAgainstPattern(
                    cursorsAtDepth[trialDepth], goalClosed,
                    trialDepth, trialUnreduced)) {
                matchedDepth = trialDepth;
                bindings = std::move(trialUnreduced);
                break;
            }
        }
        if (matchedDepth == -1) {
            throwElaborate(
                "the `by` hint's conclusion (`"
                + prettyPrintInLocalScope(
                      cursorsAtDepth[totalBinders], localBinders)
                + "`) does not unify with the goal (`"
                + prettyPrintInLocalScope(goalClosed, localBinders)
                + "`)");
        }

        // Fill any of the `matchedDepth` peeled-binder slots not
        // determined by unification by searching local binders for a
        // structurally-equal type. Process inner-binder-first
        // (bindings[0] is the innermost peeled) so a slot can depend
        // on outer slots that may already be bound. At depth k, the
        // outer slots are in domainsOutermostFirst[0..k-1] and
        // bindings[i] corresponds to position (matchedDepth - 1 - i).
        for (int innerIndex = 0; innerIndex < matchedDepth;
             ++innerIndex) {
            if (bindings[innerIndex]) continue;
            int outermostPosition = matchedDepth - 1 - innerIndex;
            ExpressionPointer domain =
                domainsOutermostFirst[outermostPosition];
            // The domain references outer binders. From the
            // perspective of the domain expression: BV(j) refers to
            // the binder at outermost position
            //   outermostPosition - 1 - j
            // i.e. innerIndex (in our bindings array) =
            //   totalBinders - 1 - (outermostPosition - 1 - j)
            //   = innerIndex + 1 + j.
            // So to use instantiateLemmaBinders (which uses
            // bindings[BV-index] = value), we build a local
            // permutation of the right slice.
            int outerSlotCount = outermostPosition;
            std::vector<ExpressionPointer> domainBindings(
                outerSlotCount);
            bool allOuterBound = true;
            for (int j = 0; j < outerSlotCount; ++j) {
                domainBindings[j] = bindings[innerIndex + 1 + j];
                if (!domainBindings[j]) {
                    allOuterBound = false;
                    break;
                }
            }
            if (!allOuterBound) {
                throwElaborate(
                    "can't infer the value of one of `by` hint's "
                    "arguments — the goal doesn't pin it down and "
                    "an outer argument it depends on is also "
                    "unbound");
            }
            ExpressionPointer expectedSlotType =
                instantiateLemmaBinders(domain, domainBindings);
            // Search local binders for one with this type. Each
            // binder's `.type` is in b-scope closed form (closed
            // over the binders that were in scope when it was
            // elaborated). To compare against `expectedSlotType`
            // (which lives in N-scope closed form), lift its BVs by
            // (N - b). Last-bound first (rightmost in localBinders)
            // so the most recent hypothesis wins ties.
            int N = static_cast<int>(localBinders.size());
            ExpressionPointer matchedTerm;
            for (int b = N - 1; b >= 0; --b) {
                int lift = N - b;
                ExpressionPointer binderTypeInScope =
                    liftBoundVariables(localBinders[b].type,
                                         lift, 0);
                if (structurallyEqual(binderTypeInScope,
                                        expectedSlotType)) {
                    matchedTerm = makeBoundVariable(N - 1 - b);
                    break;
                }
            }
            if (!matchedTerm) {
                throwElaborate(
                    "can't fill `by` hint argument of type `"
                    + prettyPrintInLocalScope(
                          expectedSlotType, localBinders)
                    + "` — no in-scope hypothesis matches it "
                    "structurally");
            }
            bindings[innerIndex] = matchedTerm;
        }

        // All bindings filled. Build the application: outermost
        // binder is bindings[matchedDepth - 1]. Only the matchedDepth
        // peeled binders get explicit applications — any remaining
        // inner Pi's of the lemma form part of the conclusion (which
        // matched the goal's Pi structure during unification) and
        // stay as-is in the resulting term's type.
        ExpressionPointer call = hintTerm;
        for (int p = 0; p < matchedDepth; ++p) {
            int innerIndex = matchedDepth - 1 - p;
            call = makeApplication(call, bindings[innerIndex]);
        }
        return call;
    }

    // Step 3 of the structured-proof feature. Elaborates `given (P)`
    // to a BoundVariable pointing at the unique in-scope hypothesis
    // of type `P`. Errors on zero matches or on ambiguity.
    ExpressionPointer elaborateGiven(
        const SurfaceGiven& given,
        const std::vector<LocalBinder>& localBinders,
        int line, int /*column*/) {
        Frame frame(*this,
            "given(...) at line " + std::to_string(line));
        ExpressionPointer requestedTypeClosed = elaborateExpression(
            *given.proposition, localBinders);
        int N = static_cast<int>(localBinders.size());
        int matchIndex = -1;
        int duplicateIndex = -1;
        // Use isDefinitionallyEqual rather than a structural compare:
        // hypotheses introduced by destructure desugarings (e.g.
        // `choose N such that P(N);`) carry their predicate type in
        // (lambda ...)(N) form before β; the user's `given(P(N))` is
        // β-reduced. Definitional equality bridges the gap.
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        ExpressionPointer requestedOpened = openOverLocalBinders(
            requestedTypeClosed, localBinders, N);
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ExpressionPointer binderTypeInScope =
                liftBoundVariables(localBinders[b].type, lift, 0);
            ExpressionPointer binderTypeOpened = openOverLocalBinders(
                binderTypeInScope, localBinders, N);
            if (isDefinitionallyEqual(environment_, openedContext,
                                        binderTypeOpened,
                                        requestedOpened)) {
                if (matchIndex == -1) {
                    matchIndex = b;
                } else {
                    duplicateIndex = b;
                    break;
                }
            }
        }
        if (matchIndex == -1) {
            throwElaborate(
                "given(`"
                + prettyPrintInLocalScope(
                      requestedTypeClosed, localBinders)
                + "`): no in-scope hypothesis matches this "
                "proposition structurally");
        }
        if (duplicateIndex != -1) {
            throwElaborate(
                "given(`"
                + prettyPrintInLocalScope(
                      requestedTypeClosed, localBinders)
                + "`): proposition is ambiguous — at least two "
                "in-scope hypotheses have this type ('"
                + localBinders[matchIndex].name
                + "' and '"
                + localBinders[duplicateIndex].name
                + "'); name one of them explicitly");
        }
        return makeBoundVariable(N - 1 - matchIndex);
    }

    // Contradiction: if the most-recent local binder is False, or
    // pairs with some other in-scope hypothesis to produce False
    // via h(h') (or h'(h)), close ANY goal via
    // `False.eliminate_proposition`.
    //
    // Restricted to the LAST local binder (cost 0 in the unified
    // cost model) as one of the pair — the mathematician's
    // convention is to write the contradictory fact as the
    // immediately-preceding `claim` and then conclude. Avoids
    // O(N²) pair search and the noise it would cause; the user
    // can always write the contradiction-introducing claim before
    // the close. Skipped if `False.eliminate_proposition` isn't
    // in scope or no local binders exist.
    ExpressionPointer tryContradiction(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {
        if (!environment_.lookup(
                "False.eliminate_proposition")) {
            return nullptr;
        }
        int N = static_cast<int>(localBinders.size());
        if (N == 0) return nullptr;
        int lastIdx = N - 1;
        int lastLift = N - lastIdx;
        ExpressionPointer lastTypeOpened = openOverLocalBinders(
            liftBoundVariables(
                localBinders[lastIdx].type, lastLift, 0),
            localBinders, N);
        // Pass 1: most-recent binder is itself `False`.
        {
            auto* asConst = std::get_if<Constant>(
                &lastTypeOpened->node);
            if (asConst && asConst->name == "False") {
                ExpressionPointer call = makeConstant(
                    "False.eliminate_proposition", {});
                call = makeApplication(call, goalClosed);
                call = makeApplication(
                    call,
                    makeBoundVariable(N - 1 - lastIdx));
                return call;
            }
        }
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        // Pass 2: (last, other) pair where one is `Not(P)` and the
        // other is `P`. Try BOTH orderings: last is Not(P) paired
        // with some other = P; or last is P paired with some other
        // = Not(P).
        auto buildProofOfFalse =
            [&](ExpressionPointer notHyp,
                ExpressionPointer pHyp) -> ExpressionPointer {
                ExpressionPointer call = makeConstant(
                    "False.eliminate_proposition", {});
                call = makeApplication(call, goalClosed);
                call = makeApplication(
                    call, makeApplication(notHyp, pHyp));
                return call;
            };
        // Case A: last : Not(P). Find some other : P.
        if (auto* pi =
                std::get_if<Pi>(&lastTypeOpened->node)) {
            auto* codomainConst = std::get_if<Constant>(
                &pi->codomain->node);
            if (codomainConst
                && codomainConst->name == "False") {
                ExpressionPointer expectedP = pi->domain;
                for (int other = N - 2; other >= 0; --other) {
                    int lift = N - other;
                    ExpressionPointer otherType =
                        openOverLocalBinders(
                            liftBoundVariables(
                                localBinders[other].type,
                                lift, 0),
                            localBinders, N);
                    if (isDefinitionallyEqual(
                            environment_, openedContext,
                            otherType, expectedP)) {
                        return buildProofOfFalse(
                            makeBoundVariable(
                                N - 1 - lastIdx),
                            makeBoundVariable(
                                N - 1 - other));
                    }
                }
            }
        }
        // Case B: last : P. Find some other : Not(P).
        for (int other = N - 2; other >= 0; --other) {
            int lift = N - other;
            ExpressionPointer otherType = openOverLocalBinders(
                liftBoundVariables(
                    localBinders[other].type, lift, 0),
                localBinders, N);
            auto* pi = std::get_if<Pi>(&otherType->node);
            if (!pi) continue;
            auto* codomainConst = std::get_if<Constant>(
                &pi->codomain->node);
            if (!codomainConst
                || codomainConst->name != "False") continue;
            if (!isDefinitionallyEqual(
                    environment_, openedContext,
                    pi->domain, lastTypeOpened)) continue;
            return buildProofOfFalse(
                makeBoundVariable(N - 1 - other),
                makeBoundVariable(N - 1 - lastIdx));
        }
        return nullptr;
    }

    // Disjunction introduction: when the goal is `Or(A, B)`, try
    // to prove `A` via the full auto-prover; if that succeeds, wrap
    // with `Or.introduceLeft`. Else try `B` and wrap with
    // `Or.introduceRight`. Left-biased — if both branches would
    // succeed, the left one wins.
    ExpressionPointer tryDisjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        auto* outerApp = std::get_if<Application>(&goalOpened->node);
        if (!outerApp) return nullptr;
        auto* innerApp = std::get_if<Application>(
            &outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head || head->name != "Or") return nullptr;
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer aClosed = closeOverLocalBinders(
            innerApp->argument, localBinders, N);
        ExpressionPointer bClosed = closeOverLocalBinders(
            outerApp->argument, localBinders, N);
        // Try Or.introduceLeft (prove A).
        if (environment_.lookup("Or.introduceLeft")) {
            ExpressionPointer proofA;
            try {
                proofA = autoProveClaim(
                    aClosed, localBinders, line);
            } catch (const ElaborateError&) { proofA = nullptr; }
              catch (const TypeError&) { proofA = nullptr; }
            if (proofA) {
                ExpressionPointer call = makeConstant(
                    "Or.introduceLeft", {});
                call = makeApplication(call, aClosed);
                call = makeApplication(call, bClosed);
                call = makeApplication(call, proofA);
                return call;
            }
        }
        // Fall through to Or.introduceRight (prove B).
        if (environment_.lookup("Or.introduceRight")) {
            ExpressionPointer proofB;
            try {
                proofB = autoProveClaim(
                    bClosed, localBinders, line);
            } catch (const ElaborateError&) { proofB = nullptr; }
              catch (const TypeError&) { proofB = nullptr; }
            if (proofB) {
                ExpressionPointer call = makeConstant(
                    "Or.introduceRight", {});
                call = makeApplication(call, aClosed);
                call = makeApplication(call, bClosed);
                call = makeApplication(call, proofB);
                return call;
            }
        }
        return nullptr;
    }

    // Unified named-fact representation. A fact carries a proof
    // term and that proof's type, plus a cost so the matcher tries
    // cheap facts first. Used by `tryContextFactMatch` to collapse
    // the old "(1) hypothesis match" and "(7) library scan"
    // strategies into one stream that doesn't care whether the
    // proof originated from a local binder or a top-level
    // declaration.
    struct ContextFact {
        int cost;
        std::string source;
        ExpressionPointer proofTerm;  // closed in current scope
        ExpressionPointer type;       // closed in current scope
    };

    std::vector<ContextFact> collectContextFacts(
        ExpressionPointer /*goalClosed*/,
        const std::vector<LocalBinder>& localBinders,
        uint64_t goalHash,
        uint64_t goalHashUnreduced) {
        std::vector<ContextFact> facts;
        int N = static_cast<int>(localBinders.size());
        // Local binders (cost 1) — last-bound first, so the most
        // recent fact wins on ties when the matcher returns.
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ContextFact fact;
            fact.cost = 1;
            fact.source = "local binder " + localBinders[b].name;
            fact.proofTerm = makeBoundVariable(N - 1 - b);
            fact.type = liftBoundVariables(
                localBinders[b].type, lift, 0);
            facts.push_back(std::move(fact));
        }
        // Library / module declarations (cost 3) — only those whose
        // conclusion's spine matches the goal's at SOME peel depth.
        // Match against BOTH the goal's WHNF-reduced spineHash AND
        // its un-reduced one: a lemma whose stated conclusion uses a
        // definitional alias (e.g. `Rational.LessOrEqual.reflexive :
        // x ≤ x` where `≤` unfolds to `IsNonneg(_ - _)`) is indexed
        // by the alias `LessOrEqual`, but the goal is WHNF'd to
        // `IsNonneg`, so a single-hash match misses it. Comparing
        // both un-reduced and reduced catches the lemma in either
        // direction.
        // Universe-polymorphic candidates are skipped (universe-arg
        // inference at use-site isn't wired up).
        for (const auto& entry : environment_.declarations) {
            const std::string& name = entry.first;
            const auto& declaration = entry.second;
            ExpressionPointer declarationType;
            size_t universeParamCount = 0;
            if (auto* def =
                    std::get_if<Definition>(&declaration)) {
                declarationType = def->type;
                universeParamCount =
                    def->universeParameters.size();
            } else if (auto* ax =
                           std::get_if<Axiom>(&declaration)) {
                declarationType = ax->type;
                universeParamCount =
                    ax->universeParameters.size();
            } else if (auto* ctor =
                           std::get_if<Constructor>(&declaration)) {
                declarationType = ctor->type;
                universeParamCount =
                    ctor->universeParameters.size();
            } else {
                continue;
            }
            if (universeParamCount != 0) continue;
            bool anyDepthMatches = false;
            ExpressionPointer depthCursor = declarationType;
            while (true) {
                uint64_t hashAtDepth = spineHash(depthCursor);
                if (hashAtDepth == goalHash
                    || hashAtDepth == goalHashUnreduced) {
                    anyDepthMatches = true;
                    break;
                }
                auto* pi = std::get_if<Pi>(&depthCursor->node);
                if (!pi) break;
                depthCursor = pi->codomain;
            }
            if (!anyDepthMatches) continue;
            ContextFact fact;
            fact.cost = 3;
            fact.source = "library " + name;
            fact.proofTerm = makeConstant(name, {});
            fact.type = declarationType;
            facts.push_back(std::move(fact));
        }
        return facts;
    }

    // Unified named-fact match. Iterates ALL in-scope facts (local
    // binders + library declarations) by cost; for each, tries
    // `autoFillHintForClaim` to fill any Pi-binders from the goal +
    // hypotheses and produce a term of the goal type. Subsumes the
    // old "direct hypothesis match" and "library scan" strategies.
    ExpressionPointer tryContextFactMatch(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalReduced = weakHeadNormalForm(
            environment_, goalClosed);
        uint64_t goalHash = spineHash(goalReduced);
        uint64_t goalHashUnreduced = spineHash(goalClosed);
        std::vector<ContextFact> facts = collectContextFacts(
            goalClosed, localBinders, goalHash, goalHashUnreduced);
        std::sort(facts.begin(), facts.end(),
            [](const ContextFact& a, const ContextFact& b) {
                return a.cost < b.cost;
            });
        for (const ContextFact& fact : facts) {
            try {
                return autoFillHintForClaim(
                    fact.proofTerm, fact.type, goalClosed,
                    localBinders, line);
            } catch (const ElaborateError&) {
                continue;
            } catch (const TypeError&) {
                continue;
            }
        }
        return nullptr;
    }

    // Unified equality fact representation. Both local-hypothesis
    // equalities and library-lemma equalities (after subexpression
    // match + instantiation) live here as already-ground
    // (lhs, rhs, carrier, proof) tuples in the current scope.
    // Cost-tagged so the bridge tries cheap facts first.
    struct ContextEquality {
        int cost;
        std::string source;
        ExpressionPointer lhs;
        ExpressionPointer rhs;
        ExpressionPointer carrierType;
        LevelPointer carrierLevel;
        ExpressionPointer proofExpr;
    };

    // Helper: walk goal subexpressions looking for library-lemma
    // matches; instantiate matched lemmas and append as ContextEquality
    // entries. Mirrors the old `tryLibraryRewriteBridge` walker's
    // safeguards (skip bare-BV subexprs and bare-BV patterns; only
    // Applications descended into).
    void collectLibraryEqualitiesAt(
        ExpressionPointer subexpr,
        const std::vector<LocalBinder>& localBinders,
        std::vector<ContextEquality>& out) {
        auto* app =
            std::get_if<Application>(&subexpr->node);
        if (!app) return;
        uint64_t key = spineHash(subexpr);
        auto range = lemmaIndex_.equal_range(key);
        for (auto iterator = range.first;
             iterator != range.second; ++iterator) {
            const RewriteLemma& lemma = iterator->second;
            ExpressionPointer pattern = lemma.reverseDirection
                ? lemma.rhs : lemma.lhs;
            if (std::holds_alternative<BoundVariable>(
                    pattern->node)) continue;
            std::vector<ExpressionPointer> bindings(
                lemma.binderCount);
            if (!matchAgainstPattern(
                    pattern, subexpr,
                    lemma.binderCount, bindings)) continue;
            bool allBound = true;
            for (auto& bn : bindings) {
                if (!bn) { allBound = false; break; }
            }
            if (!allBound) continue;
            ExpressionPointer lemmaApp = makeConstant(
                lemma.lemmaName, {});
            for (int i = lemma.binderCount - 1; i >= 0; --i) {
                lemmaApp = makeApplication(
                    lemmaApp, bindings[i]);
            }
            ExpressionPointer lemmaAppType;
            try {
                lemmaAppType = inferTypeInLocalContext(
                    localBinders, lemmaApp);
            } catch (const TypeError&) { continue; }
              catch (const ElaborateError&) { continue; }
            EqualityComponents components;
            try {
                components = extractEqualityComponents(
                    lemmaAppType, "library lemma", 0);
            } catch (const ElaborateError&) { continue; }
            // inferTypeInLocalContext returns the type in OPENED
            // form (FVars for the local binders); close it so the
            // components live in the same closed scope as goalClosed,
            // which is what abstractStructuralOccurrence + substitute
            // expect.
            int N = static_cast<int>(localBinders.size());
            ContextEquality eq;
            eq.cost = 3;
            eq.source = "library lemma " + lemma.lemmaName;
            eq.carrierType = closeOverLocalBinders(
                components.carrierType, localBinders, N);
            eq.lhs = closeOverLocalBinders(
                components.leftEndpoint, localBinders, N);
            eq.rhs = closeOverLocalBinders(
                components.rightEndpoint, localBinders, N);
            eq.carrierLevel = components.carrierUniverseLevel;
            eq.proofExpr = lemmaApp;
            out.push_back(std::move(eq));
        }
        // Recurse into Application children.
        collectLibraryEqualitiesAt(
            app->function, localBinders, out);
        collectLibraryEqualitiesAt(
            app->argument, localBinders, out);
    }

    std::vector<ContextEquality> collectContextEqualities(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {
        std::vector<ContextEquality> result;
        int N = static_cast<int>(localBinders.size());
        // Local hypotheses (cost 1) — scan last-bound first so the
        // most-recent equality wins on ties.
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ExpressionPointer hypInScope = liftBoundVariables(
                localBinders[b].type, lift, 0);
            ExpressionPointer hypReduced = weakHeadNormalForm(
                environment_, hypInScope);
            EqualityComponents components;
            try {
                components = extractEqualityComponents(
                    hypReduced, "local equality", 0);
            } catch (const ElaborateError&) { continue; }
            ContextEquality eq;
            eq.cost = 1;
            eq.source = "local binder " + localBinders[b].name;
            eq.carrierType = components.carrierType;
            eq.lhs = components.leftEndpoint;
            eq.rhs = components.rightEndpoint;
            eq.carrierLevel = components.carrierUniverseLevel;
            eq.proofExpr = makeBoundVariable(N - 1 - b);
            result.push_back(std::move(eq));
        }
        // Library lemmas matched against goal subexpressions
        // (cost 3) — walks Application subexpressions and queries
        // `lemmaIndex_` at each.
        collectLibraryEqualitiesAt(
            goalClosed, localBinders, result);
        return result;
    }

    // Unified context-equality bridge. For every equality in scope
    // (local or library, ground or instantiated), try rewriting the
    // goal by replacing one side with the other, recursing on the
    // rewritten goal. Replaces the two separate strategies (local
    // transport bridge and library-rewrite bridge) with one code
    // path so future migration of other strategies to the same
    // fact-stream model has a precedent. See TODO.md "Hammer
    // unification" for the broader plan.
    //
    // Walks structurally — recurses into Application children. Other
    // expression kinds (Pi, Lambda, Let, etc.) are walked only if
    // they're at the top, not descended; widening that is a follow-
    // up. Budget shared with both old bridges.
    ExpressionPointer tryContextEqualityBridge(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line, int budget) {
        if (budget == 0) return nullptr;
        std::vector<ContextEquality> equalities =
            collectContextEqualities(
                goalClosed, localBinders, line);
        std::sort(equalities.begin(), equalities.end(),
            [](const ContextEquality& a, const ContextEquality& b) {
                return a.cost < b.cost;
            });
        for (const ContextEquality& eq : equalities) {
            // Try both rewrite directions:
            //   direction 0: replace rhs in goal with lhs — uses eq
            //     directly (transport: motive(lhs) → motive(rhs)).
            //   direction 1: replace lhs in goal with rhs — uses
            //     symm(eq) (transport: motive(rhs) → motive(lhs)).
            for (int direction = 0; direction < 2; ++direction) {
                ExpressionPointer fromSide =
                    (direction == 0) ? eq.rhs : eq.lhs;
                ExpressionPointer toSide =
                    (direction == 0) ? eq.lhs : eq.rhs;
                int occurrences = 0;
                ExpressionPointer abstractedBody =
                    abstractStructuralOccurrence(
                        goalClosed, fromSide,
                        /*currentDepth=*/0, occurrences);
                if (occurrences == 0) continue;
                ExpressionPointer rewrittenGoal = substitute(
                    abstractedBody, 0, toSide);
                ExpressionPointer proofRewritten;
                try {
                    proofRewritten = autoProveClaim(
                        rewrittenGoal, localBinders,
                        line, budget - 1);
                } catch (const ElaborateError&) { continue; }
                  catch (const TypeError&) { continue; }
                ExpressionPointer motive = makeLambda(
                    "_rewriteHole",
                    eq.carrierType, abstractedBody);
                ExpressionPointer eqForTransport;
                ExpressionPointer transportLhs;
                ExpressionPointer transportRhs;
                if (direction == 0) {
                    eqForTransport = eq.proofExpr;
                    transportLhs = eq.lhs;
                    transportRhs = eq.rhs;
                } else {
                    eqForTransport = makeConstant(
                        "Equality.symmetry",
                        {eq.carrierLevel});
                    eqForTransport = makeApplication(
                        eqForTransport, eq.carrierType);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.lhs);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.rhs);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.proofExpr);
                    transportLhs = eq.rhs;
                    transportRhs = eq.lhs;
                }
                ExpressionPointer call = makeConstant(
                    "Equality.transport_proposition",
                    {eq.carrierLevel});
                call = makeApplication(call, eq.carrierType);
                call = makeApplication(call, motive);
                call = makeApplication(call, transportLhs);
                call = makeApplication(call, transportRhs);
                call = makeApplication(call, eqForTransport);
                call = makeApplication(call, proofRewritten);
                return call;
            }
        }
        return nullptr;
    }

    // Conjunction introduction: when the goal is `And(A, B)`,
    // recursively prove each conjunct via the same auto-prover
    // dispatch and combine with `And.introduction`. Strictly more
    // powerful than the library-scan path because each conjunct can
    // use the FULL auto-prover (not just structural hypothesis
    // match).
    //
    // Recursion guard: relies on `autoProveClaim`'s normal
    // termination — each recursive call has a strictly smaller goal
    // (A or B vs. A ∧ B), so no extra budget needed.
    ExpressionPointer tryConjunctionIntro(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        auto* outerApp = std::get_if<Application>(&goalOpened->node);
        if (!outerApp) return nullptr;
        auto* innerApp = std::get_if<Application>(
            &outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head || head->name != "And") return nullptr;
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer aClosed = closeOverLocalBinders(
            innerApp->argument, localBinders, N);
        ExpressionPointer bClosed = closeOverLocalBinders(
            outerApp->argument, localBinders, N);
        ExpressionPointer proofA;
        try {
            proofA = autoProveClaim(
                aClosed, localBinders, line);
        } catch (const ElaborateError&) { return nullptr; }
          catch (const TypeError&) { return nullptr; }
        ExpressionPointer proofB;
        try {
            proofB = autoProveClaim(
                bClosed, localBinders, line);
        } catch (const ElaborateError&) { return nullptr; }
          catch (const TypeError&) { return nullptr; }
        if (!environment_.lookup("And.introduction")) return nullptr;
        ExpressionPointer call = makeConstant(
            "And.introduction", {});
        call = makeApplication(call, aClosed);
        call = makeApplication(call, bClosed);
        call = makeApplication(call, proofA);
        call = makeApplication(call, proofB);
        return call;
    }

    // Transitivity bridge: if the goal is `H(a, c)` and
    // `<H>.transitive` exists in scope, perform a bounded BFS over
    // hypotheses of type `H(_, _)` to find a chain a → m1 → … → c,
    // then fold the chain into nested transitive applications.
    //
    // Pattern matching is STRUCTURAL (no WHNF on goal or hypothesis
    // types) — δ-reducing definitions like `Integer.LessOrEqual`
    // would unfold the named head and we'd lose `<head>.transitive`'s
    // lookup. `isDefinitionallyEqual` on individual subterms still
    // sees through reduction when comparing midpoints / endpoints.
    //
    // Each transitive call tries both hypothesis-arg orderings since
    // carriers differ in their transitive signature
    // (Natural's lemma takes `(b ≤ c) → (a ≤ b) → a ≤ c` while
    // Integer/Rational/Real's takes `(a ≤ b) → (b ≤ c) → a ≤ c`).
    //
    // BFS bounded by MAX_DEPTH (typical path lengths are 1–3).
    ExpressionPointer tryTransitivityBridge(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int /*line*/) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        auto* outerApp = std::get_if<Application>(&goalOpened->node);
        if (!outerApp) return nullptr;
        auto* innerApp = std::get_if<Application>(
            &outerApp->function->node);
        if (!innerApp) return nullptr;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head) return nullptr;
        std::string transitiveName = head->name + ".transitive";
        if (!environment_.lookup(transitiveName)) return nullptr;
        ExpressionPointer goalAOpened = innerApp->argument;
        ExpressionPointer goalCOpened = outerApp->argument;
        int N = static_cast<int>(localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);

        // Collect hypothesis edges: (source, target, binderIdx) for
        // each local binder of type `head(_, _)`.
        struct HypEdge {
            ExpressionPointer source;
            ExpressionPointer target;
            int binderIdx;
        };
        std::vector<HypEdge> edges;
        for (int b = N - 1; b >= 0; --b) {
            int lift = N - b;
            ExpressionPointer hTypeOpened = openOverLocalBinders(
                liftBoundVariables(
                    localBinders[b].type, lift, 0),
                localBinders, N);
            auto* hOuter = std::get_if<Application>(
                &hTypeOpened->node);
            if (!hOuter) continue;
            auto* hInner = std::get_if<Application>(
                &hOuter->function->node);
            if (!hInner) continue;
            auto* hHead = std::get_if<Constant>(
                &hInner->function->node);
            if (!hHead || hHead->name != head->name) continue;
            edges.push_back(
                {hInner->argument, hOuter->argument, b});
        }
        if (edges.empty()) return nullptr;

        // BFS from goalA, target goalC.
        std::vector<ExpressionPointer> reached;
        std::vector<int> reachedEdge;
        std::vector<int> reachedPred;
        reached.push_back(goalAOpened);
        reachedEdge.push_back(-1);
        reachedPred.push_back(-1);
        int targetReachedIdx = -1;
        constexpr int MAX_DEPTH = 8;
        int frontierStart = 0;
        int frontierEnd = 1;
        for (int depth = 0;
             targetReachedIdx == -1 && depth < MAX_DEPTH;
             ++depth) {
            for (int i = frontierStart;
                 i < frontierEnd && targetReachedIdx == -1;
                 ++i) {
                ExpressionPointer current = reached[i];
                for (size_t e = 0; e < edges.size(); ++e) {
                    if (!isDefinitionallyEqual(
                            environment_, openedContext,
                            edges[e].source, current)) continue;
                    ExpressionPointer target = edges[e].target;
                    bool already = false;
                    for (auto& r : reached) {
                        if (isDefinitionallyEqual(
                                environment_, openedContext,
                                r, target)) {
                            already = true;
                            break;
                        }
                    }
                    if (already) continue;
                    reached.push_back(target);
                    reachedEdge.push_back(
                        static_cast<int>(e));
                    reachedPred.push_back(i);
                    if (isDefinitionallyEqual(
                            environment_, openedContext,
                            target, goalCOpened)) {
                        targetReachedIdx =
                            static_cast<int>(reached.size()) - 1;
                        break;
                    }
                }
            }
            frontierStart = frontierEnd;
            frontierEnd = static_cast<int>(reached.size());
            if (frontierStart == frontierEnd) break;
        }
        if (targetReachedIdx == -1) return nullptr;

        // Reconstruct path: list of edge indices from source to target.
        std::vector<int> pathEdges;
        {
            int idx = targetReachedIdx;
            while (idx > 0) {
                pathEdges.push_back(reachedEdge[idx]);
                idx = reachedPred[idx];
            }
            std::reverse(pathEdges.begin(), pathEdges.end());
        }
        if (pathEdges.empty()) return nullptr;

        // Single-edge path: the hypothesis IS the proof.
        if (pathEdges.size() == 1) {
            return makeBoundVariable(
                N - 1 - edges[pathEdges[0]].binderIdx);
        }

        // Multi-edge path: fold transitive applications. accumulator
        // accProof : H(goalA, accTarget) starts with the first edge.
        ExpressionPointer accProof = makeBoundVariable(
            N - 1 - edges[pathEdges[0]].binderIdx);
        ExpressionPointer accTarget = edges[pathEdges[0]].target;
        for (size_t i = 1; i < pathEdges.size(); ++i) {
            const HypEdge& nextEdge = edges[pathEdges[i]];
            ExpressionPointer nextProof = makeBoundVariable(
                N - 1 - nextEdge.binderIdx);
            ExpressionPointer combined = buildTransitiveCall(
                transitiveName,
                goalAOpened, accTarget, nextEdge.target,
                accProof, nextProof, localBinders);
            if (!combined) return nullptr;
            accProof = combined;
            accTarget = nextEdge.target;
        }
        return accProof;
    }

    // Build `<transitiveName>(a, b, c, hAB, hBC)` (closed-form term)
    // with given a/b/c (opened) and hypothesis proofs (closed-form
    // terms in the current scope). Tries both hypothesis-arg
    // orderings since carriers differ in transitive signature.
    // Returns the first ordering that typechecks; nullptr if neither.
    ExpressionPointer buildTransitiveCall(
        const std::string& transitiveName,
        ExpressionPointer aOpened,
        ExpressionPointer bOpened,
        ExpressionPointer cOpened,
        ExpressionPointer hAB,
        ExpressionPointer hBC,
        const std::vector<LocalBinder>& localBinders) {
        int N = static_cast<int>(localBinders.size());
        ExpressionPointer aClosed = closeOverLocalBinders(
            aOpened, localBinders, N);
        ExpressionPointer bClosed = closeOverLocalBinders(
            bOpened, localBinders, N);
        ExpressionPointer cClosed = closeOverLocalBinders(
            cOpened, localBinders, N);
        for (int order = 0; order < 2; ++order) {
            ExpressionPointer call = makeConstant(
                transitiveName, {});
            call = makeApplication(call, aClosed);
            call = makeApplication(call, bClosed);
            call = makeApplication(call, cClosed);
            if (order == 0) {
                call = makeApplication(call, hAB);
                call = makeApplication(call, hBC);
            } else {
                call = makeApplication(call, hBC);
                call = makeApplication(call, hAB);
            }
            try {
                (void)inferTypeInLocalContext(
                    localBinders, call);
                return call;
            } catch (const TypeError&) { continue; }
              catch (const ElaborateError&) { continue; }
        }
        return nullptr;
    }

    // Run autoProveCalcStep on an equality goal — gives the top-
    // level claim path access to reflexivity, single-position diff
    // with `Equality.congruence` wrapping, and AC rearrangement via
    // `ring`. Returns nullptr if the goal isn't an Equality or none
    // of those strategies close it. Cheap to attempt: failure is
    // fast (extractEqualityComponents throws immediately on non-
    // Equality types) and silent.
    ExpressionPointer tryAutoProveEqualityGoal(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        ExpressionPointer goalWhnf = weakHeadNormalForm(
            environment_, goalOpened);
        EqualityComponents components;
        try {
            components = extractEqualityComponents(
                goalWhnf, "auto-prove equality goal", line);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        ExpressionPointer carrierClosed = closeOverLocalBinders(
            components.carrierType, localBinders,
            localBinders.size());
        ExpressionPointer leftClosed = closeOverLocalBinders(
            components.leftEndpoint, localBinders,
            localBinders.size());
        ExpressionPointer rightClosed = closeOverLocalBinders(
            components.rightEndpoint, localBinders,
            localBinders.size());
        try {
            return autoProveCalcStep(
                localBinders, leftClosed, rightClosed,
                carrierClosed, components.carrierUniverseLevel,
                goalClosed, line, 0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

    // Step 5 of the structured-proof feature. `claim P` (no `by`)
    // resolves the goal by:
    //   1. Context fact match — unified iteration over local binders
    //      and library declarations; each becomes a (proofTerm, type,
    //      cost) tuple; sorted by cost; for each, autoFillHintForClaim
    //      fills any Pi-binders from goal + hypotheses. Subsumes the
    //      old "direct hypothesis match" and "library scan" — same
    //      code path for both local and library facts.
    //   2. Equality battery — when the goal is an Equality, run
    //      autoProveCalcStep (reflexivity, single-position diff with
    //      `Equality.congruence` wrapping, AC rearrangement via ring).
    //      No-op for non-equality goals.
    //   3. Transitivity bridge — for `H(a, c)` goals, BFS hypothesis
    //      graph and fold `<H>.transitive` applications.
    //   4. Conjunction introduction — when the goal is `And(A, B)`,
    //      recurse on each conjunct and combine via
    //      `And.introduction`.
    //   5. Disjunction introduction — when the goal is `Or(A, B)`,
    //      try `A` first, else `B`; wrap with `Or.introduceLeft` or
    //      `Or.introduceRight` accordingly.
    //   6. Contradiction — if the in-scope hypotheses contain False
    //      or a `(h : P, h' : Not(P))` pair, close any goal via
    //      `False.eliminate_proposition`.
    //   7. Unified equality bridge — rewrite via any in-scope
    //      equality (local hypothesis or library lemma matched at a
    //      goal subexpression) and recurse on the rewritten goal.
    // v1 skips universe-polymorphic candidates (no universe inference
    // yet) and does a linear scan (acceptable at current library size;
    // an indexed lookup is a planned follow-on).
    ExpressionPointer autoProveClaim(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        int transportBudget = 1) {
        // (2) Equality battery — reflexivity, single-position diff
        // with congruence wrapping, AC rearrangement via ring. No-op
        // when the goal isn't an Equality.
        {
            ExpressionPointer attempt = tryAutoProveEqualityGoal(
                goalClosed, localBinders, line);
            if (attempt) return attempt;
        }

        // (3) Transitivity bridge — for relational goals `H(a, c)`,
        // search hypothesis pairs (h1 : H(a, b), h2 : H(b, c)) and
        // apply `<H>.transitive`. No-op when goal isn't a 2-arg
        // application of a constant head or when the transitive
        // lemma isn't in scope.
        {
            ExpressionPointer attempt = tryTransitivityBridge(
                goalClosed, localBinders, line);
            if (attempt) return attempt;
        }

        // (4) Conjunction introduction — when the goal is `And(A, B)`,
        // recursively prove each conjunct via the full auto-prover.
        {
            ExpressionPointer attempt = tryConjunctionIntro(
                goalClosed, localBinders, line);
            if (attempt) return attempt;
        }

        // (5) Disjunction introduction — when the goal is `Or(A, B)`,
        // try proving A; if that fails, try B. Left-biased.
        {
            ExpressionPointer attempt = tryDisjunctionIntro(
                goalClosed, localBinders, line);
            if (attempt) return attempt;
        }

        // (6) Contradiction — if in-scope hypotheses contain False
        // or a `(h, ¬h)` pair, close the goal via
        // `False.eliminate_proposition`.
        {
            ExpressionPointer attempt = tryContradiction(
                goalClosed, localBinders, line);
            if (attempt) return attempt;
        }

        // (1) Context fact match — unified local-hypothesis +
        // library scan. Iterates all in-scope facts (local binders
        // and applicable library declarations) by cost, trying
        // autoFillHintForClaim on each.
        {
            ExpressionPointer attempt = tryContextFactMatch(
                goalClosed, localBinders, line);
            if (attempt) return attempt;
        }

        // (7) Unified equality bridge: rewrite the goal via any
        // equality fact in context (local hypothesis OR library
        // lemma matched at a subexpression), then recurse. See
        // TODO.md "Hammer unification" — this strategy is the
        // pattern other context-iterating strategies should
        // eventually follow.
        {
            ExpressionPointer attempt = tryContextEqualityBridge(
                goalClosed, localBinders,
                line, transportBudget);
            if (attempt) return attempt;
        }

        throwElaborate(
            "claim `"
            + prettyPrintInLocalScope(goalClosed, localBinders)
            + "`: no in-scope hypothesis matches structurally, no "
            "equality battery (reflexivity / diff / ring) closes the "
            "goal, no transitivity chain reaches the goal, no "
            "conjunction split decomposes it, no in-scope "
            "contradiction lets us close it, no library theorem "
            "with this conclusion shape applies, and no context "
            "equality lets us rewrite to a provable form — add "
            "`by <lemma>` to specify");
    }

    // Elaborates `claim [P] by cases { in (A): body  in (B): body }`.
    // Strategy:
    //   1. Determine the goal (proposition P if given, else expected).
    //   2. Elaborate each arm's disjunctType.
    //   3. Find an in-scope hypothesis of type `Or armA armB` — that's
    //      the disjunction we case-split on.
    // `claim P by substitution` / `claim P by substituting <eq>` —
    // close the goal P via an equality bridge: find (or use the
    // supplied) equality `eq : a = b`, rewrite P along eq to a
    // related goal P', and find a proof of P' in the local context
    // or library. Sugar over `tryContextEqualityBridge` /
    // `Equality.transport_proposition` with better error messages
    // and (for the narrowed form) a smaller search space.
    ExpressionPointer elaborateClaimBySubstitution(
        const SurfaceStructuredClaim& claim,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        Frame frame(*this,
            "claim by substitution at line "
            + std::to_string(line));
        // Build the candidate-equality list. Default: every equality
        // in scope (the existing bridge's pool). Narrowed: a single
        // equality the user supplied as `by substituting <eq>`.
        std::vector<ContextEquality> candidates;
        if (claim.byHint) {
            // Narrowed form. Elaborate <eq>; extract its components
            // as a single ContextEquality.
            ExpressionPointer eqProof = elaborateExpression(
                *claim.byHint, localBinders);
            ExpressionPointer eqProofTypeOpened;
            try {
                eqProofTypeOpened = inferTypeInLocalContext(
                    localBinders, eqProof);
            } catch (const TypeError&) {
                throwElaborate(
                    "`by substituting`: the supplied expression "
                    "doesn't typecheck as a proof");
            }
            EqualityComponents components;
            try {
                components = extractEqualityComponents(
                    eqProofTypeOpened,
                    "by substituting argument", line);
            } catch (const ElaborateError&) {
                throwElaborate(
                    "`by substituting`: the supplied expression's "
                    "type is not an equality `a = b`");
            }
            int N = static_cast<int>(localBinders.size());
            ContextEquality eq;
            eq.cost = 1;
            eq.source = "supplied via `by substituting`";
            eq.carrierType = closeOverLocalBinders(
                components.carrierType, localBinders, N);
            eq.lhs = closeOverLocalBinders(
                components.leftEndpoint, localBinders, N);
            eq.rhs = closeOverLocalBinders(
                components.rightEndpoint, localBinders, N);
            eq.carrierLevel = components.carrierUniverseLevel;
            eq.proofExpr = eqProof;
            candidates.push_back(std::move(eq));
        } else {
            candidates = collectContextEqualities(
                goalClosed, localBinders, line);
            std::sort(candidates.begin(), candidates.end(),
                [](const ContextEquality& a, const ContextEquality& b) {
                    return a.cost < b.cost;
                });
        }
        // Goal candidates to search: first the closed form as the user
        // wrote it, then a deep-WHNF normalization (recursive WHNF
        // through Application spines). Under `unfold X in body`, the
        // surface goal type still mentions `X(args)`; only after
        // deep-WHNF does `X`'s body — and the equation's endpoint
        // buried inside it — become reachable for structural search.
        // We try the surface form first because it preserves the
        // user's intended motive shape; the deep form is the fallback
        // when the surface search comes up empty.
        std::vector<ExpressionPointer> goalForms;
        goalForms.push_back(goalClosed);
        ExpressionPointer goalDeepWhnf =
            deepWhnfThroughApplications(goalClosed);
        if (goalDeepWhnf.get() != goalClosed.get()) {
            goalForms.push_back(goalDeepWhnf);
        }
        // For each candidate, both directions, try the bridge.
        // Track per-attempt outcomes so we can produce a useful
        // diagnostic when nothing closes — the user wants to know
        // whether the failure was "no occurrence of the endpoint" or
        // "occurrence found but rewritten goal not closeable."
        struct SubstAttempt {
            const char* direction;
            int surfaceOccurrences = 0;
            int deepWhnfOccurrences = 0;
            bool rewrittenProveFailed = false;
        };
        std::vector<SubstAttempt> attemptLog;
        for (const ContextEquality& eq : candidates) {
            for (int direction = 0; direction < 2; ++direction) {
                ExpressionPointer fromSide =
                    (direction == 0) ? eq.rhs : eq.lhs;
                ExpressionPointer toSide =
                    (direction == 0) ? eq.lhs : eq.rhs;
                int occurrences = 0;
                ExpressionPointer abstractedBody;
                int surfaceCount = 0;
                int deepCount = 0;
                for (size_t formIdx = 0;
                     formIdx < goalForms.size(); ++formIdx) {
                    int formOccurrences = 0;
                    abstractedBody = abstractStructuralOccurrence(
                        goalForms[formIdx], fromSide,
                        /*currentDepth=*/0, formOccurrences);
                    if (formIdx == 0) {
                        surfaceCount = formOccurrences;
                    } else {
                        deepCount = formOccurrences;
                    }
                    if (formOccurrences > 0) {
                        occurrences = formOccurrences;
                        break;
                    }
                }
                SubstAttempt attempt;
                attempt.direction = (direction == 0)
                    ? "rhs → lhs" : "lhs → rhs";
                attempt.surfaceOccurrences = surfaceCount;
                attempt.deepWhnfOccurrences = deepCount;
                if (occurrences == 0) {
                    attemptLog.push_back(attempt);
                    continue;
                }
                ExpressionPointer rewrittenGoal = substitute(
                    abstractedBody, 0, toSide);
                ExpressionPointer proofRewritten;
                try {
                    proofRewritten = autoProveClaim(
                        rewrittenGoal, localBinders, line);
                } catch (const ElaborateError&) {
                    attempt.rewrittenProveFailed = true;
                    attemptLog.push_back(attempt);
                    continue;
                } catch (const TypeError&) {
                    attempt.rewrittenProveFailed = true;
                    attemptLog.push_back(attempt);
                    continue;
                }
                ExpressionPointer motive = makeLambda(
                    "_rewriteHole", eq.carrierType, abstractedBody);
                ExpressionPointer eqForTransport;
                ExpressionPointer transportLhs;
                ExpressionPointer transportRhs;
                if (direction == 0) {
                    eqForTransport = eq.proofExpr;
                    transportLhs = eq.lhs;
                    transportRhs = eq.rhs;
                } else {
                    eqForTransport = makeConstant(
                        "Equality.symmetry", {eq.carrierLevel});
                    eqForTransport = makeApplication(
                        eqForTransport, eq.carrierType);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.lhs);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.rhs);
                    eqForTransport = makeApplication(
                        eqForTransport, eq.proofExpr);
                    transportLhs = eq.rhs;
                    transportRhs = eq.lhs;
                }
                ExpressionPointer call = makeConstant(
                    "Equality.transport_proposition",
                    {eq.carrierLevel});
                call = makeApplication(call, eq.carrierType);
                call = makeApplication(call, motive);
                call = makeApplication(call, transportLhs);
                call = makeApplication(call, transportRhs);
                call = makeApplication(call, eqForTransport);
                call = makeApplication(call, proofRewritten);
                return call;
            }
        }
        if (claim.byHint) {
            // For the named form there's a single equality — break down
            // the per-direction outcomes so the user can distinguish
            // "endpoint not present" from "endpoint present but
            // rewritten goal isn't proveable."
            std::string detail;
            for (const SubstAttempt& a : attemptLog) {
                detail += "\n      ";
                detail += a.direction;
                detail += ": ";
                if (a.surfaceOccurrences == 0
                    && a.deepWhnfOccurrences == 0) {
                    detail +=
                        "0 occurrences (surface or deep-WHNF)";
                } else {
                    detail += "found " +
                        std::to_string(std::max(a.surfaceOccurrences,
                                                  a.deepWhnfOccurrences))
                        + " occurrence(s)";
                    if (a.surfaceOccurrences == 0
                        && a.deepWhnfOccurrences > 0) {
                        detail +=
                            " — only after deep-WHNF reduction";
                    }
                    if (a.rewrittenProveFailed) {
                        detail += "; rewritten goal not closeable by "
                                  "the auto-prover";
                    }
                }
            }
            throwElaborate(
                "`by substituting <eq>` couldn't close the goal."
                "\n  Direction search:" + detail
                + "\n  (If a direction shows occurrences but the "
                  "rewritten goal failed, the rewrite happened — but "
                  "the auto-prover couldn't discharge the result. "
                  "Add `by <proof>` to close it manually.)");
        }
        throwElaborate(
            "`by substitution` couldn't close the goal: no in-scope "
            "equality lets the auto-prover reach a provable form "
            "(consider `by substituting <specific eq>` to narrow, "
            "or supply an explicit `by <proof>`)");
    }

    //   4. Elaborate each arm body under an anonymous binder of its
    //      disjunct's type; build the two lambdas.
    //   5. Emit `Or.eliminate(A, B, Goal, leftLambda, rightLambda,
    //                          theInScopeDisjunction)`.
    // v1 limits: exactly 2 arms (binary disjunction).
    ExpressionPointer elaborateClaimByCases(
        const SurfaceStructuredClaim& claim,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {
        Frame frame(*this,
            "claim by cases at line " + std::to_string(line));

        if (claim.arms.size() != 2) {
            throwElaborate(
                "`by cases` v1 handles exactly 2 arms; got "
                + std::to_string(claim.arms.size())
                + " — n-ary disjunctions are a planned later step");
        }

        // The goal each arm must prove.
        ExpressionPointer goalClosed;
        if (claim.proposition) {
            goalClosed = elaborateExpression(
                *claim.proposition, localBinders);
        } else if (expectedType) {
            goalClosed = expectedType;
        } else {
            throwElaborate(
                "`claim by cases` needs either a proposition or an "
                "expected type from context");
        }

        // Elaborate arm disjuncts.
        ExpressionPointer leftDisjunct = elaborateExpression(
            *claim.arms[0].disjunctType, localBinders);
        ExpressionPointer rightDisjunct = elaborateExpression(
            *claim.arms[1].disjunctType, localBinders);

        // Build the expected disjunction type `Or leftDisjunct
        // rightDisjunct`. Or is a non-polymorphic Proposition.
        ExpressionPointer expectedDisjunction = makeApplication(
            makeApplication(
                makeConstant("Or", {}), leftDisjunct),
            rightDisjunct);

        // Find OR synthesize the disjunction via the unified hammer
        // dispatch. This is the same "find or synthesize" function
        // bare `claim P;` uses — local hypothesis match, library
        // scan, transitivity, the lot. If nothing in scope proves
        // the disjunction, the dispatch error message (wrapped by
        // the Frame above) tells the user exactly what failed.
        ExpressionPointer disjProof;
        try {
            disjProof = autoProveClaim(
                expectedDisjunction, localBinders, line);
        } catch (const ElaborateError&) {
            throwElaborate(
                "couldn't automatically prove `"
                + prettyPrintInLocalScope(
                      expectedDisjunction, localBinders)
                + "` to finish off `by cases` — either bring it "
                "into scope explicitly (`claim "
                + prettyPrintInLocalScope(leftDisjunct, localBinders)
                + " ∨ "
                + prettyPrintInLocalScope(rightDisjunct, localBinders)
                + " by …;`), or check that the cases really do "
                "cover the goal");
        }

        // Build each arm's lambda. Body is elaborated under
        // localBinders + the disjunct hypothesis. The hypothesis
        // takes the user-supplied `as name` if present, else
        // `_disjunct_hypothesis` (reachable via `given (P)` /
        // library lookup). The goal is lifted by 1 to account for
        // the extra binder.
        ExpressionPointer goalLifted =
            liftBoundVariables(goalClosed, 1, 0);
        auto buildArmLambda =
            [&](size_t index, ExpressionPointer domain)
                -> ExpressionPointer {
            const SurfaceStructuredClaimArm& arm = claim.arms[index];
            std::string binderName = arm.binderName.empty()
                ? "_disjunct_hypothesis" : arm.binderName;
            std::vector<LocalBinder> extendedBinders = localBinders;
            extendedBinders.push_back({binderName, domain});
            ExpressionPointer body = elaborateExpression(
                *arm.body, extendedBinders, goalLifted);
            warnIfBinderUnused(
                arm.binderName, body, arm.line, arm.column,
                "`case ... as`");
            return makeLambda(binderName, domain, body);
        };
        ExpressionPointer leftLambda = buildArmLambda(0, leftDisjunct);
        ExpressionPointer rightLambda = buildArmLambda(1, rightDisjunct);

        // Or.eliminate(A, B, Goal, leftLambda, rightLambda, disjProof).
        ExpressionPointer call = makeConstant("Or.eliminate", {});
        call = makeApplication(call, leftDisjunct);
        call = makeApplication(call, rightDisjunct);
        call = makeApplication(call, goalClosed);
        call = makeApplication(call, leftLambda);
        call = makeApplication(call, rightLambda);
        call = makeApplication(call, disjProof);
        return call;
    }

    // Elaborates a calc chain to a fold of Equality.transitivity calls.
    // Each step's proof is elaborated against the specific equality type
    // `Equality(carrier, previous, next)` so a type error points at the
    // failing step.
    //
    // For a single step the result is just the step proof (no transitivity
    // wrapper). For N ≥ 2 steps the result is left-folded:
    //   transitivity(... transitivity(transitivity(p1, p2), p3) ..., pN).
    ExpressionPointer elaborateCalc(
        const SurfaceCalc& calc,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "calc block at line " + std::to_string(line),
            localBinders, expectedType, line, column);
        ExpressionPointer previousKernel = elaborateExpression(
            *calc.initialExpression, localBinders);
        ExpressionPointer carrierTypeOpen =
            inferTypeInLocalContext(localBinders, previousKernel);
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpen, localBinders, localBinders.size());
        LevelPointer carrierLevel =
            typeUniverseOf(localBinders, previousKernel);

        // Resolve the carrier's <T>.LessOrEqual and <T>.LessThan
        // relations (and their reflexive / transitive / weaken lemmas)
        // lazily, on first use. The operator registry — populated by
        // `operator (≤) on (T, T) := <T>.LessOrEqual;` and the parallel
        // `<`/`>`/`≥` registrations — drives the name lookup. Natural
        // has no namespaced wrapper around its inductive `LessOrEqual`,
        // so we fall back to bare `LessOrEqual` for it (and don't
        // support `<` on Natural in calc, since there's no Natural-side
        // LessThan type with transitive_left/right lemmas).
        auto* carrierConstant =
            std::get_if<Constant>(&carrierTypeOpen->node);
        std::string carrierTypeName =
            carrierConstant ? carrierConstant->name : std::string{};
        std::string leqRelationName;       // e.g. "Real.LessOrEqual"
        std::string leqReflexiveName;      // e.g. "Real.LessOrEqual.reflexive"
        std::string leqTransitiveName;     // e.g. "Real.LessOrEqual.transitive"
        bool transitiveTakesProofsSwapped = false;
        std::string ltRelationName;            // e.g. "Real.LessThan"
        std::string ltTransitiveLeftName;      // e.g. "Real.LessThan.transitive_left"
        std::string ltTransitiveRightName;     // e.g. "Real.LessThan.transitive_right"
        std::string ltWeakenName;              // e.g. "Real.LessThan.weaken"
        auto resolveLeqNames = [&]() {
            if (!leqRelationName.empty()) return;
            std::string registered = environment_.lookupOperator(
                "≤", carrierTypeName, carrierTypeName);
            if (!registered.empty()) {
                leqRelationName = registered;
                leqReflexiveName = registered + ".reflexive";
                leqTransitiveName = registered + ".transitive";
            } else if (carrierTypeName == "Natural") {
                // Natural's ≤ falls back to the bare inductive
                // `LessOrEqual`. Its transitive lemma takes the proofs
                // in (b≤c, a≤b) order — historical accident from the
                // pattern-match-on-second-proof construction — so flag
                // the swap for the composition step below.
                leqRelationName = "LessOrEqual";
                leqReflexiveName = "LessOrEqual.reflexivity";
                leqTransitiveName = "LessOrEqual.transitive";
                transitiveTakesProofsSwapped = true;
            } else {
                throwElaborate(
                    "calc step uses '≤'/'≥' but no operator '≤' is "
                    "registered on (" + carrierTypeName + ", "
                    + carrierTypeName + ") — register one via "
                    "`operator (≤) on (" + carrierTypeName + ", "
                    + carrierTypeName + ") := <fn>;` first");
            }
        };
        auto resolveLtNames = [&]() {
            if (!ltRelationName.empty()) return;
            std::string registered = environment_.lookupOperator(
                "<", carrierTypeName, carrierTypeName);
            if (registered.empty()) {
                throwElaborate(
                    "calc step uses '<'/'>' but no operator '<' is "
                    "registered on (" + carrierTypeName + ", "
                    + carrierTypeName + ") — register one via "
                    "`operator (<) on (" + carrierTypeName + ", "
                    + carrierTypeName + ") := <fn>;` first");
            }
            ltRelationName = registered;
            ltTransitiveLeftName = registered + ".transitive_left";
            ltTransitiveRightName = registered + ".transitive_right";
            ltWeakenName = registered + ".weaken";
        };

        // Classify a CalcRelation along two axes:
        //   - direction: Forward (<, ≤), Backward (>, ≥), or Neutral (=).
        //     A chain may not mix Forward with Backward steps.
        //   - strictness: Equality, Weak (≤/≥), or Strict (<, >).
        enum class Direction { Neutral, Forward, Backward };
        enum class Strictness { Equality, Weak, Strict };
        auto directionOf = [](CalcRelation r) -> Direction {
            switch (r) {
                case CalcRelation::LessOrEqual:
                case CalcRelation::LessThan:
                    return Direction::Forward;
                case CalcRelation::GreaterOrEqual:
                case CalcRelation::GreaterThan:
                    return Direction::Backward;
                default:
                    return Direction::Neutral;
            }
        };
        auto strictnessOf = [](CalcRelation r) -> Strictness {
            switch (r) {
                case CalcRelation::Equality:
                    return Strictness::Equality;
                case CalcRelation::LessOrEqual:
                case CalcRelation::GreaterOrEqual:
                    return Strictness::Weak;
                case CalcRelation::LessThan:
                case CalcRelation::GreaterThan:
                    return Strictness::Strict;
            }
            return Strictness::Equality;
        };
        auto relationSymbol = [](CalcRelation r) -> const char* {
            switch (r) {
                case CalcRelation::Equality:        return "=";
                case CalcRelation::LessOrEqual:     return "≤";
                case CalcRelation::LessThan:        return "<";
                case CalcRelation::GreaterOrEqual:  return "≥";
                case CalcRelation::GreaterThan:     return ">";
            }
            return "?";
        };

        struct StepRecord {
            CalcRelation relation;
            ExpressionPointer proof;
        };
        std::vector<StepRecord> steps;
        std::vector<ExpressionPointer> endpointKernels;
        endpointKernels.push_back(previousKernel);

        for (size_t k = 0; k < calc.steps.size(); ++k) {
            const auto& step = calc.steps[k];
            Frame stepFrame(*this,
                "calc step " + std::to_string(k + 1)
                + " at line " + std::to_string(step.line),
                localBinders,
                previousKernel,
                step.line, /*column*/ 0);
            ExpressionPointer nextKernel = elaborateExpression(
                *step.nextExpression, localBinders, carrierType);
            // Build the step's expected proof type from its relation.
            // For ≥/> the relation's arguments are flipped (a ≥ b is
            // proved as b ≤ a; a > b is proved as b < a).
            ExpressionPointer stepRelationType;
            Direction stepDirection = directionOf(step.relation);
            Strictness stepStrictness = strictnessOf(step.relation);
            if (step.relation == CalcRelation::Equality) {
                stepRelationType = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {carrierLevel}),
                            carrierType),
                        previousKernel),
                    nextKernel);
            } else {
                ExpressionPointer lhs =
                    (stepDirection == Direction::Backward)
                        ? nextKernel : previousKernel;
                ExpressionPointer rhs =
                    (stepDirection == Direction::Backward)
                        ? previousKernel : nextKernel;
                std::string relationName;
                if (stepStrictness == Strictness::Strict) {
                    resolveLtNames();
                    relationName = ltRelationName;
                } else {
                    resolveLeqNames();
                    relationName = leqRelationName;
                }
                stepRelationType = makeApplication(
                    makeApplication(
                        makeConstant(relationName), lhs),
                    rhs);
            }
            ExpressionPointer stepProofKernel;
            if (step.stepProof) {
                stepProofKernel = elaborateExpression(
                    *step.stepProof, localBinders, stepRelationType);
                if (reportRedundantBy_
                    && step.relation == CalcRelation::Equality) {
                    ExpressionPointer autoAttempt;
                    try {
                        autoAttempt = autoProveCalcStep(
                            localBinders, previousKernel, nextKernel,
                            carrierType, carrierLevel,
                            stepRelationType,
                            step.line, step.column);
                    } catch (const ElaborateError&) {
                        autoAttempt = nullptr;
                    } catch (const TypeError&) {
                        autoAttempt = nullptr;
                    }
                    if (autoAttempt) {
                        std::cerr << "warning: " << moduleName_
                            << ":" << step.line << ":" << step.column
                            << ": redundant `by` on calc step — "
                            "auto-prover closes it without help\n";
                    } else {
                        // Auto-prover couldn't close on its own, but
                        // maybe the user wrote `by congruenceOf(λ, L)`
                        // and `by L` alone would close via the diff-
                        // inference fallback. That catches verbose
                        // congruenceOf wrappers the redundant-by check
                        // misses (because the lemma's preconditions
                        // aren't synthesizable without the user's call).
                        auto* surfApp =
                            std::get_if<SurfaceApplication>(
                                &step.stepProof->node);
                        if (surfApp && surfApp->arguments.size() == 2) {
                            auto* head =
                                std::get_if<SurfaceIdentifier>(
                                    &surfApp->function->node);
                            if (head
                                && head->qualifiedName == "congruenceOf"
                                && head->universeArgs.empty()) {
                                ExpressionPointer lemmaKernel;
                                try {
                                    lemmaKernel = elaborateExpression(
                                        *surfApp->arguments[1].value,
                                        localBinders);
                                } catch (const ElaborateError&) {
                                    lemmaKernel = nullptr;
                                } catch (const TypeError&) {
                                    lemmaKernel = nullptr;
                                }
                                if (lemmaKernel) {
                                    ExpressionPointer lemmaType;
                                    try {
                                        lemmaType =
                                            inferTypeInLocalContext(
                                                localBinders,
                                                lemmaKernel);
                                    } catch (const TypeError&) {
                                        lemmaType = nullptr;
                                    } catch (const ElaborateError&) {
                                        lemmaType = nullptr;
                                    }
                                    ExpressionPointer diffAttempt;
                                    if (lemmaType) {
                                        try {
                                            diffAttempt =
                                                tryDiffApplyUserProof(
                                                    localBinders,
                                                    previousKernel,
                                                    nextKernel,
                                                    lemmaKernel,
                                                    lemmaType,
                                                    step.line,
                                                    step.column);
                                        } catch (const ElaborateError&) {
                                            diffAttempt = nullptr;
                                        } catch (const TypeError&) {
                                            diffAttempt = nullptr;
                                        }
                                    }
                                    if (diffAttempt) {
                                        std::cerr << "warning: "
                                            << moduleName_ << ":"
                                            << step.line << ":"
                                            << step.column
                                            << ": redundant congruenceOf "
                                            "wrapper — `by <inner lemma>`"
                                            " alone would close this "
                                            "step (diff inference fills "
                                            "the lambda)\n";
                                    }
                                }
                            }
                        }
                    }
                }
            } else if (step.relation == CalcRelation::Equality) {
                stepProofKernel = autoProveCalcStep(
                    localBinders, previousKernel, nextKernel,
                    carrierType, carrierLevel, stepRelationType,
                    step.line, step.column);
                if (!stepProofKernel) {
                    throwElaborate(
                        "calc step has no `by <proof>` and the "
                        "auto-prover couldn't close it. Add `by "
                        "<reason>` to disambiguate.");
                }
            } else {
                // Non-equality step (≤/</≥/>) without `by`. Dispatch
                // the step's relation type through the full
                // autoProveClaim — handles hypothesis match, library
                // scan (catches `<T>.LessOrEqual.reflexive` when the
                // endpoints are defeq), conjunction/disjunction
                // intro, contradiction, etc. Equality battery still
                // runs for chains like `b = a ≤ a` whose final step
                // collapses to reflexivity of ≤ at a single point.
                try {
                    stepProofKernel = autoProveClaim(
                        stepRelationType, localBinders, step.line);
                } catch (const ElaborateError&) {
                    stepProofKernel = nullptr;
                }
                if (!stepProofKernel) {
                    throwElaborate(
                        std::string("calc ") + relationSymbol(step.relation)
                        + " step has no `by <proof>` and the auto-"
                          "prover couldn't close it from context. "
                          "Add `by <reason>`.");
                }
            }
            ExpressionPointer stepProofType = inferTypeInLocalContext(
                localBinders, stepProofKernel);
            ExpressionPointer stepRelationTypeOpened = openOverLocalBinders(
                stepRelationType, localBinders, localBinders.size());
            Context stepContext = buildContextFromLocalBinders(localBinders);
            if (!isDefinitionallyEqual(environment_, stepContext,
                                        stepProofType,
                                        stepRelationTypeOpened)) {
                // Auto-rewrite fallback for = steps only.
                ExpressionPointer rewriteAttempt;
                if (step.stepProof
                    && step.relation == CalcRelation::Equality) {
                    try {
                        rewriteAttempt = desugarRewrite(
                            step.stepProof, localBinders,
                            stepRelationType,
                            step.line, step.column);
                    } catch (const ElaborateError&) {
                        rewriteAttempt = nullptr;
                    }
                }
                if (rewriteAttempt) {
                    ExpressionPointer rewriteType =
                        inferTypeInLocalContext(localBinders,
                            rewriteAttempt);
                    if (isDefinitionallyEqual(environment_, stepContext,
                                                rewriteType,
                                                stepRelationTypeOpened)) {
                        stepProofKernel = rewriteAttempt;
                        stepProofType = rewriteType;
                    }
                }
            }
            // Diff-inference fallback: if the user's `by <proof>` has
            // type Equality(T, a, b) and the calc step's
            // (previousKernel, nextKernel) differ in a single slot at
            // (a, b), wrap with Equality.congruence. Lets the user
            // write `by lemma` instead of
            // `by congruenceOf(λm. <giant context>, lemma)`.
            if (step.stepProof
                && step.relation == CalcRelation::Equality
                && !isDefinitionallyEqual(environment_, stepContext,
                                            stepProofType,
                                            stepRelationTypeOpened)) {
                ExpressionPointer diffAttempt;
                try {
                    diffAttempt = tryDiffApplyUserProof(
                        localBinders, previousKernel, nextKernel,
                        stepProofKernel, stepProofType,
                        step.line, step.column);
                } catch (const ElaborateError&) {
                    diffAttempt = nullptr;
                } catch (const TypeError&) {
                    diffAttempt = nullptr;
                }
                if (diffAttempt) {
                    ExpressionPointer diffAttemptType =
                        inferTypeInLocalContext(localBinders,
                            diffAttempt);
                    if (isDefinitionallyEqual(environment_, stepContext,
                                                diffAttemptType,
                                                stepRelationTypeOpened)) {
                        stepProofKernel = diffAttempt;
                        stepProofType = diffAttemptType;
                    }
                }
            }
            if (!isDefinitionallyEqual(environment_, stepContext,
                                        stepProofType,
                                        stepRelationTypeOpened)) {
                TypeError error(
                    "calc step proof's type does not match the "
                    "relation claimed by this step");
                error.expectedType = stepRelationTypeOpened;
                error.actualType = stepProofType;
                rethrowKernelError(error);
            }
            steps.push_back({step.relation, stepProofKernel});
            endpointKernels.push_back(nextKernel);
            previousKernel = nextKernel;
        }

        // Optional check: look for redundant intermediate calc steps.
        // For each internal step (one that isn't the first or last
        // endpoint), see whether the auto-prover can close the
        // combined neighbouring step directly. If yes, warn — the
        // user can usually delete the intermediate `= midpoint` line
        // without losing kernel acceptance. Restricted to all-`=`
        // adjacent pairs for now (mixed `=`/`≤`/`<` combinations need
        // per-case relation arithmetic). Off by default — the
        // auto-prover dispatch is expensive on long chains.
        if (reportRedundantCalcSteps_) {
            for (size_t k = 1; k + 1 <= steps.size(); ++k) {
                // steps[k-1] takes endpointKernels[k-1] -> endpointKernels[k].
                // steps[k]   takes endpointKernels[k]   -> endpointKernels[k+1].
                // We're asking: can the auto-prover close endpointKernels[k-1]
                // (= endpointKernels[k+1]) directly? Only check when both
                // steps are Equality so the combined relation is unambiguous.
                if (steps[k - 1].relation != CalcRelation::Equality
                    || steps[k].relation != CalcRelation::Equality) {
                    continue;
                }
                ExpressionPointer combinedRelation = makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {carrierLevel}),
                            carrierType),
                        endpointKernels[k - 1]),
                    endpointKernels[k + 1]);
                ExpressionPointer autoAttempt;
                try {
                    autoAttempt = autoProveCalcStep(
                        localBinders,
                        endpointKernels[k - 1],
                        endpointKernels[k + 1],
                        carrierType, carrierLevel,
                        combinedRelation,
                        calc.steps[k - 1].line, calc.steps[k - 1].column);
                } catch (const ElaborateError&) {
                    autoAttempt = nullptr;
                } catch (const TypeError&) {
                    autoAttempt = nullptr;
                }
                if (autoAttempt) {
                    // The redundant ENDPOINT is endpointKernels[k] — it's
                    // the target of steps[k-1] and is written on that
                    // step's line. Removing that line collapses steps
                    // (k-1, k) into one step from endpoint (k-1) to
                    // endpoint (k+1), which the auto-prover can close.
                    std::cerr << "warning: " << moduleName_
                        << ":" << calc.steps[k - 1].line
                        << ":" << calc.steps[k - 1].column
                        << ": calc intermediate target at this line is "
                        "redundant — removing it lets the auto-prover "
                        "close the combined step (next endpoint at line "
                        << calc.steps[k].line << ")\n";
                }
            }
        }

        // Determine overall chain direction and strictness.
        Direction chainDirection = Direction::Neutral;
        Strictness chainStrictness = Strictness::Equality;
        for (const auto& s : steps) {
            Direction d = directionOf(s.relation);
            Strictness st = strictnessOf(s.relation);
            if (d != Direction::Neutral) {
                if (chainDirection == Direction::Neutral) {
                    chainDirection = d;
                } else if (chainDirection != d) {
                    throwElaborate(
                        "calc chain mixes forward (<, ≤) and backward "
                        "(>, ≥) inequalities — only = is allowed in "
                        "either direction");
                }
            }
            if (st == Strictness::Strict) {
                chainStrictness = Strictness::Strict;
            } else if (st == Strictness::Weak
                       && chainStrictness != Strictness::Strict) {
                chainStrictness = Strictness::Weak;
            }
        }

        // Helper: upgrade an =-proof to a ≤-proof via transport on the
        // relation's right argument. Given p : a = b, returns p' :
        // a ≤ b built as transport_proposition(T, λz. a ≤ z, a, b, p,
        // reflexive(a)). The `aExpr` reference inside the motive lambda
        // body needs its De Bruijn indices shifted up by one to account
        // for the new `z` binder we're putting around it.
        auto upgradeEqualityToLessOrEqual =
            [&](ExpressionPointer eqProof,
                ExpressionPointer aExpr,
                ExpressionPointer bExpr) -> ExpressionPointer {
            resolveLeqNames();
            ExpressionPointer aExprShifted = shift(aExpr, 1);
            ExpressionPointer motiveBody = makeApplication(
                makeApplication(
                    makeConstant(leqRelationName),
                    std::move(aExprShifted)),
                makeBoundVariable(0));
            ExpressionPointer motive = makeLambda(
                "z", carrierType, std::move(motiveBody));
            ExpressionPointer reflexive = makeApplication(
                makeConstant(leqReflexiveName), aExpr);
            ExpressionPointer call = makeConstant(
                "Equality.transport_proposition", {carrierLevel});
            call = makeApplication(std::move(call), carrierType);
            call = makeApplication(std::move(call), std::move(motive));
            call = makeApplication(std::move(call), aExpr);
            call = makeApplication(std::move(call), bExpr);
            call = makeApplication(std::move(call), std::move(eqProof));
            call = makeApplication(std::move(call), std::move(reflexive));
            return call;
        };

        // Normalize for Backward chains: reverse endpoint and step
        // order. Each Backward ≥/> step's proof already has type
        // matching the normalized direction (a ≥ b's proof is b ≤ a,
        // exactly what the reversed walk wants going from b to a).
        // But Backward = steps were elaborated with type
        // `previous = next` (user-direction); the normalized walk
        // needs `next = previous`, so we flip them via
        // Equality.symmetry.
        std::vector<ExpressionPointer> normalizedEndpoints =
            endpointKernels;
        std::vector<StepRecord> normalizedSteps = steps;
        if (chainDirection == Direction::Backward) {
            std::reverse(normalizedEndpoints.begin(),
                          normalizedEndpoints.end());
            std::reverse(normalizedSteps.begin(),
                          normalizedSteps.end());
            for (size_t k = 0; k < normalizedSteps.size(); ++k) {
                if (normalizedSteps[k].relation
                    != CalcRelation::Equality) {
                    continue;
                }
                // normalizedSteps[k] corresponds to user's step
                // (N-1-k), whose endpoints are
                // (endpointKernels[N-1-k], endpointKernels[N-k]) =
                // (normalizedEndpoints[k+1], normalizedEndpoints[k]).
                // Build symmetry over the user-direction endpoints.
                ExpressionPointer call = makeConstant(
                    "Equality.symmetry", {carrierLevel});
                call = makeApplication(std::move(call), carrierType);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k + 1]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k]);
                call = makeApplication(std::move(call),
                    normalizedSteps[k].proof);
                normalizedSteps[k].proof = std::move(call);
            }
        }

        // All-= chain: fold via Equality.transitivity (unchanged).
        if (chainStrictness == Strictness::Equality) {
            if (normalizedSteps.size() == 1) {
                return normalizedSteps[0].proof;
            }
            ExpressionPointer running = normalizedSteps[0].proof;
            for (size_t k = 1; k < normalizedSteps.size(); ++k) {
                ExpressionPointer call = makeConstant(
                    "Equality.transitivity", {carrierLevel});
                call = makeApplication(std::move(call), carrierType);
                call = makeApplication(std::move(call), normalizedEndpoints[0]);
                call = makeApplication(std::move(call), normalizedEndpoints[k]);
                call = makeApplication(std::move(call), normalizedEndpoints[k + 1]);
                call = makeApplication(std::move(call), std::move(running));
                call = makeApplication(std::move(call), normalizedSteps[k].proof);
                running = std::move(call);
            }
            return running;
        }

        // Chain has at least one ≤ or <. Process each step's proof into
        // its working form: = becomes ≤ via transport; ≤ stays ≤; < stays <.
        // Track the running proof's strictness as we fold.
        auto stepProofAsLeq = [&](size_t k) -> ExpressionPointer {
            const auto& s = normalizedSteps[k];
            if (strictnessOf(s.relation) == Strictness::Equality) {
                return upgradeEqualityToLessOrEqual(
                    s.proof,
                    normalizedEndpoints[k],
                    normalizedEndpoints[k + 1]);
            }
            // ≤ or < step: kept as-is at this point; composition will
            // pick the right transitive lemma based on strictness.
            return s.proof;
        };

        // Single-step calc: the (possibly upgraded) step proof IS the
        // result. If the chain strictness exceeds the step's, we have
        // to upgrade =-only to ≤ (chain Weak), but a single-step chain
        // can't be Strict from an = step alone.
        if (normalizedSteps.size() == 1) {
            if (strictnessOf(normalizedSteps[0].relation)
                == Strictness::Equality) {
                return stepProofAsLeq(0);
            }
            return normalizedSteps[0].proof;
        }

        // Weak-only chain (no <): compose via <T>.LessOrEqual.transitive.
        if (chainStrictness == Strictness::Weak) {
            ExpressionPointer running = stepProofAsLeq(0);
            for (size_t k = 1; k < normalizedSteps.size(); ++k) {
                ExpressionPointer nextProof = stepProofAsLeq(k);
                ExpressionPointer call =
                    makeConstant(leqTransitiveName);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[0]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k]);
                call = makeApplication(std::move(call),
                    normalizedEndpoints[k + 1]);
                if (transitiveTakesProofsSwapped) {
                    call = makeApplication(std::move(call),
                        std::move(nextProof));
                    call = makeApplication(std::move(call),
                        std::move(running));
                } else {
                    call = makeApplication(std::move(call),
                        std::move(running));
                    call = makeApplication(std::move(call),
                        std::move(nextProof));
                }
                running = std::move(call);
            }
            return running;
        }

        // Strict chain (some step is <): the running proof becomes
        // strict the first time a < step is hit, and stays strict.
        // Compose using <T>.LessThan.transitive_{left,right} plus
        // weaken as appropriate.
        auto weakenStrict =
            [&](ExpressionPointer xExpr, ExpressionPointer yExpr,
                ExpressionPointer strictProof) -> ExpressionPointer {
            ExpressionPointer call = makeConstant(ltWeakenName);
            call = makeApplication(std::move(call), xExpr);
            call = makeApplication(std::move(call), yExpr);
            call = makeApplication(std::move(call),
                std::move(strictProof));
            return call;
        };
        ExpressionPointer running;
        Strictness runningStrictness;
        if (strictnessOf(normalizedSteps[0].relation)
            == Strictness::Strict) {
            running = normalizedSteps[0].proof;
            runningStrictness = Strictness::Strict;
        } else {
            running = stepProofAsLeq(0);
            runningStrictness = Strictness::Weak;
        }
        for (size_t k = 1; k < normalizedSteps.size(); ++k) {
            Strictness stepKind =
                strictnessOf(normalizedSteps[k].relation);
            ExpressionPointer stepProof;
            if (stepKind == Strictness::Strict) {
                stepProof = normalizedSteps[k].proof;
            } else {
                // Equality or Weak: upgrade to ≤ form.
                stepProof = stepProofAsLeq(k);
            }
            ExpressionPointer xExpr = normalizedEndpoints[0];
            ExpressionPointer yExpr = normalizedEndpoints[k];
            ExpressionPointer zExpr = normalizedEndpoints[k + 1];
            if (runningStrictness == Strictness::Weak
                && stepKind != Strictness::Strict) {
                // weak ⋈ weak (incl. =-upgraded) → weak.
                ExpressionPointer call =
                    makeConstant(leqTransitiveName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                if (transitiveTakesProofsSwapped) {
                    call = makeApplication(std::move(call),
                        std::move(stepProof));
                    call = makeApplication(std::move(call),
                        std::move(running));
                } else {
                    call = makeApplication(std::move(call),
                        std::move(running));
                    call = makeApplication(std::move(call),
                        std::move(stepProof));
                }
                running = std::move(call);
            } else if (runningStrictness == Strictness::Weak
                       && stepKind == Strictness::Strict) {
                // weak ⋈ strict → strict via transitive_left(le, lt).
                ExpressionPointer call =
                    makeConstant(ltTransitiveLeftName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                call = makeApplication(std::move(call),
                    std::move(running));
                call = makeApplication(std::move(call),
                    std::move(stepProof));
                running = std::move(call);
                runningStrictness = Strictness::Strict;
            } else if (runningStrictness == Strictness::Strict
                       && stepKind != Strictness::Strict) {
                // strict ⋈ weak (incl. =-upgraded) → strict via
                // transitive_right(lt, le).
                ExpressionPointer call =
                    makeConstant(ltTransitiveRightName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                call = makeApplication(std::move(call),
                    std::move(running));
                call = makeApplication(std::move(call),
                    std::move(stepProof));
                running = std::move(call);
            } else {
                // strict ⋈ strict → strict via
                // transitive_left(weaken(running), step).
                ExpressionPointer weakened =
                    weakenStrict(xExpr, yExpr, std::move(running));
                ExpressionPointer call =
                    makeConstant(ltTransitiveLeftName);
                call = makeApplication(std::move(call), xExpr);
                call = makeApplication(std::move(call), yExpr);
                call = makeApplication(std::move(call), zExpr);
                call = makeApplication(std::move(call),
                    std::move(weakened));
                call = makeApplication(std::move(call),
                    std::move(stepProof));
                running = std::move(call);
            }
        }
        return running;
    }

    // Try to decompose `term` as `op(left, right)` where `op` is a
    // top-level Constant. Returns true with the op name, universe
    // arguments, and the two argument expressions on success.
    bool decomposeBinaryOpApplication(
        ExpressionPointer term,
        std::string& outOpName,
        std::vector<LevelPointer>& outOpUniverseArguments,
        ExpressionPointer& outLeft,
        ExpressionPointer& outRight) {
        auto* outerApp = std::get_if<Application>(&term->node);
        if (!outerApp) return false;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return false;
        auto* opConst =
            std::get_if<Constant>(&innerApp->function->node);
        if (!opConst) return false;
        outOpName = opConst->name;
        outOpUniverseArguments = opConst->universeArguments;
        outLeft = innerApp->argument;
        outRight = outerApp->argument;
        return true;
    }

    // Hook called after each theorem is added to the environment.
    // If the type fits the rewrite-lemma shape, registers it in
    // `lemmaIndex_` under both `spineHash(LHS)` and `spineHash(RHS)`
    // so the calc auto-prover can apply it in either direction.
    void registerAlgebraicShape(const std::string& theoremName,
                                  ExpressionPointer typeExpr) {
        registerGenericRewriteLemma(theoremName, typeExpr);
    }

    // Rewrite-lemma registration. If `typeExpr` has the shape
    //   Π x₁ : T₁. … Π xₙ : Tₙ. Equality.{u}(carrier, LHS, RHS)
    // *and* the theorem has no universe parameters (first-cut
    // limitation: universe-arg instantiation at use-site isn't wired
    // up yet), index the lemma under both `spineHash(LHS)` and
    // `spineHash(RHS)`. The reverse-direction entry lets the calc
    // auto-prover handle `subLeft = … RHS-shape …`, wrapping the
    // emitted proof in `Equality.symmetry`.
    //
    // We skip degenerate shapes: zero binders (the LHS would be
    // closed, which makes the matcher pointless), or an LHS that is a
    // bare BoundVariable (would match anything and is unlikely to be
    // a useful rewrite).
    void registerGenericRewriteLemma(const std::string& theoremName,
                                       ExpressionPointer typeExpr) {
        // First-cut: zero-universe-parameter lemmas only.
        const Declaration* declaration =
            environment_.lookup(theoremName);
        if (!declaration) return;
        auto* asDefinition =
            std::get_if<Definition>(declaration);
        if (!asDefinition) return;
        if (!asDefinition->universeParameters.empty()) return;
        // Peel leading Pi binders, collecting each domain in
        // outer-to-inner order.
        std::vector<ExpressionPointer> rawDomains;
        ExpressionPointer cursor = typeExpr;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            rawDomains.push_back(pi->domain);
            cursor = pi->codomain;
        }
        int binderCount = static_cast<int>(rawDomains.size());
        if (binderCount == 0) return;
        // Body must be App(App(App(Equality, carrier), lhs), rhs).
        auto* eqApp3 = std::get_if<Application>(&cursor->node);
        if (!eqApp3) return;
        auto* eqApp2 =
            std::get_if<Application>(&eqApp3->function->node);
        if (!eqApp2) return;
        auto* eqApp1 =
            std::get_if<Application>(&eqApp2->function->node);
        if (!eqApp1) return;
        auto* eqHead = std::get_if<Constant>(&eqApp1->function->node);
        if (!eqHead || eqHead->name != "Equality") return;
        ExpressionPointer lhs = eqApp2->argument;
        ExpressionPointer rhs = eqApp3->argument;
        // Skip trivially-degenerate `(a : T) → a = a` shapes.
        if (std::holds_alternative<BoundVariable>(lhs->node)
            && std::holds_alternative<BoundVariable>(rhs->node)) {
            return;
        }
        // Lift each binder's domain into the conclusion's frame so
        // `instantiateLemmaBinders` can substitute via the binding
        // vector. Pi at peel index k (0 = outermost) has its domain in
        // a frame with k outer binders; the corresponding conclusion-
        // frame index is `binderCount - 1 - k`. The lift amount is
        // `binderCount - k` so that the OUTERMOST binder (peel index 0,
        // conclusion-frame index n-1, no inner BVs in its domain) shifts
        // by n — a no-op on closed domains — and the innermost (peel
        // index n-1, conclusion-frame index 0) shifts by 1 — moving its
        // BV(0..n-2) refs (to outer binders) up to BV(1..n-1).
        std::vector<ExpressionPointer> binderTypes(binderCount);
        for (int peelIdx = 0; peelIdx < binderCount; ++peelIdx) {
            int conclusionIdx = binderCount - 1 - peelIdx;
            binderTypes[conclusionIdx] = liftBoundVariables(
                rawDomains[peelIdx], binderCount - peelIdx, 0);
        }
        // Register both directions. When a side is a bare BoundVariable
        // its spineHash is the wildcard tag, which lands the entry in
        // the wildcard bucket. That bucket is consulted only when the
        // diff position is itself a leaf (a BV/FV/Sort) — so reverse-
        // direction identity entries don't pollute regular lookups.
        RewriteLemma forwardEntry;
        forwardEntry.lemmaName = theoremName;
        forwardEntry.binderCount = binderCount;
        forwardEntry.lhs = lhs;
        forwardEntry.rhs = rhs;
        forwardEntry.binderTypes = binderTypes;
        forwardEntry.reverseDirection = false;
        lemmaIndex_.emplace(spineHash(lhs),
                              std::move(forwardEntry));
        RewriteLemma reverseEntry;
        reverseEntry.lemmaName = theoremName;
        reverseEntry.binderCount = binderCount;
        reverseEntry.lhs = lhs;
        reverseEntry.rhs = rhs;
        reverseEntry.binderTypes = std::move(binderTypes);
        reverseEntry.reverseDirection = true;
        lemmaIndex_.emplace(spineHash(rhs),
                              std::move(reverseEntry));
    }

    // Auto-prover for unannotated calc steps. Given a calc step's
    // previous and next endpoints (both kernel terms in closed form),
    // try a small bag of strategies in priority order to construct a
    // proof of `Equality.{u}(carrier, previous, next)`. Returns
    // nullptr if none succeed; the caller then errors with a
    // "supply `by <reason>`" diagnostic.
    //
    // v0 strategies:
    //   1. Definitional equality via the kernel's isDefinitionallyEqual.
    //      Catches β/ι/δ reductions (e.g. `succ(b) + x` vs `succ(b+x)`).
    //
    // Future strategies (v1+):
    //   2. Single-position diff classified as commutativity /
    //      associativity / identity / local-hypothesis.
    //   3. Multi-position composition.
    ExpressionPointer autoProveCalcStep(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        ExpressionPointer stepEqualityType,
        int line, int column) {
        (void)stepEqualityType;
        (void)column;
        (void)line;
        // Strategy 2 below wraps with Equality.congruence. If that name
        // isn't declared (small test modules sometimes omit it), we'd
        // build a term referencing an undefined constant. Only the
        // pure-reflexivity strategy 1 below is safe in that case — and
        // it's cheap to keep, so we keep going past this point but skip
        // strategy 2 below.
        const bool congruenceAvailable =
            environment_.lookup("Equality.congruence") != nullptr;
        // ζ-unfold local let-binders so the structural matchers
        // (tryClassifyDiff path-walk, lemma index) see through surface
        // abbreviations. The kernel-level Equality at the original
        // endpoints is ζ-equal to the Equality at the unfolded
        // endpoints, so a proof for the unfolded form is also a proof
        // for the original (verified by the post-elaboration
        // isDefinitionallyEqual check against the original stepRelation
        // type, which now also sees let-values via ContextEntry.value).
        previousKernel = zetaUnfoldLetBinders(previousKernel, localBinders);
        nextKernel = zetaUnfoldLetBinders(nextKernel, localBinders);
        // Strategy 1: reflexivity for definitionally-equal endpoints.
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer previousOpened = openOverLocalBinders(
            previousKernel, localBinders, localBinders.size());
        ExpressionPointer nextOpened = openOverLocalBinders(
            nextKernel, localBinders, localBinders.size());
        if (isDefinitionallyEqual(environment_, openedContext,
                                    previousOpened, nextOpened)) {
            ExpressionPointer call =
                makeConstant("reflexivity", {carrierLevel});
            call = makeApplication(std::move(call), carrierType);
            call = makeApplication(std::move(call), previousKernel);
            return call;
        }
        // Strategy 2: single-position diff classification. Walk both
        // sides in lockstep through Application nodes. At each App
        // level there are three possibilities: function parts equal
        // (descend into argument), arguments equal (descend into
        // function), or both differ (bail). We collect a list of
        // path steps and reconstruct the proof inside-out with
        // Equality.congruence wrappers.
        // Skip strategy 2 entirely if Equality.congruence isn't in
        // scope — the wrappers below would reference an undefined
        // constant, and the eventual kernel error wouldn't carry
        // calc-step attribution.
        if (!congruenceAvailable) {
            return nullptr;
        }
        struct CalcPathStep {
            enum class Kind { Arg, Fn };
            Kind kind;
            // Arg: the function part that we're keeping fixed.
            // Fn:  the argument part that we're keeping fixed.
            ExpressionPointer savedSide;
        };
        std::vector<CalcPathStep> pathStepsOutsideIn;
        ExpressionPointer leftCursor = previousKernel;
        ExpressionPointer rightCursor = nextKernel;
        ExpressionPointer innerProof = nullptr;
        // At every level we first try to classify the current pair
        // directly (commutativity / associativity / identity / local-
        // hypothesis). Only descend if no classifier fires. This lets a
        // local hypothesis whose endpoints sit at some intermediate
        // level match without us descending past it.
        while (true) {
            innerProof = tryClassifyDiff(
                localBinders, openedContext, leftCursor, rightCursor);
            if (innerProof) break;
            auto* leftApp =
                std::get_if<Application>(&leftCursor->node);
            auto* rightApp =
                std::get_if<Application>(&rightCursor->node);
            if (!leftApp || !rightApp) break;
            bool functionEqual = structurallyEqual(
                leftApp->function, rightApp->function);
            bool argumentEqual = structurallyEqual(
                leftApp->argument, rightApp->argument);
            if (functionEqual && argumentEqual) {
                return nullptr;
            }
            if (functionEqual) {
                pathStepsOutsideIn.push_back(
                    {CalcPathStep::Kind::Arg, leftApp->function});
                leftCursor = leftApp->argument;
                rightCursor = rightApp->argument;
                continue;
            }
            if (argumentEqual) {
                pathStepsOutsideIn.push_back(
                    {CalcPathStep::Kind::Fn, leftApp->argument});
                leftCursor = leftApp->function;
                rightCursor = rightApp->function;
                continue;
            }
            // Multi-position diff at this level. Bail.
            break;
        }
        if (!innerProof) {
            // Phase-2 fallback: try AC rearrangement via the existing
            // `ring` proof emitter on the full goal. This catches
            // multi-position commutative / associative shuffles like
            // `(a + b) + (c + d) = (b + a) + (d + c)` that the
            // single-position walker bails on.
            ExpressionPointer ringProof = tryAcRearrangement(
                localBinders, previousKernel, nextKernel,
                carrierType, carrierLevel, line);
            if (ringProof) return ringProof;
            return nullptr;
        }
        // Wrap from innermost out. At each step we need the type of
        // the "varying side" (lambda domain) and the type of the
        // result of applying the lambda (lambda codomain). We use
        // inferTypeInLocalContext and typeUniverseOf to compute them
        // — if either throws, bail.
        ExpressionPointer currentLeft = leftCursor;
        ExpressionPointer currentRight = rightCursor;
        ExpressionPointer currentProof = innerProof;
        try {
            for (auto iterator = pathStepsOutsideIn.rbegin();
                 iterator != pathStepsOutsideIn.rend(); ++iterator) {
                const CalcPathStep& step = *iterator;
                LevelPointer varLevel = typeUniverseOf(
                    localBinders, currentLeft);
                // inferTypeInLocalContext returns the type in OPENED form
                // (with FVar references for local binders). We splice it
                // into a kernel term that's built in CLOSED form, so we
                // must close it back — otherwise an FVar reference to a
                // local binder (e.g. `carrier : Type(0)` parameter) leaks
                // into the emitted term and the kernel rejects it as an
                // unbound internal variable.
                ExpressionPointer varType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, currentLeft),
                    localBinders, localBinders.size());
                ExpressionPointer lambdaBody;
                ExpressionPointer outerLeft, outerRight;
                if (step.kind == CalcPathStep::Kind::Arg) {
                    ExpressionPointer liftedFunction =
                        liftBoundVariables(step.savedSide, 1, 0);
                    lambdaBody = makeApplication(
                        std::move(liftedFunction),
                        makeBoundVariable(0));
                    outerLeft = makeApplication(step.savedSide,
                                                 currentLeft);
                    outerRight = makeApplication(step.savedSide,
                                                  currentRight);
                } else {
                    ExpressionPointer liftedArgument =
                        liftBoundVariables(step.savedSide, 1, 0);
                    lambdaBody = makeApplication(
                        makeBoundVariable(0),
                        std::move(liftedArgument));
                    outerLeft = makeApplication(currentLeft,
                                                 step.savedSide);
                    outerRight = makeApplication(currentRight,
                                                  step.savedSide);
                }
                ExpressionPointer lambda = makeLambda(
                    "_calc_z", varType, std::move(lambdaBody));
                LevelPointer outerLevel = typeUniverseOf(
                    localBinders, outerLeft);
                ExpressionPointer outerType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, outerLeft),
                    localBinders, localBinders.size());
                ExpressionPointer call = makeConstant(
                    "Equality.congruence",
                    {varLevel, outerLevel});
                call = makeApplication(std::move(call), varType);
                call = makeApplication(std::move(call), outerType);
                call = makeApplication(std::move(call),
                                        std::move(lambda));
                call = makeApplication(std::move(call), currentLeft);
                call = makeApplication(std::move(call), currentRight);
                call = makeApplication(std::move(call),
                                        std::move(currentProof));
                currentProof = std::move(call);
                currentLeft = std::move(outerLeft);
                currentRight = std::move(outerRight);
            }
        } catch (const TypeError&) {
            return nullptr;
        } catch (const ElaborateError&) {
            return nullptr;
        }
        (void)carrierType;
        (void)carrierLevel;
        return currentProof;
    }

    // Non-calc wrapper around tryDiffApplyUserProof. Extracts the
    // equality endpoints from `goalClosed` and dispatches to the same
    // single-position diff walker used inside calc steps. Returns the
    // wrapped proof (with type definitionally equal to `goalClosed`)
    // on success, nullptr if either the goal isn't an Equality, the
    // hint isn't an Equality, or the walker can't bridge them.
    // Speculative check: if the user wrote `congruenceOf(λ, P)` at a
    // non-calc position where bare `P` would also close the goal via
    // diff inference, warn that the wrapper is redundant. Mirrors the
    // calc-step detector at the `by` site. No-op unless
    // --check-redundant-by is on. `surfaceExpression` is the source
    // expression at the position whose expected type is
    // `expectedTypeClosed` (already-elaborated form).
    void checkRedundantCongruenceOfWrapper(
        const SurfaceExpressionPointer& surfaceExpression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedTypeClosed,
        const std::string& positionLabel) {
        if (!reportRedundantBy_ || !surfaceExpression
            || !expectedTypeClosed) return;
        auto* surfApp = std::get_if<SurfaceApplication>(
            &surfaceExpression->node);
        if (!surfApp || surfApp->arguments.size() != 2) return;
        auto* head = std::get_if<SurfaceIdentifier>(
            &surfApp->function->node);
        if (!head || head->qualifiedName != "congruenceOf"
            || !head->universeArgs.empty()) return;
        ExpressionPointer innerKernel;
        try {
            innerKernel = elaborateExpression(
                *surfApp->arguments[1].value, localBinders);
        } catch (const ElaborateError&) { return; }
          catch (const TypeError&) { return; }
        if (!innerKernel) return;
        ExpressionPointer coerced = coerceToExpectedTypeViaDiff(
            localBinders, innerKernel, expectedTypeClosed);
        if (coerced == innerKernel) return;
        ExpressionPointer coercedType;
        try {
            coercedType = inferTypeInLocalContext(
                localBinders, coerced);
        } catch (const TypeError&) { return; }
          catch (const ElaborateError&) { return; }
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        if (isSubtype(environment_, openedContext,
                       coercedType, expectedOpened)) {
            std::cerr << "warning: " << moduleName_ << ":"
                << surfaceExpression->line << ":"
                << surfaceExpression->column
                << ": redundant congruenceOf wrapper at "
                << positionLabel
                << " — the inner lemma alone would close the goal "
                "(diff inference fills the lambda)\n";
        }
    }

    // After elaborating a term with an expected type, retry with
    // diff-wrap if the inferred type doesn't subtype-match the
    // expected type and both are Equality types with a unique
    // single-position diff. Returns the (possibly wrapped) term, or
    // the original term unchanged on either match or failure. Cheap
    // when types already match (one infer + one isSubtype check).
    ExpressionPointer coerceToExpectedTypeViaDiff(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer expectedTypeClosed) {
        ExpressionPointer termTypeOpened;
        try {
            termTypeOpened = inferTypeInLocalContext(
                localBinders, term);
        } catch (const TypeError&) {
            return term;
        } catch (const ElaborateError&) {
            return term;
        }
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        if (isSubtype(environment_, openedContext,
                       termTypeOpened, expectedOpened)) {
            return term;
        }
        ExpressionPointer termTypeClosed = closeOverLocalBinders(
            termTypeOpened, localBinders, localBinders.size());
        // Try the diff-wrap first (equality coercion via
        // Equality.congruence).
        ExpressionPointer wrapped = tryDiffWrapForEqualityGoal(
            localBinders, term, termTypeClosed, expectedTypeClosed);
        if (wrapped) return wrapped;
        // Classical LEM bridge: if term : ¬¬P and expected : P, wrap
        // with Logic.double_negation_eliminate. Lets `suppose ¬P as h;
        // …; claim False` at theorem body close a goal stated as P,
        // mirroring textbook reductio ad absurdum.
        wrapped = tryDoubleNegationElimination(
            localBinders, term, termTypeClosed, expectedTypeClosed);
        if (wrapped) return wrapped;
        // Bare-proposition-as-proof. When the user writes a Proposition
        // value (e.g. `N ≤ m`) where a proof of that proposition was
        // expected, and the written value is kernel-equal to the
        // expected type, dispatch the auto-prover. Reads as math:
        // `pointwiseBound(m, N ≤ m)` instead of `pointwiseBound(m,
        // given(N ≤ m))` or a contrived named binder. Mitigation
        // against silently fixing typos: we require kernel-equality
        // first, so an unrelated proposition still fails loudly.
        wrapped = tryBarePropositionAsProof(
            localBinders, term, termTypeOpened, expectedTypeClosed);
        if (wrapped) return wrapped;
        return term;
    }

    // Coerce a Proposition-valued term into a proof of itself when
    // the term equals the expected type. Returns nullptr if either
    // (a) the term isn't of type Proposition, or (b) the term isn't
    // kernel-equal to the expected type. On match, runs the
    // auto-prover and returns the resulting proof — re-wrapping
    // any ElaborateError with a message keyed to the bare-
    // proposition slot so the user sees `couldn't prove `<P>` to
    // fill the argument` rather than a raw dispatch error.
    ExpressionPointer tryBarePropositionAsProof(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeOpened,
        ExpressionPointer expectedTypeClosed) {
        // termTypeOpened must be the Proposition sort (Sort 0).
        ExpressionPointer termTypeWhnf = weakHeadNormalForm(
            environment_, termTypeOpened);
        auto* termTypeSort = std::get_if<Sort>(&termTypeWhnf->node);
        if (!termTypeSort) return nullptr;
        auto* termTypeLevel = std::get_if<LevelConst>(
            &termTypeSort->level->node);
        if (!termTypeLevel || termTypeLevel->value != 0) return nullptr;
        // The written proposition (`term`) must be kernel-equal to
        // the expected type. Compare in the opened representation so
        // BoundVariables on both sides align against the same FreeVar
        // identities — comparing a closed term against an opened one
        // would always fail.
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        ExpressionPointer termOpened = openOverLocalBinders(
            term, localBinders, localBinders.size());
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        if (!isDefinitionallyEqual(environment_, openedContext,
                                     termOpened, expectedOpened)) {
            return nullptr;
        }
        // Dispatch the full auto-prover on the matched proposition.
        try {
            return autoProveClaim(
                expectedTypeClosed, localBinders, /*line=*/0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

    // Classical LEM bridge — when `term : Not(Not(P))` and the goal
    // is `P`, wraps with `Logic.double_negation_eliminate(P, term)`.
    // Returns nullptr if the term's type isn't Not(Not(_)), if the
    // inner proposition doesn't match `expectedTypeClosed`, or if
    // `Logic.double_negation_eliminate` isn't in scope.
    //
    // `Not(X)` unfolds to `X → False` (definition in Logic.basics);
    // we WHNF on each layer so the structural match works whether
    // the term's type is spelled `Not(Not(P))` or `(P → False) →
    // False`.
    ExpressionPointer tryDoubleNegationElimination(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term,
        ExpressionPointer termTypeClosed,
        ExpressionPointer expectedTypeClosed) {
        if (!environment_.lookup(
                "Logic.double_negation_eliminate")) {
            return nullptr;
        }
        ExpressionPointer termTypeOpened = openOverLocalBinders(
            termTypeClosed, localBinders, localBinders.size());
        ExpressionPointer outerWhnf = weakHeadNormalForm(
            environment_, termTypeOpened);
        auto* outerPi = std::get_if<Pi>(&outerWhnf->node);
        if (!outerPi) return nullptr;
        // The outer Pi's codomain lives under its binder; if it
        // mentions BoundVariable(0) it isn't a Not-shape. We check
        // by WHNF'ing and verifying it's the constant `False` (which
        // doesn't reference the binder).
        ExpressionPointer outerCodomainWhnf = weakHeadNormalForm(
            environment_, outerPi->codomain);
        auto* outerCodomainConst = std::get_if<Constant>(
            &outerCodomainWhnf->node);
        if (!outerCodomainConst
            || outerCodomainConst->name != "False") {
            return nullptr;
        }
        // The inner Pi: domain of the outer is `Not(P) = P → False`.
        ExpressionPointer innerWhnf = weakHeadNormalForm(
            environment_, outerPi->domain);
        auto* innerPi = std::get_if<Pi>(&innerWhnf->node);
        if (!innerPi) return nullptr;
        ExpressionPointer innerCodomainWhnf = weakHeadNormalForm(
            environment_, innerPi->codomain);
        auto* innerCodomainConst = std::get_if<Constant>(
            &innerCodomainWhnf->node);
        if (!innerCodomainConst
            || innerCodomainConst->name != "False") {
            return nullptr;
        }
        // Inner Pi's domain is the P we need to match. Compare
        // against the opened expected type.
        ExpressionPointer expectedOpened = openOverLocalBinders(
            expectedTypeClosed, localBinders, localBinders.size());
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        if (!isDefinitionallyEqual(environment_, openedContext,
                                     innerPi->domain, expectedOpened)) {
            return nullptr;
        }
        // Build the call: Logic.double_negation_eliminate(P, term).
        ExpressionPointer call = makeConstant(
            "Logic.double_negation_eliminate", {});
        call = makeApplication(call, expectedTypeClosed);
        call = makeApplication(call, term);
        return call;
    }

    ExpressionPointer tryDiffWrapForEqualityGoal(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer hintTerm,
        ExpressionPointer hintType,
        ExpressionPointer goalClosed) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalClosed, localBinders, localBinders.size());
        ExpressionPointer goalWhnf = weakHeadNormalForm(
            environment_, goalOpened);
        EqualityComponents goalComps;
        try {
            goalComps = extractEqualityComponents(
                goalWhnf, "diff-wrap goal", 0);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        ExpressionPointer previousKernel = closeOverLocalBinders(
            goalComps.leftEndpoint, localBinders,
            localBinders.size());
        ExpressionPointer nextKernel = closeOverLocalBinders(
            goalComps.rightEndpoint, localBinders,
            localBinders.size());
        try {
            return tryDiffApplyUserProof(
                localBinders, previousKernel, nextKernel,
                hintTerm, hintType, 0, 0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

    // Given a user-supplied `by <equationProof>` for a calc `=` step,
    // see whether the proof's equation (a = b) sits at a unique
    // single-position diff between `previousKernel` and `nextKernel`.
    // If so, wrap with the chain of `Equality.congruence` calls to
    // produce a proof of `previousKernel = nextKernel`. Returns
    // nullptr on miss. Caller already verified the user proof's type
    // didn't directly match the step's expected type, so this is the
    // diff-inference fallback ("user wrote the equation, elaborator
    // finds the slot").
    ExpressionPointer tryDiffApplyUserProof(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer userProof,
        ExpressionPointer userProofType,
        int line, int column) {
        (void)column;
        (void)line;
        // The diff-inference fallback wraps with Equality.congruence;
        // refuse the attempt if that name isn't declared, otherwise we'd
        // hand the kernel a term referencing an undefined constant and
        // the eventual addDefinition would report it without any calc-
        // step attribution context (the calc-step frame is long gone by
        // then). Returning nullptr here lets the caller fall through to
        // its normal "type mismatch" error path, which fires inside the
        // calc-step Frame and reports the line of the offending step.
        if (!environment_.lookup("Equality.congruence")) {
            return nullptr;
        }
        // Extract (carrierLevel, T, a, b) from userProofType.
        ExpressionPointer userTypeWhnf = weakHeadNormalForm(
            environment_, userProofType);
        EqualityComponents components;
        try {
            components = extractEqualityComponents(
                userTypeWhnf, "calc step diff", line);
        } catch (const ElaborateError&) {
            return nullptr;
        }
        ExpressionPointer userLeft = components.leftEndpoint;
        ExpressionPointer userRight = components.rightEndpoint;
        ExpressionPointer userCarrier = components.carrierType;
        LevelPointer userCarrierLevel = components.carrierUniverseLevel;
        // ζ-unfold local let-binders (consistent with autoProveCalcStep).
        previousKernel = zetaUnfoldLetBinders(previousKernel, localBinders);
        nextKernel = zetaUnfoldLetBinders(nextKernel, localBinders);
        Context openedContext = buildContextFromLocalBinders(localBinders);
        // Lockstep walk: descend via App nodes, at each level check
        // if the user proof matches (forward or symmetric).
        struct CalcPathStep {
            enum class Kind { Arg, Fn };
            Kind kind;
            ExpressionPointer savedSide;
        };
        std::vector<CalcPathStep> pathStepsOutsideIn;
        ExpressionPointer leftCursor = previousKernel;
        ExpressionPointer rightCursor = nextKernel;
        ExpressionPointer innerProof = nullptr;
        ExpressionPointer userLeftOpened = openOverLocalBinders(
            userLeft, localBinders, localBinders.size());
        ExpressionPointer userRightOpened = openOverLocalBinders(
            userRight, localBinders, localBinders.size());
        ExpressionPointer userCarrierClosed = closeOverLocalBinders(
            userCarrier, localBinders, localBinders.size());
        while (true) {
            ExpressionPointer leftOpened = openOverLocalBinders(
                leftCursor, localBinders, localBinders.size());
            ExpressionPointer rightOpened = openOverLocalBinders(
                rightCursor, localBinders, localBinders.size());
            bool forwardMatch =
                isDefinitionallyEqual(environment_, openedContext,
                                       leftOpened, userLeftOpened)
                && isDefinitionallyEqual(environment_, openedContext,
                                          rightOpened, userRightOpened);
            if (forwardMatch) {
                innerProof = userProof;
                break;
            }
            bool symmetricMatch =
                isDefinitionallyEqual(environment_, openedContext,
                                       leftOpened, userRightOpened)
                && isDefinitionallyEqual(environment_, openedContext,
                                          rightOpened, userLeftOpened);
            if (symmetricMatch) {
                // Wrap with Equality.symmetry.
                ExpressionPointer symmetryCall = makeConstant(
                    "Equality.symmetry", {userCarrierLevel});
                symmetryCall = makeApplication(
                    std::move(symmetryCall), userCarrierClosed);
                symmetryCall = makeApplication(
                    std::move(symmetryCall),
                    closeOverLocalBinders(userRight, localBinders,
                                            localBinders.size()));
                symmetryCall = makeApplication(
                    std::move(symmetryCall),
                    closeOverLocalBinders(userLeft, localBinders,
                                            localBinders.size()));
                symmetryCall = makeApplication(
                    std::move(symmetryCall), userProof);
                innerProof = std::move(symmetryCall);
                break;
            }
            // Descend through Application nodes. If structural compare
            // bails (neither function nor argument structurally equal),
            // retry once after WHNF — unfolds Definition heads (e.g.
            // `Rational.subtract` → `+`/`negate`) and exposes reduced
            // App spines (`Natural.add(successor(_), _)` → `successor(
            // Natural.add(_, _))`). The reconstruction below uses the
            // post-WHNF saved sides; the resulting proof type is
            // definitionally equal to the original calc-step type, so
            // the caller's coercion accepts it.
            auto descendOrWhnf = [&]() -> bool {
                auto* leftApp =
                    std::get_if<Application>(&leftCursor->node);
                auto* rightApp =
                    std::get_if<Application>(&rightCursor->node);
                if (leftApp && rightApp) {
                    bool functionEqual = structurallyEqual(
                        leftApp->function, rightApp->function);
                    bool argumentEqual = structurallyEqual(
                        leftApp->argument, rightApp->argument);
                    if (functionEqual && argumentEqual) return false;
                    if (functionEqual) {
                        pathStepsOutsideIn.push_back(
                            {CalcPathStep::Kind::Arg,
                             leftApp->function});
                        leftCursor = leftApp->argument;
                        rightCursor = rightApp->argument;
                        return true;
                    }
                    if (argumentEqual) {
                        pathStepsOutsideIn.push_back(
                            {CalcPathStep::Kind::Fn,
                             leftApp->argument});
                        leftCursor = leftApp->function;
                        rightCursor = rightApp->function;
                        return true;
                    }
                }
                ExpressionPointer leftWhnf = weakHeadNormalForm(
                    environment_, leftCursor);
                ExpressionPointer rightWhnf = weakHeadNormalForm(
                    environment_, rightCursor);
                bool leftChanged =
                    !structurallyEqual(leftWhnf, leftCursor);
                bool rightChanged =
                    !structurallyEqual(rightWhnf, rightCursor);
                if (!leftChanged && !rightChanged) return false;
                leftCursor = leftWhnf;
                rightCursor = rightWhnf;
                return true;
            };
            if (!descendOrWhnf()) break;
        }
        if (!innerProof) return nullptr;
        // Wrap from innermost out with Equality.congruence (mirrors
        // autoProveCalcStep's wrapping loop).
        ExpressionPointer currentLeft = leftCursor;
        ExpressionPointer currentRight = rightCursor;
        ExpressionPointer currentProof = innerProof;
        try {
            for (auto iterator = pathStepsOutsideIn.rbegin();
                 iterator != pathStepsOutsideIn.rend(); ++iterator) {
                const CalcPathStep& step = *iterator;
                LevelPointer varLevel = typeUniverseOf(
                    localBinders, currentLeft);
                ExpressionPointer varType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, currentLeft),
                    localBinders, localBinders.size());
                ExpressionPointer lambdaBody;
                ExpressionPointer outerLeft, outerRight;
                if (step.kind == CalcPathStep::Kind::Arg) {
                    ExpressionPointer liftedFunction =
                        liftBoundVariables(step.savedSide, 1, 0);
                    lambdaBody = makeApplication(
                        std::move(liftedFunction),
                        makeBoundVariable(0));
                    outerLeft = makeApplication(step.savedSide,
                                                 currentLeft);
                    outerRight = makeApplication(step.savedSide,
                                                  currentRight);
                } else {
                    ExpressionPointer liftedArgument =
                        liftBoundVariables(step.savedSide, 1, 0);
                    lambdaBody = makeApplication(
                        makeBoundVariable(0),
                        std::move(liftedArgument));
                    outerLeft = makeApplication(currentLeft,
                                                 step.savedSide);
                    outerRight = makeApplication(currentRight,
                                                  step.savedSide);
                }
                ExpressionPointer lambda = makeLambda(
                    "_calc_z", varType, std::move(lambdaBody));
                LevelPointer outerLevel = typeUniverseOf(
                    localBinders, outerLeft);
                ExpressionPointer outerType = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, outerLeft),
                    localBinders, localBinders.size());
                ExpressionPointer call = makeConstant(
                    "Equality.congruence", {varLevel, outerLevel});
                call = makeApplication(std::move(call), varType);
                call = makeApplication(std::move(call), outerType);
                call = makeApplication(std::move(call),
                                        std::move(lambda));
                call = makeApplication(std::move(call), currentLeft);
                call = makeApplication(std::move(call), currentRight);
                call = makeApplication(std::move(call),
                                        std::move(currentProof));
                currentProof = std::move(call);
                currentLeft = std::move(outerLeft);
                currentRight = std::move(outerRight);
            }
        } catch (const TypeError&) {
            return nullptr;
        } catch (const ElaborateError&) {
            return nullptr;
        }
        return currentProof;
    }

    // Phase-2 fallback: invoke the existing `ring` proof emitter on
    // the goal `Equality(carrier, previous, next)`. Handles
    // multi-position AC rearrangement that the single-position
    // walker bails on. Returns nullptr on miss (e.g., the goal
    // isn't a pure sum or pure product of the same multiset of
    // atoms).
    ExpressionPointer tryAcRearrangement(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        int line) {
        ExpressionPointer expectedType = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {carrierLevel}),
                    carrierType),
                previousKernel),
            nextKernel);
        try {
            return elaborateRing(localBinders, expectedType, line, 0);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    }

    // Phase 3 first-order matcher. Walks `pattern` (a lemma's LHS or
    // RHS, in closed-over-binders form) against `subject` (a term
    // from the calc step's diff position, in closed-over-local-binders
    // form). A BoundVariable in the pattern with index < binderCount
    // is treated as a metavariable: on first occurrence it binds to
    // the subject sub-term; on subsequent occurrences the new binding
    // must be `structurallyEqual` to the existing one. Non-BV
    // positions must match exactly (with `levelsDefinitionallyEqual`
    // for Sort levels and Constant universe arguments).
    //
    // On success, `bindings[i]` holds the value matched against the
    // lemma's binder with de Bruijn index `i` (so `bindings[0]` is the
    // innermost binder). On failure, `bindings` may be partially
    // populated; the caller treats that as "no match".
    //
    // `piDepth` tracks how many local Pi binders the matcher has
    // descended into during recursion. A pattern BV index < piDepth
    // refers to a descended Pi binder (must match the subject's BV
    // literally). A pattern BV index in [piDepth, piDepth +
    // binderCount) refers to lemma metavariable slot
    // `(index - piDepth)`.
    bool matchAgainstPattern(
        ExpressionPointer pattern,
        ExpressionPointer subject,
        int binderCount,
        std::vector<ExpressionPointer>& bindings,
        int piDepth = 0) {
        if (auto* patternBV =
                std::get_if<BoundVariable>(&pattern->node)) {
            int idx = patternBV->deBruijnIndex;
            if (idx >= piDepth && idx < piDepth + binderCount) {
                int slot = idx - piDepth;
                // The subject must live in the OUTER scope (no
                // references to the piDepth local Pi binders); else
                // the binding would be unground when the lemma is
                // applied. Detect and bail.
                if (piDepth > 0
                    && referencesAnyBoundInRange(
                           subject, 0, piDepth)) {
                    return false;
                }
                // Shift the subject down by piDepth so it lives in
                // the same scope as the other bindings (the
                // lemma-application context).
                ExpressionPointer shiftedSubject = piDepth > 0
                    ? liftBoundVariables(subject, -piDepth, 0)
                    : subject;
                if (!bindings[slot]) {
                    bindings[slot] = shiftedSubject;
                    return true;
                }
                return structurallyEqual(
                    bindings[slot], shiftedSubject);
            }
            // idx < piDepth: descended Pi binder; idx >=
            // piDepth + binderCount: outer-scope binder. Either
            // way, subject must be the same BV index.
            auto* s = std::get_if<BoundVariable>(&subject->node);
            return s && s->deBruijnIndex == idx;
        }
        if (pattern->node.index() != subject->node.index()) {
            // Kind mismatch — try WHNF on the subject. A δ-defined
            // head (e.g. `Integer.LessOrEqual` unfolding to an
            // `Exists`) might expose the shape the pattern wants.
            ExpressionPointer subjectWhnf = weakHeadNormalForm(
                environment_, subject);
            if (subjectWhnf.get() != subject.get()) {
                return matchAgainstPattern(
                    pattern, subjectWhnf,
                    binderCount, bindings, piDepth);
            }
            return false;
        }
        if (auto* p = std::get_if<BoundVariable>(&pattern->node)) {
            (void)p;
            // Handled above; this branch is for the
            // (pattern is non-BV but subject is BV) reject case.
            return false;
        }
        if (auto* p = std::get_if<FreeVariable>(&pattern->node)) {
            auto* s = std::get_if<FreeVariable>(&subject->node);
            return p->name == s->name && p->origin == s->origin;
        }
        if (auto* p = std::get_if<Sort>(&pattern->node)) {
            auto* s = std::get_if<Sort>(&subject->node);
            return levelsDefinitionallyEqual(p->level, s->level);
        }
        if (auto* p = std::get_if<Application>(&pattern->node)) {
            auto* s = std::get_if<Application>(&subject->node);
            if (s) {
                // Structural attempt — bindings is scratch; save in
                // case we need to retry after WHNF.
                std::vector<ExpressionPointer> savedBindings =
                    bindings;
                if (matchAgainstPattern(
                        p->function, s->function,
                        binderCount, bindings, piDepth)
                    && matchAgainstPattern(
                        p->argument, s->argument,
                        binderCount, bindings, piDepth)) {
                    return true;
                }
                bindings = savedBindings;
            }
            // Structural failed (or subject kinds disagreed). Try
            // WHNF on the subject: a δ/ι-reducing head (e.g.
            // `successor(p) * q` → `q + p*q`) might expose the App
            // shape the pattern needs. Bail if WHNF is a no-op.
            ExpressionPointer subjectWhnf = weakHeadNormalForm(
                environment_, subject);
            if (subjectWhnf.get() != subject.get()) {
                return matchAgainstPattern(
                    pattern, subjectWhnf,
                    binderCount, bindings, piDepth);
            }
            return false;
        }
        if (auto* p = std::get_if<Constant>(&pattern->node)) {
            auto* s = std::get_if<Constant>(&subject->node);
            if (p->name != s->name) return false;
            if (p->universeArguments.size()
                    != s->universeArguments.size()) {
                return false;
            }
            for (size_t i = 0; i < p->universeArguments.size(); ++i) {
                if (!levelsDefinitionallyEqual(
                        p->universeArguments[i],
                        s->universeArguments[i])) {
                    return false;
                }
            }
            return true;
        }
        if (auto* p = std::get_if<Pi>(&pattern->node)) {
            auto* s = std::get_if<Pi>(&subject->node);
            // The Pi binder itself is a local fresh variable in both
            // pattern and subject; recurse into domain at the same
            // piDepth (the binder isn't visible from its own domain)
            // and into codomain at piDepth + 1.
            return matchAgainstPattern(p->domain, s->domain,
                                          binderCount, bindings, piDepth)
                && matchAgainstPattern(p->codomain, s->codomain,
                                          binderCount, bindings,
                                          piDepth + 1);
        }
        // Lambda / Let are rare in lemma LHSs and need extra binder
        // bookkeeping; bail conservatively.
        return false;
    }

    // Does `expression` contain any BoundVariable in the half-open
    // range `[low, high)` (interpreted in expression's own scope)?
    // Used by matchAgainstPattern to detect when a candidate metavar
    // binding would reference a local Pi binder that won't survive
    // when the lemma is applied in the outer context.
    bool referencesAnyBoundInRange(
        ExpressionPointer expression, int low, int high,
        int currentDepth = 0) {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            int idx = bv->deBruijnIndex - currentDepth;
            return idx >= low && idx < high;
        }
        if (auto* app =
                std::get_if<Application>(&expression->node)) {
            return referencesAnyBoundInRange(
                       app->function, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       app->argument, low, high, currentDepth);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesAnyBoundInRange(
                       pi->domain, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       pi->codomain, low, high, currentDepth + 1);
        }
        if (auto* lam = std::get_if<Lambda>(&expression->node)) {
            return referencesAnyBoundInRange(
                       lam->domain, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       lam->body, low, high, currentDepth + 1);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return referencesAnyBoundInRange(
                       let->type, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       let->value, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       let->body, low, high, currentDepth + 1);
        }
        return false;
    }

    // Simultaneously substitute the matched bindings into a lemma's
    // LHS or RHS. The lemma's expression is in closed-over-binders
    // form: BoundVariable indices `0..bindings.size()-1` refer to the
    // lemma's metavariable binders; `bindings[i]` is the value for
    // BV(i), expressed in the *subject's* (calc-step) scope. The
    // result lives in the subject's scope.
    //
    // We do this in a single walk rather than chaining the kernel's
    // single-binder `substitute`. The chained-substitute approach
    // corrupts a binding's BoundVariable indices the second time the
    // walker passes over it: after substituting BV(0) → bindings[0],
    // a subsequent `substitute(_, 0, bindings[1])` walks the entire
    // tree (including bindings[0]) and decrements BV(>=1) — clobbering
    // bindings[0]'s outer-binder references. A single combined walk
    // sidesteps that by treating each binding as opaque once placed.
    // Emit an "unused name" warning when a binder a user explicitly
    // named (let, claim, suppose, choose, case … as, by_induction
    // with ih, etc.) is closed and the body it scopes over never
    // references it. The body is elaborated under the binder, so a
    // BV(0) inside `body` refers to the just-introduced name. Names
    // starting with '_' are anonymous (e.g. synthesised calc names)
    // and skipped. Gated by `--check-redundant-by` (default on).
    //
    // `form` is a short noun phrase describing where the binder came
    // from — embedded directly into the warning so the user knows
    // which surface construct to edit (e.g. "let binding",
    // "`case … as`", "`suppose … as`").
    void warnIfBinderUnused(
        const std::string& name,
        ExpressionPointer bodyUnderBinder,
        int line, int column,
        const char* form) {
        warnIfBinderUnusedAtIndex(
            name, bodyUnderBinder, /*relativeIndex=*/0,
            line, column, form);
    }

    // Variant taking an explicit relative BV index. Multi-binder
    // lambdas (`function (x : T) (y : U) => …`) push N binders
    // before elaborating the body, so binder i (0-based, outer-
    // first) is at BV(N - 1 - i) relative to that body.
    void warnIfBinderUnusedAtIndex(
        const std::string& name,
        ExpressionPointer bodyUnderBinders,
        int relativeIndex,
        int line, int column,
        const char* form) {
        if (!reportRedundantBy_) return;
        if (name.empty() || name[0] == '_') return;
        if (referencesBoundVariable(bodyUnderBinders, relativeIndex)) return;
        emitUnusedNameWarning(name, line, column, form);
    }

    // Variant: check at the surface-AST level by walking the body
    // expression and looking for any `SurfaceIdentifier` referencing
    // `name`. Useful when the binder is introduced via a desugaring
    // (e.g. `choose N such that …;` builds a destructure) and we
    // don't have a clean post-elaboration body to inspect. False-
    // negatives are possible if the user shadows `name` inside the
    // body — that's tolerated; the warning is advisory.
    void warnIfSurfaceNameUnused(
        const std::string& name,
        const SurfaceExpression& body,
        int line, int column,
        const char* form) {
        if (!reportRedundantBy_) return;
        if (name.empty() || name[0] == '_') return;
        if (surfaceMentionsName(body, name)) return;
        emitUnusedNameWarning(name, line, column, form);
    }

    // True if `expression` contains any construct that hands the goal
    // to the auto-prover at elaboration time (`claim` in any of its
    // shapes — bare, with proposition, with `by cases`, with
    // substitution; `contradiction` likewise). Used by the `choose`
    // unused-name check: when the auto-prover runs inside the body,
    // it can consume any in-scope hypothesis, so a witness name `N`
    // bound by `choose N such that P(N);` is potentially used through
    // the anonymous P(N) hypothesis even if N never appears in the
    // body's surface tree.
    bool surfaceContainsAutoProverInvocation(
        const SurfaceExpression& expression) {
        if (std::get_if<SurfaceStructuredClaim>(&expression.node)) {
            return true;
        }
        // Walk children of every surface variant we know about,
        // looking for nested auto-prover-using constructs. Cheapest
        // by far is reusing surfaceMentionsName's tree walk via a
        // lambda — but its body is large and special-cased per
        // variant; easier to walk the same shape here.
        if (auto* app =
                std::get_if<SurfaceApplication>(&expression.node)) {
            if (app->function
                && surfaceContainsAutoProverInvocation(*app->function))
                return true;
            for (const auto& arg : app->arguments) {
                if (arg.value && surfaceContainsAutoProverInvocation(
                                      *arg.value))
                    return true;
            }
            return false;
        }
        if (auto* lambda =
                std::get_if<SurfaceLambda>(&expression.node)) {
            return lambda->body
                && surfaceContainsAutoProverInvocation(*lambda->body);
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            if (let->value
                && surfaceContainsAutoProverInvocation(*let->value))
                return true;
            return let->body
                && surfaceContainsAutoProverInvocation(*let->body);
        }
        if (auto* asc =
                std::get_if<SurfaceAscription>(&expression.node)) {
            return asc->expression
                && surfaceContainsAutoProverInvocation(*asc->expression);
        }
        if (auto* cas = std::get_if<SurfaceCases>(&expression.node)) {
            if (cas->scrutinee
                && surfaceContainsAutoProverInvocation(*cas->scrutinee))
                return true;
            for (const auto& clause : cas->clauses) {
                if (clause.body
                    && surfaceContainsAutoProverInvocation(
                            *clause.body))
                    return true;
            }
            return false;
        }
        if (auto* calcNode =
                std::get_if<SurfaceCalc>(&expression.node)) {
            // A `by`-less calc step IS an auto-prover invocation.
            for (const auto& step : calcNode->steps) {
                if (!step.stepProof) return true;
                if (step.stepProof
                    && surfaceContainsAutoProverInvocation(
                            *step.stepProof))
                    return true;
            }
            return calcNode->initialExpression
                && surfaceContainsAutoProverInvocation(
                        *calcNode->initialExpression);
        }
        if (auto* tup =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            for (const auto& c : tup->components) {
                if (c && surfaceContainsAutoProverInvocation(*c))
                    return true;
            }
            return false;
        }
        if (auto* choose =
                std::get_if<SurfaceChoose>(&expression.node)) {
            if (choose->predicate
                && surfaceContainsAutoProverInvocation(
                        *choose->predicate))
                return true;
            return choose->body
                && surfaceContainsAutoProverInvocation(*choose->body);
        }
        if (auto* given =
                std::get_if<SurfaceGiven>(&expression.node)) {
            return given->proposition
                && surfaceContainsAutoProverInvocation(
                        *given->proposition);
        }
        if (auto* unfold =
                std::get_if<SurfaceUnfold>(&expression.node)) {
            return unfold->body
                && surfaceContainsAutoProverInvocation(*unfold->body);
        }
        if (auto* note =
                std::get_if<SurfaceNote>(&expression.node)) {
            // `note <prop>;` itself invokes the auto-prover.
            if (note->proposition) return true;
            return note->body
                && surfaceContainsAutoProverInvocation(*note->body);
        }
        if (auto* decide =
                std::get_if<SurfaceDecide>(&expression.node)) {
            if (decide->yesBody
                && surfaceContainsAutoProverInvocation(*decide->yesBody))
                return true;
            return decide->noBody
                && surfaceContainsAutoProverInvocation(*decide->noBody);
        }
        // Leaves (identifier, numeric literal, sort, type, etc.) and
        // any variants not enumerated above can't host an auto-prover
        // call — return false.
        return false;
    }

    void emitUnusedNameWarning(
        const std::string& name, int line, int column,
        const char* form) {
        std::cerr << "warning: " << moduleName_
            << ":" << line << ":" << column
            << ": unused name `" << name
            << "` introduced by " << form
            << " — the body never references it; drop it\n";
    }

    bool surfaceMentionsName(
        const SurfaceExpression& expression,
        const std::string& name) {
        if (auto* id =
                std::get_if<SurfaceIdentifier>(&expression.node)) {
            return id->qualifiedName == name;
        }
        if (auto* app =
                std::get_if<SurfaceApplication>(&expression.node)) {
            if (surfaceMentionsName(*app->function, name)) return true;
            for (const auto& arg : app->arguments) {
                if (arg.value
                    && surfaceMentionsName(*arg.value, name)) {
                    return true;
                }
            }
            return false;
        }
        if (auto* pi =
                std::get_if<SurfacePiType>(&expression.node)) {
            if (pi->binder.type
                && surfaceMentionsName(*pi->binder.type, name))
                return true;
            return pi->codomain
                && surfaceMentionsName(*pi->codomain, name);
        }
        if (auto* lambda =
                std::get_if<SurfaceLambda>(&expression.node)) {
            if (lambda->binder.type
                && surfaceMentionsName(*lambda->binder.type, name))
                return true;
            return lambda->body
                && surfaceMentionsName(*lambda->body, name);
        }
        if (auto* let =
                std::get_if<SurfaceLet>(&expression.node)) {
            if (let->type
                && surfaceMentionsName(*let->type, name)) return true;
            if (let->value
                && surfaceMentionsName(*let->value, name)) return true;
            return let->body
                && surfaceMentionsName(*let->body, name);
        }
        if (auto* asc =
                std::get_if<SurfaceAscription>(&expression.node)) {
            if (asc->expression
                && surfaceMentionsName(*asc->expression, name))
                return true;
            return asc->type
                && surfaceMentionsName(*asc->type, name);
        }
        if (auto* bin =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (bin->left
                && surfaceMentionsName(*bin->left, name)) return true;
            return bin->right
                && surfaceMentionsName(*bin->right, name);
        }
        if (auto* un =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            return un->operand
                && surfaceMentionsName(*un->operand, name);
        }
        if (auto* tup =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            for (const auto& c : tup->components) {
                if (c && surfaceMentionsName(*c, name)) return true;
            }
            return false;
        }
        if (auto* cas =
                std::get_if<SurfaceCases>(&expression.node)) {
            if (cas->scrutinee
                && surfaceMentionsName(*cas->scrutinee, name))
                return true;
            for (const auto& clause : cas->clauses) {
                if (clause.body
                    && surfaceMentionsName(*clause.body, name))
                    return true;
            }
            return false;
        }
        if (auto* calcNode =
                std::get_if<SurfaceCalc>(&expression.node)) {
            if (calcNode->initialExpression
                && surfaceMentionsName(
                    *calcNode->initialExpression, name))
                return true;
            for (const auto& step : calcNode->steps) {
                if (step.nextExpression
                    && surfaceMentionsName(
                        *step.nextExpression, name)) return true;
                if (step.stepProof
                    && surfaceMentionsName(
                        *step.stepProof, name)) return true;
            }
            return false;
        }
        if (auto* claim =
                std::get_if<SurfaceStructuredClaim>(&expression.node)) {
            if (claim->proposition
                && surfaceMentionsName(*claim->proposition, name))
                return true;
            if (claim->byHint
                && surfaceMentionsName(*claim->byHint, name))
                return true;
            for (const auto& arm : claim->arms) {
                if (arm.body
                    && surfaceMentionsName(*arm.body, name))
                    return true;
                if (arm.disjunctType
                    && surfaceMentionsName(
                        *arm.disjunctType, name)) return true;
            }
            return false;
        }
        if (auto* choose =
                std::get_if<SurfaceChoose>(&expression.node)) {
            if (choose->predicate
                && surfaceMentionsName(*choose->predicate, name))
                return true;
            return choose->body
                && surfaceMentionsName(*choose->body, name);
        }
        if (auto* given =
                std::get_if<SurfaceGiven>(&expression.node)) {
            return given->proposition
                && surfaceMentionsName(*given->proposition, name);
        }
        if (auto* note =
                std::get_if<SurfaceNote>(&expression.node)) {
            if (note->goalType
                && surfaceMentionsName(*note->goalType, name))
                return true;
            if (note->proposition
                && surfaceMentionsName(*note->proposition, name))
                return true;
            return note->body
                && surfaceMentionsName(*note->body, name);
        }
        if (auto* decide =
                std::get_if<SurfaceDecide>(&expression.node)) {
            if (decide->proposition
                && surfaceMentionsName(*decide->proposition, name))
                return true;
            if (decide->yesBody
                && surfaceMentionsName(*decide->yesBody, name))
                return true;
            return decide->noBody
                && surfaceMentionsName(*decide->noBody, name);
        }
        // Leaf / specialised nodes (numeric literal, Type,
        // Proposition, hammer, sorry, ring, etc.) don't have
        // identifier subterms to recurse into.
        return false;
    }

    // Whether `expression` references a BoundVariable at the relative
    // de Bruijn index `targetIndex` (counting outward from the
    // expression's enclosing scope). Used by `warnIfBinderUnused`
    // for the user-binder unused-name warning: after elaborating
    // the body, we check whether it has any BV(0) reference (i.e.
    // uses the just-introduced binder).
    bool referencesBoundVariable(
        ExpressionPointer expression, int targetIndex) {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            return bv->deBruijnIndex == targetIndex;
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return referencesBoundVariable(
                       application->function, targetIndex)
                || referencesBoundVariable(
                       application->argument, targetIndex);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesBoundVariable(pi->domain, targetIndex)
                || referencesBoundVariable(
                       pi->codomain, targetIndex + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return referencesBoundVariable(lambda->domain, targetIndex)
                || referencesBoundVariable(
                       lambda->body, targetIndex + 1);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return referencesBoundVariable(let->type, targetIndex)
                || referencesBoundVariable(let->value, targetIndex)
                || referencesBoundVariable(let->body, targetIndex + 1);
        }
        return false;
    }

    // Whether every BoundVariable reference in `expression` that maps
    // to a lemma binder (relative index < bindings.size()) has a
    // non-null entry in `bindings`. Used by the precondition-discharge
    // pass in `tryLemmaIndexLookup` to know whether a binder type can
    // be safely instantiated yet, given only partial bindings.
    bool binderReferencesAllBound(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth = 0) {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            if (bv->deBruijnIndex < nestedBinderDepth) return true;
            int relative = bv->deBruijnIndex - nestedBinderDepth;
            if (relative >= static_cast<int>(bindings.size())) {
                return true;
            }
            return bindings[relative] != nullptr;
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return binderReferencesAllBound(
                       application->function, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       application->argument, bindings, nestedBinderDepth);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return binderReferencesAllBound(
                       pi->domain, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       pi->codomain, bindings, nestedBinderDepth + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return binderReferencesAllBound(
                       lambda->domain, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       lambda->body, bindings, nestedBinderDepth + 1);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return binderReferencesAllBound(
                       let->type, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       let->value, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       let->body, bindings, nestedBinderDepth + 1);
        }
        return true;
    }

    ExpressionPointer instantiateLemmaBinders(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth = 0) {
        int N = static_cast<int>(bindings.size());
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            if (bv->deBruijnIndex < nestedBinderDepth) {
                return expression;
            }
            int relative = bv->deBruijnIndex - nestedBinderDepth;
            if (relative < N) {
                return liftBoundVariables(bindings[relative],
                                            nestedBinderDepth, 0);
            }
            // A reference past the lemma's own binders. Library
            // rewrite lemmas shouldn't produce one, but if they do,
            // close the gap left by the eliminated lemma binders.
            return makeBoundVariable(
                bv->deBruijnIndex - N);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                instantiateLemmaBinders(application->function,
                                          bindings, nestedBinderDepth),
                instantiateLemmaBinders(application->argument,
                                          bindings, nestedBinderDepth));
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                instantiateLemmaBinders(pi->domain, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(pi->codomain, bindings,
                                          nestedBinderDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                instantiateLemmaBinders(lambda->domain, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(lambda->body, bindings,
                                          nestedBinderDepth + 1));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                instantiateLemmaBinders(let->type, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(let->value, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(let->body, bindings,
                                          nestedBinderDepth + 1));
        }
        return expression;
    }

    // Phase 3 lemma-index lookup. Tries to close `subLeft = subRight`
    // (at a single calc-step diff position) using a registered rewrite
    // lemma. Subsumes the bespoke commutativity / associativity /
    // identity classifiers and additionally fires on arbitrary
    // user-written rewrite lemmas. Returns nullptr on miss; caller
    // falls through to the local-hypothesis path and then to the
    // Phase-2 AC-rearrangement fallback.
    ExpressionPointer tryLemmaIndexLookup(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
        // We look up two buckets: the subLeft-keyed bucket, and the
        // wildcard bucket. The wildcard bucket holds reverse-direction
        // entries for lemmas whose RHS is a bare metavariable (e.g.
        // the identity `(x : T) → op(x, unit) = x`, which we want to
        // fire when subLeft is `x` and subRight is `op(x, unit)`). The
        // forward-direction entry of those lemmas, indexed under their
        // op-headed LHS, lands in the regular bucket as usual.
        std::vector<uint64_t> keys;
        keys.push_back(spineHash(subLeft));
        ExpressionPointer wildcardProbe = makeBoundVariable(0);
        uint64_t wildcardKey = spineHash(wildcardProbe);
        if (wildcardKey != keys[0]) {
            keys.push_back(wildcardKey);
        }
        for (uint64_t key : keys) {
        auto range = lemmaIndex_.equal_range(key);
        for (auto iterator = range.first;
             iterator != range.second; ++iterator) {
            const RewriteLemma& lemma = iterator->second;
            std::vector<ExpressionPointer> bindings(lemma.binderCount);
            ExpressionPointer patternFor = lemma.reverseDirection
                ? lemma.rhs : lemma.lhs;
            ExpressionPointer otherSide = lemma.reverseDirection
                ? lemma.lhs : lemma.rhs;
            if (!matchAgainstPattern(patternFor, subLeft,
                                       lemma.binderCount, bindings)) {
                continue;
            }
            // Symmetric pass: also match `otherSide` against
            // `subRight` so the lemma's binders get filled from
            // WHICHEVER side carries them. Without this, a lemma
            // stated `-x + x = 0` would fire on `-1 + 1 = 0` (the
            // matched LHS binds x) but NOT on `0 = -1 + 1` (the
            // matched RHS is bare, leaving x unbound). matchAgainst-
            // Pattern's set-or-check logic also doubles as the
            // consistency check that used to live in the
            // `structurallyEqual(expectedOther, subRight)` line
            // below — when bindings overlap between the two sides,
            // re-binding the same slot to the same subterm succeeds,
            // and a conflict between the two sides correctly rejects
            // the lemma.
            if (!matchAgainstPattern(otherSide, subRight,
                                       lemma.binderCount, bindings)) {
                continue;
            }
            // Discharge unbound preconditions outer-to-inner: a binder
            // type at conclusion-frame index i may reference outer
            // binders (index > i), so we need those filled first.
            // Pattern matching populates LHS/RHS slots; this pass
            // populates propositional preconditions by searching local
            // hypotheses for proofs of the instantiated type. Lemmas
            // like `padic_valuation_multiplicative(prime, a, b)
            // (primality)(aPos)(bPos)` have primality/aPos/bPos in
            // scope via the user's `claim`s — the discharge finds them
            // and the lemma fires without an explicit `by`.
            bool dischargedAll = true;
            if (static_cast<int>(lemma.binderTypes.size())
                == lemma.binderCount) {
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                for (int i = lemma.binderCount - 1; i >= 0; --i) {
                    if (bindings[i]) continue;
                    if (!binderReferencesAllBound(
                            lemma.binderTypes[i], bindings)) {
                        dischargedAll = false;
                        break;
                    }
                    ExpressionPointer slotType = instantiateLemmaBinders(
                        lemma.binderTypes[i], bindings);
                    ExpressionPointer slotTypeOpened =
                        openOverLocalBinders(slotType, localBinders,
                                              localBinders.size());
                    ExpressionPointer slotTypeNormalised;
                    try {
                        slotTypeNormalised = weakHeadNormalForm(
                            environment_, slotTypeOpened);
                    } catch (const TypeError&) {
                        dischargedAll = false;
                        break;
                    }
                    bool found = false;
                    for (int j =
                             static_cast<int>(localBinders.size()) - 1;
                         j >= 0; --j) {
                        ExpressionPointer candidateType =
                            openOverLocalBinders(
                                localBinders[j].type, localBinders, j);
                        bool eq;
                        try {
                            eq = isDefinitionallyEqual(environment_,
                                openedContext, candidateType,
                                slotTypeNormalised);
                        } catch (const TypeError&) {
                            eq = false;
                        }
                        if (eq) {
                            int deBruijnIndex =
                                static_cast<int>(localBinders.size())
                                - 1 - j;
                            bindings[i] =
                                makeBoundVariable(deBruijnIndex);
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        dischargedAll = false;
                        break;
                    }
                }
            } else {
                // Older registration without binderTypes; fall back to
                // the original all-or-nothing check.
                dischargedAll = false;
                for (const auto& binding : bindings) {
                    if (!binding) { dischargedAll = false; break; }
                    dischargedAll = true;
                }
            }
            if (!dischargedAll) continue;
            bool allBound = true;
            for (const auto& binding : bindings) {
                if (!binding) { allBound = false; break; }
            }
            if (!allBound) continue;
            // The two `matchAgainstPattern` calls above already
            // enforced `otherSide[bindings] = subRight` structurally,
            // so the redundant re-check that used to live here is
            // gone. (Propositional preconditions filled by the
            // discharge pass don't appear in `otherSide` — they're
            // referenced from binder types, not from the conclusion's
            // LHS/RHS — so they don't change the check's outcome.)
            // Assemble the lemma application: `lemmaName(binding_for_BV(n-1),
            // …, binding_for_BV(0))` — outer binder first since that's
            // the order of the Π chain.
            ExpressionPointer call =
                makeConstant(lemma.lemmaName, {});
            for (int i = lemma.binderCount - 1; i >= 0; --i) {
                call = makeApplication(std::move(call), bindings[i]);
            }
            if (!lemma.reverseDirection) {
                return call;
            }
            // Reverse direction: lemma proves `RHS = LHS` but the diff
            // wants `subLeft = subRight` where subLeft matches the
            // lemma's RHS. So the lemma instance proves
            // `subRight = subLeft`, which we wrap with
            // `Equality.symmetry` to get the desired direction.
            ExpressionPointer carrierClosed;
            LevelPointer carrierLevelAtThisLevel;
            try {
                carrierClosed = inferTypeInLocalContext(
                    localBinders, subLeft);
                carrierLevelAtThisLevel = typeUniverseOf(
                    localBinders, subLeft);
            } catch (const TypeError&) {
                continue;
            } catch (const ElaborateError&) {
                continue;
            }
            ExpressionPointer symmetryCall = makeConstant(
                "Equality.symmetry", {carrierLevelAtThisLevel});
            symmetryCall = makeApplication(
                std::move(symmetryCall), carrierClosed);
            symmetryCall = makeApplication(
                std::move(symmetryCall), subRight);
            symmetryCall = makeApplication(
                std::move(symmetryCall), subLeft);
            symmetryCall = makeApplication(
                std::move(symmetryCall), std::move(call));
            return symmetryCall;
        }
        }
        return nullptr;
    }

    // Try to prove `Equality(_, subLeft, subRight)` at a single
    // diff position. Strategies, in order:
    //   1. Lemma-index lookup (`tryLemmaIndexLookup`): bucket library
    //      rewrite lemmas by `spineHash(LHS)` and `spineHash(RHS)`,
    //      run a small first-order matcher on hits, emit the lemma
    //      application (wrapping in `Equality.symmetry` for reverse
    //      direction). Subsumes commutativity / associativity /
    //      identity / arbitrary user-written rewrite lemmas.
    //   2. Local hypothesis match: a binder of type
    //      `Equality(_, subLeft, subRight)` or its symmetric form is
    //      used directly (with a symmetry wrap on the symmetric case).
    // Returns nullptr on miss. Result is in CLOSED-over-localBinders
    // form.
    ExpressionPointer tryClassifyDiff(
        const std::vector<LocalBinder>& localBinders,
        const Context& openedContext,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
        if (ExpressionPointer proof = tryLemmaIndexLookup(
                localBinders, subLeft, subRight)) {
            return proof;
        }
        // Local hypothesis match (forward and symmetric). Scan
        // local binders for one whose type is
        // Equality(_, subLeft, subRight) or
        // Equality(_, subRight, subLeft).
        {
            ExpressionPointer subLeftOpened = openOverLocalBinders(
                subLeft, localBinders, localBinders.size());
            ExpressionPointer subRightOpened = openOverLocalBinders(
                subRight, localBinders, localBinders.size());
            for (int i =
                     static_cast<int>(localBinders.size()) - 1;
                 i >= 0; --i) {
                ExpressionPointer binderTypeOpened = openOverLocalBinders(
                    localBinders[i].type, localBinders, i);
                ExpressionPointer normalized = weakHeadNormalForm(
                    environment_, binderTypeOpened);
                // Expect App(App(App(Equality, carrier), x), y).
                auto* app3 =
                    std::get_if<Application>(&normalized->node);
                if (!app3) continue;
                auto* app2 =
                    std::get_if<Application>(&app3->function->node);
                if (!app2) continue;
                auto* app1 =
                    std::get_if<Application>(&app2->function->node);
                if (!app1) continue;
                auto* head =
                    std::get_if<Constant>(&app1->function->node);
                if (!head || head->name != "Equality") continue;
                ExpressionPointer eqLeft = app2->argument;
                ExpressionPointer eqRight = app3->argument;
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                if (isDefinitionallyEqual(environment_,
                        openedContext, eqLeft, subLeftOpened)
                    && isDefinitionallyEqual(environment_,
                        openedContext, eqRight, subRightOpened)) {
                    return makeBoundVariable(deBruijnIndex);
                }
                if (isDefinitionallyEqual(environment_,
                        openedContext, eqLeft, subRightOpened)
                    && isDefinitionallyEqual(environment_,
                        openedContext, eqRight, subLeftOpened)) {
                    // Wrap with Equality.symmetry.
                    auto* carrierConst =
                        std::get_if<Constant>(&app1->argument->node);
                    (void)carrierConst;
                    ExpressionPointer carrierAtThisLevel =
                        app1->argument;
                    LevelPointer carrierLevelAtThisLevel;
                    if (!head->universeArguments.empty()) {
                        carrierLevelAtThisLevel =
                            head->universeArguments[0];
                    } else {
                        // Should not happen: Equality is universe-
                        // polymorphic and always has a level arg.
                        return nullptr;
                    }
                    ExpressionPointer carrierClosed =
                        closeOverLocalBinders(
                            carrierAtThisLevel, localBinders,
                            localBinders.size());
                    ExpressionPointer hypBoundVar =
                        makeBoundVariable(deBruijnIndex);
                    ExpressionPointer symmetryCall = makeConstant(
                        "Equality.symmetry",
                        {carrierLevelAtThisLevel});
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), carrierClosed);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), subRight);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), subLeft);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall),
                        std::move(hypBoundVar));
                    return symmetryCall;
                }
            }
        }
        return nullptr;
    }

    // Legacy `?` hammer placeholder and its helpers (tryDirectHammer,
    // tryLocalHypothesisApplication, tryConstructorDisjointness,
    // tryContradictionFromHypotheses, elaborateHammerPlaceholder) have
    // been removed. Bare `claim P` / no-`by` `claim N : T;` /
    // `contradiction;` now flow through `autoProveClaim`, which
    // subsumes every strategy the hammer ran and goes well beyond it
    // (equality battery, transitivity bridge, conjunction / disjunction
    // intro, library scan, context-equality rewriting).
    // ----------------------------------------------------------------------
    // Commutative-ring decision tactic `ring`.
    //
    // v1 scope: handles pure-multiplication rearrangement. Both sides
    // of the goal `e1 = e2` must be products built from `<T>.multiply`
    // applied to atoms (anything not built from `<T>.multiply`). The
    // tactic reifies both sides as multisets of atoms, compares them,
    // and — on match — emits a proof using insertion-sort style swaps
    // (`<T>.multiply_commutative`) and associativity rewrites
    // (`<T>.multiply_associative`).
    //
    // Out of scope for v1: addition, distributivity, identity (1·x=x),
    // zero (0·x=0), negation, mixed sums-of-products. For those the
    // user keeps writing manual calc chains for now.
    //
    // Recognized carriers: any `T` whose head-Constant name has
    // `<T>.multiply`, `<T>.multiply_commutative`, and
    // `<T>.multiply_associative` in scope. We probe by lookup.

    // Flatten a kernel multiplication chain into a vector of factor
    // ExpressionPointers. Returns `false` if the term isn't a pure
    // product over the given carrier (e.g., contains a `<T>.add`).
    bool flattenRingProduct(
        ExpressionPointer term,
        const std::string& carrierOpName,
        std::vector<ExpressionPointer>& factorsOut) {
        // Walk: if `term = Application(Application(Constant(<carrier>.<op>, ...), a), b)`,
        // recursively flatten a and b. Otherwise treat as atom.
        // `<op>` is "multiply" or "add" depending on which axiom-set
        // the ring tactic is using for this goal.
        if (auto* outer = std::get_if<Application>(&term->node)) {
            if (auto* inner =
                    std::get_if<Application>(&outer->function->node)) {
                if (auto* op =
                        std::get_if<Constant>(&inner->function->node)) {
                    if (op->name == carrierOpName) {
                        if (!flattenRingProduct(inner->argument,
                                                  carrierOpName,
                                                  factorsOut)) {
                            return false;
                        }
                        if (!flattenRingProduct(outer->argument,
                                                  carrierOpName,
                                                  factorsOut)) {
                            return false;
                        }
                        return true;
                    }
                }
            }
        }
        factorsOut.push_back(term);
        return true;
    }

    // Build a left-associated product `((f0 * f1) * f2) * ... * fn-1`
    // from a vector of factor kernel terms. Caller guarantees the
    // vector is non-empty.
    ExpressionPointer assembleLeftAssociatedProduct(
        const std::string& carrierMultiplyName,
        const std::vector<ExpressionPointer>& factors) {
        ExpressionPointer accumulator = factors[0];
        for (size_t i = 1; i < factors.size(); ++i) {
            accumulator = makeApplication(
                makeApplication(makeConstant(carrierMultiplyName),
                                 accumulator),
                factors[i]);
        }
        return accumulator;
    }

    // Total order on ExpressionPointers used to sort factor multisets
    // canonically. Compares by:
    //   1. node variant index
    //   2. variant-specific keys (de Bruijn index, name, etc.)
    //   3. children (for compound nodes)
    int compareExpressionStructure(
        ExpressionPointer left, ExpressionPointer right) {
        if (left.get() == right.get()) return 0;
        if (left->node.index() < right->node.index()) return -1;
        if (left->node.index() > right->node.index()) return 1;
        if (auto* a = std::get_if<BoundVariable>(&left->node)) {
            auto* b = std::get_if<BoundVariable>(&right->node);
            if (a->deBruijnIndex < b->deBruijnIndex) return -1;
            if (a->deBruijnIndex > b->deBruijnIndex) return 1;
            return 0;
        }
        if (auto* a = std::get_if<FreeVariable>(&left->node)) {
            auto* b = std::get_if<FreeVariable>(&right->node);
            int nameCmp = a->name.compare(b->name);
            if (nameCmp != 0) return nameCmp < 0 ? -1 : 1;
            return 0;
        }
        if (auto* a = std::get_if<Constant>(&left->node)) {
            auto* b = std::get_if<Constant>(&right->node);
            return a->name.compare(b->name) < 0 ? -1
                 : a->name.compare(b->name) > 0 ?  1 : 0;
        }
        if (auto* a = std::get_if<Application>(&left->node)) {
            auto* b = std::get_if<Application>(&right->node);
            int fcmp = compareExpressionStructure(
                a->function, b->function);
            if (fcmp != 0) return fcmp;
            return compareExpressionStructure(a->argument, b->argument);
        }
        if (auto* a = std::get_if<Lambda>(&left->node)) {
            auto* b = std::get_if<Lambda>(&right->node);
            int dcmp = compareExpressionStructure(a->domain, b->domain);
            if (dcmp != 0) return dcmp;
            return compareExpressionStructure(a->body, b->body);
        }
        if (auto* a = std::get_if<Pi>(&left->node)) {
            auto* b = std::get_if<Pi>(&right->node);
            int dcmp = compareExpressionStructure(a->domain, b->domain);
            if (dcmp != 0) return dcmp;
            return compareExpressionStructure(a->codomain, b->codomain);
        }
        // Other variants: treat as equal (shouldn't appear as atoms).
        return 0;
    }

    // `ring` — close an `e1 = e2` goal in a commutative ring.
    // v1: handles pure-multiplication rearrangement.
    ExpressionPointer elaborateRing(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "ring at line " + std::to_string(line),
                    localBinders, expectedType, line, column);
        if (!expectedType) {
            throwElaborate(
                "`ring` needs an expected type from context — use it "
                "in a calc step or as the body of a theorem with a "
                "declared equality conclusion");
        }
        EqualityComponents goal =
            extractEqualityComponents(expectedType, "ring", line);
        std::string carrierName = headConstantName(goal.carrierType);
        // Try the multiplicative axioms first; if the goal isn't a
        // pure product, try the additive axioms. Either is acceptable
        // — both reduce to the same insertion-sort + reassociate
        // proof emitter parameterised by a RingAxiomNames triple.
        auto buildAxioms =
            [&](const std::string& opSuffix) -> RingAxiomNames {
            return RingAxiomNames{
                carrierName + "." + opSuffix,
                carrierName + "." + opSuffix + "_associative",
                carrierName + "." + opSuffix + "_commutative"};
        };
        auto axiomsAvailable =
            [&](const RingAxiomNames& a) -> bool {
            return environment_.lookup(a.op) != nullptr
                && environment_.lookup(a.associative) != nullptr
                && environment_.lookup(a.commutative) != nullptr;
        };
        std::vector<ExpressionPointer> leftFactors, rightFactors;
        RingAxiomNames axioms;
        // Helper: try one axiom set; succeed if the factor multisets
        // match (after sort).
        auto try_axioms =
            [&](const RingAxiomNames& candidate) -> bool {
            if (!axiomsAvailable(candidate)) return false;
            std::vector<ExpressionPointer> lf, rf;
            if (!flattenRingProduct(goal.leftEndpoint, candidate.op, lf)
                || !flattenRingProduct(goal.rightEndpoint,
                                           candidate.op, rf)) {
                return false;
            }
            if (lf.size() != rf.size()) return false;
            std::vector<ExpressionPointer> ls = lf;
            std::vector<ExpressionPointer> rs = rf;
            auto cmp = [this](ExpressionPointer a,
                                ExpressionPointer b) {
                return compareExpressionStructure(a, b) < 0;
            };
            std::sort(ls.begin(), ls.end(), cmp);
            std::sort(rs.begin(), rs.end(), cmp);
            for (size_t i = 0; i < ls.size(); ++i) {
                if (!structurallyEqual(ls[i], rs[i])) return false;
            }
            leftFactors = std::move(lf);
            rightFactors = std::move(rf);
            return true;
        };
        if (try_axioms(buildAxioms("multiply"))) {
            axioms = buildAxioms("multiply");
        } else if (try_axioms(buildAxioms("add"))) {
            axioms = buildAxioms("add");
        } else {
            // v1 (pure-AC for one operator) can't close the goal.
            // Fall through to v2, which normalises both sides to a
            // sum-of-monomials canonical form (handles distributivity,
            // 0/1 identity, negation, and like-term cancellation
            // within ±1 coefficient).
            return elaborateRingV2(
                /*localBinders*/{},
                goal.leftEndpoint, goal.rightEndpoint,
                goal.carrierType, goal.carrierUniverseLevel,
                carrierName, line);
        }
        if (leftFactors.size() != rightFactors.size()) {
            throwElaborate(
                "`ring`: left side has "
                + std::to_string(leftFactors.size())
                + " factors, right side has "
                + std::to_string(rightFactors.size())
                + " — multisets cannot match");
        }
        // Compute a sorted canonical order. Sort both sides by the
        // structural comparator; check the sorted vectors are
        // factor-wise structurally equal.
        std::vector<ExpressionPointer> leftSorted = leftFactors;
        std::vector<ExpressionPointer> rightSorted = rightFactors;
        auto cmp = [this](ExpressionPointer a, ExpressionPointer b) {
            return compareExpressionStructure(a, b) < 0;
        };
        std::sort(leftSorted.begin(), leftSorted.end(), cmp);
        std::sort(rightSorted.begin(), rightSorted.end(), cmp);
        for (size_t i = 0; i < leftSorted.size(); ++i) {
            if (!structurallyEqual(leftSorted[i], rightSorted[i])) {
                throwElaborate(
                    "`ring`: factor multisets differ — left and right "
                    "sides cannot be brought to the same canonical "
                    "product");
            }
        }
        // Build a kernel proof: LHS = canonical = RHS.
        // canonical = left-associated product of leftSorted.
        ExpressionPointer canonicalKernel =
            assembleLeftAssociatedProduct(axioms.op, leftSorted);
        ExpressionPointer leftProof =
            proveProductEqualsSorted(goal.leftEndpoint, leftFactors,
                                      leftSorted, axioms,
                                      goal.carrierType,
                                      goal.carrierUniverseLevel, line);
        ExpressionPointer rightProof =
            proveProductEqualsSorted(goal.rightEndpoint, rightFactors,
                                      rightSorted, axioms,
                                      goal.carrierType,
                                      goal.carrierUniverseLevel, line);
        // rightProof: RHS = canonical. We need canonical = RHS via
        // symmetry, then chain via transitivity.
        ExpressionPointer rightProofSymm = makeConstant(
            "Equality.symmetry", {goal.carrierUniverseLevel});
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           goal.carrierType);
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           goal.rightEndpoint);
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           canonicalKernel);
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           std::move(rightProof));
        ExpressionPointer finalProof = makeConstant(
            "Equality.transitivity", {goal.carrierUniverseLevel});
        finalProof = makeApplication(std::move(finalProof),
                                       goal.carrierType);
        finalProof = makeApplication(std::move(finalProof),
                                       goal.leftEndpoint);
        finalProof = makeApplication(std::move(finalProof),
                                       canonicalKernel);
        finalProof = makeApplication(std::move(finalProof),
                                       goal.rightEndpoint);
        finalProof = makeApplication(std::move(finalProof),
                                       std::move(leftProof));
        finalProof = makeApplication(std::move(finalProof),
                                       std::move(rightProofSymm));
        return finalProof;
    }

    // Prove `originalProduct = canonical` where `canonical` is the
    // left-associated product of `sortedFactors`. The original is
    // assumed to be some product over the same factor multiset; v1
    // proof: build the canonical kernel term as the target and let
    // the kernel verify definitional equality of the factor multiset
    // via a chain of multiply_associative + multiply_commutative.
    //
    // Simpler v1 approach: build proofs INSERTION-SORT style. Maintain
    // a "current" arrangement; at each step, find the position of the
    // next sorted factor in the current arrangement; commute it left
    // until in position. Each commute is a multiply_commutative
    // application wrapped in congruenceOf for the surrounding context.
    //
    // For now: if `originalFactors` already equal `sortedFactors`
    // element-wise (the goal is already canonical), emit reflexivity.
    // Otherwise (factors differ in order), defer to a fuller proof
    // generator — but emit an honest "not yet implemented" error.
    // Shift every BoundVariable in `expression` whose de-Bruijn index
    // is >= threshold up by `increment`. Used when embedding a kernel
    // term inside a new lambda binder.
    ExpressionPointer liftBoundVariables(
        ExpressionPointer expression, int increment, int threshold) {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            if (bv->deBruijnIndex >= threshold) {
                return makeBoundVariable(
                    bv->deBruijnIndex + increment);
            }
            return expression;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                liftBoundVariables(pi->domain, increment, threshold),
                liftBoundVariables(pi->codomain, increment,
                                     threshold + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                liftBoundVariables(lambda->domain, increment, threshold),
                liftBoundVariables(lambda->body, increment,
                                     threshold + 1));
        }
        if (auto* app = std::get_if<Application>(&expression->node)) {
            return makeApplication(
                liftBoundVariables(app->function, increment, threshold),
                liftBoundVariables(app->argument, increment, threshold));
        }
        return expression;
    }

    // Names of the ring axioms for one binary operation on a carrier.
    // For multiplicative use: ("Integer.multiply",
    // "Integer.multiply_associative", "Integer.multiply_commutative").
    // For additive use: same shape with `.add` instead of `.multiply`.
    struct RingAxiomNames {
        std::string op;            // e.g. "Integer.multiply"
        std::string associative;   // e.g. "Integer.multiply_associative"
        std::string commutative;   // e.g. "Integer.multiply_commutative"
    };

    // Build `<op>(left, right)`.
    ExpressionPointer buildRingOp(
        const std::string& opName,
        ExpressionPointer left, ExpressionPointer right) {
        ExpressionPointer call = makeConstant(opName);
        call = makeApplication(std::move(call), std::move(left));
        call = makeApplication(std::move(call), std::move(right));
        return call;
    }

    // Build `<op>(left, right)` — alias kept for the old call sites in
    // case they're still around. (Should be replaced as call sites
    // migrate to the generalised form.)
    ExpressionPointer buildRingMultiply(
        const std::string& carrierName,
        ExpressionPointer left, ExpressionPointer right) {
        return buildRingOp(carrierName + ".multiply",
                            std::move(left), std::move(right));
    }

    // Build `Equality.transitivity.{u}(T, A, B, C, p1, p2)`.
    ExpressionPointer buildEqualityTransitivity(
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer A, ExpressionPointer B, ExpressionPointer C,
        ExpressionPointer p1, ExpressionPointer p2) {
        ExpressionPointer call = makeConstant(
            "Equality.transitivity", {universeLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(A));
        call = makeApplication(std::move(call), std::move(B));
        call = makeApplication(std::move(call), std::move(C));
        call = makeApplication(std::move(call), std::move(p1));
        call = makeApplication(std::move(call), std::move(p2));
        return call;
    }

    // Build `Equality.symmetry.{u}(T, A, B, p)` where p : A = B.
    ExpressionPointer buildEqualitySymmetry(
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer A, ExpressionPointer B,
        ExpressionPointer p) {
        ExpressionPointer call = makeConstant(
            "Equality.symmetry", {universeLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(A));
        call = makeApplication(std::move(call), std::move(B));
        call = makeApplication(std::move(call), std::move(p));
        return call;
    }

    // Build `Equality.congruence.{u, u}(T, T, λ : T → T, x, y, p)`
    // where p : x = y; returns proof of λ(x) = λ(y). Carrier and
    // codomain types are the same here (we only use it for ring-level
    // congruence).
    ExpressionPointer buildEqualityCongruenceSameCarrier(
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer lambda,
        ExpressionPointer x, ExpressionPointer y,
        ExpressionPointer p) {
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {universeLevel, universeLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), std::move(lambda));
        call = makeApplication(std::move(call), std::move(x));
        call = makeApplication(std::move(call), std::move(y));
        call = makeApplication(std::move(call), std::move(p));
        return call;
    }

    // Build `<axioms.associative>(P, a, b) : (P op a) op b =
    // P op (a op b)`.
    ExpressionPointer buildRingAssoc(
        const RingAxiomNames& axioms,
        ExpressionPointer P, ExpressionPointer a, ExpressionPointer b) {
        ExpressionPointer call =
            makeConstant(axioms.associative);
        call = makeApplication(std::move(call), std::move(P));
        call = makeApplication(std::move(call), std::move(a));
        call = makeApplication(std::move(call), std::move(b));
        return call;
    }

    // Build `<axioms.commutative>(a, b) : a op b = b op a`.
    ExpressionPointer buildRingCommute(
        const RingAxiomNames& axioms,
        ExpressionPointer a, ExpressionPointer b) {
        ExpressionPointer call =
            makeConstant(axioms.commutative);
        call = makeApplication(std::move(call), std::move(a));
        call = makeApplication(std::move(call), std::move(b));
        return call;
    }

    // Build `reflexivity.{u}(T, x) : x = x`.
    ExpressionPointer buildReflexivity(
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer x) {
        ExpressionPointer call = makeConstant(
            "reflexivity", {universeLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(x));
        return call;
    }

    // Build a proof : left_assoc(factors_with_swap) = left_assoc(factors).
    // Reading direction matches insertion-sort's chained proof: each
    // step's RHS is the freshly-rearranged form. `swapPosition` swaps
    // factors[swapPosition - 1] and factors[swapPosition]; result is
    // the proof of the new full product being equal to the previous.
    //
    // For positions just to the LEFT of swap, factors[0..swapPosition-2]
    // become the "prefix" P inside the proof; for positions just to
    // the RIGHT (swapPosition+1..n-1), each adds a congruenceOf-wrap
    // around the inner proof.
    //
    // Returns proof : left_assoc(factors) =
    //                 left_assoc(factors_after_swap)
    ExpressionPointer buildAdjacentSwapProof(
        const RingAxiomNames& axioms,
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        const std::vector<ExpressionPointer>& factors,
        size_t swapPosition) {
        // swapPosition is the index of the SECOND of the two factors
        // being swapped (so factors[swapPosition - 1] and
        // factors[swapPosition] get exchanged). 1 <= swapPosition < n.
        size_t k = swapPosition;
        const ExpressionPointer& a = factors[k - 1];
        const ExpressionPointer& b = factors[k];
        // Step A: build the base swap proof at the level just enclosing
        // factors a and b.
        ExpressionPointer baseProof;
        ExpressionPointer baseLHS;  // left-assoc of factors[0..k]
        ExpressionPointer baseRHS;  // left-assoc with k-1 and k swapped
        if (k == 1) {
            // No prefix; the level-1 subtree is just `a op b`.
            // Proof: commutative(a, b) : a op b = b op a.
            baseProof = buildRingCommute(axioms, a, b);
            baseLHS = buildRingOp(axioms.op, a, b);
            baseRHS = buildRingOp(axioms.op, b, a);
        } else {
            // Prefix P = left-assoc of factors[0..k-1] (positions 0
            // through k-2). Then base subtree = (P op a) op b.
            std::vector<ExpressionPointer> prefixFactors(
                factors.begin(),
                factors.begin() + static_cast<long>(k - 1));
            ExpressionPointer P = assembleLeftAssociatedProduct(
                axioms.op, prefixFactors);
            // Step 1: (P op a) op b = P op (a op b) by associative
            ExpressionPointer pTimesAB =
                buildRingOp(axioms.op, P,
                    buildRingOp(axioms.op, a, b));
            ExpressionPointer pTimesA_TimesB =
                buildRingOp(axioms.op,
                    buildRingOp(axioms.op, P, a), b);
            ExpressionPointer step1 =
                buildRingAssoc(axioms, P, a, b);
            // Step 2: P op (a op b) = P op (b op a) via congruence with
            // λz. P op z. Lift P's bound-vars into the new lambda scope.
            ExpressionPointer plift = liftBoundVariables(P, 1, 0);
            ExpressionPointer lambdaBody = buildRingOp(
                axioms.op, plift, makeBoundVariable(0));
            ExpressionPointer lambdaPTimesZ = makeLambda(
                "_ring_swap_z", carrierType, lambdaBody);
            ExpressionPointer commutProof =
                buildRingCommute(axioms, a, b);
            ExpressionPointer aTimesB =
                buildRingOp(axioms.op, a, b);
            ExpressionPointer bTimesA =
                buildRingOp(axioms.op, b, a);
            ExpressionPointer step2 = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambdaPTimesZ,
                aTimesB, bTimesA, commutProof);
            // Step 3: P op (b op a) = (P op b) op a via sym associative
            ExpressionPointer pTimesBA =
                buildRingOp(axioms.op, P,
                    buildRingOp(axioms.op, b, a));
            ExpressionPointer pTimesB_TimesA =
                buildRingOp(axioms.op,
                    buildRingOp(axioms.op, P, b), a);
            ExpressionPointer assocPBA =
                buildRingAssoc(axioms, P, b, a);
            ExpressionPointer step3 = buildEqualitySymmetry(
                universeLevel, carrierType,
                pTimesB_TimesA, pTimesBA, assocPBA);
            // Chain: transitivity(step1, transitivity(step2, step3))
            ExpressionPointer step23 = buildEqualityTransitivity(
                universeLevel, carrierType,
                pTimesAB, pTimesBA, pTimesB_TimesA, step2, step3);
            baseProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                pTimesA_TimesB, pTimesAB, pTimesB_TimesA,
                step1, step23);
            baseLHS = pTimesA_TimesB;
            baseRHS = pTimesB_TimesA;
        }
        // Step B: lift through factors[k+1..n-1] via congruences
        // λz. z op factors[j] for each j > k.
        ExpressionPointer currentProof = baseProof;
        ExpressionPointer currentLHS = baseLHS;
        ExpressionPointer currentRHS = baseRHS;
        for (size_t j = k + 1; j < factors.size(); ++j) {
            ExpressionPointer fjLifted =
                liftBoundVariables(factors[j], 1, 0);
            ExpressionPointer lambdaBody = buildRingOp(
                axioms.op, makeBoundVariable(0), fjLifted);
            ExpressionPointer lambda = makeLambda(
                "_ring_lift_z", carrierType, lambdaBody);
            ExpressionPointer newLHS = buildRingOp(
                axioms.op, currentLHS, factors[j]);
            ExpressionPointer newRHS = buildRingOp(
                axioms.op, currentRHS, factors[j]);
            currentProof = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambda,
                currentLHS, currentRHS, currentProof);
            currentLHS = std::move(newLHS);
            currentRHS = std::move(newRHS);
        }
        return currentProof;
    }

    // Re-associate `expression` (an expression of `<Carrier>.multiply`s
    // and atoms) into left-associated form. Returns a proof of
    // `expression = left_assoc(flatten(expression))`.
    //
    // For the special case where the expression is already
    // left-associated, returns reflexivity.
    ExpressionPointer buildLeftAssocReassocProof(
        const RingAxiomNames& axioms,
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer expression) {
        const std::string& opName = axioms.op;
        std::vector<ExpressionPointer> factors;
        if (!flattenRingProduct(expression, opName, factors)) {
            // Shouldn't happen — caller already flattened.
            throwElaborate("ring: internal reassociate failure");
        }
        ExpressionPointer canonical =
            assembleLeftAssociatedProduct(opName, factors);
        if (structurallyEqual(expression, canonical)) {
            return buildReflexivity(universeLevel, carrierType,
                                      expression);
        }
        // Recursive case: expression = A * B where B is itself a
        // product. We re-associate: A * B = ... we want (left part of
        // A's factors plus the first factor of B) * (rest of B). The
        // cleanest path: structurally process.
        //
        // Walk expression: if it's leftFactor * rightFactor where
        // rightFactor is `X * Y` (a product), then:
        //   leftFactor * (X * Y) = (leftFactor * X) * Y  by sym assoc.
        //   recurse on the new form, prefix with that one assoc step.
        // Else if leftFactor is itself a product, recurse on leftFactor:
        //   leftFactor * rightFactor: combine leftFactor's reassoc
        //   proof with congruenceOf(λx. x * rightFactor, ...).
        // Else (both atoms): we'd be at single-element case, handled
        // by the equality check above.
        auto outerApp =
            std::get_if<Application>(&expression->node);
        if (!outerApp) {
            throwElaborate("ring: unexpected non-application in "
                            "reassociate");
        }
        auto innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) {
            throwElaborate("ring: unexpected non-op head");
        }
        ExpressionPointer leftSubExpr = innerApp->argument;
        ExpressionPointer rightSubExpr = outerApp->argument;
        // Check if rightSubExpr is itself `<op>(X, Y)`.
        auto rightOuterApp =
            std::get_if<Application>(&rightSubExpr->node);
        if (rightOuterApp) {
            auto rightInnerApp =
                std::get_if<Application>(
                    &rightOuterApp->function->node);
            if (rightInnerApp) {
                auto rightHead = std::get_if<Constant>(
                    &rightInnerApp->function->node);
                if (rightHead
                    && rightHead->name == opName) {
                    // expression = L op (X op Y).
                    ExpressionPointer X = rightInnerApp->argument;
                    ExpressionPointer Y = rightOuterApp->argument;
                    // Step: L op (X op Y) = (L op X) op Y
                    // by sym associative(L, X, Y).
                    ExpressionPointer assocProof = buildRingAssoc(
                        axioms, leftSubExpr, X, Y);
                    ExpressionPointer LXTimesY = buildRingOp(
                        axioms.op,
                        buildRingOp(
                            axioms.op, leftSubExpr, X),
                        Y);
                    ExpressionPointer LTimesXY = buildRingOp(
                        axioms.op, leftSubExpr,
                        buildRingOp(axioms.op, X, Y));
                    ExpressionPointer symAssoc = buildEqualitySymmetry(
                        universeLevel, carrierType,
                        LXTimesY, LTimesXY, assocProof);
                    ExpressionPointer recProof =
                        buildLeftAssocReassocProof(
                            axioms, universeLevel, carrierType,
                            LXTimesY);
                    return buildEqualityTransitivity(
                        universeLevel, carrierType,
                        expression, LXTimesY, canonical,
                        symAssoc, recProof);
                }
            }
        }
        // Right is atomic. Recurse on the left subexpression.
        ExpressionPointer leftCanonical;
        {
            std::vector<ExpressionPointer> leftFactors;
            if (!flattenRingProduct(leftSubExpr, opName,
                                      leftFactors)) {
                throwElaborate(
                    "ring: internal flatten failure (left)");
            }
            leftCanonical = assembleLeftAssociatedProduct(
                opName, leftFactors);
        }
        ExpressionPointer leftProof = buildLeftAssocReassocProof(
            axioms, universeLevel, carrierType, leftSubExpr);
        // Build lambda: λ z. z op rightSubExpr.
        ExpressionPointer rightLifted =
            liftBoundVariables(rightSubExpr, 1, 0);
        ExpressionPointer lambdaBody = buildRingOp(
            axioms.op, makeBoundVariable(0), rightLifted);
        ExpressionPointer lambda = makeLambda(
            "_ring_assoc_z", carrierType, lambdaBody);
        return buildEqualityCongruenceSameCarrier(
            universeLevel, carrierType, lambda,
            leftSubExpr, leftCanonical, leftProof);
    }

    ExpressionPointer proveProductEqualsSorted(
        ExpressionPointer original,
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingAxiomNames& axioms,
        ExpressionPointer carrierType,
        LevelPointer carrierUniverseLevel,
        int line) {
        (void)line;
        const std::string& opName = axioms.op;
        ExpressionPointer canonical =
            assembleLeftAssociatedProduct(opName, sortedFactors);
        if (sortedFactors.size() <= 1) {
            if (structurallyEqual(original, canonical)) {
                return buildReflexivity(carrierUniverseLevel,
                                          carrierType, original);
            }
            throwElaborate(
                "ring: single-factor case but factors don't match");
        }
        ExpressionPointer reassocProof = buildLeftAssocReassocProof(
            axioms, carrierUniverseLevel, carrierType, original);
        ExpressionPointer leftAssocOriginal =
            assembleLeftAssociatedProduct(opName, originalFactors);
        std::vector<ExpressionPointer> current = originalFactors;
        ExpressionPointer sortProof = buildReflexivity(
            carrierUniverseLevel, carrierType, leftAssocOriginal);
        ExpressionPointer currentExpr = leftAssocOriginal;
        for (size_t i = 0; i < sortedFactors.size(); ++i) {
            size_t j = i;
            while (j < current.size()
                   && !structurallyEqual(current[j],
                                            sortedFactors[i])) {
                ++j;
            }
            if (j >= current.size()) {
                throwElaborate(
                    "ring: factor multiset matched but element not "
                    "found during sort — internal error");
            }
            while (j > i) {
                ExpressionPointer swapProof = buildAdjacentSwapProof(
                    axioms, carrierUniverseLevel, carrierType,
                    current, j);
                std::vector<ExpressionPointer> newCurrent = current;
                std::swap(newCurrent[j - 1], newCurrent[j]);
                ExpressionPointer newExpr =
                    assembleLeftAssociatedProduct(
                        opName, newCurrent);
                sortProof = buildEqualityTransitivity(
                    carrierUniverseLevel, carrierType,
                    leftAssocOriginal, currentExpr, newExpr,
                    sortProof, swapProof);
                current = std::move(newCurrent);
                currentExpr = std::move(newExpr);
                --j;
            }
        }
        if (!structurallyEqual(currentExpr, canonical)) {
            throwElaborate(
                "ring: insertion sort ended with mismatched form — "
                "internal error");
        }
        return buildEqualityTransitivity(
            carrierUniverseLevel, carrierType,
            original, leftAssocOriginal, canonical,
            reassocProof, sortProof);
    }

    // =====================================================================
    // Ring v2 — polynomial canonicalisation
    //
    // Decision procedure that extends v1 with distributivity, identity
    // (0 and 1), and negation. Both sides of `e1 = e2` are normalised
    // to a sum-of-monomials over opaque atoms; the atoms are keyed by
    // subtree hash (so we compare by hash, not by structural equality).
    //
    // A `monomialSignature` is the lex-sorted vector of factor hashes
    // appearing in a monomial (with multiplicity). A polynomial is a
    // `std::map<monomialSignature, signed coefficient>`, with the zero
    // coefficient entries omitted.
    //
    // v2 of v2 (this version) restricts coefficients to {-1, 0, +1}.
    // Goals that, after distributivity, collect a like-term coefficient
    // outside that range (e.g. `a + a = 2 · a`) bail back to the v1
    // path's error message — they're handled by a future v3.
    //
    // Proof generation is staged: this first commit lands the
    // normaliser + the decision path. If the polynomials agree but the
    // proof emitter isn't yet ready, the tactic emits a clear error so
    // we never silently regress.
    // =====================================================================

    struct RingV2Context {
        std::string carrierName;           // e.g. "Rational"
        ExpressionPointer carrierType;      // Constant("Rational")
        LevelPointer carrierUniverseLevel;  // for Equality.* applications

        std::string addName;                // "<carrier>.add"
        std::string multiplyName;           // "<carrier>.multiply"
        std::string negateName;             // "<carrier>.negate"
        std::string subtractName;           // "<carrier>.subtract"
        std::string zeroName;               // "<carrier>.zero"
        std::string oneName;                // "<carrier>.one"

        // Atom table: hash → kernel expression. Filled lazily while
        // normalising. We trust 64-bit hashes — the canonicalisation is
        // sound even on a collision (different terms would happen to be
        // treated as the same atom, which would cause the polynomial
        // comparison to spuriously succeed for unequal goals — but the
        // proof emitter would then fail to produce a kernel-valid
        // proof, which the kernel catches at verification time).
        std::unordered_map<uint64_t, ExpressionPointer> atoms;
    };

    // A polynomial as map<signature, coefficient>, signature = sorted
    // vector of atom hashes (with multiplicity), coefficient = signed
    // integer.
    using RingMonomialSignature = std::vector<uint64_t>;
    using RingPolynomial = std::map<RingMonomialSignature, int>;

    // Drop zero-coefficient entries (caller is expected to call this
    // after any arithmetic that can produce a zero).
    void ringPolynomialCompact(RingPolynomial& polynomial) {
        for (auto iter = polynomial.begin(); iter != polynomial.end(); ) {
            if (iter->second == 0) {
                iter = polynomial.erase(iter);
            } else {
                ++iter;
            }
        }
    }

    // polynomial += other, in place.
    void ringPolynomialAccumulate(
        RingPolynomial& polynomial,
        const RingPolynomial& other) {
        for (const auto& entry : other) {
            polynomial[entry.first] += entry.second;
        }
        ringPolynomialCompact(polynomial);
    }

    // polynomial -= other, in place.
    void ringPolynomialSubtract(
        RingPolynomial& polynomial,
        const RingPolynomial& other) {
        for (const auto& entry : other) {
            polynomial[entry.first] -= entry.second;
        }
        ringPolynomialCompact(polynomial);
    }

    // Negate every coefficient.
    void ringPolynomialNegate(RingPolynomial& polynomial) {
        for (auto& entry : polynomial) {
            entry.second = -entry.second;
        }
    }

    // result := left · right (full pointwise distribute).
    RingPolynomial ringPolynomialMultiply(
        const RingPolynomial& left, const RingPolynomial& right) {
        RingPolynomial result;
        for (const auto& leftEntry : left) {
            for (const auto& rightEntry : right) {
                // Merged signature = sorted concat of the two factor
                // lists. Both inputs are sorted, so a merge keeps it
                // sorted in linear time.
                RingMonomialSignature mergedSignature;
                mergedSignature.reserve(
                    leftEntry.first.size() + rightEntry.first.size());
                std::merge(
                    leftEntry.first.begin(), leftEntry.first.end(),
                    rightEntry.first.begin(), rightEntry.first.end(),
                    std::back_inserter(mergedSignature));
                result[mergedSignature] += leftEntry.second
                                            * rightEntry.second;
            }
        }
        ringPolynomialCompact(result);
        return result;
    }

    // Construct the polynomial representing `1` (single constant
    // monomial with empty factor list and coefficient 1).
    RingPolynomial ringPolynomialOne() {
        RingPolynomial polynomial;
        polynomial[RingMonomialSignature{}] = 1;
        return polynomial;
    }

    // Construct the polynomial representing a single atom (one monomial
    // with one factor and coefficient 1). Side effect: register the atom
    // in `context.atoms` keyed by its hash.
    RingPolynomial ringPolynomialAtom(
        RingV2Context& context, ExpressionPointer atom) {
        uint64_t atomHash = atom->hash;
        auto insertion = context.atoms.emplace(atomHash, atom);
        (void)insertion;  // first writer wins; subsequent hits reuse
                            // the existing pointer (assumed
                            // structurally equal modulo hash collision)
        RingPolynomial polynomial;
        polynomial[RingMonomialSignature{atomHash}] = 1;
        return polynomial;
    }

    // Recognise `<context.opName>(left, right)` and produce (left,
    // right). Returns true on a match.
    bool matchBinaryRingOp(
        ExpressionPointer expression,
        const std::string& opName,
        ExpressionPointer& leftOut,
        ExpressionPointer& rightOut) {
        auto* outerApp =
            std::get_if<Application>(&expression->node);
        if (!outerApp) return false;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return false;
        auto* head =
            std::get_if<Constant>(&innerApp->function->node);
        if (!head || head->name != opName) return false;
        leftOut = innerApp->argument;
        rightOut = outerApp->argument;
        return true;
    }

    // Recognise `<context.negateName>(inner)` and produce `inner`.
    bool matchUnaryRingNegate(
        ExpressionPointer expression,
        const std::string& negateName,
        ExpressionPointer& innerOut) {
        auto* outerApp =
            std::get_if<Application>(&expression->node);
        if (!outerApp) return false;
        auto* head =
            std::get_if<Constant>(&outerApp->function->node);
        if (!head || head->name != negateName) return false;
        innerOut = outerApp->argument;
        return true;
    }

    // True if `expression` is `<carrier>.zero` (head Constant whose
    // name matches `context.zeroName`).
    bool matchRingZero(ExpressionPointer expression,
                          const std::string& zeroName) {
        auto* head = std::get_if<Constant>(&expression->node);
        return head != nullptr && head->name == zeroName;
    }

    // True if `expression` is `<carrier>.one`.
    bool matchRingOne(ExpressionPointer expression,
                         const std::string& oneName) {
        auto* head = std::get_if<Constant>(&expression->node);
        return head != nullptr && head->name == oneName;
    }

    // Convert a kernel expression to a RingPolynomial, registering
    // opaque subterms as atoms along the way. Recursive: add /
    // multiply / negate are unfolded; zero and one are bottomed out;
    // everything else is an atom.
    RingPolynomial normaliseToRingPolynomial(
        ExpressionPointer expression, RingV2Context& context) {
        // zero — empty polynomial.
        if (matchRingZero(expression, context.zeroName)) {
            return RingPolynomial{};
        }
        // one — single empty-factor monomial.
        if (matchRingOne(expression, context.oneName)) {
            return ringPolynomialOne();
        }
        // add — recurse + accumulate.
        ExpressionPointer left;
        ExpressionPointer right;
        if (matchBinaryRingOp(expression, context.addName,
                                 left, right)) {
            RingPolynomial polynomial =
                normaliseToRingPolynomial(left, context);
            RingPolynomial rightPolynomial =
                normaliseToRingPolynomial(right, context);
            ringPolynomialAccumulate(polynomial, rightPolynomial);
            return polynomial;
        }
        // multiply — recurse + multiply.
        if (matchBinaryRingOp(expression, context.multiplyName,
                                 left, right)) {
            RingPolynomial leftPolynomial =
                normaliseToRingPolynomial(left, context);
            RingPolynomial rightPolynomial =
                normaliseToRingPolynomial(right, context);
            return ringPolynomialMultiply(
                leftPolynomial, rightPolynomial);
        }
        // subtract — recurse + subtract. The carrier's `subtract` is
        // defined as `x + -y`, so this is delta-equivalent to the
        // add/negate path; we handle it directly so the surface syntax
        // `a - b` works without the user having to expand it.
        if (matchBinaryRingOp(expression, context.subtractName,
                                 left, right)) {
            RingPolynomial leftPolynomial =
                normaliseToRingPolynomial(left, context);
            RingPolynomial rightPolynomial =
                normaliseToRingPolynomial(right, context);
            ringPolynomialSubtract(leftPolynomial, rightPolynomial);
            return leftPolynomial;
        }
        // negate — recurse + flip.
        ExpressionPointer inner;
        if (matchUnaryRingNegate(expression, context.negateName,
                                    inner)) {
            RingPolynomial polynomial =
                normaliseToRingPolynomial(inner, context);
            ringPolynomialNegate(polynomial);
            return polynomial;
        }
        // Otherwise: an opaque atom.
        return ringPolynomialAtom(context, expression);
    }

    // Build the kernel expression for `1 + 1 + ... + 1` with N copies
    // of `<context.oneName>`, left-associated.  N must be >= 1.
    ExpressionPointer buildRingCoefficientExpression(
        int count, const RingV2Context& context) {
        ExpressionPointer one = makeConstant(context.oneName);
        if (count == 1) return one;
        ExpressionPointer accumulator = one;
        for (int i = 1; i < count; ++i) {
            ExpressionPointer onePlus = makeConstant(context.oneName);
            accumulator = buildRingOp(context.addName,
                                        std::move(accumulator),
                                        std::move(onePlus));
        }
        return accumulator;
    }

    // Build the kernel expression for one monomial in canonical form.
    // Coefficient must be non-zero. Factors is the sorted signature.
    // The shape is:
    //    coefficientExpr * (factor_0 * factor_1 * ... * factor_{n-1})
    // with the inner product left-associated. If |coefficient| == 1,
    // we drop the `coefficientExpr *` prefix (with a `negate` wrap if
    // the coefficient is negative). If the factor list is empty, the
    // monomial is just `coefficientExpr` (possibly negated).
    ExpressionPointer buildCanonicalMonomial(
        const RingMonomialSignature& factors,
        int coefficient,
        const RingV2Context& context) {
        const int magnitude = coefficient > 0 ? coefficient : -coefficient;
        ExpressionPointer factorProduct;
        if (!factors.empty()) {
            std::vector<ExpressionPointer> atomTerms;
            atomTerms.reserve(factors.size());
            for (uint64_t factorHash : factors) {
                auto found = context.atoms.find(factorHash);
                if (found == context.atoms.end()) {
                    throwElaborate(
                        "ring v2: internal error — atom hash missing "
                        "from atom table");
                }
                atomTerms.push_back(found->second);
            }
            factorProduct = assembleLeftAssociatedProduct(
                context.multiplyName, atomTerms);
        }
        ExpressionPointer monomial;
        if (magnitude == 1) {
            // No explicit coefficient. If no factors, the monomial is
            // just `one`.
            monomial = factorProduct ? factorProduct
                                      : makeConstant(context.oneName);
        } else {
            ExpressionPointer coefficientExpr =
                buildRingCoefficientExpression(magnitude, context);
            monomial = factorProduct
                ? buildRingOp(context.multiplyName,
                                std::move(coefficientExpr),
                                std::move(factorProduct))
                : std::move(coefficientExpr);
        }
        if (coefficient < 0) {
            ExpressionPointer negate = makeConstant(context.negateName);
            monomial = makeApplication(std::move(negate),
                                          std::move(monomial));
        }
        return monomial;
    }

    // Build the canonical-form kernel expression for a polynomial.
    // Empty polynomial → `zero`. Single monomial → that monomial.
    // Multiple monomials → left-associated sum in std::map order
    // (i.e., ordered by lex of factor signature, which is determined
    // by subtree hashes — so the order is stable but unspecified).
    ExpressionPointer buildCanonicalPolynomial(
        const RingPolynomial& polynomial,
        const RingV2Context& context) {
        if (polynomial.empty()) {
            return makeConstant(context.zeroName);
        }
        std::vector<ExpressionPointer> monomials;
        monomials.reserve(polynomial.size());
        for (const auto& entry : polynomial) {
            monomials.push_back(buildCanonicalMonomial(
                entry.first, entry.second, context));
        }
        ExpressionPointer accumulator = monomials[0];
        for (size_t i = 1; i < monomials.size(); ++i) {
            accumulator = buildRingOp(context.addName,
                                        std::move(accumulator),
                                        monomials[i]);
        }
        return accumulator;
    }

    // Compare two polynomials for equality (canonical-form match).
    bool ringPolynomialsAgree(
        const RingPolynomial& left, const RingPolynomial& right) {
        if (left.size() != right.size()) return false;
        auto leftIter = left.begin();
        auto rightIter = right.begin();
        while (leftIter != left.end()) {
            if (leftIter->first != rightIter->first) return false;
            if (leftIter->second != rightIter->second) return false;
            ++leftIter;
            ++rightIter;
        }
        return true;
    }

    // =====================================================================
    // Ring v2 — proof emitter helpers.
    //
    // The decision step already canonicalises both endpoints to the same
    // polynomial. The emitter produces a proof of
    //     leftEndpoint = canonical(polynomial) = rightEndpoint
    // by recursive descent on each endpoint's kernel structure. At each
    // node (add/multiply/negate) the recursive sub-proofs are joined via
    // congruence, and a "merge" step reconciles the canonical-of-parts
    // form with the canonical-of-whole form.
    //
    // Coefficient guard: |coeff| <= 1 throughout. Larger collected
    // coefficients (e.g. a + a → 2·a) are out of scope for v2 and the
    // top-level decision step bails with a clear error before we reach
    // the proof emitter.
    // =====================================================================

    // Carrier-specific axiom names. Library carriers split into two
    // naming conventions: Rational/Real/PAdic use `zero_add` /
    // `add_zero` / `one_multiply` / `multiply_one`; Integer uses
    // `add_identity_left` / `add_identity_right` /
    // `multiply_identity_left` / `multiply_identity_right`. We probe
    // both, prefer whichever is in scope.
    struct RingV2AxiomNames {
        std::string addZeroRight;          // a + 0 = a
        std::string zeroAddLeft;           // 0 + a = a
        std::string multiplyOneRight;      // a * 1 = a
        std::string oneMultiplyLeft;       // 1 * a = a
        std::string multiplyZeroLeft;      // 0 * a = 0
        std::string multiplyZeroRight;     // a * 0 = 0
        std::string addNegateRight;        // a + -a = 0
        std::string addNegateLeft;         // -a + a = 0
        std::string negateNegate;          // -(-a) = a
        std::string negateAdd;             // -(a + b) = -a + -b
        std::string multiplyNegateLeft;    // -a * b = -(a * b)
        std::string multiplyNegateRight;   // a * -b = -(a * b)
        std::string distributivityLeft;    // a * (b + c) = a*b + a*c
        std::string distributivityRight;   // (a + b) * c = a*c + b*c
        std::string addAssociative;
        std::string addCommutative;
        std::string multiplyAssociative;
        std::string multiplyCommutative;
    };

    std::string pickAxiomName(const std::string& candidateOne,
                                 const std::string& candidateTwo) {
        if (environment_.lookup(candidateOne) != nullptr) {
            return candidateOne;
        }
        if (environment_.lookup(candidateTwo) != nullptr) {
            return candidateTwo;
        }
        return std::string{};
    }

    RingV2AxiomNames resolveRingV2AxiomNames(
        const std::string& carrierName) {
        RingV2AxiomNames names;
        names.zeroAddLeft = pickAxiomName(
            carrierName + ".zero_add",
            carrierName + ".add_identity_left");
        names.addZeroRight = pickAxiomName(
            carrierName + ".add_zero",
            carrierName + ".add_identity_right");
        names.oneMultiplyLeft = pickAxiomName(
            carrierName + ".one_multiply",
            carrierName + ".multiply_identity_left");
        names.multiplyOneRight = pickAxiomName(
            carrierName + ".multiply_one",
            carrierName + ".multiply_identity_right");
        names.multiplyZeroLeft = pickAxiomName(
            carrierName + ".multiply_zero_left",
            carrierName + ".zero_multiply");
        names.multiplyZeroRight = pickAxiomName(
            carrierName + ".multiply_zero_right",
            carrierName + ".multiply_zero");
        names.addNegateRight = pickAxiomName(
            carrierName + ".add_negate_right",
            carrierName + ".add_negate_right");
        names.addNegateLeft = pickAxiomName(
            carrierName + ".add_negate_left",
            carrierName + ".add_negate_left");
        names.negateNegate = pickAxiomName(
            carrierName + ".negate_negate",
            carrierName + ".negate_negate");
        names.negateAdd = pickAxiomName(
            carrierName + ".negate_add",
            carrierName + ".negate_add");
        names.multiplyNegateLeft = pickAxiomName(
            carrierName + ".multiply_negate_left",
            carrierName + ".multiply_negate_left");
        names.multiplyNegateRight = pickAxiomName(
            carrierName + ".multiply_negate_right",
            carrierName + ".multiply_negate_right");
        names.distributivityLeft = carrierName + ".distributivity_left";
        names.distributivityRight = carrierName + ".distributivity_right";
        names.addAssociative = carrierName + ".add_associative";
        names.addCommutative = carrierName + ".add_commutative";
        names.multiplyAssociative = carrierName + ".multiply_associative";
        names.multiplyCommutative = carrierName + ".multiply_commutative";
        return names;
    }

    void demandAxiomName(const std::string& axiomName,
                            const std::string& description,
                            const std::string& carrierName) {
        if (axiomName.empty()
            || environment_.lookup(axiomName) == nullptr) {
            throwElaborate(
                "`ring` (v2): carrier `" + carrierName
                + "` is missing axiom `" + description
                + "` — required for this goal");
        }
    }

    // Build `<negateName>(inner)`.
    ExpressionPointer buildRingNegate(
        const std::string& negateName, ExpressionPointer inner) {
        return makeApplication(makeConstant(negateName), std::move(inner));
    }

    // Render a signed-monomial pair `(signature, sign)` to its canonical
    // kernel form. Just an alias for buildCanonicalMonomial.
    ExpressionPointer buildSignedMonomialKernel(
        const RingMonomialSignature& signature,
        int sign,
        const RingV2Context& context) {
        return buildCanonicalMonomial(signature, sign, context);
    }

    struct SignedMonomial {
        RingMonomialSignature signature;
        int sign;  // +1 or -1
    };

    std::vector<SignedMonomial> polynomialToSignedMonomials(
        const RingPolynomial& polynomial) {
        std::vector<SignedMonomial> output;
        output.reserve(polynomial.size());
        for (const auto& entry : polynomial) {
            output.push_back({entry.first, entry.second});
        }
        return output;
    }

    // Left-associated sum of kernel summands. summands must be non-empty.
    ExpressionPointer assembleLeftAssociatedSum(
        const std::string& addName,
        const std::vector<ExpressionPointer>& summands) {
        ExpressionPointer accumulator = summands[0];
        for (size_t i = 1; i < summands.size(); ++i) {
            accumulator = buildRingOp(
                addName, std::move(accumulator), summands[i]);
        }
        return accumulator;
    }

    // ----------------------------------------------------------------
    // Sum-AC building blocks: re-using v1's flatten/reassoc/sort
    // machinery but on the additive operator. Each "atom" of the sum
    // is an opaque kernel expression (a fully-rendered signed monomial).
    // ----------------------------------------------------------------

    // Re-associate `expression` (an arbitrary tree of `<addName>` and
    // opaque leaves) into a left-associated sum and return a proof
    // `expression = leftAssoc(flatten(expression))`.
    ExpressionPointer reassociateSumLeftProof(
        ExpressionPointer expression,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        RingAxiomNames addAxioms{
            context.addName,
            axiomNames.addAssociative,
            axiomNames.addCommutative};
        return buildLeftAssocReassocProof(
            addAxioms, context.carrierUniverseLevel,
            context.carrierType, expression);
    }

    // Insertion-sort proof on a left-associated sum: given the original
    // factor list and the desired (sorted) factor list, produces a
    // proof `leftAssoc(originalFactors) = leftAssoc(sortedFactors)`.
    ExpressionPointer sortSumLeftAssocProof(
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        RingAxiomNames addAxioms{
            context.addName,
            axiomNames.addAssociative,
            axiomNames.addCommutative};
        ExpressionPointer original = assembleLeftAssociatedProduct(
            context.addName, originalFactors);
        return proveProductEqualsSorted(
            original, originalFactors, sortedFactors,
            addAxioms, context.carrierType,
            context.carrierUniverseLevel, /*line*/0);
    }

    // Same as sortSumLeftAssocProof but using the multiplicative
    // operator. Used by proveMultiplyMerge to sort factors within a
    // monomial.
    ExpressionPointer sortMultiplyLeftAssocProof(
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        RingAxiomNames multiplyAxioms{
            context.multiplyName,
            axiomNames.multiplyAssociative,
            axiomNames.multiplyCommutative};
        ExpressionPointer original = assembleLeftAssociatedProduct(
            context.multiplyName, originalFactors);
        return proveProductEqualsSorted(
            original, originalFactors, sortedFactors,
            multiplyAxioms, context.carrierType,
            context.carrierUniverseLevel, /*line*/0);
    }

    // Same as reassociateSumLeftProof but on the multiplicative
    // operator.
    ExpressionPointer reassociateMultiplyLeftProof(
        ExpressionPointer expression,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        RingAxiomNames multiplyAxioms{
            context.multiplyName,
            axiomNames.multiplyAssociative,
            axiomNames.multiplyCommutative};
        return buildLeftAssocReassocProof(
            multiplyAxioms, context.carrierUniverseLevel,
            context.carrierType, expression);
    }

    // ----------------------------------------------------------------
    // Top-level recursive descent and merge steps.
    // Each merge takes already-canonical operand polynomials and emits
    // a proof reconciling `(canonicalLeft) op (canonicalRight)` with
    // `canonical(leftPoly op rightPoly)`.
    // ----------------------------------------------------------------

    // ----------------------------------------------------------------
    // proveEqualsCanonical: recursive descent producing a kernel proof
    // `expression = canonical(polynomial(expression))`.
    // ----------------------------------------------------------------
    ExpressionPointer proveEqualsCanonical_impl(
        ExpressionPointer expression,
        RingV2Context& context,
        const RingV2AxiomNames& axiomNames,
        RingPolynomial& polynomialOut) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // Match zero.
        if (matchRingZero(expression, context.zeroName)) {
            polynomialOut = RingPolynomial{};
            return buildReflexivity(universeLevel, carrierType, expression);
        }
        // Match one.
        if (matchRingOne(expression, context.oneName)) {
            polynomialOut = ringPolynomialOne();
            return buildReflexivity(universeLevel, carrierType, expression);
        }
        // Match negate(inner).
        {
            ExpressionPointer inner;
            if (matchUnaryRingNegate(expression, context.negateName, inner)) {
                RingPolynomial innerPoly;
                ExpressionPointer innerProof = proveEqualsCanonical(
                    inner, context, axiomNames, innerPoly);
                // Build proof: negate(inner) = negate(canonical(innerPoly))
                // via congruence with λz. negate(z).
                ExpressionPointer innerCanonical =
                    buildCanonicalPolynomial(innerPoly, context);
                // λ z : T. negate(z). z has de-Bruijn index 0.
                ExpressionPointer lambdaBody = buildRingNegate(
                    context.negateName, makeBoundVariable(0));
                ExpressionPointer lambda = makeLambda(
                    "_ring_negate_z", carrierType, lambdaBody);
                ExpressionPointer congrProof =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        inner, innerCanonical, innerProof);
                // Now: negate(inner) = negate(canonical(innerPoly)).
                // Compose with negate-merge:
                //   negate(canonical(innerPoly)) = canonical(-innerPoly).
                RingPolynomial negatedPoly = innerPoly;
                ringPolynomialNegate(negatedPoly);
                polynomialOut = negatedPoly;
                ExpressionPointer mergeProof = proveNegateMerge(
                    innerPoly, context, axiomNames);
                ExpressionPointer canonicalNegated =
                    buildCanonicalPolynomial(negatedPoly, context);
                ExpressionPointer fullProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingNegate(context.negateName, innerCanonical),
                    canonicalNegated,
                    congrProof, mergeProof);
                return fullProof;
            }
        }
        // Match subtract(left, right) — bridge to add(left, negate(right))
        // via reflexivity (the carrier's `subtract` is defined as
        // `x + -y`, so the kernel collapses them under δ).
        {
            ExpressionPointer left, right;
            if (matchBinaryRingOp(expression, context.subtractName,
                                     left, right)) {
                ExpressionPointer equivalent = buildRingOp(
                    context.addName,
                    left,
                    buildRingNegate(context.negateName, right));
                ExpressionPointer equivalentProof =
                    proveEqualsCanonical(
                        equivalent, context, axiomNames,
                        polynomialOut);
                ExpressionPointer canonical =
                    buildCanonicalPolynomial(polynomialOut, context);
                ExpressionPointer bridge =
                    buildReflexivity(universeLevel, carrierType,
                                       expression);
                return buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression, equivalent, canonical,
                    bridge, equivalentProof);
            }
        }
        // Match add(left, right).
        {
            ExpressionPointer left, right;
            if (matchBinaryRingOp(expression, context.addName,
                                     left, right)) {
                RingPolynomial leftPoly, rightPoly;
                ExpressionPointer leftProof = proveEqualsCanonical(
                    left, context, axiomNames, leftPoly);
                ExpressionPointer rightProof = proveEqualsCanonical(
                    right, context, axiomNames, rightPoly);
                ExpressionPointer leftCanonical =
                    buildCanonicalPolynomial(leftPoly, context);
                ExpressionPointer rightCanonical =
                    buildCanonicalPolynomial(rightPoly, context);
                // Step 1: add(left, right) = add(leftCanonical, right)
                // via congruence λz. z + right.
                ExpressionPointer rightLifted =
                    liftBoundVariables(right, 1, 0);
                ExpressionPointer lambdaLeftBody = buildRingOp(
                    context.addName, makeBoundVariable(0), rightLifted);
                ExpressionPointer lambdaLeft = makeLambda(
                    "_ring_add_z", carrierType, lambdaLeftBody);
                ExpressionPointer step1 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaLeft,
                        left, leftCanonical, leftProof);
                // Step 2: add(leftCanonical, right)
                //          = add(leftCanonical, rightCanonical)
                // via congruence λz. leftCanonical + z.
                ExpressionPointer leftCanLifted =
                    liftBoundVariables(leftCanonical, 1, 0);
                ExpressionPointer lambdaRightBody = buildRingOp(
                    context.addName, leftCanLifted, makeBoundVariable(0));
                ExpressionPointer lambdaRight = makeLambda(
                    "_ring_add_z", carrierType, lambdaRightBody);
                ExpressionPointer step2 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaRight,
                        right, rightCanonical, rightProof);
                ExpressionPointer step12 = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.addName, leftCanonical, right),
                    buildRingOp(context.addName, leftCanonical,
                                  rightCanonical),
                    step1, step2);
                // Step 3 (merge): add(leftCanonical, rightCanonical)
                //                  = canonical(leftPoly + rightPoly)
                RingPolynomial mergedPoly = leftPoly;
                ringPolynomialAccumulate(mergedPoly, rightPoly);
                polynomialOut = mergedPoly;
                ExpressionPointer mergeProof = proveAddMerge(
                    leftPoly, rightPoly, context, axiomNames);
                ExpressionPointer mergedCanonical =
                    buildCanonicalPolynomial(mergedPoly, context);
                return buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.addName, leftCanonical,
                                  rightCanonical),
                    mergedCanonical,
                    step12, mergeProof);
            }
        }
        // Match multiply(left, right).
        {
            ExpressionPointer left, right;
            if (matchBinaryRingOp(expression, context.multiplyName,
                                     left, right)) {
                RingPolynomial leftPoly, rightPoly;
                ExpressionPointer leftProof = proveEqualsCanonical(
                    left, context, axiomNames, leftPoly);
                ExpressionPointer rightProof = proveEqualsCanonical(
                    right, context, axiomNames, rightPoly);
                ExpressionPointer leftCanonical =
                    buildCanonicalPolynomial(leftPoly, context);
                ExpressionPointer rightCanonical =
                    buildCanonicalPolynomial(rightPoly, context);
                ExpressionPointer rightLifted =
                    liftBoundVariables(right, 1, 0);
                ExpressionPointer lambdaLeftBody = buildRingOp(
                    context.multiplyName, makeBoundVariable(0),
                    rightLifted);
                ExpressionPointer lambdaLeft = makeLambda(
                    "_ring_mul_z", carrierType, lambdaLeftBody);
                ExpressionPointer step1 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaLeft,
                        left, leftCanonical, leftProof);
                ExpressionPointer leftCanLifted =
                    liftBoundVariables(leftCanonical, 1, 0);
                ExpressionPointer lambdaRightBody = buildRingOp(
                    context.multiplyName, leftCanLifted,
                    makeBoundVariable(0));
                ExpressionPointer lambdaRight = makeLambda(
                    "_ring_mul_z", carrierType, lambdaRightBody);
                ExpressionPointer step2 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaRight,
                        right, rightCanonical, rightProof);
                ExpressionPointer step12 = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.multiplyName, leftCanonical, right),
                    buildRingOp(context.multiplyName, leftCanonical,
                                  rightCanonical),
                    step1, step2);
                RingPolynomial mergedPoly =
                    ringPolynomialMultiply(leftPoly, rightPoly);
                polynomialOut = mergedPoly;
                ExpressionPointer mergeProof = proveMultiplyMerge(
                    leftPoly, rightPoly, context, axiomNames);
                ExpressionPointer mergedCanonical =
                    buildCanonicalPolynomial(mergedPoly, context);
                return buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.multiplyName, leftCanonical,
                                  rightCanonical),
                    mergedCanonical,
                    step12, mergeProof);
            }
        }
        // Otherwise: an opaque atom. Its canonical kernel is itself.
        polynomialOut = ringPolynomialAtom(context, expression);
        ExpressionPointer canonicalKernel =
            buildCanonicalPolynomial(polynomialOut, context);
        if (!structurallyEqual(expression, canonicalKernel)) {
            throwElaborate(
                "`ring` (v2): atom's canonical kernel mismatched the "
                "atom itself (internal error)");
        }
        return buildReflexivity(universeLevel, carrierType, expression);
    }

    ExpressionPointer proveEqualsCanonical(
        ExpressionPointer expression,
        RingV2Context& context,
        const RingV2AxiomNames& axiomNames,
        RingPolynomial& polynomialOut) {
        return proveEqualsCanonical_impl(
            expression, context, axiomNames, polynomialOut);
    }

    // ----------------------------------------------------------------
    // proveAddMerge: prove
    //   canonical(leftPoly) + canonical(rightPoly) = canonical(leftPoly + rightPoly)
    // ----------------------------------------------------------------
    //
    // Cases by emptiness of inputs:
    //   * Both empty:  LHS = zero + zero, RHS = zero. Not currently
    //     supported (would need a zero_add or add_zero step). We bail.
    //   * leftPoly empty: LHS = zero + canonical(rightPoly), RHS = canonical(rightPoly).
    //     Use zero_add (a.k.a. add_identity_left).
    //   * rightPoly empty: symmetric.
    //   * Both non-empty: full sum-AC sort + cancel.
    ExpressionPointer proveAddMerge(
        const RingPolynomial& leftPoly,
        const RingPolynomial& rightPoly,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        ExpressionPointer leftCanonical =
            buildCanonicalPolynomial(leftPoly, context);
        ExpressionPointer rightCanonical =
            buildCanonicalPolynomial(rightPoly, context);
        ExpressionPointer leftPlusRight = buildRingOp(
            context.addName, leftCanonical, rightCanonical);
        RingPolynomial mergedPoly = leftPoly;
        ringPolynomialAccumulate(mergedPoly, rightPoly);
        ExpressionPointer mergedCanonical =
            buildCanonicalPolynomial(mergedPoly, context);
        if (leftPoly.empty() && rightPoly.empty()) {
            // zero + zero = zero. Use zero_add(zero) :  0 + 0 = 0.
            demandAxiomName(axiomNames.zeroAddLeft, "zero_add/add_identity_left",
                              context.carrierName);
            ExpressionPointer zeroConst = makeConstant(context.zeroName);
            ExpressionPointer call =
                makeApplication(makeConstant(axiomNames.zeroAddLeft),
                                  zeroConst);
            return call;
        }
        if (leftPoly.empty()) {
            // zero + canonical(rightPoly) = canonical(rightPoly).
            demandAxiomName(axiomNames.zeroAddLeft, "zero_add/add_identity_left",
                              context.carrierName);
            ExpressionPointer call =
                makeApplication(makeConstant(axiomNames.zeroAddLeft),
                                  rightCanonical);
            return call;
        }
        if (rightPoly.empty()) {
            // canonical(leftPoly) + zero = canonical(leftPoly).
            demandAxiomName(axiomNames.addZeroRight, "add_zero/add_identity_right",
                              context.carrierName);
            ExpressionPointer call =
                makeApplication(makeConstant(axiomNames.addZeroRight),
                                  leftCanonical);
            return call;
        }
        // Both non-empty.  Build the flat summand list from leftPoly
        // and rightPoly's canonical forms.  Each entry is a fully-
        // rendered signed monomial kernel.
        std::vector<SignedMonomial> combinedMonomials =
            polynomialToSignedMonomials(leftPoly);
        for (const auto& entry : rightPoly) {
            combinedMonomials.push_back({entry.first, entry.second});
        }
        std::vector<ExpressionPointer> combinedKernels;
        combinedKernels.reserve(combinedMonomials.size());
        for (const auto& m : combinedMonomials) {
            combinedKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Step 1: re-associate `leftCanonical + rightCanonical` into a
        // flat left-associated chain over `combinedKernels`. Treat each
        // monomial kernel as opaque. We do this by reassociateSumLeftProof.
        ExpressionPointer leftAssocCombined = assembleLeftAssociatedSum(
            context.addName, combinedKernels);
        ExpressionPointer reassocProof = reassociateSumLeftProof(
            leftPlusRight, context, axiomNames);
        // Step 2: insertion-sort by structural order so that all merged-
        // poly monomials' kernel forms appear in std::map signature
        // order, with cancelling (M, -M) pairs becoming adjacent.
        //
        // We want the sorted order to MATCH the canonical-of-merged
        // form's iteration order (std::map signature ascending). We do
        // this by computing the target sorted vector as the canonical
        // sequence of monomial kernels INTERSPERSED with the cancelling
        // pairs that should disappear.
        //
        // Concretely: walk combinedMonomials sorted by signature. Group
        // entries with the same signature; if the group has two entries
        // with opposite signs, they cancel — place them adjacent in the
        // target list. Otherwise (single entry, or two entries with the
        // same sign which would mean coefficient ±2, ruled out by the
        // coefficient guard), the entry survives in the canonical form
        // and is placed at its canonical position.
        //
        // Build:
        //   * sortedKernels: a vector of ExpressionPointers in the order
        //     we want after sorting. Surviving monomials first/in-order,
        //     cancelled-pairs grouped at the end. Actually simpler:
        //     emit pairs first (so we can cancel from the right), then
        //     survivors. But that re-orders the survivors w.r.t.
        //     canonical. Alternative: emit survivors and pairs in
        //     positional order, and during cancellation we walk back
        //     through.
        //
        // Easier approach: place ALL surviving monomials at the head of
        // the sorted vector (in canonical sig order), then all cancel-
        // pairs at the tail (each pair as (M, -M) adjacent). After
        // sort, cancel each pair right-to-left, applying add_negate_*
        // and dropping the resulting zero.
        std::vector<SignedMonomial> sortedSignedMonomials;
        // Group by signature.
        std::map<RingMonomialSignature, std::vector<int>> bySig;
        for (const auto& m : combinedMonomials) {
            bySig[m.signature].push_back(m.sign);
        }
        // Survivors first, in canonical signature order. Cancel pairs
        // collected to the side.
        std::vector<std::pair<RingMonomialSignature, int>> cancelPairs;
        for (const auto& [sig, signs] : bySig) {
            if (signs.size() == 1) {
                sortedSignedMonomials.push_back({sig, signs[0]});
            } else if (signs.size() == 2
                       && signs[0] + signs[1] == 0) {
                // (M, -M) — collect for cancellation. The merged-poly
                // does not contain this signature.
                cancelPairs.push_back({sig, +1});
            } else {
                throwElaborate(
                    "`ring` (v2): proveAddMerge encountered a signature "
                    "with " + std::to_string(signs.size())
                    + " entries — coefficient guard should have caught this");
            }
        }
        // Verify: surviving monomials, in std::map signature order,
        // EXACTLY match canonicalMergedPoly's order.
        std::vector<SignedMonomial> mergedMonomials =
            polynomialToSignedMonomials(mergedPoly);
        if (sortedSignedMonomials.size() != mergedMonomials.size()) {
            throwElaborate(
                "`ring` (v2): proveAddMerge: survivor count mismatched "
                "merged polynomial size (internal error)");
        }
        for (size_t i = 0; i < mergedMonomials.size(); ++i) {
            if (sortedSignedMonomials[i].signature
                    != mergedMonomials[i].signature
                || sortedSignedMonomials[i].sign
                    != mergedMonomials[i].sign) {
                throwElaborate(
                    "`ring` (v2): proveAddMerge: survivors don't match "
                    "merged polynomial entry-by-entry (internal error)");
            }
        }
        // Append cancellation pairs.
        for (const auto& [sig, _] : cancelPairs) {
            sortedSignedMonomials.push_back({sig, +1});
            sortedSignedMonomials.push_back({sig, -1});
        }
        // Convert sortedSignedMonomials to kernels and sort the
        // *combinedKernels* into that order via insertion-sort proof.
        std::vector<ExpressionPointer> sortedKernels;
        sortedKernels.reserve(sortedSignedMonomials.size());
        for (const auto& m : sortedSignedMonomials) {
            sortedKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // The sortSumLeftAssocProof expects a vector that's a
        // permutation of combinedKernels (treated as the "factor
        // multiset"). proveProductEqualsSorted does insertion-sort
        // using compareExpressionStructure for direction. But we
        // want a SPECIFIC target permutation, not the
        // structurally-sorted one. proveProductEqualsSorted accepts
        // arbitrary sorted targets — let me check.
        //
        // Looking at proveProductEqualsSorted: it walks i = 0..n-1,
        // for each i finds the first j with current[j] = sorted[i],
        // and swaps it down to position i via adjacent swaps. So
        // ANY permutation of the original factor multiset works as
        // the "sorted" target.
        ExpressionPointer sortProof = sortSumLeftAssocProof(
            combinedKernels, sortedKernels, context, axiomNames);
        ExpressionPointer leftAssocSorted = assembleLeftAssociatedProduct(
            context.addName, sortedKernels);
        // Chain so far: leftPlusRight = leftAssocCombined (via
        // reassocProof) = leftAssocSorted (via sortProof).
        ExpressionPointer chainSoFar = buildEqualityTransitivity(
            universeLevel, carrierType,
            leftPlusRight, leftAssocCombined, leftAssocSorted,
            reassocProof, sortProof);
        if (cancelPairs.empty()) {
            // Surviving monomials only: leftAssocSorted == mergedCanonical.
            // Check that and return chainSoFar.
            if (!structurallyEqual(leftAssocSorted, mergedCanonical)) {
                throwElaborate(
                    "`ring` (v2): proveAddMerge expected leftAssocSorted "
                    "to match canonical(mergedPoly) (no cancellations) "
                    "but they differ (internal error)");
            }
            return chainSoFar;
        }
        // Cancellations needed. Walk sortedKernels from right to left,
        // collapsing each (M, -M) tail-pair via:
        //   1. associativity: (((prefix + M) + -M) + tail) — no, after
        //      sort we already placed pairs at the very tail. The
        //      current form is `((prefix) + M_p) + (-M_p)` (for the
        //      rightmost pair). We use:
        //      add_associative(prefix, M, -M) :
        //        prefix + M + -M = prefix + (M + -M)
        //      add_negate_right(M) : M + -M = 0
        //      congruence with λz. prefix + z to get
        //        prefix + (M + -M) = prefix + 0
        //      add_zero_right(prefix) (i.e. add_zero) : prefix + 0 = prefix
        //   2. Then iterate: drop the next pair from the tail.
        demandAxiomName(axiomNames.addNegateRight, "add_negate_right",
                          context.carrierName);
        demandAxiomName(axiomNames.addZeroRight, "add_zero/add_identity_right",
                          context.carrierName);
        // current: ExpressionPointer for the current form. Starts as
        // leftAssocSorted. Each cancellation step removes the last two
        // summands (the (M, -M) pair).
        ExpressionPointer currentForm = leftAssocSorted;
        ExpressionPointer chainProof = chainSoFar;
        std::vector<ExpressionPointer> remainingKernels = sortedKernels;
        for (size_t pairIndex = 0; pairIndex < cancelPairs.size();
             ++pairIndex) {
            // Pop the last two from remainingKernels: they are (M, -M).
            if (remainingKernels.size() < 2) {
                throwElaborate(
                    "`ring` (v2): cancellation underrun (internal error)");
            }
            ExpressionPointer negM = remainingKernels.back();
            remainingKernels.pop_back();
            ExpressionPointer M = remainingKernels.back();
            remainingKernels.pop_back();
            ExpressionPointer prefix;
            bool prefixSingle = (remainingKernels.size() == 1);
            if (prefixSingle) {
                prefix = remainingKernels[0];
            } else {
                prefix = assembleLeftAssociatedProduct(
                    context.addName, remainingKernels);
            }
            // currentForm has shape:
            //   ((prefix) + M) + (-M)
            // Step A: associativity. (prefix + M) + (-M) = prefix + (M + (-M)).
            ExpressionPointer assocProof = makeConstant(
                axiomNames.addAssociative);
            assocProof = makeApplication(assocProof, prefix);
            assocProof = makeApplication(assocProof, M);
            assocProof = makeApplication(assocProof, negM);
            ExpressionPointer formA = buildRingOp(
                context.addName, prefix,
                buildRingOp(context.addName, M, negM));
            // Step B: congruence with λz. prefix + z, where the inner
            // step is `add_negate_right(M) : M + (-M) = 0`.
            ExpressionPointer addNegProof = makeConstant(
                axiomNames.addNegateRight);
            addNegProof = makeApplication(addNegProof, M);
            ExpressionPointer prefixLifted =
                liftBoundVariables(prefix, 1, 0);
            ExpressionPointer lambdaBodyB = buildRingOp(
                context.addName, prefixLifted, makeBoundVariable(0));
            ExpressionPointer lambdaB = makeLambda(
                "_ring_cancel_z", carrierType, lambdaBodyB);
            ExpressionPointer zeroConst = makeConstant(context.zeroName);
            ExpressionPointer congrB =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaB,
                    buildRingOp(context.addName, M, negM),
                    zeroConst,
                    addNegProof);
            ExpressionPointer formB = buildRingOp(
                context.addName, prefix, zeroConst);
            // Step C: add_zero_right(prefix) : prefix + 0 = prefix.
            ExpressionPointer addZeroProof = makeConstant(
                axiomNames.addZeroRight);
            addZeroProof = makeApplication(addZeroProof, prefix);
            // Compose: currentForm → formA via assocProof,
            //          formA → formB via congrB,
            //          formB → prefix via addZeroProof.
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formA, formB,
                assocProof, congrB);
            ExpressionPointer stepABC = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formB, prefix,
                stepAB, addZeroProof);
            // Now chain with chainProof.
            chainProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                leftPlusRight, currentForm, prefix,
                chainProof, stepABC);
            currentForm = prefix;
        }
        // After all cancellations, currentForm should be the merged
        // canonical form (sortedKernels of just the survivors,
        // left-associated). Or if zero survivors remain, it's zero.
        // Check structural equality with mergedCanonical.
        if (remainingKernels.empty()) {
            // All summands cancelled. The current chain ends at `prefix`
            // from the last step — but the last step needed at least
            // one survivor as prefix (we'd have crashed otherwise).
            // So this branch shouldn't trigger here; mergedPoly was non-empty.
            // Actually wait: if all summands cancel, mergedPoly is empty,
            // and mergedCanonical is zero. The above loop ASSUMED there's
            // a prefix to drop the zero into. We'd need a special case.
            throwElaborate(
                "`ring` (v2): proveAddMerge total-cancellation case "
                "(empty merged polynomial) is not implemented");
        }
        if (!structurallyEqual(currentForm, mergedCanonical)) {
            throwElaborate(
                "`ring` (v2): proveAddMerge ended with shape mismatched "
                "with canonical(mergedPoly) (internal error)");
        }
        return chainProof;
    }

    // ----------------------------------------------------------------
    // proveMultiplyMerge: prove
    //   canonical(leftPoly) * canonical(rightPoly) = canonical(leftPoly * rightPoly)
    // ----------------------------------------------------------------
    //
    // Strategy (full distribution):
    //   1. Fully distribute the product into a sum of monomial-products.
    //      We expand `(L_1 + ... + L_p) * (R_1 + ... + R_q)` via repeated
    //      distributivity_right / distributivity_left.
    //   2. Each summand `L_i * R_j` is then sign-pushed (multiply_negate_*
    //      + negate_negate) so its outer wrapper is at most one negate,
    //      and its factor product is left-associated.
    //   3. Sort factors within each summand by hash signature.
    //   4. Sort the summands by canonical order (per std::map merge).
    //   5. Cancel any (M, -M) pairs that arise.
    //
    // To stay implementable in v2 v1, the merge currently restricts to
    // the case where the EXPANSION DOES NOT PRODUCE CANCELLATION: i.e.
    // each pair of input monomials L_i × R_j yields a distinct merged
    // signature. (Cancellations would arise only when distinct L*R pairs
    // happen to produce identical signatures with opposite signs — rare
    // in our test set.)
    //
    // Implementation in steps:
    //   * Determine the canonical merged poly = leftPoly · rightPoly.
    //   * The "naive expanded form" is the left-associated sum
    //       (L_1·R_1) + (L_1·R_2) + ... + (L_p·R_q)
    //     (in lexicographic L-then-R order). For SINGLE-element leftPoly
    //     OR single-element rightPoly this collapses cleanly.
    //   * For each row i we use distributivity_right to peel
    //       (L_i + rest) * R = L_i*R + rest*R     (rest is left side of L)
    //     then recurse. Symmetric for the inner with distributivity_left.
    //
    // For implementation simplicity in v2 v1, we handle:
    //   (a) Both single-summand: just product-of-monomials path.
    //   (b) Left single, right multi: distributivity_left, then per-
    //       summand monomial canonicalisation.
    //   (c) Left multi, right single: distributivity_right.
    //   (d) Left multi, right multi: distributivity_right peels one row
    //       at a time, recursing.
    ExpressionPointer proveMultiplyMerge(
        const RingPolynomial& leftPoly,
        const RingPolynomial& rightPoly,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        ExpressionPointer leftCanonical =
            buildCanonicalPolynomial(leftPoly, context);
        ExpressionPointer rightCanonical =
            buildCanonicalPolynomial(rightPoly, context);
        ExpressionPointer leftTimesRight = buildRingOp(
            context.multiplyName, leftCanonical, rightCanonical);
        RingPolynomial mergedPoly = ringPolynomialMultiply(
            leftPoly, rightPoly);
        ExpressionPointer mergedCanonical =
            buildCanonicalPolynomial(mergedPoly, context);
        // Edge: one side empty. Then leftPoly · rightPoly = empty, and
        // we need multiply_zero_*.
        if (leftPoly.empty()) {
            demandAxiomName(axiomNames.multiplyZeroLeft,
                              "multiply_zero_left", context.carrierName);
            ExpressionPointer call = makeApplication(
                makeConstant(axiomNames.multiplyZeroLeft),
                rightCanonical);
            return call;
        }
        if (rightPoly.empty()) {
            demandAxiomName(axiomNames.multiplyZeroRight,
                              "multiply_zero_right", context.carrierName);
            ExpressionPointer call = makeApplication(
                makeConstant(axiomNames.multiplyZeroRight),
                leftCanonical);
            return call;
        }
        // For now we handle ONLY the common case: no like-term
        // collisions in mergedPoly (i.e. mergedPoly's size equals
        // leftPoly.size() * rightPoly.size()). With coefficient ±1
        // throughout, like-term collisions would necessarily mean
        // signature collisions across pairs, which trigger the
        // cancellation path. Test cases (1)-(4) all satisfy the
        // no-collision condition.
        if (mergedPoly.size() != leftPoly.size() * rightPoly.size()) {
            throwElaborate(
                "`ring` (v2): proveMultiplyMerge with cross-pair "
                "cancellations not yet supported");
        }
        // Build the "naively expanded" sum:
        //   sum_{i,j} (L_i * R_j)
        // in the order (i, j) = (0, 0..q-1), (1, 0..q-1), ..., (p-1, ...).
        // Render each L_i and R_j as canonical monomial kernels.
        std::vector<SignedMonomial> leftSigned =
            polynomialToSignedMonomials(leftPoly);
        std::vector<SignedMonomial> rightSigned =
            polynomialToSignedMonomials(rightPoly);
        std::vector<ExpressionPointer> leftMonomialKernels;
        for (const auto& m : leftSigned) {
            leftMonomialKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        std::vector<ExpressionPointer> rightMonomialKernels;
        for (const auto& m : rightSigned) {
            rightMonomialKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Step 1: prove leftCanonical * rightCanonical = sum_{i,j} L_i * R_j.
        // We do this in two sub-phases:
        //   1a: leftCanonical * rightCanonical
        //         = sum_i (L_i * rightCanonical)      via distributivity_right (peel rows)
        //   1b: each L_i * rightCanonical
        //         = sum_j (L_i * R_j)                via distributivity_left
        //   1c: combine inner sums into the flat outer form.
        //
        // For implementation we use a simpler iterative approach:
        // expand row-by-row applying distributivity_right.
        demandAxiomName(axiomNames.distributivityRight,
                          "distributivity_right", context.carrierName);
        demandAxiomName(axiomNames.distributivityLeft,
                          "distributivity_left", context.carrierName);
        // Phase 1a: expand the outer left into a sum of (L_i * rightCanonical).
        // We achieve this by peeling the leftmost group from the
        // left-associated `L_1 + ... + L_p`. Each peel uses
        // distributivity_right(prefix, L_i, rightCanonical):
        //   (prefix + L_i) * R = prefix*R + L_i*R.
        //
        // For p = 1: leftCanonical = L_0, so leftCanonical * rightCanonical
        //            = L_0 * rightCanonical — no peeling needed.
        // For p > 1: leftCanonical = (((L_0 + L_1) + L_2) + ... + L_{p-1}),
        //            we peel right-to-left.
        //
        // Track current form (an ExpressionPointer) and current proof
        // (leftTimesRight = currentForm). Start with currentForm = leftTimesRight,
        // currentProof = reflexivity.
        ExpressionPointer currentForm = leftTimesRight;
        ExpressionPointer currentProof = buildReflexivity(
            universeLevel, carrierType, currentForm);
        // Helper: given a left-associated sum of length n (kernels in
        // `summands`), return the left-associated kernel.
        auto leftAssoc = [&](const std::vector<ExpressionPointer>& v)
            -> ExpressionPointer {
            return assembleLeftAssociatedProduct(context.addName, v);
        };
        // We peel from the right: at each step, we have
        //   currentForm = (sum_of_first_i_terms) * rightCanonical
        //                  + (already-peeled tail summands)
        // The tail is a left-associated sum: (L_i*R) + (L_{i+1}*R) + ...
        // After all peels, currentForm becomes
        //   L_0 * R + L_1 * R + ... + L_{p-1} * R   (left-associated).
        if (leftSigned.size() == 1) {
            // No peeling needed for this phase.
        } else {
            // Walk i from p-1 down to 1; at each step, peel L_i out of
            // the leftmost factor.
            // Initial form of "leftFactor": leftCanonical (full).
            ExpressionPointer leftFactor = leftCanonical;
            for (size_t i = leftSigned.size(); i > 1; --i) {
                // leftFactor at this iteration = leftAssoc(L_0..L_{i-1}).
                // It has shape (smallerLeftFactor + L_{i-1}) by left-assoc.
                size_t lastIdx = i - 1;
                // smallerLeftFactor = leftAssoc(L_0..L_{i-2}).
                std::vector<ExpressionPointer> smallerKernels(
                    leftMonomialKernels.begin(),
                    leftMonomialKernels.begin()
                        + static_cast<long>(lastIdx));
                ExpressionPointer smallerLeftFactor;
                if (smallerKernels.size() == 1) {
                    smallerLeftFactor = smallerKernels[0];
                } else {
                    smallerLeftFactor = leftAssoc(smallerKernels);
                }
                ExpressionPointer Li = leftMonomialKernels[lastIdx];
                // distributivity_right(smallerLeftFactor, L_{lastIdx}, R)
                //   : (smallerLeftFactor + L_{lastIdx}) * R
                //     = smallerLeftFactor * R + L_{lastIdx} * R
                ExpressionPointer distRightCall = makeConstant(
                    axiomNames.distributivityRight);
                distRightCall = makeApplication(distRightCall,
                                                  smallerLeftFactor);
                distRightCall = makeApplication(distRightCall, Li);
                distRightCall = makeApplication(distRightCall,
                                                  rightCanonical);
                // The LHS of distRightCall:
                //   (smallerLeftFactor + L_{lastIdx}) * R = leftFactor * R
                // RHS: smallerLeftFactor * R + L_{lastIdx} * R.
                ExpressionPointer lhsExpanded = buildRingOp(
                    context.multiplyName, leftFactor, rightCanonical);
                ExpressionPointer rhsExpanded = buildRingOp(
                    context.addName,
                    buildRingOp(context.multiplyName, smallerLeftFactor,
                                  rightCanonical),
                    buildRingOp(context.multiplyName, Li, rightCanonical));
                // currentForm at this point has shape:
                //   leftFactor * R                         (if i == p)
                //   or (leftFactor * R) + tail              (if i < p)
                ExpressionPointer stepProof;
                ExpressionPointer newForm;
                if (i == leftSigned.size()) {
                    // currentForm == lhsExpanded.
                    stepProof = distRightCall;
                    newForm = rhsExpanded;
                } else {
                    // currentForm == lhsExpanded + tail.
                    // Build the tail kernel.
                    std::vector<ExpressionPointer> tailSummands;
                    for (size_t k = i; k < leftSigned.size(); ++k) {
                        tailSummands.push_back(buildRingOp(
                            context.multiplyName,
                            leftMonomialKernels[k], rightCanonical));
                    }
                    ExpressionPointer tailKernel;
                    if (tailSummands.size() == 1) {
                        tailKernel = tailSummands[0];
                    } else {
                        tailKernel = leftAssoc(tailSummands);
                    }
                    // Apply congruence with λz. z + tail.
                    ExpressionPointer tailLifted =
                        liftBoundVariables(tailKernel, 1, 0);
                    ExpressionPointer lambdaBody = buildRingOp(
                        context.addName, makeBoundVariable(0), tailLifted);
                    ExpressionPointer lambda = makeLambda(
                        "_ring_distR_z", carrierType, lambdaBody);
                    stepProof = buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        lhsExpanded, rhsExpanded, distRightCall);
                    newForm = buildRingOp(
                        context.addName, rhsExpanded, tailKernel);
                }
                // currentProof was: leftTimesRight = currentForm.
                // stepProof: currentForm = newForm.
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, newForm,
                    currentProof, stepProof);
                currentForm = newForm;
                leftFactor = smallerLeftFactor;
            }
            // After this loop currentForm has shape:
            //   ((L_0 * R) + (L_1 * R)) + ... + (L_{p-1} * R)
            // but possibly with a non-flat shape (the loop produced
            // a "rhsExpanded + tail" nested structure, not a flat left-
            // associated sum). Need to reassociate.
            //
            // Reassociate to left-associated form (treating L_i * R as
            // opaque atoms).
            std::vector<ExpressionPointer> phase1ATargetSummands;
            for (size_t k = 0; k < leftSigned.size(); ++k) {
                phase1ATargetSummands.push_back(buildRingOp(
                    context.multiplyName,
                    leftMonomialKernels[k], rightCanonical));
            }
            ExpressionPointer phase1ATargetKernel = leftAssoc(
                phase1ATargetSummands);
            if (!structurallyEqual(currentForm, phase1ATargetKernel)) {
                // Reassociate via add-AC.
                ExpressionPointer reassocProof = reassociateSumLeftProof(
                    currentForm, context, axiomNames);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, phase1ATargetKernel,
                    currentProof, reassocProof);
                currentForm = phase1ATargetKernel;
            }
        }
        // currentForm now equals the left-associated sum of (L_i * R)
        // for i=0..p-1, where R = rightCanonical.
        // Phase 1b: for each i, expand L_i * R into sum over j of L_i * R_j.
        // We do this one row at a time. After expanding row i, the
        // current form has shape:
        //   [already-expanded rows 0..i-1]   (flat sum of L_k * R_l)
        //     + [(L_i * R_0) + (L_i * R_1) + ... + (L_i * R_{q-1})]   (this row)
        //     + [unexpanded rows i+1..p-1]   (each as L_k * R)
        // All wrapped into a left-associated chain.
        //
        // For simplicity we expand all rows then reassociate, similar
        // to phase 1a but on the inner level.
        //
        // To expand L_i * (R_0 + ... + R_{q-1}) into a sum of L_i * R_j
        // via distributivity_left, we peel the rightmost R from the
        // sum (mirror of phase 1a):
        //   L_i * (smallerRSum + R_{q-1})
        //     = L_i * smallerRSum + L_i * R_{q-1}     via distributivity_left
        //
        // Result list of summands after both phases:
        std::vector<ExpressionPointer> phase1BAllSummands;
        for (size_t i = 0; i < leftSigned.size(); ++i) {
            for (size_t j = 0; j < rightSigned.size(); ++j) {
                phase1BAllSummands.push_back(buildRingOp(
                    context.multiplyName,
                    leftMonomialKernels[i],
                    rightMonomialKernels[j]));
            }
        }
        // We need to transform currentForm into the left-assoc of
        // phase1BAllSummands. Approach: walk each row and apply
        // distributivity_left + congruence to expand it in place.
        if (rightSigned.size() > 1) {
            // For each row i (in order), apply distributivity_left to
            // its (L_i * R) factor. We use congruence with a motive that
            // targets exactly position i in the left-associated sum.
            // To avoid the complexity of building a motive that
            // surgically modifies a position deep in a left-associated
            // sum, we use a per-row chain:
            //
            //   For row i: locate (L_i * R) somewhere in currentForm,
            //   replace it with the expansion (L_i*R_0 + ... + L_i*R_{q-1}).
            //   The replacement is an opaque-equal transformation —
            //   `congruenceOf(motive, proofOfL_iR=expansion)`.
            //
            // We'll handle this by recursively walking the current form
            // and emitting congruences as we go.
            // Implementation: build a helper that, given the row index
            // and a kernel-form representation, finds the unique
            // structural occurrence of (L_i * R) in the current form
            // and applies the expansion. We exploit the fact that we
            // KNOW the current form's structure exactly (it's the left-
            // assoc of all L_k * R), so we can target it precisely.
            //
            // Strategy: process rows left-to-right. After processing
            // rows 0..i-1, currentForm has shape:
            //   ((((expanded_0) + ... + expanded_{i-1}) + (L_i * R))
            //     + (L_{i+1} * R)) + ... + (L_{p-1} * R)
            // where each expanded_k is the left-assoc of L_k*R_0..L_k*R_{q-1}.
            //
            // To expand row i: locate (L_i * R) in the position
            // described above. Build a motive that wraps z at that
            // position. Apply congruence with proof: L_i * R = expanded_i.
            //
            // To build the proof L_i * R = expanded_i (where R = R_0 + R_1 + ... + R_{q-1}):
            // Apply distributivity_left repeatedly. Specifically:
            //   L_i * (smallerR + R_{q-1}) = L_i * smallerR + L_i * R_{q-1}
            // recurse on the left side. We'll do this in a small helper.
            for (size_t i = 0; i < leftSigned.size(); ++i) {
                // Build proof for the row expansion.
                ExpressionPointer Li = leftMonomialKernels[i];
                // Build "L_i * R_j" summands.
                std::vector<ExpressionPointer> rowSummands;
                for (size_t j = 0; j < rightSigned.size(); ++j) {
                    rowSummands.push_back(buildRingOp(
                        context.multiplyName, Li,
                        rightMonomialKernels[j]));
                }
                // Expansion: left-assoc of rowSummands.
                ExpressionPointer expandedRow;
                if (rowSummands.size() == 1) {
                    expandedRow = rowSummands[0];
                } else {
                    expandedRow = leftAssoc(rowSummands);
                }
                // Build proof Li * R = expandedRow.
                // Iterative peel from the right: at each step k
                // (k = q-1 down to 1), we expand Li * (smallerR + R_k).
                ExpressionPointer rowCurrent = buildRingOp(
                    context.multiplyName, Li, rightCanonical);
                ExpressionPointer rowProof = buildReflexivity(
                    universeLevel, carrierType, rowCurrent);
                if (rightSigned.size() > 1) {
                    ExpressionPointer rightFactor = rightCanonical;
                    for (size_t k = rightSigned.size(); k > 1; --k) {
                        size_t lastIdx = k - 1;
                        std::vector<ExpressionPointer> smallerRKernels(
                            rightMonomialKernels.begin(),
                            rightMonomialKernels.begin()
                                + static_cast<long>(lastIdx));
                        ExpressionPointer smallerR;
                        if (smallerRKernels.size() == 1) {
                            smallerR = smallerRKernels[0];
                        } else {
                            smallerR = leftAssoc(smallerRKernels);
                        }
                        ExpressionPointer Rk =
                            rightMonomialKernels[lastIdx];
                        // distributivity_left(Li, smallerR, Rk):
                        //   Li * (smallerR + Rk) = Li * smallerR + Li * Rk
                        ExpressionPointer distLeftCall = makeConstant(
                            axiomNames.distributivityLeft);
                        distLeftCall = makeApplication(distLeftCall, Li);
                        distLeftCall = makeApplication(distLeftCall,
                                                          smallerR);
                        distLeftCall = makeApplication(distLeftCall, Rk);
                        ExpressionPointer lhsExpanded = buildRingOp(
                            context.multiplyName, Li, rightFactor);
                        ExpressionPointer rhsExpanded = buildRingOp(
                            context.addName,
                            buildRingOp(context.multiplyName, Li,
                                          smallerR),
                            buildRingOp(context.multiplyName, Li, Rk));
                        ExpressionPointer stepProof;
                        ExpressionPointer newRowForm;
                        if (k == rightSigned.size()) {
                            stepProof = distLeftCall;
                            newRowForm = rhsExpanded;
                        } else {
                            // rowCurrent has shape lhsExpanded + tail.
                            std::vector<ExpressionPointer> tailSummands(
                                rowSummands.begin()
                                    + static_cast<long>(k),
                                rowSummands.end());
                            ExpressionPointer tailKernel;
                            if (tailSummands.size() == 1) {
                                tailKernel = tailSummands[0];
                            } else {
                                tailKernel = leftAssoc(tailSummands);
                            }
                            ExpressionPointer tailLifted =
                                liftBoundVariables(tailKernel, 1, 0);
                            ExpressionPointer lambdaBody = buildRingOp(
                                context.addName,
                                makeBoundVariable(0), tailLifted);
                            ExpressionPointer lambda = makeLambda(
                                "_ring_distL_z", carrierType, lambdaBody);
                            stepProof =
                                buildEqualityCongruenceSameCarrier(
                                    universeLevel, carrierType, lambda,
                                    lhsExpanded, rhsExpanded, distLeftCall);
                            newRowForm = buildRingOp(
                                context.addName, rhsExpanded, tailKernel);
                        }
                        rowProof = buildEqualityTransitivity(
                            universeLevel, carrierType,
                            buildRingOp(context.multiplyName, Li,
                                          rightCanonical),
                            rowCurrent, newRowForm,
                            rowProof, stepProof);
                        rowCurrent = newRowForm;
                        rightFactor = smallerR;
                    }
                    // Reassociate rowCurrent → expandedRow.
                    if (!structurallyEqual(rowCurrent, expandedRow)) {
                        ExpressionPointer reassocProof =
                            reassociateSumLeftProof(
                                rowCurrent, context, axiomNames);
                        rowProof = buildEqualityTransitivity(
                            universeLevel, carrierType,
                            buildRingOp(context.multiplyName, Li,
                                          rightCanonical),
                            rowCurrent, expandedRow,
                            rowProof, reassocProof);
                        rowCurrent = expandedRow;
                    }
                }
                // rowProof : Li * R = expandedRow.
                // Apply this rewrite in currentForm by building a
                // congruence. Position of (Li * R) in currentForm:
                // after processing rows 0..i-1, currentForm has the
                // shape described above. We'll build a motive lambda
                // tailored to that exact position.
                //
                // Concretely: the form is
                //   ((((expanded_0 + ... + expanded_{i-1}) + (L_i * R))
                //     + (L_{i+1} * R)) + ...) + (L_{p-1} * R)
                // We need a motive `λ z. (((expanded_0 + ... + expanded_{i-1}) + z) + (L_{i+1}*R)) + ... + (L_{p-1}*R)`.
                ExpressionPointer postExpansionPrefix;  // expanded rows
                std::vector<ExpressionPointer> postPrefixSummands;
                for (size_t k = 0; k < i; ++k) {
                    // expanded_k = left-assoc of (L_k * R_0..R_{q-1}).
                    std::vector<ExpressionPointer> kSummands;
                    for (size_t jj = 0; jj < rightSigned.size(); ++jj) {
                        kSummands.push_back(buildRingOp(
                            context.multiplyName,
                            leftMonomialKernels[k],
                            rightMonomialKernels[jj]));
                    }
                    ExpressionPointer kKernel;
                    if (kSummands.size() == 1) {
                        kKernel = kSummands[0];
                    } else {
                        kKernel = leftAssoc(kSummands);
                    }
                    postPrefixSummands.push_back(kKernel);
                }
                std::vector<ExpressionPointer> tailSummands;
                for (size_t k = i + 1; k < leftSigned.size(); ++k) {
                    tailSummands.push_back(buildRingOp(
                        context.multiplyName,
                        leftMonomialKernels[k], rightCanonical));
                }
                // Build lambda body. The pattern:
                //   ... ( ((postPrefixSums) + z) + tailSums[0] ) + tailSums[1] ...
                // First, build the "left part" = left-assoc of
                // postPrefixSums, then `+ z` to it.
                ExpressionPointer lambdaInner;
                {
                    // Build left part with proper bound-variable lift.
                    // postPrefixSums are kernel expressions from the
                    // OUTER context — they don't reference the lambda's
                    // bound variable, so we lift them by 1.
                    std::vector<ExpressionPointer> liftedPrefix;
                    for (const auto& s : postPrefixSummands) {
                        liftedPrefix.push_back(liftBoundVariables(s, 1, 0));
                    }
                    ExpressionPointer leftPart;
                    if (liftedPrefix.empty()) {
                        // No prefix; the body starts with z.
                        leftPart = makeBoundVariable(0);
                    } else {
                        if (liftedPrefix.size() == 1) {
                            leftPart = buildRingOp(
                                context.addName, liftedPrefix[0],
                                makeBoundVariable(0));
                        } else {
                            ExpressionPointer prefixKernel =
                                leftAssoc(liftedPrefix);
                            leftPart = buildRingOp(
                                context.addName, prefixKernel,
                                makeBoundVariable(0));
                        }
                    }
                    // Now extend with `+ tailSummands[0] + ... + tailSummands[last]`.
                    for (const auto& tk : tailSummands) {
                        ExpressionPointer tkLifted =
                            liftBoundVariables(tk, 1, 0);
                        leftPart = buildRingOp(
                            context.addName, leftPart, tkLifted);
                    }
                    lambdaInner = leftPart;
                }
                ExpressionPointer lambda = makeLambda(
                    "_ring_rowexp_z", carrierType, lambdaInner);
                // x = Li * R; y = expandedRow.
                ExpressionPointer xExpr = buildRingOp(
                    context.multiplyName, Li, rightCanonical);
                ExpressionPointer congrProof =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        xExpr, expandedRow, rowProof);
                // The proof: currentForm (which equals λ(xExpr) by
                // beta-reduction of the application of lambda to xExpr)
                // = λ(expandedRow).
                // Substitute into the lambda body to get the new form.
                auto substituteBV0 = [&](ExpressionPointer body,
                                            ExpressionPointer arg)
                    -> ExpressionPointer {
                    return substituteBoundVariable(body, arg, 0);
                };
                ExpressionPointer newForm = substituteBV0(
                    lambdaInner, expandedRow);
                // Sanity: currentForm should equal substituteBV0(lambdaInner, xExpr).
                ExpressionPointer expectedCurrent = substituteBV0(
                    lambdaInner, xExpr);
                if (!structurallyEqual(currentForm, expectedCurrent)) {
                    throwElaborate(
                        "`ring` (v2) phase1b: motive's xExpr-form does "
                        "not match currentForm (internal error)");
                }
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, newForm,
                    currentProof, congrProof);
                currentForm = newForm;
            }
            // After all rows, currentForm = nested expansion. Reassociate
            // to flat sum of all L_i * R_j.
            ExpressionPointer phase1BFlatKernel = leftAssoc(
                phase1BAllSummands);
            if (!structurallyEqual(currentForm, phase1BFlatKernel)) {
                ExpressionPointer reassocProof = reassociateSumLeftProof(
                    currentForm, context, axiomNames);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, phase1BFlatKernel,
                    currentProof, reassocProof);
                currentForm = phase1BFlatKernel;
            }
        }
        // currentForm is now the left-associated sum of all p*q
        // pairs L_i * R_j (in row-major order).
        // Phase 2: for each summand L_i * R_j, transform it into the
        // canonical monomial form for the merged-signature monomial.
        // The merged monomial sig is sort(L_i.sig ++ R_j.sig), and
        // its sign is L_i.sign * R_j.sign.
        //
        // L_i * R_j as a kernel is:
        //   * if both positive: leftProduct * rightProduct
        //   * if one negative: negate(positive_one) * positive_other
        //                       — needs multiply_negate_left/right
        //                       to push outside
        //   * if both negative: negate(...) * negate(...)
        //                       — needs both rules + negate_negate
        //
        // Then the factors of the resulting product need to be
        // re-associated and sorted (sort by hash) to canonical order.
        //
        // We rewrite each summand position-by-position via congruence.
        for (size_t i = 0; i < leftSigned.size(); ++i) {
            for (size_t j = 0; j < rightSigned.size(); ++j) {
                size_t flatIndex = i * rightSigned.size() + j;
                // The current summand at flatIndex is buildRingOp(*, Li, Rj).
                ExpressionPointer Li = leftMonomialKernels[i];
                ExpressionPointer Rj = rightMonomialKernels[j];
                ExpressionPointer summandKernel = buildRingOp(
                    context.multiplyName, Li, Rj);
                // Compute the target monomial:
                RingMonomialSignature mergedSig;
                mergedSig.reserve(leftSigned[i].signature.size()
                                    + rightSigned[j].signature.size());
                std::merge(leftSigned[i].signature.begin(),
                            leftSigned[i].signature.end(),
                            rightSigned[j].signature.begin(),
                            rightSigned[j].signature.end(),
                            std::back_inserter(mergedSig));
                int mergedSign = leftSigned[i].sign * rightSigned[j].sign;
                ExpressionPointer targetMonomial =
                    buildSignedMonomialKernel(
                        mergedSig, mergedSign, context);
                if (structurallyEqual(summandKernel, targetMonomial)) {
                    // No transformation needed.
                    continue;
                }
                // Build a proof: summandKernel = targetMonomial.
                ExpressionPointer summandProof = proveSignedProductEqualsMonomial(
                    Li, Rj,
                    leftSigned[i], rightSigned[j],
                    mergedSig, mergedSign,
                    targetMonomial, context, axiomNames);
                // Apply at position flatIndex in currentForm. We need a
                // motive that targets exactly that position in the flat
                // left-associated sum.
                ExpressionPointer congrProof =
                    rewriteFlatSummandAtPositionProof(
                        currentForm, flatIndex,
                        leftSigned.size() * rightSigned.size(),
                        summandKernel, targetMonomial,
                        summandProof, context);
                ExpressionPointer newCurrent =
                    rewriteFlatSummandAtPosition(
                        currentForm, flatIndex,
                        leftSigned.size() * rightSigned.size(),
                        targetMonomial, context);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, newCurrent,
                    currentProof, congrProof);
                currentForm = newCurrent;
            }
        }
        // currentForm is now a flat sum of canonical monomials in
        // row-major (L_i*R_j) order. Need to sort to canonical
        // std::map order.
        std::vector<ExpressionPointer> flatSummands;
        // Re-derive flatSummands from currentForm by flattening.
        flattenRingProduct(currentForm, context.addName, flatSummands);
        // Target order = canonical monomials in mergedPoly order.
        std::vector<SignedMonomial> mergedMonomials =
            polynomialToSignedMonomials(mergedPoly);
        std::vector<ExpressionPointer> sortedKernels;
        for (const auto& m : mergedMonomials) {
            sortedKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Apply sum-AC sort (sortSumLeftAssocProof handles ANY target permutation).
        ExpressionPointer sortProof = sortSumLeftAssocProof(
            flatSummands, sortedKernels, context, axiomNames);
        ExpressionPointer sortedKernel = assembleLeftAssociatedProduct(
            context.addName, sortedKernels);
        currentProof = buildEqualityTransitivity(
            universeLevel, carrierType,
            leftTimesRight, currentForm, sortedKernel,
            currentProof, sortProof);
        currentForm = sortedKernel;
        // Final check.
        if (!structurallyEqual(currentForm, mergedCanonical)) {
            throwElaborate(
                "`ring` (v2): proveMultiplyMerge final form does not "
                "match canonical(mergedPoly) (internal error)");
        }
        return currentProof;
    }

    // Substitute every BoundVariable with the given index in `body` by
    // `argument`. Indices below the target are decreased by 1 only when
    // the substitution makes a position pass through a binder (we don't
    // walk through binders here — there are none in our motives, which
    // are flat applications + constants + the single bound variable
    // we're substituting).
    //
    // For our use we just need a shallow substitution: replace
    // BoundVariable(0) with `argument`, treating the body as a kernel
    // expression that doesn't introduce any further binders.
    ExpressionPointer substituteBoundVariable(
        ExpressionPointer body, ExpressionPointer argument, int target) {
        if (auto* bv = std::get_if<BoundVariable>(&body->node)) {
            if (bv->deBruijnIndex == target) {
                return argument;
            }
            if (bv->deBruijnIndex > target) {
                return makeBoundVariable(bv->deBruijnIndex - 1);
            }
            return body;
        }
        if (auto* app = std::get_if<Application>(&body->node)) {
            return makeApplication(
                substituteBoundVariable(app->function, argument, target),
                substituteBoundVariable(app->argument, argument, target));
        }
        if (auto* lam = std::get_if<Lambda>(&body->node)) {
            // Walk under the binder.
            // Lift `argument` by 1 because the body inside the lambda
            // has one more binding.
            ExpressionPointer argLifted =
                liftBoundVariables(argument, 1, 0);
            return makeLambda(lam->displayHint,
                substituteBoundVariable(lam->domain, argument, target),
                substituteBoundVariable(lam->body, argLifted, target + 1));
        }
        if (auto* pi = std::get_if<Pi>(&body->node)) {
            ExpressionPointer argLifted =
                liftBoundVariables(argument, 1, 0);
            return makePi(pi->displayHint,
                substituteBoundVariable(pi->domain, argument, target),
                substituteBoundVariable(pi->codomain, argLifted, target + 1));
        }
        return body;
    }

    // Rewrite the summand at position `position` in a flat left-
    // associated sum of `totalCount` summands. Caller supplies the
    // current form, the proof that the summand at that position equals
    // `newSummand`, and we construct the resulting form's expression
    // and the congruence proof.
    //
    // For position `position` in a left-associated sum:
    //   sum = ((((s_0 + s_1) + s_2) + ...) + s_{n-1})
    // To target s_k for rewriting, we build the motive
    //   λ z. ((((s_0 + ... + s_{k-1}) + z) + s_{k+1}) + ...) + s_{n-1}.
    ExpressionPointer rewriteFlatSummandAtPosition(
        ExpressionPointer currentForm,
        size_t position, size_t totalCount,
        ExpressionPointer replacement,
        const RingV2Context& context) {
        std::vector<ExpressionPointer> summands;
        flattenRingProduct(currentForm, context.addName, summands);
        if (summands.size() != totalCount) {
            throwElaborate(
                "`ring` (v2): rewriteFlatSummandAtPosition: flatten "
                "count " + std::to_string(summands.size())
                + " != expected " + std::to_string(totalCount));
        }
        summands[position] = replacement;
        return assembleLeftAssociatedProduct(context.addName, summands);
    }

    ExpressionPointer rewriteFlatSummandAtPositionProof(
        ExpressionPointer currentForm,
        size_t position, size_t totalCount,
        ExpressionPointer oldSummand,
        ExpressionPointer newSummand,
        ExpressionPointer summandProof,
        const RingV2Context& context) {
        std::vector<ExpressionPointer> summands;
        flattenRingProduct(currentForm, context.addName, summands);
        if (summands.size() != totalCount) {
            throwElaborate(
                "`ring` (v2): rewriteFlatSummandAtPositionProof: flatten "
                "count " + std::to_string(summands.size())
                + " != expected " + std::to_string(totalCount));
        }
        // Build the motive lambda. The body has the form of the flat
        // sum with summands[position] replaced by BoundVariable(0).
        // Lift other summands by 1 to account for the new binder.
        std::vector<ExpressionPointer> bodySummands;
        for (size_t k = 0; k < summands.size(); ++k) {
            if (k == position) {
                bodySummands.push_back(makeBoundVariable(0));
            } else {
                bodySummands.push_back(liftBoundVariables(summands[k], 1, 0));
            }
        }
        ExpressionPointer body = assembleLeftAssociatedProduct(
            context.addName, bodySummands);
        ExpressionPointer lambda = makeLambda(
            "_ring_summand_z", context.carrierType, body);
        return buildEqualityCongruenceSameCarrier(
            context.carrierUniverseLevel, context.carrierType, lambda,
            oldSummand, newSummand, summandProof);
    }

    // Prove `Li * Rj = targetMonomial` where Li, Rj are signed-monomial
    // kernels and targetMonomial = canonical kernel of (sign(Li)*sign(Rj),
    // sort(Li.sig ++ Rj.sig)).
    //
    // Steps (depending on signs):
    //   (++): Li * Rj = leftProduct * rightProduct. Flatten + sort the
    //         combined factors. The merged sign is +, so the canonical
    //         is just the product with no negate wrapper.
    //   (+-): Li * (-Mj) = -(Li * Mj). Use multiply_negate_right. Then
    //         the inner Li * Mj is the same as (++) case but with
    //         positive Mj. So: rewrite Rj → -Mj using nothing (it IS
    //         -Mj), apply multiply_negate_right, then recurse.
    //   (-+): symmetric, multiply_negate_left.
    //   (--): (-Mi) * (-Mj) = -(-Mi * Mj) = Mi * Mj. Both rules + negate_negate.
    //
    // After sign-pushing the outer negate, we have ±(product_of_factors).
    // The inner product is leftFactors * rightFactors with shapes:
    //   leftFactors  = leftProduct  (a left-assoc product of Li.sig atoms)
    //   rightFactors = rightProduct (left-assoc of Rj.sig atoms)
    // Concatenating: leftProduct * rightProduct. Re-associate to flat,
    // then sort to match mergedSig. Wrap in negate if mergedSign == -1.
    ExpressionPointer proveSignedProductEqualsMonomial(
        ExpressionPointer Li, ExpressionPointer Rj,
        const SignedMonomial& leftMono, const SignedMonomial& rightMono,
        const RingMonomialSignature& /*mergedSig*/, int mergedSign,
        ExpressionPointer targetMonomial,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // The "positive" base monomial kernels (no negate wrapper):
        ExpressionPointer Mi = buildSignedMonomialKernel(
            leftMono.signature, +1, context);
        ExpressionPointer Mj = buildSignedMonomialKernel(
            rightMono.signature, +1, context);
        // Start: Li * Rj. Goal: targetMonomial.
        // Move outer negates inside step by step until we have
        // (Mi * Mj) wrapped in 0..2 negates. Each negate-push is a
        // multiply_negate_left/right rewrite. Two negates collapse via
        // negate_negate.
        ExpressionPointer currentForm = buildRingOp(
            context.multiplyName, Li, Rj);
        ExpressionPointer currentProof = buildReflexivity(
            universeLevel, carrierType, currentForm);
        ExpressionPointer startForm = currentForm;
        // Step S1: if Li is -Mi, push the outer negate of Li outside the
        // product: Li * Rj = (-Mi) * Rj = -(Mi * Rj) via
        // multiply_negate_left.
        if (leftMono.sign < 0) {
            demandAxiomName(axiomNames.multiplyNegateLeft,
                              "multiply_negate_left", context.carrierName);
            ExpressionPointer call = makeConstant(axiomNames.multiplyNegateLeft);
            call = makeApplication(call, Mi);
            call = makeApplication(call, Rj);
            // call : (-Mi) * Rj = -(Mi * Rj)
            ExpressionPointer newForm = buildRingNegate(
                context.negateName,
                buildRingOp(context.multiplyName, Mi, Rj));
            currentProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                startForm, currentForm, newForm,
                currentProof, call);
            currentForm = newForm;
        }
        // Step S2: if Rj is -Mj, push the negate around the product
        // outside as well.
        if (rightMono.sign < 0) {
            demandAxiomName(axiomNames.multiplyNegateRight,
                              "multiply_negate_right", context.carrierName);
            // Two cases: the current "product part" is either
            //   Mi * Rj    (if Li was positive)
            //   Mi * Rj inside a negate wrapper (if Li was negative).
            if (leftMono.sign > 0) {
                // currentForm == Mi * Rj. Apply multiply_negate_right(Mi, Mj):
                // Mi * (-Mj) = -(Mi * Mj).
                ExpressionPointer call = makeConstant(
                    axiomNames.multiplyNegateRight);
                call = makeApplication(call, Mi);
                call = makeApplication(call, Mj);
                ExpressionPointer newForm = buildRingNegate(
                    context.negateName,
                    buildRingOp(context.multiplyName, Mi, Mj));
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, call);
                currentForm = newForm;
            } else {
                // currentForm == -(Mi * Rj) where Rj == -Mj.
                // Use congruence λz. -z, with proof Mi * Rj = -(Mi * Mj)
                // via multiply_negate_right.
                ExpressionPointer call = makeConstant(
                    axiomNames.multiplyNegateRight);
                call = makeApplication(call, Mi);
                call = makeApplication(call, Mj);
                ExpressionPointer innerOld = buildRingOp(
                    context.multiplyName, Mi, Rj);
                ExpressionPointer innerNew = buildRingNegate(
                    context.negateName,
                    buildRingOp(context.multiplyName, Mi, Mj));
                ExpressionPointer lambdaBody = buildRingNegate(
                    context.negateName, makeBoundVariable(0));
                ExpressionPointer lambda = makeLambda(
                    "_ring_negouter_z", carrierType, lambdaBody);
                ExpressionPointer congr =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        innerOld, innerNew, call);
                // newForm = -(- (Mi * Mj))
                ExpressionPointer newForm = buildRingNegate(
                    context.negateName, innerNew);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, congr);
                currentForm = newForm;
                // Then collapse via negate_negate.
                demandAxiomName(axiomNames.negateNegate,
                                  "negate_negate", context.carrierName);
                ExpressionPointer nnCall = makeConstant(
                    axiomNames.negateNegate);
                nnCall = makeApplication(nnCall,
                                            buildRingOp(context.multiplyName,
                                                          Mi, Mj));
                // nnCall : -(-(Mi*Mj)) = Mi*Mj
                ExpressionPointer collapsedForm = buildRingOp(
                    context.multiplyName, Mi, Mj);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, collapsedForm,
                    currentProof, nnCall);
                currentForm = collapsedForm;
            }
        }
        // After steps S1/S2, currentForm has one of:
        //   Mi * Mj                  (mergedSign == +1)
        //   -(Mi * Mj)               (mergedSign == -1)
        // (The (--) case landed at Mi*Mj after the two pushes + negate_negate.)
        // Now sort the factors of the inner product.
        // Get the inner product expression.
        ExpressionPointer innerProductForm;
        bool wrappedInNegate;
        if (mergedSign > 0) {
            innerProductForm = currentForm;
            wrappedInNegate = false;
        } else {
            // currentForm = -(Mi * Mj)
            auto* outerApp =
                std::get_if<Application>(&currentForm->node);
            if (!outerApp) {
                throwElaborate(
                    "`ring` (v2): proveSignedProductEqualsMonomial: "
                    "negative branch has malformed shape");
            }
            innerProductForm = outerApp->argument;
            wrappedInNegate = true;
        }
        // Flatten the inner product and sort factors.
        std::vector<ExpressionPointer> innerFactors;
        if (!flattenRingProduct(innerProductForm, context.multiplyName,
                                   innerFactors)) {
            throwElaborate(
                "`ring` (v2): inner product not pure-multiply (internal)");
        }
        // The target product is built by buildCanonicalMonomial from
        // mergedSig and +1 sign. Use it to get the factor order we want.
        // (mergedSig is sort(Li.sig ++ Rj.sig).) Read off the canonical
        // factor list by flattening targetMonomial's "inner product" too.
        ExpressionPointer targetInner;
        if (mergedSign > 0) {
            targetInner = targetMonomial;
        } else {
            auto* outerApp =
                std::get_if<Application>(&targetMonomial->node);
            if (!outerApp) {
                throwElaborate(
                    "`ring` (v2): target signed monomial malformed");
            }
            targetInner = outerApp->argument;
        }
        std::vector<ExpressionPointer> targetFactors;
        if (!flattenRingProduct(targetInner, context.multiplyName,
                                   targetFactors)) {
            throwElaborate(
                "`ring` (v2): target inner product not pure-multiply");
        }
        if (innerFactors.size() != targetFactors.size()) {
            throwElaborate(
                "`ring` (v2): factor count mismatch in monomial merge "
                "(internal error)");
        }
        // Reassociate innerProductForm to left-associated.
        ExpressionPointer innerLeftAssoc =
            assembleLeftAssociatedProduct(
                context.multiplyName, innerFactors);
        ExpressionPointer innerReassocProof;
        if (structurallyEqual(innerProductForm, innerLeftAssoc)) {
            innerReassocProof = buildReflexivity(
                universeLevel, carrierType, innerProductForm);
        } else {
            innerReassocProof = reassociateMultiplyLeftProof(
                innerProductForm, context, axiomNames);
        }
        // Sort innerFactors to target order.
        ExpressionPointer innerSortProof = sortMultiplyLeftAssocProof(
            innerFactors, targetFactors, context, axiomNames);
        ExpressionPointer innerSortedKernel = assembleLeftAssociatedProduct(
            context.multiplyName, targetFactors);
        ExpressionPointer innerChain = buildEqualityTransitivity(
            universeLevel, carrierType,
            innerProductForm, innerLeftAssoc, innerSortedKernel,
            innerReassocProof, innerSortProof);
        // Now innerChain : innerProductForm = innerSortedKernel.
        // If wrappedInNegate: apply congruence with λz. -z.
        ExpressionPointer outerChain;
        ExpressionPointer outerNewForm;
        if (wrappedInNegate) {
            ExpressionPointer lambdaBody = buildRingNegate(
                context.negateName, makeBoundVariable(0));
            ExpressionPointer lambda = makeLambda(
                "_ring_finalneg_z", carrierType, lambdaBody);
            outerChain = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambda,
                innerProductForm, innerSortedKernel, innerChain);
            outerNewForm = buildRingNegate(
                context.negateName, innerSortedKernel);
        } else {
            outerChain = innerChain;
            outerNewForm = innerSortedKernel;
        }
        currentProof = buildEqualityTransitivity(
            universeLevel, carrierType,
            startForm, currentForm, outerNewForm,
            currentProof, outerChain);
        currentForm = outerNewForm;
        if (!structurallyEqual(currentForm, targetMonomial)) {
            throwElaborate(
                "`ring` (v2): signed-product merge ended with mismatch "
                "(internal error)");
        }
        return currentProof;
    }

    // ----------------------------------------------------------------
    // proveNegateMerge: prove
    //   negate(canonical(innerPoly)) = canonical(-innerPoly)
    // ----------------------------------------------------------------
    //
    // Strategy:
    //   1. Push the outer negate through every `+` via negate_add.
    //   2. For each summand: if it was a positive monomial M, negate(M)
    //      is the canonical form of -M; if it was a negative monomial
    //      -M = negate(M), negate(negate(M)) collapses to M via
    //      negate_negate.
    //   3. Re-sort to match canonical(-innerPoly) (signatures are
    //      unchanged by sign flip, so the order is the same).
    //
    // Edge case: innerPoly empty → negate(zero) which we don't support.
    ExpressionPointer proveNegateMerge(
        const RingPolynomial& innerPoly,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        if (innerPoly.empty()) {
            throwElaborate(
                "`ring` (v2): negation of zero polynomial requires "
                "`negate_zero` which is not in scope");
        }
        ExpressionPointer innerCanonical =
            buildCanonicalPolynomial(innerPoly, context);
        RingPolynomial negatedPoly = innerPoly;
        ringPolynomialNegate(negatedPoly);
        ExpressionPointer negatedCanonical =
            buildCanonicalPolynomial(negatedPoly, context);
        ExpressionPointer startForm = buildRingNegate(
            context.negateName, innerCanonical);
        std::vector<SignedMonomial> innerSigned =
            polynomialToSignedMonomials(innerPoly);
        std::vector<ExpressionPointer> innerKernels;
        for (const auto& m : innerSigned) {
            innerKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Phase 1: push outer negate inward through all `+`.
        // After phase 1: form = negate(s_0) + negate(s_1) + ... + negate(s_{k-1})
        //                  (left-associated)
        // Special case: k == 1, no `+` to push through.
        ExpressionPointer currentForm = startForm;
        ExpressionPointer currentProof = buildReflexivity(
            universeLevel, carrierType, currentForm);
        if (innerSigned.size() > 1) {
            demandAxiomName(axiomNames.negateAdd, "negate_add",
                              context.carrierName);
            // Build running prefixes: prefix[i] = s_0 + ... + s_i for
            // i = 0..k-1. prefix[k-1] = innerCanonical.
            std::vector<ExpressionPointer> runningPrefix;
            runningPrefix.push_back(innerKernels[0]);
            for (size_t i = 1; i < innerSigned.size(); ++i) {
                runningPrefix.push_back(buildRingOp(
                    context.addName, runningPrefix[i - 1], innerKernels[i]));
            }
            // Walk i from k-1 down to 1: push negate through the
            // outermost `+` of `negate(prefix[i])`.
            //
            // At step i, currentForm has the shape:
            //   negate(prefix[i]) + negate(s_{i+1}) + ... + negate(s_{k-1})
            //                                       (left-associated)
            // (For i == k-1, it's just negate(prefix[k-1]) = negate(innerCanonical).)
            //
            // Apply negate_add(prefix[i-1], s_i) :
            //   negate(prefix[i-1] + s_i) = negate(prefix[i-1]) + negate(s_i)
            // i.e. negate(prefix[i]) = negate(prefix[i-1]) + negate(s_i).
            // Lift via congruence with λz. z + tail.
            for (size_t i = innerSigned.size(); i > 1; --i) {
                size_t idx = i - 1;  // index of s_i in innerKernels
                ExpressionPointer subjectPrefix = runningPrefix[idx - 1];
                ExpressionPointer subjectSi = innerKernels[idx];
                ExpressionPointer negAddCall = makeConstant(
                    axiomNames.negateAdd);
                negAddCall = makeApplication(negAddCall, subjectPrefix);
                negAddCall = makeApplication(negAddCall, subjectSi);
                // negAddCall has type
                //   negate(prefix[idx-1] + s_idx) = negate(prefix[idx-1]) + negate(s_idx)
                ExpressionPointer xExpr = buildRingNegate(
                    context.negateName, runningPrefix[idx]);
                ExpressionPointer yExpr = buildRingOp(
                    context.addName,
                    buildRingNegate(context.negateName, runningPrefix[idx - 1]),
                    buildRingNegate(context.negateName, innerKernels[idx]));
                // Tail (already-pushed summands): negate(s_{idx+1}) + ... + negate(s_{k-1})
                std::vector<ExpressionPointer> tail;
                for (size_t j = idx + 1; j < innerSigned.size(); ++j) {
                    tail.push_back(buildRingNegate(
                        context.negateName, innerKernels[j]));
                }
                ExpressionPointer stepProof;
                ExpressionPointer newForm;
                if (tail.empty()) {
                    stepProof = negAddCall;
                    newForm = yExpr;
                } else {
                    ExpressionPointer tailKernel;
                    if (tail.size() == 1) {
                        tailKernel = tail[0];
                    } else {
                        tailKernel = assembleLeftAssociatedProduct(
                            context.addName, tail);
                    }
                    ExpressionPointer tailLifted = liftBoundVariables(
                        tailKernel, 1, 0);
                    ExpressionPointer lambdaBody = buildRingOp(
                        context.addName, makeBoundVariable(0), tailLifted);
                    ExpressionPointer lambda = makeLambda(
                        "_ring_negpush_z", carrierType, lambdaBody);
                    stepProof = buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        xExpr, yExpr, negAddCall);
                    newForm = buildRingOp(
                        context.addName, yExpr, tailKernel);
                }
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, stepProof);
                currentForm = newForm;
            }
            // Reassociate currentForm to flat left-associated sum of
            // negate(innerKernels[i]) for i=0..k-1.
            std::vector<ExpressionPointer> flatNeg;
            for (const auto& ik : innerKernels) {
                flatNeg.push_back(buildRingNegate(context.negateName, ik));
            }
            ExpressionPointer flatNegLeftAssoc = assembleLeftAssociatedProduct(
                context.addName, flatNeg);
            if (!structurallyEqual(currentForm, flatNegLeftAssoc)) {
                ExpressionPointer reassoc = reassociateSumLeftProof(
                    currentForm, context, axiomNames);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, flatNegLeftAssoc,
                    currentProof, reassoc);
                currentForm = flatNegLeftAssoc;
            }
        } else {
            // k == 1; currentForm == negate(innerKernels[0]) already.
            // Continue.
        }
        // Phase 2: simplify each summand. innerKernels[i] is either:
        //   * positive monomial M (sign = +1): negate(M) is canonical
        //     form of -M. No further work.
        //   * negative monomial -M = negate(M) (sign = -1, the kernel
        //     starts with `negate`). Then negate(negate(M)) = M via
        //     negate_negate.
        for (size_t i = 0; i < innerSigned.size(); ++i) {
            if (innerSigned[i].sign > 0) continue;
            demandAxiomName(axiomNames.negateNegate, "negate_negate",
                              context.carrierName);
            // The kernel innerKernels[i] is `negate(M_pos)` where M_pos
            // is the positive form. So negate(negate(M_pos)) → M_pos.
            ExpressionPointer M_pos = buildSignedMonomialKernel(
                innerSigned[i].signature, +1, context);
            ExpressionPointer oldSummand = buildRingNegate(
                context.negateName, innerKernels[i]);
            ExpressionPointer newSummand = M_pos;
            // The proof: negate(negate(M_pos)) = M_pos via negate_negate(M_pos).
            ExpressionPointer nnCall = makeConstant(axiomNames.negateNegate);
            nnCall = makeApplication(nnCall, M_pos);
            // Apply at position i in the flat sum.
            if (innerSigned.size() == 1) {
                // currentForm == oldSummand. Direct.
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newSummand,
                    currentProof, nnCall);
                currentForm = newSummand;
            } else {
                ExpressionPointer congrProof =
                    rewriteFlatSummandAtPositionProof(
                        currentForm, i, innerSigned.size(),
                        oldSummand, newSummand, nnCall, context);
                ExpressionPointer newCurrent =
                    rewriteFlatSummandAtPosition(
                        currentForm, i, innerSigned.size(),
                        newSummand, context);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newCurrent,
                    currentProof, congrProof);
                currentForm = newCurrent;
            }
        }
        // Now each summand is the canonical signed form of the
        // sign-flipped monomial — directly the kernel of -innerPoly's
        // monomials, in the same signature order.
        if (!structurallyEqual(currentForm, negatedCanonical)) {
            throwElaborate(
                "`ring` (v2): proveNegateMerge final form mismatched "
                "negated canonical (internal error)");
        }
        return currentProof;
    }

    // =====================================================================
    // Mod-(2^64 - 59) value fingerprint
    //
    // Diagnostic used by `ring` / `field` when symbolic decision fails:
    // evaluate both sides as elements of GF(p) for p = 2^64 - 59, with
    // each "opaque atom" replaced by its 64-bit subtree hash. If the
    // values disagree, the identity is (with overwhelming probability)
    // not a polynomial / field identity at all — the user's math is
    // wrong, not the tactic's. If the values agree, the goal is almost
    // certainly true and the symbolic failure points at a tactic
    // limitation (or a missing hypothesis).
    //
    // False-positive rate (agreeing on an unequal identity) is bounded
    // by Schwartz-Zippel: roughly `degree / p`, well under 2^-50 for
    // any sensible goal. False negatives (disagreeing on an equal
    // identity) require a 64-bit hash collision and are equally rare.
    //
    // Division by zero in the evaluator (a denominator's fingerprint
    // happens to be 0) returns nullopt and we say so clearly rather
    // than misleading the user with a false claim.
    // =====================================================================

    static constexpr uint64_t kFingerprintModulus =
        18446744073709551557ull;  // 2^64 - 59 (prime)

    uint64_t fingerprintAdd(uint64_t leftValue, uint64_t rightValue) const {
        // Both inputs are < p < 2^64, so sum fits in unsigned 64 with
        // at most one wraparound. Reduce mod p with a single conditional.
        uint64_t sum = leftValue + rightValue;
        // Overflow OR sum >= p both want reduction by p.
        if (sum < leftValue || sum >= kFingerprintModulus) {
            sum -= kFingerprintModulus;
        }
        return sum;
    }

    uint64_t fingerprintSubtract(
        uint64_t leftValue, uint64_t rightValue) const {
        return leftValue >= rightValue
            ? leftValue - rightValue
            : leftValue + (kFingerprintModulus - rightValue);
    }

    uint64_t fingerprintNegate(uint64_t value) const {
        return value == 0 ? 0 : kFingerprintModulus - value;
    }

    uint64_t fingerprintMultiply(
        uint64_t leftValue, uint64_t rightValue) const {
        // 64-bit × 64-bit needs 128 bits; rely on the compiler's
        // __int128 (clang / gcc on every platform this project targets).
        return (uint64_t)(((__uint128_t)leftValue
                            * (__uint128_t)rightValue)
                           % (__uint128_t)kFingerprintModulus);
    }

    uint64_t fingerprintModularPower(
        uint64_t base, uint64_t exponent) const {
        uint64_t result = 1;
        uint64_t current = base % kFingerprintModulus;
        while (exponent > 0) {
            if (exponent & 1ull) {
                result = fingerprintMultiply(result, current);
            }
            current = fingerprintMultiply(current, current);
            exponent >>= 1;
        }
        return result;
    }

    // Modular inverse via Fermat's little theorem: a^(p-2) mod p.
    // Returns nullopt iff a == 0 (no inverse, division by zero).
    std::optional<uint64_t> fingerprintModularInverse(uint64_t value) const {
        if (value % kFingerprintModulus == 0) return std::nullopt;
        return fingerprintModularPower(value, kFingerprintModulus - 2);
    }

    // Recursively evaluate an expression as an element of GF(p), with
    // opaque atoms replaced by their cached subtree hash. Returns
    // nullopt on division by zero (a `<C>.reciprocal_function` applied
    // to something whose fingerprint is 0).
    std::optional<uint64_t> evaluateFingerprint(
        ExpressionPointer expression,
        const std::string& carrierName) const {
        const std::string addName       = carrierName + ".add";
        const std::string subtractName  = carrierName + ".subtract";
        const std::string multiplyName  = carrierName + ".multiply";
        const std::string negateName    = carrierName + ".negate";
        const std::string zeroName      = carrierName + ".zero";
        const std::string oneName       = carrierName + ".one";
        const std::string reciprocalName
            = carrierName + ".reciprocal_function";
        // Constants.
        if (auto* head = std::get_if<Constant>(&expression->node)) {
            if (head->name == zeroName) return uint64_t{0};
            if (head->name == oneName) return uint64_t{1};
        }
        // Binary operators (peel two Application layers).
        if (auto* outer = std::get_if<Application>(&expression->node)) {
            if (auto* inner =
                    std::get_if<Application>(&outer->function->node)) {
                if (auto* head =
                        std::get_if<Constant>(&inner->function->node)) {
                    if (head->name == addName
                        || head->name == subtractName
                        || head->name == multiplyName) {
                        auto leftValue = evaluateFingerprint(
                            inner->argument, carrierName);
                        auto rightValue = evaluateFingerprint(
                            outer->argument, carrierName);
                        if (!leftValue || !rightValue) return std::nullopt;
                        if (head->name == addName) {
                            return fingerprintAdd(*leftValue, *rightValue);
                        }
                        if (head->name == subtractName) {
                            return fingerprintSubtract(
                                *leftValue, *rightValue);
                        }
                        return fingerprintMultiply(*leftValue, *rightValue);
                    }
                }
            }
            // Unary operators (one Application layer).
            if (auto* head =
                    std::get_if<Constant>(&outer->function->node)) {
                if (head->name == negateName) {
                    auto value = evaluateFingerprint(
                        outer->argument, carrierName);
                    if (!value) return std::nullopt;
                    return fingerprintNegate(*value);
                }
                if (head->name == reciprocalName) {
                    auto value = evaluateFingerprint(
                        outer->argument, carrierName);
                    if (!value) return std::nullopt;
                    return fingerprintModularInverse(*value);
                }
            }
        }
        // Otherwise: opaque atom. Use the cached subtree hash mod p.
        return expression->hash % kFingerprintModulus;
    }

    // Build the "(fingerprint mod (2^64 - 59): …)" diagnostic suffix
    // to append onto a ring/field failure. Always returns a string —
    // even when the evaluator gives up, the user learns something.
    std::string buildFingerprintDiagnostic(
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        const std::string& carrierName) const {
        auto leftValue =
            evaluateFingerprint(leftEndpoint, carrierName);
        auto rightValue =
            evaluateFingerprint(rightEndpoint, carrierName);
        if (!leftValue || !rightValue) {
            return "\n(fingerprint mod (2^64 - 59): division by zero "
                   "during evaluation — either a denominator that "
                   "needs a nonzero hypothesis, or a 1-in-2^64 hash "
                   "collision; can't diagnose either way)";
        }
        if (*leftValue == *rightValue) {
            return "\n(fingerprint mod (2^64 - 59): LHS = RHS = "
                 + std::to_string(*leftValue)
                 + " — the identity is almost certainly true; this "
                   "looks like a tactic limitation, not a real "
                   "mathematical mismatch)";
        }
        return "\n(fingerprint mod (2^64 - 59): LHS = "
             + std::to_string(*leftValue) + ", RHS = "
             + std::to_string(*rightValue)
             + " — the identity is FALSE as a polynomial / field "
               "identity; the goal as stated is not provable)";
    }

    // v2 of the ring tactic. Called as a fallback when v1 (pure-AC)
    // can't close the goal. Returns the proof on success; throws
    // otherwise. `expectedType` is the equality goal.
    ExpressionPointer elaborateRingV2(
        const std::vector<LocalBinder>& /*localBinders*/,
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        ExpressionPointer carrierType,
        LevelPointer carrierUniverseLevel,
        const std::string& carrierName,
        int line) {
        RingV2Context context;
        context.carrierName = carrierName;
        context.carrierType = carrierType;
        context.carrierUniverseLevel = carrierUniverseLevel;
        context.addName       = carrierName + ".add";
        context.multiplyName  = carrierName + ".multiply";
        context.negateName    = carrierName + ".negate";
        context.subtractName  = carrierName + ".subtract";
        context.zeroName      = carrierName + ".zero";
        context.oneName       = carrierName + ".one";
        // Sanity-check the carrier supports the v2 vocabulary. We only
        // require add + multiply at the moment — zero, one, and negate
        // are optional (a goal that doesn't mention them won't need
        // them).
        if (environment_.lookup(context.addName) == nullptr
            || environment_.lookup(context.multiplyName) == nullptr) {
            throwElaborate(
                "`ring` (v2): carrier `" + carrierName
                + "` does not have both `.add` and `.multiply` in scope");
        }
        RingPolynomial leftPolynomial =
            normaliseToRingPolynomial(leftEndpoint, context);
        RingPolynomial rightPolynomial =
            normaliseToRingPolynomial(rightEndpoint, context);
        if (!ringPolynomialsAgree(leftPolynomial, rightPolynomial)) {
            throwElaborate(
                "`ring`: the two sides do not have equal polynomial "
                "canonical forms over `" + carrierName + "` — they "
                "are not equal as commutative-ring expressions"
                + buildFingerprintDiagnostic(
                      leftEndpoint, rightEndpoint, carrierName));
        }
        // Coefficient guard: v2's proof emitter only supports
        // coefficients in {-1, 0, +1}. Drop into a clear error if a
        // larger coefficient survives (e.g., `a + a` collected to 2·a).
        for (const auto& entry : leftPolynomial) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`ring` (v2): the canonical form has a monomial "
                    "with coefficient " + std::to_string(entry.second)
                    + " — v2 only handles coefficients in {-1, +1} for "
                    "now (collected like-terms with larger multipliers "
                    "are a follow-up)"
                    + buildFingerprintDiagnostic(
                          leftEndpoint, rightEndpoint, carrierName));
            }
        }
        // Resolve carrier-specific axiom names. Names that aren't
        // needed for this particular goal are allowed to remain
        // unresolved; the merge helpers `demandAxiomName` only what
        // they actually use.
        RingV2AxiomNames axiomNames =
            resolveRingV2AxiomNames(carrierName);
        // We always need add/multiply assoc and commute (used by
        // every non-trivial merge step).
        demandAxiomName(axiomNames.addAssociative,
                          "add_associative", carrierName);
        demandAxiomName(axiomNames.addCommutative,
                          "add_commutative", carrierName);
        demandAxiomName(axiomNames.multiplyAssociative,
                          "multiply_associative", carrierName);
        demandAxiomName(axiomNames.multiplyCommutative,
                          "multiply_commutative", carrierName);
        // Build per-side proofs that each endpoint equals canonical.
        RingPolynomial leftPolyOut, rightPolyOut;
        ExpressionPointer leftProof = proveEqualsCanonical(
            leftEndpoint, context, axiomNames, leftPolyOut);
        ExpressionPointer rightProof = proveEqualsCanonical(
            rightEndpoint, context, axiomNames, rightPolyOut);
        ExpressionPointer canonicalKernel =
            buildCanonicalPolynomial(leftPolynomial, context);
        // canonicalKernel built from leftPolynomial — equal to the
        // one produced from rightPolynomial since the polynomials
        // agree (we just checked).
        // rightProof : rightEndpoint = canonicalKernel; flip via sym.
        ExpressionPointer rightProofSymm = buildEqualitySymmetry(
            carrierUniverseLevel, carrierType,
            rightEndpoint, canonicalKernel, std::move(rightProof));
        ExpressionPointer finalProof = buildEqualityTransitivity(
            carrierUniverseLevel, carrierType,
            leftEndpoint, canonicalKernel, rightEndpoint,
            std::move(leftProof), std::move(rightProofSymm));
        (void)line;
        return finalProof;
    }

    // =====================================================================
    // `field(h1, h2, ...)` — extends ring v2 with the side relation
    // `t_i * reciprocal_function(t_i) = 1` for each user-supplied
    // hypothesis `h_i : ¬(t_i = Rational.zero)`.
    //
    // Strategy: normalise both sides via ring v2 treating
    // `reciprocal_function(t_i)` and `t_i` as opaque atoms. In each
    // monomial of the canonical polynomial, count matched (t_i, r_i)
    // pairs and contract them (each contraction drops one t_i and one
    // r_i from the monomial's factor signature). After contraction the
    // polynomials of both sides should agree; if not, the goal is not a
    // field identity (or the user supplied insufficient hypotheses).
    //
    // The proof is built as a five-segment chain:
    //
    //   LHS = ring_canonical(LHS)
    //       = field_canonical(LHS)         -- via per-monomial contraction
    //       = field_canonical(RHS)         -- reflexivity (literally equal)
    //       = ring_canonical(RHS)          -- symmetric of contraction
    //       = RHS
    //
    // Each per-monomial contraction proof rearranges the monomial's
    // factor list via ring v1 AC machinery, then applies
    // `reciprocal_function_multiplies` plus `multiply_one` to remove
    // each (t_i, r_i) pair from the tail.
    // =====================================================================

    // A registered (t_i, r_i) pair from the user's nonzero hypotheses.
    struct FieldReciprocalPair {
        ExpressionPointer baseAtom;        // t_i kernel expression
        ExpressionPointer reciprocalAtom;  // reciprocal_function(t_i)
        ExpressionPointer multipliesProof; // proof : t_i * reciprocal_function(t_i) = 1
        uint64_t baseHash;
        uint64_t reciprocalHash;
    };

    // Contract a sorted monomial signature using the supplied pairs.
    // Returns the new signature with up to `min(#t, #r)` of each pair
    // removed. Side-effect: writes the number of pairs cancelled per
    // pair index into `pairsRemovedOut`.
    RingMonomialSignature contractMonomialSignature(
        const RingMonomialSignature& signature,
        const std::vector<FieldReciprocalPair>& pairs,
        std::vector<int>& pairsRemovedOut) {
        // Count occurrences of each atom hash in the signature.
        std::unordered_map<uint64_t, int> counts;
        for (uint64_t hash : signature) ++counts[hash];
        pairsRemovedOut.assign(pairs.size(), 0);
        // For each pair, contract.
        for (size_t i = 0; i < pairs.size(); ++i) {
            int baseCount = counts[pairs[i].baseHash];
            int reciprocalCount = counts[pairs[i].reciprocalHash];
            int toRemove = std::min(baseCount, reciprocalCount);
            if (toRemove > 0) {
                counts[pairs[i].baseHash] -= toRemove;
                counts[pairs[i].reciprocalHash] -= toRemove;
                pairsRemovedOut[i] = toRemove;
            }
        }
        // Rebuild signature from counts. Preserve the order of distinct
        // hashes from the original signature (deduplicating).
        RingMonomialSignature result;
        result.reserve(signature.size());
        std::unordered_map<uint64_t, int> emitted;
        for (uint64_t hash : signature) {
            int targetCount = counts[hash];
            int& alreadyEmitted = emitted[hash];
            if (alreadyEmitted < targetCount) {
                result.push_back(hash);
                ++alreadyEmitted;
            }
        }
        // The signature must remain sorted (since `RingMonomialSignature`
        // is sorted by hash). The original signature was sorted; rebuild
        // by walking sorted-hash to count.
        std::sort(result.begin(), result.end());
        return result;
    }

    // Build a polynomial from a `ring_canonical_polynomial` by applying
    // contractions monomial-by-monomial. Aggregates like terms (same
    // signature) by summing coefficients. Out-of-band: the per-monomial
    // contraction record (signature → list-of-pair-removals) is filled
    // in `contractionRecords` for the proof emitter.
    struct FieldMonomialContraction {
        RingMonomialSignature originalSignature;
        int originalCoefficient;
        RingMonomialSignature contractedSignature;
        std::vector<int> pairsRemoved;  // by pair index
    };
    RingPolynomial buildContractedPolynomial(
        const RingPolynomial& original,
        const std::vector<FieldReciprocalPair>& pairs,
        std::vector<FieldMonomialContraction>& contractionRecords) {
        RingPolynomial contracted;
        contractionRecords.clear();
        for (const auto& entry : original) {
            std::vector<int> pairsRemoved;
            RingMonomialSignature newSig =
                contractMonomialSignature(entry.first, pairs, pairsRemoved);
            contracted[newSig] += entry.second;
            contractionRecords.push_back({
                entry.first, entry.second,
                newSig, std::move(pairsRemoved)});
        }
        ringPolynomialCompact(contracted);
        return contracted;
    }

    // Build a proof
    //   (factor_0 * ... * factor_{n-1})
    //     = (factor'_0 * ... * factor'_{n-k-1})
    // where the right side is the left side with the indicated
    // (baseAtom, reciprocalAtom) pairs removed.  `factorList` is the
    // monomial's full factor list (in canonical order, repeated per
    // multiplicity).  `pairs` is the registry; `pairsRemoved[i]`
    // indicates how many copies of pair i should be removed.
    //
    // Strategy:
    //   1. Compute the surviving factor list by removing pair members
    //      from the back to front (this matches the canonical iteration
    //      order, which is hash-sorted).
    //   2. Build the "rearranged" factor list = survivingFactors ++
    //      [t_1, r_1, t_1, r_1, ...] (one (t, r) pair per cancellation).
    //   3. Prove `factorList-product = rearranged-product` via
    //      `proveProductEqualsSorted` (ring v1 AC, ANY permutation).
    //   4. Cancel pairs from the tail: each step uses
    //        ((prefix * t) * r) = prefix * (t * r)     (multiply_associative)
    //        prefix * (t * r) = prefix * 1             (congr + multiplies_proof)
    //        prefix * 1 = prefix                       (multiply_one)
    //   5. Repeat until all pairs are cancelled.
    //
    // Returns the proof.  Requires factorList.size() > 0.
    ExpressionPointer buildFactorContractionProof(
        const std::vector<ExpressionPointer>& factorList,
        const std::vector<FieldReciprocalPair>& pairs,
        const std::vector<int>& pairsRemoved,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        const std::string& multiplyName = context.multiplyName;
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        if (factorList.empty()) {
            throwElaborate(
                "`field`: factor list empty in contraction proof "
                "(internal error)");
        }
        // Step 1: build surviving factor list.
        //
        // Remove instances of (t_i, r_i) from factorList — we remove
        // pairsRemoved[i] copies of t_i and pairsRemoved[i] copies of
        // r_i. Use a multiset count.
        std::vector<bool> keep(factorList.size(), true);
        std::vector<size_t> removedTIndices;       // indices in factorList of removed t_i's
        std::vector<size_t> removedRIndices;       // indices in factorList of removed r_i's
        std::vector<size_t> pairIndexForRemovedT;  // pair index per removed t (parallel to removedTIndices)
        for (size_t pi = 0; pi < pairs.size(); ++pi) {
            int toRemove = pairsRemoved[pi];
            if (toRemove <= 0) continue;
            int removed = 0;
            for (size_t fi = 0; fi < factorList.size() && removed < toRemove; ++fi) {
                if (!keep[fi]) continue;
                if (factorList[fi]->hash == pairs[pi].baseHash) {
                    keep[fi] = false;
                    removedTIndices.push_back(fi);
                    pairIndexForRemovedT.push_back(pi);
                    ++removed;
                }
            }
            if (removed < toRemove) {
                throwElaborate(
                    "`field`: requested removal of more `t` copies than "
                    "present (internal error)");
            }
            removed = 0;
            for (size_t fi = 0; fi < factorList.size() && removed < toRemove; ++fi) {
                if (!keep[fi]) continue;
                if (factorList[fi]->hash == pairs[pi].reciprocalHash) {
                    keep[fi] = false;
                    removedRIndices.push_back(fi);
                    ++removed;
                }
            }
            if (removed < toRemove) {
                throwElaborate(
                    "`field`: requested removal of more `r` copies than "
                    "present (internal error)");
            }
        }
        // Build the surviving factor list and the rearranged list.
        std::vector<ExpressionPointer> survivors;
        for (size_t fi = 0; fi < factorList.size(); ++fi) {
            if (keep[fi]) survivors.push_back(factorList[fi]);
        }
        // The rearranged list: survivors first, then for each removed
        // pair the (t, r) pair appended.
        std::vector<ExpressionPointer> rearranged = survivors;
        // Walk removedTIndices in order; each corresponds to a pair.
        for (size_t k = 0; k < removedTIndices.size(); ++k) {
            size_t pi = pairIndexForRemovedT[k];
            rearranged.push_back(pairs[pi].baseAtom);
            rearranged.push_back(pairs[pi].reciprocalAtom);
        }
        if (rearranged.size() != factorList.size()) {
            throwElaborate(
                "`field`: rearranged factor count mismatch (internal error)");
        }
        // Step 3: prove factorList-product = rearranged-product.
        RingAxiomNames multiplyAxioms{
            multiplyName, axiomNames.multiplyAssociative,
            axiomNames.multiplyCommutative};
        ExpressionPointer originalProduct =
            assembleLeftAssociatedProduct(multiplyName, factorList);
        ExpressionPointer rearrangedProduct =
            assembleLeftAssociatedProduct(multiplyName, rearranged);
        ExpressionPointer reassocProof;
        if (factorList.size() == 1) {
            // Single factor, no cancellations should be possible
            // (a single factor can be either t or r alone, not both).
            if (removedTIndices.size() != 0) {
                throwElaborate(
                    "`field`: single-factor monomial with pair removal "
                    "(internal error)");
            }
            return buildReflexivity(universeLevel, carrierType, originalProduct);
        } else {
            reassocProof = proveProductEqualsSorted(
                originalProduct, factorList, rearranged,
                multiplyAxioms, carrierType, universeLevel, /*line*/0);
        }
        // Step 4: cancel pairs from the tail.
        // Current form: rearrangedProduct =
        //     (((survivors-product) * t_1) * r_1) * t_2 * r_2 * ... * t_k * r_k
        // (all left-associated). We peel right-to-left.
        //
        // If there are zero removed pairs, we should match survivors == rearranged
        // == factorList exactly, and reassocProof : factorList-product = survivors-product.
        if (removedTIndices.empty()) {
            return reassocProof;
        }
        // Need: at least one survivor (so the cancellation has a prefix
        // to land in). If there are zero survivors, the contracted form
        // is `1`, but we still need to handle the cancellation against
        // `1`. We handle this by using the survivor list including a
        // synthetic `1` at the front when needed.
        //
        // Concretely: if survivors is empty, the original factor list
        // was entirely (t, r) pairs. Then we need to prove that
        // `t_1 * r_1 * ... * t_k * r_k = 1`. We use a sequence of
        // collapses, starting with `(t_1 * r_1) = 1` (the innermost pair)
        // and lifting outward.
        ExpressionPointer survivorsProduct;
        bool noSurvivors = survivors.empty();
        ExpressionPointer oneConst = makeConstant(context.oneName);
        if (noSurvivors) {
            // We'll start with the trick: rearranged-product =
            // 1 * (t_1 * r_1 * ... * t_k * r_k). Hmm, but rearranged-product
            // is just t_1 * r_1 * ... * t_k * r_k (no leading 1). We'd
            // need to insert a 1 — that's a `one_multiply` reverse.
            //
            // Cleanest: prove the equality by induction-style:
            //   first pair: t_1 * r_1 = 1, by multipliesProof of the matching pair.
            //   subsequent pairs (k > 1): we have current form
            //     (((t_1 * r_1) * t_2) * r_2) * ... * t_k * r_k
            //     associativity collapse: (... * t_k) * r_k = ... * (t_k * r_k)
            //     simplify (t_k * r_k) → 1
            //     simplify (... * 1) → ...
            //   recurse.
            //
            // Since there are at least 2 factors in `rearranged`, and the
            // first 2 are a (t, r) pair, the base case can be: leave
            // the (t_1, r_1) prefix intact while we collapse pairs to the
            // right; at the very end, collapse the last remaining pair
            // (t_1, r_1) to 1.
            //
            // Simpler implementation: do exactly the same cancellation
            // loop as the survivor case, but treat the first (t_1, r_1)
            // pair as a "synthetic survivor" — i.e. start by collapsing
            // pairs 2..k, leaving prefix = t_1 * r_1. Then a final step
            // collapses (t_1 * r_1) = 1.
            //
            // Implementation: start `currentForm = rearrangedProduct =
            //  (((t_1*r_1)*t_2)*r_2)*...*t_k*r_k`. Collapse pairs from
            // the right.
            survivorsProduct =
                assembleLeftAssociatedProduct(multiplyName,
                    {pairs[pairIndexForRemovedT[0]].baseAtom,
                     pairs[pairIndexForRemovedT[0]].reciprocalAtom});
        } else if (survivors.size() == 1) {
            survivorsProduct = survivors[0];
        } else {
            survivorsProduct = assembleLeftAssociatedProduct(
                multiplyName, survivors);
        }
        // The `currentForm` represents the kernel-level current shape.
        ExpressionPointer currentForm = rearrangedProduct;
        ExpressionPointer chainProof = reassocProof;
        // We need `multiply_associative`, `multiply_one`/`one_multiply`,
        // and the cancellation lemma (the `multipliesProof` per pair).
        demandAxiomName(axiomNames.multiplyOneRight,
                          "multiply_one/multiply_identity_right",
                          context.carrierName);
        demandAxiomName(axiomNames.multiplyAssociative,
                          "multiply_associative", context.carrierName);
        // Track remaining (t, r) suffix: how many pairs still need to
        // be cancelled. Walk right-to-left.
        // The number of pairs total:
        size_t totalPairs = removedTIndices.size();
        // After cancellation k pairs, current form is:
        //   prefix * (remaining_pairs_t1) * (remaining_pairs_r1) * ...
        // We index pairs in REVERSE order of cancellation, from the
        // rightmost (last appended) to the leftmost.
        for (size_t step = 0; step < totalPairs; ++step) {
            // The rightmost remaining pair index in pairIndexForRemovedT
            // is `totalPairs - 1 - step`. Get t and r.
            size_t pairListIdx = totalPairs - 1 - step;
            // The "prefix" (left of the trailing (t, r) pair) is:
            //   if noSurvivors and this is the last (innermost) pair:
            //     no prefix — `currentForm` is exactly `t * r`
            //   else:
            //     prefix is whatever sits to the left of the last (t, r)
            //
            // Build prefix as a left-associated product of the relevant
            // pieces.
            std::vector<ExpressionPointer> prefixPieces;
            if (!noSurvivors) {
                for (const auto& s : survivors) prefixPieces.push_back(s);
            }
            // Append remaining pairs (those still to be cancelled,
            // before this step's pair).
            for (size_t earlier = 0; earlier < pairListIdx; ++earlier) {
                size_t epi = pairIndexForRemovedT[earlier];
                prefixPieces.push_back(pairs[epi].baseAtom);
                prefixPieces.push_back(pairs[epi].reciprocalAtom);
            }
            size_t curPairIdx = pairIndexForRemovedT[pairListIdx];
            ExpressionPointer tExpr = pairs[curPairIdx].baseAtom;
            ExpressionPointer rExpr = pairs[curPairIdx].reciprocalAtom;
            ExpressionPointer multipliesProof =
                pairs[curPairIdx].multipliesProof;
            // Case A: prefix is empty. currentForm == t * r.
            if (prefixPieces.empty()) {
                // currentForm should equal `t * r`. Apply multiplies
                // proof to get `1`.
                ExpressionPointer tTimesR = buildRingOp(
                    multiplyName, tExpr, rExpr);
                if (!structurallyEqual(currentForm, tTimesR)) {
                    throwElaborate(
                        "`field`: cancellation step expected `t*r` "
                        "form but got different shape (internal error)");
                }
                // currentForm = t * r, multipliesProof : t * r = 1.
                chainProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    originalProduct, currentForm, oneConst,
                    chainProof, multipliesProof);
                currentForm = oneConst;
                continue;
            }
            // Case B: prefix non-empty. currentForm has shape
            //   ((prefix-product) * t) * r
            // (because all factors are left-associated, and this pair
            // is at the very end).
            ExpressionPointer prefixProduct;
            if (prefixPieces.size() == 1) {
                prefixProduct = prefixPieces[0];
            } else {
                prefixProduct = assembleLeftAssociatedProduct(
                    multiplyName, prefixPieces);
            }
            // Expected currentForm = ((prefixProduct) * t) * r.
            ExpressionPointer expectedShape = buildRingOp(
                multiplyName,
                buildRingOp(multiplyName, prefixProduct, tExpr),
                rExpr);
            if (!structurallyEqual(currentForm, expectedShape)) {
                throwElaborate(
                    "`field`: cancellation step expected "
                    "`(prefix * t) * r` form (internal error)");
            }
            // Step B.1: associativity:
            //   (prefixProduct * t) * r = prefixProduct * (t * r)
            ExpressionPointer assocProof = makeConstant(
                axiomNames.multiplyAssociative);
            assocProof = makeApplication(assocProof, prefixProduct);
            assocProof = makeApplication(assocProof, tExpr);
            assocProof = makeApplication(assocProof, rExpr);
            ExpressionPointer formA = buildRingOp(
                multiplyName, prefixProduct,
                buildRingOp(multiplyName, tExpr, rExpr));
            // Step B.2: congruence with λz. prefix * z, substitute
            //   t * r ← 1 via multipliesProof.
            ExpressionPointer prefixLifted =
                liftBoundVariables(prefixProduct, 1, 0);
            ExpressionPointer lambdaBody = buildRingOp(
                multiplyName, prefixLifted, makeBoundVariable(0));
            ExpressionPointer lambda = makeLambda(
                "_field_cancel_z", carrierType, lambdaBody);
            ExpressionPointer tTimesR = buildRingOp(
                multiplyName, tExpr, rExpr);
            ExpressionPointer congrB = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambda,
                tTimesR, oneConst, multipliesProof);
            ExpressionPointer formB = buildRingOp(
                multiplyName, prefixProduct, oneConst);
            // Step B.3: multiply_one(prefixProduct) : prefix * 1 = prefix.
            ExpressionPointer multOneProof = makeConstant(
                axiomNames.multiplyOneRight);
            multOneProof = makeApplication(multOneProof, prefixProduct);
            // Compose: currentForm = formA = formB = prefixProduct.
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formA, formB,
                assocProof, congrB);
            ExpressionPointer stepABC = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formB, prefixProduct,
                stepAB, multOneProof);
            // Chain with `originalProduct = currentForm`.
            chainProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                originalProduct, currentForm, prefixProduct,
                chainProof, stepABC);
            currentForm = prefixProduct;
        }
        // After all cancellations, currentForm should equal
        // survivorsProduct (or, if noSurvivors and we cancelled all
        // pairs, `oneConst`).
        ExpressionPointer expectedFinal;
        if (noSurvivors) {
            expectedFinal = oneConst;
        } else if (survivors.size() == 1) {
            expectedFinal = survivors[0];
        } else {
            expectedFinal = assembleLeftAssociatedProduct(
                multiplyName, survivors);
        }
        if (!structurallyEqual(currentForm, expectedFinal)) {
            throwElaborate(
                "`field`: cancellation ended at unexpected form "
                "(internal error)");
        }
        return chainProof;
    }

    // Build kernel proof of `monomialCanonicalKernel = contractedCanonicalKernel`,
    // where `monomialCanonicalKernel` is the canonical form of an
    // original monomial (signature, coefficient) and
    // `contractedCanonicalKernel` is the canonical form of the
    // contracted monomial (after removing the indicated pairs).
    // The two coefficients must be equal in magnitude (no like-term
    // collisions at the per-monomial level — those are handled by the
    // caller).
    //
    // The proof is built on the factor-product level (without the
    // outer sign-wrap) and then lifted through the negate (if the
    // coefficient is -1) via congruence.
    ExpressionPointer buildMonomialContractionProof(
        const RingMonomialSignature& originalSignature,
        int coefficient,
        const RingMonomialSignature& contractedSignature,
        const std::vector<int>& pairsRemoved,
        const std::vector<FieldReciprocalPair>& pairs,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // No pair removals: nothing to do.
        bool anyRemoval = false;
        for (int n : pairsRemoved) if (n > 0) { anyRemoval = true; break; }
        ExpressionPointer monomialKernel = buildCanonicalMonomial(
            originalSignature, coefficient, context);
        if (!anyRemoval) {
            return buildReflexivity(universeLevel, carrierType, monomialKernel);
        }
        ExpressionPointer contractedKernel = buildCanonicalMonomial(
            contractedSignature, coefficient, context);
        // Build the factor list (kernel terms) for the original
        // monomial. The signature is sorted by hash; look up each.
        std::vector<ExpressionPointer> originalFactors;
        originalFactors.reserve(originalSignature.size());
        for (uint64_t h : originalSignature) {
            auto it = context.atoms.find(h);
            if (it == context.atoms.end()) {
                throwElaborate(
                    "`field`: atom hash missing during contraction "
                    "(internal error)");
            }
            originalFactors.push_back(it->second);
        }
        // Build the contracted factor list.
        std::vector<ExpressionPointer> contractedFactors;
        contractedFactors.reserve(contractedSignature.size());
        for (uint64_t h : contractedSignature) {
            auto it = context.atoms.find(h);
            if (it == context.atoms.end()) {
                throwElaborate(
                    "`field`: atom hash missing during contraction "
                    "(internal error)");
            }
            contractedFactors.push_back(it->second);
        }
        // Factor-product proof: original-product = contracted-product.
        // Use buildFactorContractionProof.
        if (originalFactors.empty()) {
            throwElaborate(
                "`field`: empty original factor list with removals "
                "(internal error)");
        }
        ExpressionPointer factorProof = buildFactorContractionProof(
            originalFactors, pairs, pairsRemoved, context, axiomNames);
        // Now lift through the coefficient/sign wrap.
        // buildCanonicalMonomial structure:
        //   magnitude 1 + non-empty factors: monomial = factor-product.
        //   magnitude 1 + empty factors:     monomial = `one`.
        // Coefficient < 0 wraps in negate.
        //
        // Our case: anyRemoval == true means original had >= 2 factors
        // (at least one (t, r) pair). So originalFactors non-empty,
        // monomialKernel = factor-product or -factor-product.
        // The contracted may have empty factor list (everything cancelled).
        //
        // Case 1: coefficient = +1, both non-empty.
        //   monomialKernel = original-factor-product.
        //   contractedKernel = contracted-factor-product.
        //   Proof = factorProof.
        // Case 2: coefficient = +1, contracted factors empty.
        //   monomialKernel = original-factor-product.
        //   contractedKernel = `one`.
        //   factorProof : original-product = `one`. ✓
        // Case 3: coefficient = -1, both non-empty.
        //   monomialKernel = -(original-factor-product).
        //   contractedKernel = -(contracted-factor-product).
        //   Apply congruence λz. -z to factorProof.
        // Case 4: coefficient = -1, contracted empty.
        //   monomialKernel = -(original-factor-product).
        //   contractedKernel = -(one).
        //   Apply congruence λz. -z.
        if (coefficient == 1) {
            // monomialKernel is the original factor product (or `one`
            // if empty original factors — but we asserted non-empty).
            // The contracted kernel is contracted-factor-product (or
            // `one` if empty). buildFactorContractionProof returns the
            // proof at the factor-product level, which matches.
            //
            // However: buildCanonicalMonomial(empty, +1) returns `one`,
            // and our contracted-factor-product when empty is also `one`
            // since assembleLeftAssociatedProduct isn't called on empty.
            // We need to verify the shapes match what buildCanonicalMonomial
            // produces.
            //
            // Verify by comparing structurally.
            ExpressionPointer originalProduct =
                assembleLeftAssociatedProduct(
                    context.multiplyName, originalFactors);
            ExpressionPointer contractedProduct;
            if (contractedFactors.empty()) {
                contractedProduct = makeConstant(context.oneName);
            } else if (contractedFactors.size() == 1) {
                contractedProduct = contractedFactors[0];
            } else {
                contractedProduct = assembleLeftAssociatedProduct(
                    context.multiplyName, contractedFactors);
            }
            // buildFactorContractionProof returns proof of
            //   originalProduct = contractedProduct
            // (or = oneConst if everything cancelled). Match.
            if (!structurallyEqual(monomialKernel, originalProduct)) {
                throwElaborate(
                    "`field`: monomial kernel mismatch (coeff +1) "
                    "(internal error)");
            }
            if (!structurallyEqual(contractedKernel, contractedProduct)) {
                throwElaborate(
                    "`field`: contracted kernel mismatch (coeff +1) "
                    "(internal error)");
            }
            return factorProof;
        }
        // coefficient == -1.
        ExpressionPointer originalProduct =
            assembleLeftAssociatedProduct(
                context.multiplyName, originalFactors);
        ExpressionPointer contractedProduct;
        if (contractedFactors.empty()) {
            contractedProduct = makeConstant(context.oneName);
        } else if (contractedFactors.size() == 1) {
            contractedProduct = contractedFactors[0];
        } else {
            contractedProduct = assembleLeftAssociatedProduct(
                context.multiplyName, contractedFactors);
        }
        // Lambda: λz. negate(z).
        ExpressionPointer lambdaBody = buildRingNegate(
            context.negateName, makeBoundVariable(0));
        ExpressionPointer lambda = makeLambda(
            "_field_neg_z", carrierType, lambdaBody);
        ExpressionPointer negCongr = buildEqualityCongruenceSameCarrier(
            universeLevel, carrierType, lambda,
            originalProduct, contractedProduct, factorProof);
        return negCongr;
    }

    // Build kernel proof of `canonical(P) = canonical(P_contracted)`
    // where P_contracted is the polynomial obtained from P by
    // contracting each monomial individually.  This assumes no
    // collisions: each contracted monomial has a unique signature in
    // P_contracted, and coefficients are unchanged. The proof works
    // by walking the canonical sum left-to-right and applying
    // per-monomial congruences.
    ExpressionPointer buildPolynomialContractionProof(
        const RingPolynomial& originalPoly,
        const RingPolynomial& contractedPoly,
        const std::vector<FieldMonomialContraction>& contractionRecords,
        const std::vector<FieldReciprocalPair>& pairs,
        const RingV2Context& context,
        const RingV2AxiomNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // No-collision assumption: contractedPoly has the same number
        // of monomials as the original (since each original monomial
        // maps to a unique contracted signature, with the same coefficient).
        if (originalPoly.size() != contractedPoly.size()) {
            throwElaborate(
                "`field`: contracted polynomial has like-term "
                "collisions across distinct original monomials — not "
                "yet supported by the field tactic. (This happens "
                "when the equation requires combining contracted "
                "monomials.)");
        }
        // Edge case: empty polynomial.
        if (originalPoly.empty()) {
            // canonical of empty = zero. Reflexivity.
            return buildReflexivity(universeLevel, carrierType,
                                      makeConstant(context.zeroName));
        }
        // Build per-monomial kernels and per-monomial contraction proofs.
        // Iterate originalPoly in canonical order (std::map order on signature).
        std::vector<ExpressionPointer> originalMonomialKernels;
        std::vector<ExpressionPointer> contractedMonomialKernels;
        std::vector<ExpressionPointer> perMonomialProofs;
        // Build a lookup: original sig → contraction record.
        std::map<RingMonomialSignature, size_t> recordIndex;
        for (size_t i = 0; i < contractionRecords.size(); ++i) {
            recordIndex[contractionRecords[i].originalSignature] = i;
        }
        for (const auto& entry : originalPoly) {
            auto it = recordIndex.find(entry.first);
            if (it == recordIndex.end()) {
                throwElaborate(
                    "`field`: contraction record missing for original "
                    "signature (internal error)");
            }
            const FieldMonomialContraction& rec =
                contractionRecords[it->second];
            ExpressionPointer originalKernel = buildCanonicalMonomial(
                rec.originalSignature, rec.originalCoefficient, context);
            ExpressionPointer contractedKernel = buildCanonicalMonomial(
                rec.contractedSignature, rec.originalCoefficient, context);
            ExpressionPointer proof = buildMonomialContractionProof(
                rec.originalSignature, rec.originalCoefficient,
                rec.contractedSignature, rec.pairsRemoved, pairs,
                context, axiomNames);
            originalMonomialKernels.push_back(originalKernel);
            contractedMonomialKernels.push_back(contractedKernel);
            perMonomialProofs.push_back(proof);
        }
        // canonical(originalPoly) is left-assoc sum of originalMonomialKernels.
        // We need a proof that it equals left-assoc sum of contractedMonomialKernels.
        //
        // We chain n proofs (one per monomial), each being a congruence
        // step that rewrites the i-th monomial's slot in the sum.
        //
        // BUT — the canonical of contracted may iterate in a DIFFERENT
        // order from the original (the std::map signature order may
        // shuffle after contraction). We need to handle that: after
        // per-position rewrites, the result is
        //   left_assoc(contractedMonomialKernels_in_original_order)
        // but `canonical(contractedPoly)` is
        //   left_assoc(contractedMonomialKernels_in_canonical_order).
        // These may differ in summand order.
        //
        // To bridge: apply ring v1 AC on the additive operator to sort
        // the summands.
        //
        // Step 1: per-position rewrites → contracted-monomials-in-original-order.
        // Step 2: AC sort → canonical(contractedPoly).
        ExpressionPointer originalCanonical =
            assembleLeftAssociatedSum(context.addName, originalMonomialKernels);
        ExpressionPointer afterPerPos =
            assembleLeftAssociatedSum(context.addName, contractedMonomialKernels);
        // Per-position rewrite chain.
        ExpressionPointer chainProof;
        if (originalMonomialKernels.size() == 1) {
            chainProof = perMonomialProofs[0];
        } else {
            // Build chain: for each i, congruence with a motive that
            // surgically replaces the i-th summand in the left-assoc
            // chain.
            //
            // The current form after k rewrites is:
            //   contracted_0 + contracted_1 + ... + contracted_{k-1}
            //     + original_k + original_{k+1} + ... + original_{n-1}
            // (all left-associated). To rewrite the k-th slot we use
            // congruenceOf(λz. ..., perMonomialProofs[k]).
            ExpressionPointer currentForm = originalCanonical;
            ExpressionPointer currentProof = buildReflexivity(
                universeLevel, carrierType, originalCanonical);
            size_t n = originalMonomialKernels.size();
            for (size_t k = 0; k < n; ++k) {
                // Build the motive: λz. <left-assoc with z in slot k>.
                // The pieces: contracted_0..contracted_{k-1}, then z,
                // then original_{k+1}..original_{n-1}.
                std::vector<ExpressionPointer> liftedPrefix;
                for (size_t i = 0; i < k; ++i) {
                    liftedPrefix.push_back(
                        liftBoundVariables(
                            contractedMonomialKernels[i], 1, 0));
                }
                std::vector<ExpressionPointer> liftedSuffix;
                for (size_t i = k + 1; i < n; ++i) {
                    liftedSuffix.push_back(
                        liftBoundVariables(
                            originalMonomialKernels[i], 1, 0));
                }
                // Build the motive expression.
                ExpressionPointer motive;
                if (k == 0) {
                    motive = makeBoundVariable(0);
                } else if (liftedPrefix.size() == 1) {
                    motive = buildRingOp(
                        context.addName, liftedPrefix[0],
                        makeBoundVariable(0));
                } else {
                    ExpressionPointer prefixSum =
                        assembleLeftAssociatedSum(
                            context.addName, liftedPrefix);
                    motive = buildRingOp(
                        context.addName, prefixSum,
                        makeBoundVariable(0));
                }
                for (const auto& s : liftedSuffix) {
                    motive = buildRingOp(
                        context.addName, motive, s);
                }
                ExpressionPointer lambda = makeLambda(
                    "_field_poly_z", carrierType, motive);
                // The "new form" after rewriting slot k.
                std::vector<ExpressionPointer> newSummands;
                for (size_t i = 0; i < k; ++i) {
                    newSummands.push_back(contractedMonomialKernels[i]);
                }
                newSummands.push_back(contractedMonomialKernels[k]);
                for (size_t i = k + 1; i < n; ++i) {
                    newSummands.push_back(originalMonomialKernels[i]);
                }
                ExpressionPointer newForm =
                    assembleLeftAssociatedSum(
                        context.addName, newSummands);
                ExpressionPointer congrProof =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        originalMonomialKernels[k],
                        contractedMonomialKernels[k],
                        perMonomialProofs[k]);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    originalCanonical, currentForm, newForm,
                    currentProof, congrProof);
                currentForm = newForm;
            }
            chainProof = currentProof;
        }
        // Now we have proof: originalCanonical = afterPerPos
        // (i.e. left-assoc sum of contractedMonomialKernels in
        // original-order).
        ExpressionPointer canonicalContracted =
            buildCanonicalPolynomial(contractedPoly, context);
        if (structurallyEqual(afterPerPos, canonicalContracted)) {
            return chainProof;
        }
        // Need to reorder via ring v1 AC on add.
        std::vector<ExpressionPointer> contractedMonomialKernelsCanonical;
        for (const auto& entry : contractedPoly) {
            contractedMonomialKernelsCanonical.push_back(
                buildCanonicalMonomial(entry.first, entry.second, context));
        }
        RingAxiomNames addAxioms{
            context.addName, axiomNames.addAssociative,
            axiomNames.addCommutative};
        // Sort `contractedMonomialKernels` (original order) into
        // `contractedMonomialKernelsCanonical` (canonical order) — same
        // multiset of monomials, different orders.
        ExpressionPointer sortProof = proveProductEqualsSorted(
            afterPerPos, contractedMonomialKernels,
            contractedMonomialKernelsCanonical,
            addAxioms, carrierType, universeLevel, /*line*/0);
        return buildEqualityTransitivity(
            universeLevel, carrierType,
            originalCanonical, afterPerPos, canonicalContracted,
            chainProof, sortProof);
    }

    // Walk a kernel expression and accumulate every `reciprocal_function`
    // application's argument into `argumentsOut` (deduplicating by hash).
    void collectReciprocalArguments(
        ExpressionPointer expression,
        const std::string& reciprocalFunctionName,
        std::unordered_map<uint64_t, ExpressionPointer>& argumentsOut) {
        if (auto* app = std::get_if<Application>(&expression->node)) {
            if (auto* head =
                    std::get_if<Constant>(&app->function->node)) {
                if (head->name == reciprocalFunctionName) {
                    argumentsOut.emplace(
                        app->argument->hash, app->argument);
                    // Continue into the argument too (nested
                    // reciprocals would be unusual but possible).
                }
            }
            collectReciprocalArguments(
                app->function, reciprocalFunctionName, argumentsOut);
            collectReciprocalArguments(
                app->argument, reciprocalFunctionName, argumentsOut);
            return;
        }
        if (auto* lam = std::get_if<Lambda>(&expression->node)) {
            collectReciprocalArguments(
                lam->domain, reciprocalFunctionName, argumentsOut);
            collectReciprocalArguments(
                lam->body, reciprocalFunctionName, argumentsOut);
            return;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            collectReciprocalArguments(
                pi->domain, reciprocalFunctionName, argumentsOut);
            collectReciprocalArguments(
                pi->codomain, reciprocalFunctionName, argumentsOut);
            return;
        }
        // Other variants: no children to walk.
    }

    // `field(h1, h2, ..., hn)` — closes a Rational (or any field with a
    // `reciprocal_function`) equality using `ring` plus the
    // `reciprocal_function_multiplies` law and the user-supplied
    // nonzero hypotheses.
    ExpressionPointer elaborateField(
        const SurfaceField& fieldTactic,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "field at line " + std::to_string(line),
                    localBinders, expectedType, line, column);
        if (!expectedType) {
            throwElaborate(
                "`field` needs an expected type from context — use it "
                "as the body of a theorem with a declared equality "
                "conclusion");
        }
        // Open the expected type over local binders so that local
        // variables appear as FreeVariables — this lets us match
        // against hypothesis types (which arrive opened).
        ExpressionPointer expectedTypeOpened = openOverLocalBinders(
            expectedType, localBinders, localBinders.size());
        EqualityComponents goal =
            extractEqualityComponents(expectedTypeOpened, "field", line);
        std::string carrierName = headConstantName(goal.carrierType);
        // Set up the ring v2 context.
        RingV2Context context;
        context.carrierName = carrierName;
        context.carrierType = goal.carrierType;
        context.carrierUniverseLevel = goal.carrierUniverseLevel;
        context.addName       = carrierName + ".add";
        context.multiplyName  = carrierName + ".multiply";
        context.negateName    = carrierName + ".negate";
        context.subtractName  = carrierName + ".subtract";
        context.zeroName      = carrierName + ".zero";
        context.oneName       = carrierName + ".one";
        if (environment_.lookup(context.addName) == nullptr
            || environment_.lookup(context.multiplyName) == nullptr) {
            throwElaborate(
                "`field`: carrier `" + carrierName
                + "` does not have both `.add` and `.multiply` in scope");
        }
        std::string reciprocalFunctionName =
            carrierName + ".reciprocal_function";
        std::string reciprocalMultipliesName =
            carrierName + ".reciprocal_function_multiplies";
        if (environment_.lookup(reciprocalFunctionName) == nullptr) {
            throwElaborate(
                "`field`: carrier `" + carrierName
                + "` does not have `reciprocal_function` in scope");
        }
        if (environment_.lookup(reciprocalMultipliesName) == nullptr) {
            throwElaborate(
                "`field`: carrier `" + carrierName
                + "` does not have `reciprocal_function_multiplies` in scope");
        }
        // Collect reciprocal_function arguments from both sides.
        std::unordered_map<uint64_t, ExpressionPointer> recipArgsMap;
        collectReciprocalArguments(
            goal.leftEndpoint, reciprocalFunctionName, recipArgsMap);
        collectReciprocalArguments(
            goal.rightEndpoint, reciprocalFunctionName, recipArgsMap);
        // Elaborate user hypotheses. Each h_i should have type
        // ¬(t_i = zero) ≡ (t_i = zero) → False.
        std::vector<FieldReciprocalPair> pairs;
        std::vector<bool> matchedArguments;
        std::vector<uint64_t> recipArgHashes;
        std::vector<ExpressionPointer> recipArgKernels;
        for (const auto& kv : recipArgsMap) {
            recipArgHashes.push_back(kv.first);
            recipArgKernels.push_back(kv.second);
        }
        matchedArguments.assign(recipArgHashes.size(), false);
        for (const auto& hypothesisSurface :
                 fieldTactic.nonzeroHypotheses) {
            ExpressionPointer hypothesisKernel = elaborateExpression(
                *hypothesisSurface, localBinders);
            // Open the hypothesis kernel so it lives in the same
            // FreeVariable namespace as our opened goal.
            ExpressionPointer hypothesisKernelOpened = openOverLocalBinders(
                hypothesisKernel, localBinders, localBinders.size());
            // Infer type: should be (t = zero) → False.
            ExpressionPointer hypothesisType;
            try {
                hypothesisType = weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(localBinders, hypothesisKernel));
            } catch (const TypeError& kernelError) {
                rethrowKernelError(kernelError);
            }
            // Walk hypothesisType: expect Pi(_ : Equality(carrier, t, zero), _, False).
            // Surface form `¬(t = zero)` is `(t = zero) → False`,
            // which kernel-side is Pi(_ : Equality(carrier, t, zero), False).
            auto* piNode = std::get_if<Pi>(&hypothesisType->node);
            if (!piNode) {
                throwElaborate(
                    "`field`: hypothesis is not a `¬(t = Rational.zero)` "
                    "(not a function type)");
            }
            ExpressionPointer domain = weakHeadNormalForm(
                environment_, piNode->domain);
            EqualityComponents domainComponents;
            try {
                domainComponents = extractEqualityComponents(
                    domain, "field hypothesis", line);
            } catch (const ElaborateError&) {
                throwElaborate(
                    "`field`: hypothesis domain is not an equality");
            }
            // Check carrier matches.
            if (!structurallyEqual(
                    domainComponents.carrierType, goal.carrierType)) {
                throwElaborate(
                    "`field`: hypothesis carrier doesn't match goal "
                    "carrier");
            }
            // Check the RHS of the equality is `zero`. We accept the
            // bare Constant before WHNF (definitions unfold under
            // delta-reduction, so `Rational.zero` would reduce away;
            // the user almost always writes the literal name).
            ExpressionPointer rhsRaw = domainComponents.rightEndpoint;
            auto* rhsConst = std::get_if<Constant>(&rhsRaw->node);
            if (!rhsConst || rhsConst->name != context.zeroName) {
                throwElaborate(
                    "`field`: hypothesis is not of shape `¬(t = "
                    + context.zeroName + ")`");
            }
            // Locate which recipArg matches.
            ExpressionPointer baseAtom = domainComponents.leftEndpoint;
            uint64_t baseHash = baseAtom->hash;
            // Find recipArg with same hash.
            size_t matchedIndex = recipArgHashes.size();
            for (size_t i = 0; i < recipArgHashes.size(); ++i) {
                if (recipArgHashes[i] == baseHash) {
                    matchedIndex = i;
                    break;
                }
            }
            if (matchedIndex == recipArgHashes.size()) {
                // Hypothesis doesn't correspond to any
                // reciprocal_function call. Tolerate (ignore).
                continue;
            }
            if (matchedArguments[matchedIndex]) continue;  // duplicate
            matchedArguments[matchedIndex] = true;
            // Build the reciprocal_function(t) kernel.
            ExpressionPointer reciprocalAtom = makeApplication(
                makeConstant(reciprocalFunctionName), baseAtom);
            // Build proof `multipliesProof : t * reciprocal_function(t) = 1`.
            // Call: reciprocal_function_multiplies(t, hypothesisKernel).
            // Use the opened hypothesis kernel so it composes with the
            // opened goal terms.
            ExpressionPointer multipliesProof = makeConstant(
                reciprocalMultipliesName);
            multipliesProof = makeApplication(multipliesProof, baseAtom);
            multipliesProof = makeApplication(multipliesProof,
                                                hypothesisKernelOpened);
            FieldReciprocalPair pair;
            pair.baseAtom = baseAtom;
            pair.reciprocalAtom = reciprocalAtom;
            pair.multipliesProof = multipliesProof;
            pair.baseHash = baseHash;
            pair.reciprocalHash = reciprocalAtom->hash;
            pairs.push_back(pair);
        }
        // Check we matched all reciprocal_function arguments.
        for (size_t i = 0; i < recipArgHashes.size(); ++i) {
            if (!matchedArguments[i]) {
                throwElaborate(
                    "`field`: no nonzero hypothesis supplied for one "
                    "of the `reciprocal_function` arguments — pass a "
                    "hypothesis `¬(t = " + context.zeroName + ")` for "
                    "every distinct `t` appearing inside "
                    "`reciprocal_function(t)` on either side of the "
                    "goal");
            }
        }
        // Normalize both sides to ring polynomials.
        RingPolynomial leftPolynomial =
            normaliseToRingPolynomial(goal.leftEndpoint, context);
        RingPolynomial rightPolynomial =
            normaliseToRingPolynomial(goal.rightEndpoint, context);
        // Make sure that for each (t_i, r_i) pair we have the atoms
        // registered in the context atom table — they must have been
        // registered by the normalization above (assuming both atoms
        // appear in at least one side). Pre-register them here to be safe.
        for (const auto& p : pairs) {
            context.atoms.emplace(p.baseHash, p.baseAtom);
            context.atoms.emplace(p.reciprocalHash, p.reciprocalAtom);
        }
        // Contract polynomials.
        std::vector<FieldMonomialContraction> leftContractionRecords;
        RingPolynomial leftContracted = buildContractedPolynomial(
            leftPolynomial, pairs, leftContractionRecords);
        std::vector<FieldMonomialContraction> rightContractionRecords;
        RingPolynomial rightContracted = buildContractedPolynomial(
            rightPolynomial, pairs, rightContractionRecords);
        if (!ringPolynomialsAgree(leftContracted, rightContracted)) {
            throwElaborate(
                "`field`: after clearing reciprocals, the two sides "
                "still don't agree as polynomials — the goal is not a "
                "valid field identity (or the hypothesis set is "
                "insufficient)"
                + buildFingerprintDiagnostic(
                      goal.leftEndpoint, goal.rightEndpoint,
                      carrierName));
        }
        // Coefficient guard: ±1 throughout.
        for (const auto& entry : leftContracted) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`field`: the canonical form has a monomial with "
                    "coefficient " + std::to_string(entry.second)
                    + " — the underlying ring v2 only handles "
                    "coefficients in {-1, +1}");
            }
        }
        for (const auto& entry : leftPolynomial) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`field`: the LHS polynomial has a monomial with "
                    "coefficient " + std::to_string(entry.second)
                    + " — the underlying ring v2 only handles "
                    "coefficients in {-1, +1}");
            }
        }
        for (const auto& entry : rightPolynomial) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`field`: the RHS polynomial has a monomial with "
                    "coefficient " + std::to_string(entry.second)
                    + " — the underlying ring v2 only handles "
                    "coefficients in {-1, +1}");
            }
        }
        // Resolve axiom names.
        RingV2AxiomNames axiomNames =
            resolveRingV2AxiomNames(carrierName);
        demandAxiomName(axiomNames.addAssociative,
                          "add_associative", carrierName);
        demandAxiomName(axiomNames.addCommutative,
                          "add_commutative", carrierName);
        demandAxiomName(axiomNames.multiplyAssociative,
                          "multiply_associative", carrierName);
        demandAxiomName(axiomNames.multiplyCommutative,
                          "multiply_commutative", carrierName);
        // Step 1: LHS = ring-canonical(LHS) via proveEqualsCanonical.
        RingPolynomial leftPolyOut, rightPolyOut;
        ExpressionPointer leftRingProof = proveEqualsCanonical(
            goal.leftEndpoint, context, axiomNames, leftPolyOut);
        ExpressionPointer rightRingProof = proveEqualsCanonical(
            goal.rightEndpoint, context, axiomNames, rightPolyOut);
        ExpressionPointer leftRingCanonical =
            buildCanonicalPolynomial(leftPolynomial, context);
        ExpressionPointer rightRingCanonical =
            buildCanonicalPolynomial(rightPolynomial, context);
        // Step 2: ring-canonical(LHS) = field-canonical(LHS) via
        //         buildPolynomialContractionProof.
        ExpressionPointer leftContractedCanonical =
            buildCanonicalPolynomial(leftContracted, context);
        ExpressionPointer rightContractedCanonical =
            buildCanonicalPolynomial(rightContracted, context);
        ExpressionPointer leftContractionProof =
            buildPolynomialContractionProof(
                leftPolynomial, leftContracted,
                leftContractionRecords, pairs, context, axiomNames);
        ExpressionPointer rightContractionProof =
            buildPolynomialContractionProof(
                rightPolynomial, rightContracted,
                rightContractionRecords, pairs, context, axiomNames);
        // Step 3: field-canonical(LHS) = field-canonical(RHS). The two
        // canonical kernels must be structurally equal (the polynomials
        // are equal, and buildCanonicalPolynomial is deterministic).
        if (!structurallyEqual(leftContractedCanonical,
                                  rightContractedCanonical)) {
            throwElaborate(
                "`field`: field-canonical kernels differ even though "
                "polynomials agreed (internal error)");
        }
        // Step 4: symmetric of step 2 for RHS.
        ExpressionPointer rightContractionProofSym = buildEqualitySymmetry(
            goal.carrierUniverseLevel, goal.carrierType,
            rightRingCanonical, rightContractedCanonical,
            rightContractionProof);
        // Step 5: symmetric of step 1 for RHS.
        ExpressionPointer rightRingProofSym = buildEqualitySymmetry(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.rightEndpoint, rightRingCanonical,
            rightRingProof);
        // Compose chain: LHS = leftRingCanonical = leftContractedCanonical
        //   = rightRingCanonical = RHS.
        ExpressionPointer chain12 = buildEqualityTransitivity(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.leftEndpoint, leftRingCanonical,
            leftContractedCanonical,
            leftRingProof, leftContractionProof);
        // leftContractedCanonical and rightContractedCanonical are
        // structurally equal, so we can chain via either kernel as the
        // bridge.
        ExpressionPointer chain1234 = buildEqualityTransitivity(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.leftEndpoint, leftContractedCanonical,
            rightRingCanonical,
            chain12, rightContractionProofSym);
        ExpressionPointer chain12345 = buildEqualityTransitivity(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.leftEndpoint, rightRingCanonical, goal.rightEndpoint,
            chain1234, rightRingProofSym);
        // The proof is built in OPENED form (over local-binder
        // FreeVariables). Close it before returning so the caller's
        // BoundVariable-form expectedType matches.
        return closeOverLocalBinders(
            chain12345, localBinders, localBinders.size());
    }

    // `sorry` — desugars to either `Internal.sorry_proposition(<P>)`
    // (when the expected type is a Proposition, i.e. lives in `Sort 0`)
    // or `Internal.sorry.{u}(<T>)` (when the expected type lives in
    // `Type(u) = Sort (u+1)` for some u). Either way emits a warning at
    // the use site so the gap is visible in the build log.
    ExpressionPointer elaborateSorry(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "sorry placeholder at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "`sorry` needs an expected type from context — wrap "
                "with an ascription `(sorry : T)` or supply one via "
                "context");
        }
        // Determine: is the expected type a Proposition (`Sort 0`) or
        // a Type-universe value (`Sort (u+1)` for some u ≥ 0)?
        bool isProposition = false;
        LevelPointer universeLevel;
        try {
            Context openedContext = buildContextFromLocalBinders(localBinders);
            ExpressionPointer expectedTypeOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            ExpressionPointer typeOfType = inferType(
                environment_, openedContext, expectedTypeOpened);
            ExpressionPointer typeOfTypeReduced = weakHeadNormalForm(
                environment_, typeOfType);
            auto* sortNode = std::get_if<Sort>(&typeOfTypeReduced->node);
            if (!sortNode) {
                throwElaborate(
                    "`sorry` cannot determine the universe of the "
                    "expected type — its type is not a Sort");
            }
            LevelPointer sortLevel = sortNode->level;
            if (auto* successor =
                    std::get_if<LevelSuccessor>(&sortLevel->node)) {
                universeLevel = successor->base;
            } else if (auto* constant =
                            std::get_if<LevelConst>(&sortLevel->node)) {
                if (constant->value == 0) {
                    isProposition = true;
                } else {
                    universeLevel = makeLevelConst(constant->value - 1);
                }
            } else {
                throwElaborate(
                    "`sorry`: expected type's universe is neither "
                    "`Proposition` nor `Type(u)` for a known u");
            }
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        std::string axiomName = isProposition
            ? "Internal.sorry_proposition"
            : "Internal.sorry";
        if (environment_.lookup(axiomName) == nullptr) {
            throwElaborate(
                "`sorry` requires `" + axiomName + "` in scope "
                "(import axioms)");
        }
        std::cerr << "warning: `sorry` used"
                  << (currentDeclarationName_.empty()
                          ? ""
                          : (" in '" + currentDeclarationName_ + "'"))
                  << " at line " << line << "\n";
        ExpressionPointer call;
        if (isProposition) {
            call = makeConstant(axiomName);
        } else {
            call = makeConstant(axiomName, {universeLevel});
        }
        call = makeApplication(std::move(call), expectedType);
        return call;
    }

    // `⟨a, b, ..., n⟩` at expected type `I(...)`: desugars to a call of
    // I's unique constructor. When the constructor takes more value-args
    // than there are tuple components, the user's tuple is under-sized
    // and we error. When the constructor takes exactly N value-args, we
    // emit a direct constructor application. When the constructor takes
    // K < N value-args and K == 2, we right-associate: `⟨a, b, c⟩` at
    // `Exists(_, _)` becomes `Exists.introduce(a, ⟨b, c⟩)` and the inner
    // `⟨b, c⟩` is elaborated against the second-argument's expected
    // type. (This is the conventional shape for nested Exists/And.)
    ExpressionPointer elaborateAnonymousTuple(
        const SurfaceAnonymousTuple& tuple,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {

        if (!expectedType) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' needs an expected type from "
                "context (line " + std::to_string(line) + ")");
        }
        ExpressionPointer head =
            weakHeadNormalForm(environment_, expectedType);
        ExpressionPointer headFunction = head;
        while (auto* application =
                   std::get_if<Application>(&headFunction->node)) {
            headFunction = application->function;
        }
        auto* constant = std::get_if<Constant>(&headFunction->node);
        if (!constant) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": expected type does not have an inductive head");
        }
        const Declaration* inductiveDecl =
            environment_.lookup(constant->name);
        auto* inductive = inductiveDecl
            ? std::get_if<Inductive>(inductiveDecl) : nullptr;
        if (!inductive) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": expected type's head '" + constant->name
                + "' is not an inductive");
        }
        if (inductive->constructorNames.size() != 1) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": expected single-constructor inductive, but '"
                + constant->name + "' has "
                + std::to_string(inductive->constructorNames.size())
                + " constructors");
        }
        const std::string& constructorName =
            inductive->constructorNames[0];
        const Declaration* constructorDecl =
            environment_.lookup(constructorName);
        auto* constructor = constructorDecl
            ? std::get_if<Constructor>(constructorDecl) : nullptr;
        if (!constructor) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line)
                + ": constructor '" + constructorName
                + "' missing from environment");
        }
        int totalPiCount = countLeadingPis(constructor->type);
        int valueArgumentCount =
            totalPiCount - inductive->numParameters;
        size_t componentCount = tuple.components.size();
        if (componentCount == 0) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' is empty at line "
                + std::to_string(line));
        }
        // Build a SurfaceApplication and re-elaborate it so that the
        // existing constructor parameter inference path handles it.
        std::vector<SurfaceExpressionPointer> components;
        if (static_cast<int>(componentCount) == valueArgumentCount) {
            components = tuple.components;
        } else if (valueArgumentCount == 2 && componentCount > 2) {
            components.push_back(tuple.components[0]);
            std::vector<SurfaceExpressionPointer> tail(
                tuple.components.begin() + 1, tuple.components.end());
            components.push_back(makeSurfaceAnonymousTuple(
                std::move(tail), line, column));
        } else {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' at line "
                + std::to_string(line) + ": constructor '"
                + constructorName + "' takes "
                + std::to_string(valueArgumentCount)
                + " value argument(s), got "
                + std::to_string(componentCount)
                + " tuple component(s)");
        }
        SurfaceExpressionPointer constructorReference =
            makeSurfaceIdentifier(constructorName, {}, line, column);
        SurfaceExpressionPointer surfaceCall = makeSurfaceApplication(
            std::move(constructorReference), std::move(components),
            line, column);
        return elaborateExpression(*surfaceCall, localBinders,
                                    expectedType);
    }

    // Handle a `cases` / `obtain` expression whose scrutinee is a
    // `Quotient.{u}(T, R)` value. Quotient is an axiomatic primitive,
    // not an inductive, so the standard recursor path doesn't apply.
    // We build a `Quotient.induct.{u}(T, R, motive, λ rep ⇒ body,
    // scrutinee)` term directly.
    //
    // Restrictions: exactly one clause; pattern shape
    // `Quotient.mk(rep)` with a single bare-name argument; scrutinee is
    // a local-binder variable (so we can abstract it from the goal).
    // Expected type must reduce to a Proposition since `Quotient.induct`
    // requires a Proposition-valued motive.
    ExpressionPointer elaborateQuotientCases(
        const SurfaceCases& cases,
        ExpressionPointer scrutinee,
        ExpressionPointer scrutineeTypeOpened,
        const std::vector<ExpressionPointer>& inductiveArguments,
        const Constant& quotientConstant,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "quotient-cases at line " + std::to_string(line));

        // Verify scrutinee is a local-binder variable so we can
        // abstract it from the goal.
        auto* scrutineeBoundVariable =
            std::get_if<BoundVariable>(&scrutinee->node);
        if (!scrutineeBoundVariable
            || scrutineeBoundVariable->deBruijnIndex < 0
            || scrutineeBoundVariable->deBruijnIndex
                   >= static_cast<int>(localBinders.size())) {
            throwElaborate(
                "quotient-cases scrutinee must be a local-binder "
                "variable (a parameter or let-binding name)");
        }
        int scrutineeDeBruijn = scrutineeBoundVariable->deBruijnIndex;

        // Quotient takes 2 args: T and R. The kernel's universe-arg
        // count is always 1 for Quotient.
        if (inductiveArguments.size() != 2) {
            throwElaborate(
                "internal: Quotient applied to "
                + std::to_string(inductiveArguments.size())
                + " arguments, expected 2 (T, R)");
        }
        if (quotientConstant.universeArguments.size() != 1) {
            throwElaborate(
                "internal: Quotient should have exactly one universe "
                "argument");
        }
        LevelPointer quotientUniverse =
            quotientConstant.universeArguments[0];
        ExpressionPointer carrierTypeOpened = inductiveArguments[0];
        ExpressionPointer relationOpened = inductiveArguments[1];
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpened, localBinders, localBinders.size());
        ExpressionPointer relation = closeOverLocalBinders(
            relationOpened, localBinders, localBinders.size());
        ExpressionPointer scrutineeType = closeOverLocalBinders(
            scrutineeTypeOpened, localBinders, localBinders.size());

        if (cases.clauses.size() != 1) {
            throwElaborate(
                "quotient-cases takes exactly one clause "
                "(`Quotient.mk(rep) => …`), got "
                + std::to_string(cases.clauses.size()));
        }
        const SurfaceCasesClause& clause = cases.clauses[0];

        // Pattern must be `Quotient.mk(rep_name)` — a constructor
        // pattern with name "Quotient.mk" and exactly one bare-name
        // argument (the representative binder).
        auto* constructorPattern = std::get_if<SurfacePatternConstructor>(
            &clause.pattern->node);
        if (!constructorPattern
            || constructorPattern->constructorName != "Quotient.mk") {
            throwElaborate(
                "quotient-cases pattern must be `Quotient.mk(rep_name)`");
        }
        if (constructorPattern->arguments.size() != 1) {
            throwElaborate(
                "quotient-cases: `Quotient.mk` pattern takes one "
                "argument (the representative-binder name), got "
                + std::to_string(
                    constructorPattern->arguments.size()));
        }
        auto* bareNamePattern = std::get_if<SurfacePatternBareName>(
            &constructorPattern->arguments[0]->node);
        if (!bareNamePattern) {
            throwElaborate(
                "quotient-cases: the argument inside `Quotient.mk(…)` "
                "must be a bare identifier that names the "
                "representative");
        }
        std::string representativeName = bareNamePattern->name;

        // Build the motive: `λ q : Quotient.{u}(T, R) ⇒
        // expectedType[scrutinee := q]`. We abstract the scrutinee's
        // local index out of expectedType; the resulting body's
        // BoundVariable(0) refers to the new motive binder.
        ExpressionPointer motiveBody =
            abstractOverBoundVariables(expectedType, {scrutineeDeBruijn});
        ExpressionPointer motive = makeLambda(
            "_quotient_target", scrutineeType, motiveBody);

        // Set up the inner local-binder context with the representative
        // binder on top.
        std::vector<LocalBinder> innerBinders = localBinders;
        innerBinders.push_back({representativeName, carrierType});

        // Build the body's expected type as `motive(Quotient.mk(T, R, rep))`
        // in inner context. Shift outer terms up by 1 to account for the
        // new binder; rep is BoundVariable(0). The kernel's WHNF will
        // beta-reduce when needed.
        ExpressionPointer carrierTypeInner = shift(carrierType, 1);
        ExpressionPointer relationInner = shift(relation, 1);
        ExpressionPointer motiveInner = shift(motive, 1);
        ExpressionPointer mkAppliedToRep =
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeConstant("Quotient.mk", {quotientUniverse}),
                        carrierTypeInner),
                    relationInner),
                makeBoundVariable(0));
        ExpressionPointer bodyExpectedType =
            makeApplication(motiveInner, mkAppliedToRep);

        // Elaborate the body in the extended local context.
        ExpressionPointer bodyKernel =
            elaborateExpression(*clause.body, innerBinders,
                                 bodyExpectedType);

        // Wrap the body in the representative-case lambda.
        ExpressionPointer representativeCaseLambda = makeLambda(
            representativeName, carrierType, bodyKernel);

        // Final application: Quotient.induct(T, R, motive,
        //                                     λ rep ⇒ body, scrutinee).
        ExpressionPointer quotientInductHead =
            makeConstant("Quotient.induct", {quotientUniverse});
        return makeApplication(
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeApplication(quotientInductHead, carrierType),
                        relation),
                    motive),
                representativeCaseLambda),
            scrutinee);
    }

    // Render a `SurfacePattern` back into a `SurfaceExpression` for
    // use as the right-hand side of the per-arm equation in the
    // `cases X with equalityHypothesisName { … }` desugaring.
    // Constructor patterns become applications of the constructor's
    // name to the bound argument names. Tuple patterns are
    // disallowed (the convoy doesn't add information on
    // single-constructor inductives, and the rest of the desugar
    // would have to re-route through the tuple's lone constructor —
    // not worth the complexity for the v1 cut).
    SurfaceExpressionPointer patternToSurfaceExpression(
        SurfacePatternPointer pattern) {
        int line = pattern->line;
        int column = pattern->column;
        if (auto* bare =
                std::get_if<SurfacePatternBareName>(&pattern->node)) {
            return makeSurfaceIdentifier(bare->name, {},
                                          line, column);
        }
        if (auto* constructorPattern =
                std::get_if<SurfacePatternConstructor>(&pattern->node)) {
            SurfaceExpressionPointer head = makeSurfaceIdentifier(
                constructorPattern->constructorName, {}, line, column);
            if (constructorPattern->arguments.empty()) {
                return head;
            }
            std::vector<SurfaceArgument> arguments;
            for (const auto& argumentPattern :
                     constructorPattern->arguments) {
                SurfaceArgument argument;
                argument.value =
                    patternToSurfaceExpression(argumentPattern);
                arguments.push_back(std::move(argument));
            }
            return makeSurfaceApplication(std::move(head),
                                           std::move(arguments),
                                           line, column);
        }
        throwElaborate(
            "cases ... with equalityHypothesis: tuple patterns are "
            "not yet supported in the convoy desugaring; the "
            "`function`+`cases` form still works as a fallback");
        return nullptr;  // unreachable
    }

    // `cases X with equalityHypothesisName { … }` — the "convoy" form.
    //
    // Each arm gets an extra binder
    //   `equalityHypothesisName : X = <constructor pattern>`
    // in scope. Implements the user's explicit
    //   `(function (caseScrutineeVariable : T)
    //              (equalityHypothesisOuter : X = caseScrutineeVariable) =>
    //      (cases caseScrutineeVariable {
    //         | ctor(args) => function (equalityHypothesisName : X = ctor(args)) => body
    //       } : (… : X = caseScrutineeVariable) → Goal)(
    //          equalityHypothesisOuter))
    //   (X)(reflexivity(X))`
    // pattern, but without the user having to write any of it.
    //
    // Kernel-level details:
    //   - The user's expected type `Goal` is passed in CLOSED form
    //     (BoundVariable indices relative to the surrounding theorem
    //     binders). We extend localBinders with the two new convoy
    //     binders and lift Goal accordingly when we drop it into the
    //     inner Pi.
    //   - The "constructor pattern as surface expression" is
    //     reconstructed from each clause's pattern; the names that
    //     bind constructor arguments inside the pattern reappear as
    //     references in the equation type, so the elaborator wires
    //     them up by name during the inner case-arm elaboration.
    //   - The inner cases is elaborated against an expected type of
    //     `(_inner : X = caseScrutineeVariable) → Goal`. The standard
    //     `elaborateCasesExpression` motive-inference picks the
    //     scrutinee-abstracted motive `λ s. (… : X = s) → Goal` from
    //     this; each arm then has expected type
    //     `(… : X = <constructor pattern>) → Goal`, which is exactly
    //     the surface lambda we wrapped around the user's body.
    ExpressionPointer elaborateCasesWithEqualityHypothesis(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "cases ... with " + cases.equalityHypothesisName
            + " at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "cases X with " + cases.equalityHypothesisName
                + " { … } needs an expected type from context");
        }
        // (1) Elaborate the scrutinee X. Get T (closed) and its
        // universe level.
        ExpressionPointer scrutineeKernel = elaborateExpression(
            *cases.scrutinee, localBinders);
        ExpressionPointer scrutineeTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, scrutineeKernel));
        ExpressionPointer scrutineeType = closeOverLocalBinders(
            scrutineeTypeOpened, localBinders, localBinders.size());
        LevelPointer scrutineeUniverse =
            typeUniverseOf(localBinders, scrutineeKernel);

        // (2) Names for the two convoy binders. The internal "_" prefix
        // avoids any chance of colliding with user-visible names; the
        // user only ever sees `equalityHypothesisName` (theirs).
        const std::string caseScrutineeName =
            "_caseScrutineeFor_" + cases.equalityHypothesisName;
        const std::string outerEqualityName =
            "_equalityHypothesisOuterFor_"
            + cases.equalityHypothesisName;

        // (3) Build the equality-type for the OUTER binder in extended
        // scope. After adding `caseScrutineeName : T` to localBinders,
        // BoundVariable(0) refers to that binder, and references to the
        // original local binders shift up by 1.
        ExpressionPointer scrutineeTypeLiftedOnce =
            liftBoundVariables(scrutineeType, 1, 0);
        ExpressionPointer scrutineeKernelLiftedOnce =
            liftBoundVariables(scrutineeKernel, 1, 0);
        ExpressionPointer outerEqualityType = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {scrutineeUniverse}),
                    scrutineeTypeLiftedOnce),
                scrutineeKernelLiftedOnce),
            makeBoundVariable(0));

        std::vector<LocalBinder> extendedLocalBinders = localBinders;
        extendedLocalBinders.push_back(
            {caseScrutineeName, scrutineeType});
        extendedLocalBinders.push_back(
            {outerEqualityName, outerEqualityType});

        // (4) Construct the synthetic `SurfaceCases` whose scrutinee is
        // the new binder `caseScrutineeName` and whose arm bodies are
        // wrapped in
        //   function (equalityHypothesisName : X = <ctor pattern>) =>
        //     <original body>
        // so the equation binder is visible inside the user's body
        // while the rest of the surface elaboration runs unchanged.
        std::vector<SurfaceCasesClause> wrappedClauses;
        for (const auto& clause : cases.clauses) {
            SurfaceCasesClause wrappedClause;
            wrappedClause.pattern = clause.pattern;
            wrappedClause.line = clause.line;
            wrappedClause.column = clause.column;
            SurfaceExpressionPointer patternExpression =
                patternToSurfaceExpression(clause.pattern);
            // `cases.scrutinee = patternExpression` via the surface
            // binary-operator builder; the existing elaborator path
            // turns this into `Equality.{…}(T, X, ctorPattern)`.
            SurfaceExpressionPointer equationType =
                makeSurfaceBinaryOperation(
                    "=", cases.scrutinee, patternExpression,
                    clause.line, clause.column);
            SurfaceBinder equationBinder;
            equationBinder.names = {cases.equalityHypothesisName};
            equationBinder.type = equationType;
            equationBinder.isImplicit = false;
            wrappedClause.body = makeSurfaceLambda(
                std::move(equationBinder), clause.body,
                clause.line, clause.column);
            wrappedClauses.push_back(std::move(wrappedClause));
        }
        SurfaceExpressionPointer innerScrutinee = makeSurfaceIdentifier(
            caseScrutineeName, {}, line, column);
        SurfaceExpressionPointer syntheticCasesSurface =
            makeSurfaceCases(std::move(innerScrutinee),
                              std::move(wrappedClauses), line, column);

        // (5) Expected type for the inner cases, expressed in the
        // *extended* scope: `(eqInner : X = caseScrutineeVariable) → Goal`.
        // In closed form at extended depth: X lifted by 2, the
        // BoundVariable(1) reference to caseScrutineeVariable (depth + 2
        // means BV(0) is outerEqualityName, BV(1) is caseScrutineeName).
        ExpressionPointer scrutineeTypeLiftedTwice =
            liftBoundVariables(scrutineeType, 2, 0);
        ExpressionPointer scrutineeKernelLiftedTwice =
            liftBoundVariables(scrutineeKernel, 2, 0);
        ExpressionPointer innerEqualityType = makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {scrutineeUniverse}),
                    scrutineeTypeLiftedTwice),
                scrutineeKernelLiftedTwice),
            makeBoundVariable(1));
        // The Pi codomain lives one binder deeper than the extended
        // scope (i.e. orig + 3 binders total). Goal was closed at
        // orig, so lift by 3.
        ExpressionPointer goalLiftedByThree =
            liftBoundVariables(expectedType, 3, 0);
        ExpressionPointer innerExpectedType = makePi(
            "_innerEqualityHypothesisUnused",
            innerEqualityType, goalLiftedByThree);

        // (6) Elaborate the synthetic cases at the extended scope.
        ExpressionPointer innerCasesKernel = elaborateExpression(
            *syntheticCasesSurface, extendedLocalBinders,
            innerExpectedType);

        // (7) Apply the inner cases to outerEquality (BoundVariable(0)
        // at extended scope). The result has type `Goal` lifted by 2.
        ExpressionPointer appliedToOuter = makeApplication(
            innerCasesKernel, makeBoundVariable(0));

        // (8) Wrap in the two outer Lambdas (closing the convoy
        // binders).
        ExpressionPointer wrappedOuterEquality = makeLambda(
            outerEqualityName, outerEqualityType, appliedToOuter);
        ExpressionPointer wrappedCaseScrutinee = makeLambda(
            caseScrutineeName, scrutineeType, wrappedOuterEquality);

        // (9) Apply to (X, reflexivity(T, X)). reflexivity types as
        // `X = X`; the kernel reduces the outer Lambda's β to align
        // it with the Pi domain `X = caseScrutineeVariable`.
        ExpressionPointer reflexivityCall = makeApplication(
            makeApplication(
                makeConstant("reflexivity", {scrutineeUniverse}),
                scrutineeType),
            scrutineeKernel);
        ExpressionPointer fullyApplied = makeApplication(
            makeApplication(wrappedCaseScrutinee, scrutineeKernel),
            reflexivityCall);
        return fullyApplied;
        (void)column;
    }

    // `cases X refining h_1, …, h_N { case ctor: body … }` — the
    // "F1" sugar that automates the convoy pattern for binders whose
    // types mention the scrutinee.
    //
    // Desugars to:
    //
    //   (cases X {
    //      case ctor(args): function (h_1) (h_2) … (h_N) => body
    //      …
    //    } : (h_1 : T_h_1) → (h_2 : T_h_2) → … → (h_N : T_h_N) → Goal
    //   )(h_1, h_2, …, h_N)
    //
    // The inner-cases motive is `λ x. (h_1 : T_h_1(x)) → … → Goal(x)`,
    // so each arm's body has type `(h_1 : T_h_1(ctor(args))) → … →
    // Goal(ctor(args))` — the lambdas pick up the refined hypothesis
    // types via motive specialisation, no explicit annotation needed.
    // Outer application closes the chain by feeding the original
    // (unrefined-named-but-now-refined-at-this-case) binders back in.
    ExpressionPointer elaborateCasesWithRefining(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        if (!expectedType) {
            throwElaborate(
                "cases ... refining ... { ... } needs an expected "
                "type from context");
        }
        Frame frame(*this,
            "cases ... refining ... at line " + std::to_string(line));

        // (1) Resolve each refining name to its position in
        // localBinders (BoundVariable index from innermost) and its
        // type at depth localBinders.size() (lift from the depth at
        // which the binder was declared).
        int refiningCount = static_cast<int>(cases.refiningNames.size());
        std::vector<int> refiningBoundVariableIndices;
        std::vector<ExpressionPointer> refiningTypesAtOuterDepth;
        int totalBinders = static_cast<int>(localBinders.size());
        for (const auto& name : cases.refiningNames) {
            int positionInArray = -1;
            for (int i = totalBinders - 1; i >= 0; --i) {
                if (localBinders[i].name == name) {
                    positionInArray = i;
                    break;
                }
            }
            if (positionInArray < 0) {
                throwElaborate(
                    "cases ... refining " + name + ": no binder named '"
                    + name + "' is in scope");
            }
            refiningBoundVariableIndices.push_back(
                totalBinders - 1 - positionInArray);
            int liftAmount = totalBinders - positionInArray;
            refiningTypesAtOuterDepth.push_back(
                liftBoundVariables(
                    localBinders[positionInArray].type,
                    liftAmount, 0));
        }

        // (2) Build the wrapped expected type at the outer depth:
        //   Π (h_1 : T_1) Π (h_2 : T_2') … Π (h_N : T_N') Goal'
        // where each T_i' has references to h_1, …, h_{i-1} replaced
        // by the corresponding Π binder (and Goal' has all of h_1…h_N
        // replaced). This is the "generalize" / "revert" telescope
        // construction: we abstract one refining binder at a time,
        // starting from the innermost (h_N) and working outward.
        //
        // For each step, abstractOverBoundVariable shifts every OTHER
        // outer BV up by 1 to make room for the new Π's binder at
        // BV(0). So after `k` iterations, an outer BV originally at
        // index `j` (and not yet abstracted) lives at `j + k`. The
        // domain of the Π we're constructing must also be abstracted
        // against any refining binder we've already moved into the
        // chain — that's what the inner loop on `j` does for each T_i.
        ExpressionPointer wrappedExpectedType = expectedType;
        for (int i = refiningCount - 1; i >= 0; --i) {
            // abstractOverBoundVariable tracks binder depth itself —
            // we always pass the binder's *outer* BV index (relative
            // to depth = totalBinders), and the function lifts other
            // references for us.
            int outerIdx = refiningBoundVariableIndices[i];
            wrappedExpectedType = abstractOverBoundVariable(
                wrappedExpectedType, outerIdx);
            // T_i itself may reference any refining binder we already
            // moved into the chain (those at j > i, which were
            // processed first because we iterate in reverse). Apply
            // the same abstractions to T_i.
            ExpressionPointer domain = refiningTypesAtOuterDepth[i];
            for (int j = refiningCount - 1; j > i; --j) {
                domain = abstractOverBoundVariable(
                    domain, refiningBoundVariableIndices[j]);
            }
            wrappedExpectedType = makePi(
                cases.refiningNames[i],
                std::move(domain),
                std::move(wrappedExpectedType));
        }

        // (3) Wrap each clause body in `function (h_1) (h_2) … (h_N)
        // => body`. The lambda binders use the same names the user
        // wrote, shadowing the outer same-named binders inside the
        // body. No type annotations on the lambdas — the motive-
        // derived domain tells each lambda what its parameter type is.
        //
        // The shadowing requires the elaborator's opening pass to
        // generate distinct FreeVariable names for the inner lambda
        // binders so unification (e.g., implicit-arg inference inside
        // Equality.symmetry) doesn't confuse them with the outer
        // binders. We rely on openingNameFor's collision-avoidance
        // for that.
        std::vector<SurfaceCasesClause> wrappedClauses;
        for (const auto& clause : cases.clauses) {
            SurfaceExpressionPointer body = clause.body;
            for (int i = refiningCount - 1; i >= 0; --i) {
                SurfaceBinder binder;
                binder.names = {cases.refiningNames[i]};
                binder.type = nullptr;
                binder.isImplicit = false;
                body = makeSurfaceLambda(
                    std::move(binder), body,
                    clause.line, clause.column);
            }
            SurfaceCasesClause wrappedClause;
            wrappedClause.pattern = clause.pattern;
            wrappedClause.body = std::move(body);
            wrappedClause.line = clause.line;
            wrappedClause.column = clause.column;
            wrappedClauses.push_back(std::move(wrappedClause));
        }
        SurfaceExpressionPointer syntheticCases = makeSurfaceCases(
            cases.scrutinee, std::move(wrappedClauses), line, column);

        // (4) Elaborate the synthetic cases against the wrapped Pi
        // chain.
        ExpressionPointer innerCasesKernel = elaborateExpression(
            *syntheticCases, localBinders, wrappedExpectedType);

        // (5) Apply the result to (h_1, h_2, …, h_N), each as a
        // BoundVariable reference into the outer context. The kernel
        // unwinds the Pi chain at the original Goal type.
        for (int i = 0; i < refiningCount; ++i) {
            innerCasesKernel = makeApplication(
                std::move(innerCasesKernel),
                makeBoundVariable(refiningBoundVariableIndices[i]));
        }
        return innerCasesKernel;
    }

    // `note goal : T;` / `note <prop>;` — elaboration-time assertions
    // that don't change the proof state. Both desugar to the rest of
    // the block elaborated at the unchanged expected type, but the
    // elaborator runs a check first:
    //   `note goal : T` — check that the declared T is definitionally
    //     equal to the current expected type. On mismatch, error
    //     pointing at the noted form vs the actual goal.
    //   `note P` — elaborate P as a Proposition and run the
    //     auto-prover on it. If the prover can't close P, error.
    // The returned term is the body's elaboration: nothing about the
    // assertion remains in the produced kernel term.
    ExpressionPointer elaborateNoteExpression(
        const SurfaceNote& note,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "note at line " + std::to_string(line),
            localBinders, expectedType, line, /*column=*/0);
        if (note.goalType) {
            if (!expectedType) {
                throwElaborate(
                    "`note goal : T` needs an expected type from "
                    "context (none available at line "
                    + std::to_string(line) + ")");
            }
            ExpressionPointer declaredKernel = elaborateExpression(
                *note.goalType, localBinders);
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            ExpressionPointer declaredOpen = openOverLocalBinders(
                declaredKernel, localBinders, localBinders.size());
            ExpressionPointer expectedOpen = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            if (!isDefinitionallyEqual(
                    environment_, openedContext,
                    declaredOpen, expectedOpen)) {
                throwElaborate(
                    std::string("`note goal :` mismatch at line ")
                    + std::to_string(line) + ":\n"
                    + "  noted form:    "
                    + prettyPrintInLocalScope(declaredKernel, localBinders)
                    + "\n  actual goal:   "
                    + prettyPrintInLocalScope(expectedType, localBinders));
            }
        } else if (note.proposition) {
            ExpressionPointer propKernel = elaborateExpression(
                *note.proposition, localBinders,
                makeSort(makeLevelConst(0)));
            try {
                (void)autoProveClaim(propKernel, localBinders, line);
            } catch (const ElaborateError&) {
                throwElaborate(
                    std::string("`note <proposition>` at line ")
                    + std::to_string(line)
                    + ": the auto-prover could not close the noted "
                    "proposition: "
                    + prettyPrintInLocalScope(propKernel, localBinders));
            } catch (const TypeError&) {
                throwElaborate(
                    std::string("`note <proposition>` at line ")
                    + std::to_string(line)
                    + ": the auto-prover raised a type error on the "
                    "noted proposition: "
                    + prettyPrintInLocalScope(propKernel, localBinders));
            }
        } else {
            throwElaborate(
                "internal: SurfaceNote with neither goalType nor "
                "proposition set");
        }
        return elaborateExpression(*note.body, localBinders, expectedType);
    }

    // `decide P { | yes m => arm_yes | no n => arm_no }` — classical
    // case-split on whether P holds, hiding the auto-transport
    // bookkeeping the user would otherwise write by hand.
    //
    // The expected type Goal must mention `Logic.classical_decidable(P)`
    // structurally (after WHNF + structural deep-β attempts). We
    // abstract that occurrence to form a motive
    //   motive = λ s : Logic.Decidable(P). Goal[s/X]
    // and build the recursor application
    //   Logic.Decidable_recursor.{u}(P, motive, λp. arm_yes, λn. arm_no, X)
    // where `u` is the universe level of Goal (typically 0 since we're
    // proving a Proposition). Each arm body's expected type is
    // motive(yes(p)) / motive(no(n)) — which the kernel β/ι-reduces in
    // surrounding wrappers like `bisectionStepWithDec(…, decision)`,
    // so the user just writes the math witness without any explicit
    // transport.
    ExpressionPointer elaborateDecideExpression(
        const SurfaceDecide& decide,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "decide expression at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "decide P { … } needs an expected type from context");
        }
        // (1) Elaborate the proposition P (with expected type
        // Proposition = Sort(0)).
        ExpressionPointer propositionKernel = elaborateExpression(
            *decide.proposition, localBinders, makeSort(makeLevelConst(0)));

        // (2) Build the scrutinee X = Logic.classical_decidable(P).
        ExpressionPointer scrutineeKernel = makeApplication(
            makeConstant("Logic.classical_decidable", {}),
            propositionKernel);

        // (3) Build Logic.Decidable(P) — the scrutinee's type.
        ExpressionPointer decidablePType = makeApplication(
            makeConstant("Logic.Decidable", {}),
            propositionKernel);

        // (4) Abstract every structural occurrence of X in expectedType
        // to form the motive's body. The user may have written P in
        // terms of in-scope let-binders (e.g.
        //   let intervals := bisectionIntervals(…);
        //   decide IsUpperBound(subset, halve(left(intervals) + right(intervals))) {…}
        // ) but the goal type predates the let-bindings and inlines
        // their values. ζ-unfold the target's let-references so its
        // literal form matches the goal's structure.
        ExpressionPointer targetReduced = zetaUnfoldLetBinders(
            scrutineeKernel, localBinders, /*currentDepth=*/0);
        std::string targetHeadName =
            applicationHeadConstantName(targetReduced);
        int occurrences = 0;
        int whnfFuel = 2048;
        ExpressionPointer motiveBody = abstractStructuralOccurrenceWithWHNF(
            expectedType, targetReduced, targetHeadName,
            /*currentDepth=*/0, occurrences, whnfFuel);
        if (occurrences == 0) {
            // No occurrence of `Logic.classical_decidable(P)` in the
            // goal — use a constant motive `λs. Goal`. The arms each
            // prove the goal directly without reduction. This is the
            // proposition-only case (the user just wants `if P then …
            // else …` reasoning, no value-level branching threaded
            // through the goal). Lift expectedType by 1 to leave a
            // free BV(0) for the motive's target parameter.
            motiveBody = liftBoundVariables(
                expectedType, /*increment=*/1, /*threshold=*/0);
        }

        // (5) Infer the motive's universe (Goal's level). For
        // Proposition-valued Goals this is 0; for Type-valued Goals it
        // can be higher. Compute by inferring the type of expectedType
        // and reading its Sort level.
        LevelPointer motiveLevel;
        {
            Context openedContext = buildContextFromLocalBinders(localBinders);
            ExpressionPointer goalOpenedForLevel = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            ExpressionPointer goalType = inferType(
                environment_, openedContext, goalOpenedForLevel);
            ExpressionPointer goalTypeWHNF = weakHeadNormalForm(
                environment_, goalType);
            auto* sortNode = std::get_if<Sort>(&goalTypeWHNF->node);
            if (!sortNode) {
                throwElaborate(
                    "decide P { … } at line " + std::to_string(line)
                    + ": goal's type does not normalise to a Sort");
            }
            motiveLevel = sortNode->level;
        }

        // (6) Build motive M = Lambda(_decideTarget : Decidable(P), motiveBody).
        ExpressionPointer motive = makeLambda(
            "_decideTarget", decidablePType, motiveBody);

        // (7) Build each arm. For yes: lambda over a binder of type P,
        // body elaborated at motiveBody[yes(P, BV(0))/BV(0)] in the
        // extended scope. Similarly for no with Not(P).
        const std::string yesBinder =
            decide.yesBinderName.empty() ? std::string("_") : decide.yesBinderName;
        const std::string noBinder =
            decide.noBinderName.empty() ? std::string("_") : decide.noBinderName;

        // P lifted into the arm's body scope (one binder added).
        ExpressionPointer propositionLifted =
            liftBoundVariables(propositionKernel, 1, 0);

        // yes(P_lifted, BV(0)) — the constructor applied to the arm's binder.
        ExpressionPointer yesAppliedToBinder = makeApplication(
            makeApplication(
                makeConstant("Logic.Decidable.yes", {}),
                propositionLifted),
            makeBoundVariable(0));
        // no(P_lifted, BV(0)) — similar.
        ExpressionPointer noAppliedToBinder = makeApplication(
            makeApplication(
                makeConstant("Logic.Decidable.no", {}),
                propositionLifted),
            makeBoundVariable(0));

        // The motive's body was built with BV(0) bound to the motive's
        // target (Decidable(P)) parameter, with localBinder refs at
        // BV(1..N). We want the arm's expected type in the extended
        // scope `localBinders + [armBinder]`, where BV(0) is the arm
        // binder and BV(1..N) are the localBinders.
        //
        // `substitute(motiveBody, 0, value)` β-reduces, replacing
        // BV(0) with `value` AND decrementing every other BV by 1 (as
        // if the motive's binder is being removed). That would mis-
        // align the localBinder refs in the extended scope. To keep
        // them aligned, first lift motiveBody by 1 above its motive-
        // target binder (BV(0) stays, BV(K+1) → BV(K+2)); then
        // substitute, which restores BV(K+2) → BV(K+1) — exactly the
        // localBinder slots in the extended scope.
        ExpressionPointer motiveBodyLifted =
            liftBoundVariables(motiveBody, /*increment=*/1,
                                /*threshold=*/1);
        ExpressionPointer yesArmExpectedType =
            substitute(motiveBodyLifted, 0, yesAppliedToBinder);
        ExpressionPointer noArmExpectedType =
            substitute(motiveBodyLifted, 0, noAppliedToBinder);

        // Not(P) for the no arm's binder.
        ExpressionPointer notP = makeApplication(
            makeConstant("Not", {}), propositionKernel);

        // Yes arm scope: extend with the binder.
        std::vector<LocalBinder> yesScope = localBinders;
        yesScope.push_back({yesBinder, propositionKernel});
        ExpressionPointer yesBodyElab = elaborateExpression(
            *decide.yesBody, yesScope, yesArmExpectedType);
        ExpressionPointer yesArm = makeLambda(
            yesBinder, propositionKernel, yesBodyElab);

        std::vector<LocalBinder> noScope = localBinders;
        noScope.push_back({noBinder, notP});
        ExpressionPointer noBodyElab = elaborateExpression(
            *decide.noBody, noScope, noArmExpectedType);
        ExpressionPointer noArm = makeLambda(
            noBinder, notP, noBodyElab);

        // (8) Build the recursor application:
        // Logic.Decidable_recursor.{u}(P, motive, yesArm, noArm, X).
        ExpressionPointer recursorCall = makeConstant(
            "Logic.Decidable_recursor", {motiveLevel});
        recursorCall = makeApplication(recursorCall, propositionKernel);
        recursorCall = makeApplication(recursorCall, motive);
        recursorCall = makeApplication(recursorCall, yesArm);
        recursorCall = makeApplication(recursorCall, noArm);
        recursorCall = makeApplication(recursorCall, scrutineeKernel);
        // Pre-typecheck the assembled application to produce a
        // detailed error before the kernel's generic "Application:
        // argument type does not match Pi domain" message hits. We
        // open over localBinders so inferType can walk freely; on
        // failure, dump every arg with its expected/actual types so
        // the diagnostic points at which slot is the culprit.
        try {
            Context openedContext =
                buildContextFromLocalBinders(localBinders);
            ExpressionPointer openedCall = openOverLocalBinders(
                recursorCall, localBinders, localBinders.size());
            (void)inferType(environment_, openedContext, openedCall);
        } catch (const TypeError& kernelError) {
            const std::string scope =
                std::string("decide expression at line ")
                + std::to_string(line);
            std::string detail;
            detail += scope + ":\n  kernel rejected the assembled\n"
                      "  Logic.Decidable_recursor application —\n  ";
            detail += kernelError.what();
            detail += "\n\n  Args, in application order:\n";
            const std::vector<std::pair<std::string, ExpressionPointer>>
                argSlots = {
                    {"(1) proposition P", propositionKernel},
                    {"(2) motive (Decidable(P) -> Sort u)", motive},
                    {"(3) yes case ((p:P) -> motive(yes P p))", yesArm},
                    {"(4) no case ((np:Not P) -> motive(no P np))", noArm},
                    {"(5) scrutinee (Decidable P)", scrutineeKernel},
                };
            for (const auto& slot : argSlots) {
                detail += "    " + slot.first + ":\n";
                detail += "      term: "
                       + prettyPrintInLocalScope(slot.second, localBinders)
                       + "\n";
                try {
                    Context ctx =
                        buildContextFromLocalBinders(localBinders);
                    ExpressionPointer openedSlot = openOverLocalBinders(
                        slot.second, localBinders, localBinders.size());
                    ExpressionPointer slotType = inferType(
                        environment_, ctx, openedSlot);
                    ExpressionPointer slotTypeClosed = closeOverLocalBinders(
                        slotType, localBinders, localBinders.size());
                    detail += "      type: "
                           + prettyPrintInLocalScope(
                                 slotTypeClosed, localBinders)
                           + "\n";
                } catch (const TypeError& ignored) {
                    detail += "      type: <could not infer: ";
                    detail += ignored.what();
                    detail += ">\n";
                }
            }
            throwElaborate(detail);
        }
        return recursorCall;
    }

    // `cases scrutinee { | pattern => body | ... }`. Phase 1 covers
    // non-indexed inductives only. Re-uses the existing
    // `buildCaseLambda` helper by synthesizing a minimal pattern-match
    // declaration whose cases mirror the user's clauses.
    ExpressionPointer elaborateCasesExpression(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // The `cases X refining h1, h2, … { … }` variant lifts the
        // listed binders into the recursor's motive so each arm sees
        // the refined types automatically. Routes through a dedicated
        // desugaring; cannot be combined with `with equalityHypothesisName`
        // (they're orthogonal but no use site has needed both yet).
        if (!cases.refiningNames.empty()) {
            if (!cases.equalityHypothesisName.empty()) {
                throwElaborate(
                    "cases ... with <eq> refining ... is not supported; "
                    "use one or the other");
            }
            return elaborateCasesWithRefining(
                cases, localBinders, expectedType, line, column);
        }
        // The `cases X with equalityHypothesisName { … }` variant
        // routes through a dedicated convoy desugaring; everything
        // below is the plain `cases X { … }` path.
        if (!cases.equalityHypothesisName.empty()) {
            return elaborateCasesWithEqualityHypothesis(
                cases, localBinders, expectedType, line, column);
        }

        Frame frame(*this,
            "cases expression at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "needs an expected type from context — wrap with an "
                "ascription `(cases … : T)` or supply one via context");
        }

        // Elaborate scrutinee + infer + normalise type. The inferred type
        // comes back in "opened" form — local-binder references are
        // Internal-origin FreeVariables. Decompose the opened form to
        // find the inductive head, then close every piece we plan to
        // embed in the motive or pass to buildCaseLambda so they're back
        // in BoundVariable form.
        ExpressionPointer scrutinee =
            elaborateExpression(*cases.scrutinee, localBinders);
        ExpressionPointer scrutineeTypeOpened = weakHeadNormalForm(
            environment_, inferTypeInLocalContext(localBinders, scrutinee));

        std::vector<ExpressionPointer> inductiveArguments;
        ExpressionPointer cursor = scrutineeTypeOpened;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            inductiveArguments.insert(inductiveArguments.begin(),
                                       application->argument);
            cursor = weakHeadNormalForm(environment_, application->function);
        }
        auto* constant = std::get_if<Constant>(&cursor->node);
        if (!constant) {
            throw ElaborateError(
                "cases scrutinee at line " + std::to_string(line)
                + ": type's head is not an inductive constant after "
                "normalisation");
        }
        // Quotient is not an inductive — it's an axiomatic kernel
        // primitive eliminated via `Quotient.induct`. When the scrutinee
        // is a value of `Quotient.{u}(T, R)` and the user supplied a
        // single clause `Quotient.mk(rep) => body`, dispatch to a
        // dedicated handler that builds the induct application directly.
        // This is the "WLOG pick a representative" sugar — the
        // mathematician's natural reading of a quotient elimination.
        if (constant->name == "Quotient") {
            return elaborateQuotientCases(
                cases, scrutinee, scrutineeTypeOpened,
                inductiveArguments, *constant,
                localBinders, expectedType, line, column);
        }
        const Declaration* inductiveDecl =
            environment_.lookup(constant->name);
        auto* inductive = inductiveDecl
            ? std::get_if<Inductive>(inductiveDecl) : nullptr;
        if (!inductive) {
            throw ElaborateError(
                "cases scrutinee at line " + std::to_string(line)
                + ": type '" + constant->name + "' is not an inductive");
        }
        if (static_cast<int>(inductiveArguments.size())
            < inductive->numParameters) {
            throw ElaborateError(
                "cases at line " + std::to_string(line)
                + ": inductive '" + constant->name + "' applied to fewer "
                  "than its parameter count");
        }
        // Close every piece coming out of opened-form inference back to
        // local-binder BoundVariables. The motive and parameterValues
        // passed to buildCaseLambda must live in the same scope as
        // localBinders (BoundVariables, not Internal FreeVariables).
        ExpressionPointer scrutineeType = closeOverLocalBinders(
            scrutineeTypeOpened, localBinders, localBinders.size());
        std::vector<ExpressionPointer> parameterValues;
        for (int p = 0; p < inductive->numParameters; ++p) {
            parameterValues.push_back(closeOverLocalBinders(
                inductiveArguments[p], localBinders,
                localBinders.size()));
        }
        std::vector<ExpressionPointer> indexValues(
            inductiveArguments.begin() + inductive->numParameters,
            inductiveArguments.end());
        // For indexed inductives, each index must be a distinct local
        // variable BoundVariable. The motive will abstract over those
        // variables, and the recursor will take their values back as
        // arguments after the case lambdas.
        std::vector<int> indexLocalIndices;
        for (size_t k = 0; k < indexValues.size(); ++k) {
            // After closeOverLocalBinders the value is in localBinders'
            // BoundVariable form. Look up the index value's variable.
            ExpressionPointer indexClosed = closeOverLocalBinders(
                indexValues[k], localBinders, localBinders.size());
            auto* boundVariable =
                std::get_if<BoundVariable>(&indexClosed->node);
            if (!boundVariable) {
                throw ElaborateError(
                    "cases at line " + std::to_string(line)
                    + ": index " + std::to_string(k)
                    + " of scrutinee type must be a local variable");
            }
            int idx = boundVariable->deBruijnIndex;
            if (idx < 0
                || idx >= static_cast<int>(localBinders.size())) {
                throw ElaborateError(
                    "cases at line " + std::to_string(line)
                    + ": index " + std::to_string(k)
                    + " of scrutinee type references an out-of-scope "
                      "binder");
            }
            for (int seen : indexLocalIndices) {
                if (seen == idx) {
                    throw ElaborateError(
                        "cases at line " + std::to_string(line)
                        + ": the same local variable is used for "
                          "two different scrutinee indices");
                }
            }
            indexLocalIndices.push_back(idx);
            // Replace the opened-form index value with its closed form
            // so downstream code uses local-binder BoundVariables.
            indexValues[k] = indexClosed;
        }
        const std::vector<LevelPointer>& inductiveUniverseArguments =
            constant->universeArguments;

        // Look up the recursor.
        std::string recursorName = constant->name + "_recursor";
        const Declaration* recursorDecl =
            environment_.lookup(recursorName);
        if (!recursorDecl) {
            throw ElaborateError(
                "cases at line " + std::to_string(line)
                + ": no recursor for inductive '" + constant->name + "'");
        }
        auto* recursor = std::get_if<Recursor>(recursorDecl);
        if (!recursor) {
            throw ElaborateError(
                "cases at line " + std::to_string(line)
                + ": '" + recursorName + "' is not a recursor");
        }

        // Build the motive. The structure depends on whether the
        // inductive is indexed and whether the scrutinee is a local
        // variable:
        //
        //   motive = Lambda(idx_0, T_0,
        //              Lambda(idx_1, T_1,
        //                …
        //                Lambda(target, ScrutTypeInMotive,
        //                  expectedType abstracted over [idx_0, …, scrutVar]))).
        //
        // Each index's BoundVariable in expectedType is replaced with
        // the corresponding motive-bound index variable; the
        // scrutinee variable (if local) is replaced with the target
        // binder; other references are shifted up by N+1 (N indices
        // plus 1 target).
        int scrutineeLocalIndex = -1;
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&scrutinee->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= 0
                && index < static_cast<int>(localBinders.size())) {
                scrutineeLocalIndex = index;
            }
        }
        // Build the abstraction list: indices first (outermost
        // Lambdas), then the scrutinee variable (innermost / target).
        std::vector<int> abstractionList = indexLocalIndices;
        if (scrutineeLocalIndex >= 0) {
            abstractionList.push_back(scrutineeLocalIndex);
        }
        ExpressionPointer motiveBody;
        if (!abstractionList.empty()) {
            motiveBody =
                abstractOverBoundVariables(expectedType, abstractionList);
        } else {
            motiveBody = shift(expectedType, 1);
        }
        // Compute the scrutinee type as it should appear in the
        // motive's target-Lambda position (i.e., after the index
        // Lambdas have been wrapped but before the target Lambda is).
        // The scrutinee type lives in localBinders scope; abstracting
        // it over the indices yields the same value in
        // {localBinders - indices + index_Lambdas} scope.
        ExpressionPointer scrutineeTypeInMotive;
        if (indexLocalIndices.empty()) {
            scrutineeTypeInMotive = scrutineeType;
        } else {
            scrutineeTypeInMotive = abstractOverBoundVariables(
                scrutineeType, indexLocalIndices);
        }
        // Wrap motiveBody with the innermost Lambda (target), using
        // scrutineeTypeInMotive as its domain.
        ExpressionPointer motive = makeLambda(
            "_cases_target", scrutineeTypeInMotive, motiveBody);
        // For each index, wrap with another outer Lambda. We walk in
        // reverse so the OUTERMOST Lambda (indices[0]) ends up last.
        // `indexLocalIndices[k]` is a de Bruijn index; convert to the
        // localBinders array position by inverting against size.
        for (int k = static_cast<int>(indexLocalIndices.size()) - 1;
             k >= 0; --k) {
            int deBruijn = indexLocalIndices[k];
            int arrayPosition = static_cast<int>(localBinders.size())
                - 1 - deBruijn;
            ExpressionPointer indexType =
                localBinders[arrayPosition].type;
            motive = makeLambda(localBinders[arrayPosition].name,
                                 indexType, motive);
        }

        // Infer the motive's universe level by asking the kernel for
        // its type (a Pi ending in a Sort). Local binders' types may
        // reference earlier locals, so open them via openOverLocalBinders.
        LevelPointer motiveLevel;
        {
            Context openedContext = buildContextFromLocalBinders(localBinders);
            ExpressionPointer motiveType =
                inferType(environment_, openedContext,
                           openOverLocalBinders(
                               motive, localBinders,
                               localBinders.size()));
            ExpressionPointer motiveCursor = motiveType;
            while (auto* pi = std::get_if<Pi>(&motiveCursor->node)) {
                motiveCursor = pi->codomain;
            }
            auto* sortNode = std::get_if<Sort>(&motiveCursor->node);
            if (!sortNode) {
                throw ElaborateError(
                    "internal: cases motive type doesn't end in a Sort "
                    "(line " + std::to_string(line) + ")");
            }
            motiveLevel = sortNode->level;
        }

        // Build a synthetic pattern-match declaration so we can reuse
        // buildCaseLambda. Each user clause becomes a SurfacePatternCase
        // with a single pattern. Tuple patterns are first translated to
        // constructor patterns (only meaningful for single-constructor
        // inductives — checked here).
        SurfaceDefinitionDeclaration syntheticDeclaration;
        // The synthetic name is used only by rewriteRecursiveCalls,
        // which looks for calls of this name in the case body. We pick
        // a name no user would write so it can never match.
        syntheticDeclaration.name =
            "_cases_at_line_" + std::to_string(line)
            + "_column_" + std::to_string(column);
        syntheticDeclaration.isTheorem = false;
        for (const auto& clause : cases.clauses) {
            SurfacePatternPointer pattern = clause.pattern;
            SurfaceExpressionPointer body = clause.body;
            if (auto* tupleNode = std::get_if<SurfacePatternTuple>(
                    &pattern->node)) {
                if (inductive->constructorNames.size() != 1) {
                    throw ElaborateError(
                        "cases at line " + std::to_string(clause.line)
                        + ": anonymous tuple pattern '⟨...⟩' only works "
                          "for single-constructor inductives, but '"
                        + constant->name + "' has "
                        + std::to_string(
                            inductive->constructorNames.size())
                        + " constructors");
                }
                const std::string& ctorName =
                    inductive->constructorNames[0];
                const Declaration* ctorDecl =
                    environment_.lookup(ctorName);
                auto* ctorDeclaration = ctorDecl
                    ? std::get_if<Constructor>(ctorDecl) : nullptr;
                if (!ctorDeclaration) {
                    throw ElaborateError(
                        "cases at line " + std::to_string(clause.line)
                        + ": constructor '" + ctorName
                        + "' missing from environment");
                }
                int totalPi = countLeadingPis(ctorDeclaration->type);
                int valueArgCount =
                    totalPi - inductive->numParameters;
                size_t componentCount = tupleNode->components.size();
                if (static_cast<int>(componentCount) == valueArgCount) {
                    pattern = makeSurfacePatternConstructor(
                        ctorName, tupleNode->components,
                        clause.line, clause.column);
                } else if (valueArgCount == 2 && componentCount > 2) {
                    // Right-associate: outer pattern binds first
                    // component directly and a fresh name for the rest;
                    // body is wrapped in an inner cases that
                    // destructures the rest via a tuple pattern with
                    // one fewer component.
                    std::string freshName =
                        "_tupleRest_" + std::to_string(line) + "_"
                        + std::to_string(clause.line) + "_"
                        + std::to_string(clause.column);
                    std::vector<SurfacePatternPointer> outerArgs;
                    outerArgs.push_back(tupleNode->components[0]);
                    outerArgs.push_back(makeSurfacePatternBareName(
                        freshName, clause.line, clause.column));
                    pattern = makeSurfacePatternConstructor(
                        ctorName, std::move(outerArgs),
                        clause.line, clause.column);
                    std::vector<SurfacePatternPointer> restComponents(
                        tupleNode->components.begin() + 1,
                        tupleNode->components.end());
                    SurfacePatternPointer restPattern =
                        makeSurfacePatternTuple(
                            std::move(restComponents),
                            clause.line, clause.column);
                    SurfaceExpressionPointer freshReference =
                        makeSurfaceIdentifier(freshName, {},
                                               clause.line, clause.column);
                    SurfaceCasesClause innerClause;
                    innerClause.pattern = std::move(restPattern);
                    innerClause.body = body;
                    innerClause.line = clause.line;
                    innerClause.column = clause.column;
                    std::vector<SurfaceCasesClause> innerClauses;
                    innerClauses.push_back(std::move(innerClause));
                    body = makeSurfaceCases(
                        std::move(freshReference),
                        std::move(innerClauses),
                        clause.line, clause.column);
                } else {
                    throw ElaborateError(
                        "cases at line " + std::to_string(clause.line)
                        + ": anonymous tuple pattern has "
                        + std::to_string(componentCount)
                        + " component(s) but constructor '" + ctorName
                        + "' takes " + std::to_string(valueArgCount));
                }
            }
            SurfacePatternCase patternCase;
            patternCase.patterns.push_back(std::move(pattern));
            patternCase.body = std::move(body);
            patternCase.line = clause.line;
            patternCase.column = clause.column;
            syntheticDeclaration.cases.push_back(std::move(patternCase));
        }

        // Build a case lambda for each constructor (in declared order).
        std::vector<ExpressionPointer> caseLambdas;
        for (const auto& constructorName : inductive->constructorNames) {
            caseLambdas.push_back(buildCaseLambda(
                syntheticDeclaration, constructorName, constant->name,
                inductiveUniverseArguments, motive, parameterValues,
                localBinders));
        }

        // Assemble the recursor call. For large-eliminating recursors
        // the motive's universe level is an additional universe arg
        // appended after the inductive's own universe args.
        bool recursorHasMotiveLevel =
            recursor->universeParameters.size()
            > inductive->universeParameters.size();
        std::vector<LevelPointer> recursorUniverseArguments =
            inductiveUniverseArguments;
        if (recursorHasMotiveLevel) {
            recursorUniverseArguments.push_back(motiveLevel);
        }
        ExpressionPointer applied =
            makeConstant(recursorName,
                          std::move(recursorUniverseArguments));
        for (const auto& parameterValue : parameterValues) {
            applied = makeApplication(applied, parameterValue);
        }
        applied = makeApplication(applied, motive);
        for (auto& caseLambda : caseLambdas) {
            applied =
                makeApplication(applied, std::move(caseLambda));
        }
        // Apply index values in scrutinee order, then the scrutinee
        // itself. For non-indexed inductives this loop is empty.
        for (const auto& indexValue : indexValues) {
            applied = makeApplication(applied, indexValue);
        }
        applied = makeApplication(applied, scrutinee);
        return applied;
    }

    ExpressionPointer elaborateIdentifier(
        const SurfaceIdentifier& identifier,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {

        for (int i = static_cast<int>(localBinders.size()) - 1; i >= 0; --i) {
            if (localBinders[i].name == identifier.qualifiedName) {
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                if (!identifier.universeArgs.empty()) {
                    throw ElaborateError(
                        "local variable '" + identifier.qualifiedName
                        + "' cannot take universe arguments (line "
                        + std::to_string(line) + ")");
                }
                return makeBoundVariable(deBruijnIndex);
            }
        }
        bool isCurrentDeclaration =
            !currentDeclarationName_.empty()
            && currentDeclarationName_ == identifier.qualifiedName;
        const Declaration* environmentDeclaration =
            environment_.lookup(identifier.qualifiedName);
        if (!isCurrentDeclaration && !environmentDeclaration) {
            throw ElaborateError(
                "unknown identifier '" + identifier.qualifiedName
                + "' at line " + std::to_string(line)
                + ", column " + std::to_string(column));
        }
        std::vector<LevelPointer> universeArguments;
        if (!identifier.universeArgs.empty()) {
            for (const auto& level : identifier.universeArgs) {
                universeArguments.push_back(elaborateLevel(*level));
            }
        } else if (isCurrentDeclaration
                   && !currentUniverseParametersOrdered_.empty()) {
            // Self-reference auto-fill: when the inductive or theorem
            // currently being declared mentions itself, the universe
            // arguments are exactly its own universe parameters.
            // External references must always be explicit — universe
            // inference is left for a future iteration.
            for (const auto& parameterName :
                 currentUniverseParametersOrdered_) {
                universeArguments.push_back(makeLevelParam(parameterName));
            }
        } else if (environmentDeclaration
                   && universeParameterCount(*environmentDeclaration) > 0) {
            throw ElaborateError(
                "constant '" + identifier.qualifiedName + "' requires "
                + std::to_string(
                      universeParameterCount(*environmentDeclaration))
                + " universe argument(s); supply them explicitly with "
                ".{...} at line " + std::to_string(line));
        }
        return makeConstant(identifier.qualifiedName,
                            std::move(universeArguments));
    }

    // Counts the number of leading Pi binders in a kernel type. Used
    // for under-application detection at constructor call sites.
    static int countLeadingPis(ExpressionPointer type) {
        int count = 0;
        ExpressionPointer cursor = type;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            ++count;
            cursor = pi->codomain;
        }
        return count;
    }

    // Determines the universe arguments to use when elaborating a
    // constructor call without explicit `.{...}`. Tries, in order:
    //   1. If expectedType reduces to a head Constant for the same
    //      inductive, use its universe arguments.
    //   2. Otherwise, fall back to zeros (suitable for Proposition-
    //      valued inductives; for Type-polymorphic inductives the user
    //      should supply `.{u}` if zeros don't fit).
    std::vector<LevelPointer> universeArgumentsForConstructorCall(
        const Constructor& constructor,
        const Inductive& inductive,
        ExpressionPointer expectedType) {
        const size_t universeParameterCount =
            constructor.universeParameters.size();
        if (universeParameterCount == 0) return {};
        if (expectedType) {
            ExpressionPointer cursor =
                weakHeadNormalForm(environment_, expectedType);
            while (auto* application =
                       std::get_if<Application>(&cursor->node)) {
                cursor = application->function;
            }
            if (auto* constant =
                    std::get_if<Constant>(&cursor->node)) {
                if (constant->name == constructor.inductiveName
                    && constant->universeArguments.size()
                       == universeParameterCount) {
                    return constant->universeArguments;
                }
            }
        }
        (void)inductive;
        std::vector<LevelPointer> zeros;
        for (size_t i = 0; i < universeParameterCount; ++i) {
            zeros.push_back(makeLevelConst(0));
        }
        return zeros;
    }

    // Elaborates a call to a constructor where the user has omitted the
    // inductive's parameter arguments — e.g. `And.introduction(a, b)`
    // instead of `And.introduction(A, B, a, b)`. Infers each parameter
    // by (a) elaborating value args, inferring their types, and
    // unifying against the constructor's value-arg domains, and
    // (b) if any parameters remain unassigned and an expectedType is
    // provided, unifying the constructor's result type against
    // expectedType.
    // Generalised leading-argument inference. Takes a declaration's
    // (universe-substituted) type, the count of leading Pis to treat as
    // inferable metavariables, and the user-supplied trailing arguments.
    // Returns a vector of inferred kernel terms for the leading positions
    // (in declaration order) plus a vector of elaborated trailing args.
    //
    // The unification machinery is shared with constructor parameter
    // inference: open the leading Pis as Internal-origin FreeVariables,
    // backward-unify the result type against `expectedType` if available,
    // then elaborate each trailing arg in order and unify its inferred
    // type against the Pi domain (with previously-resolved metavariables
    // substituted).
    struct CallInferenceResult {
        std::vector<ExpressionPointer> leadingValues;     // inferred
        std::vector<ExpressionPointer> trailingValues;    // user args
    };
    CallInferenceResult inferLeadingArguments(
        const std::string& diagnosticName,
        ExpressionPointer instantiatedDeclarationType,
        int numLeadingToInfer,
        const std::vector<SurfaceExpressionPointer>& trailingArgumentsSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        const std::string& metavariablePrefix,
        int line) {

        // Open each leading Pi with an Internal-origin FreeVariable
        // serving as a metavariable.
        std::vector<std::string> leadingFreshNames;
        std::set<std::string> metavariableNames;
        ExpressionPointer cursor = instantiatedDeclarationType;
        for (int i = 0; i < numLeadingToInfer; ++i) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "internal: declaration '" + diagnosticName
                    + "' has fewer leading Pis than expected (line "
                    + std::to_string(line) + ")");
            }
            std::string fresh =
                metavariablePrefix + std::to_string(i) + "_"
                + diagnosticName;
            leadingFreshNames.push_back(fresh);
            metavariableNames.insert(fresh);
            cursor = openBinder(pi->codomain, fresh,
                                 FreeVariableOrigin::Internal);
        }

        // Backward inference FIRST, before elaborating trailing args.
        // Open every trailing-arg Pi as well (with Internal FreeVars
        // distinct from the leading metavariables), then unify the
        // result against `expectedType` if it was supplied. This lets
        // the trailing-arg elaborations below see fully-resolved
        // expected domain types, which is essential for nested
        // under-applied calls.
        std::map<std::string, ExpressionPointer> assignment;
        if (expectedType) {
            ExpressionPointer resultProbe = cursor;
            for (size_t j = 0;
                 j < trailingArgumentsSurface.size(); ++j) {
                auto* pi = std::get_if<Pi>(&resultProbe->node);
                if (!pi) break;
                std::string trailingArgumentFresh =
                    "_callTrailingArgument_" + std::to_string(j);
                resultProbe = openBinder(pi->codomain,
                                          trailingArgumentFresh,
                                          FreeVariableOrigin::Internal);
            }
            // Structural match first, without unfolding. Works when
            // both sides share the same head.
            unifyConstructorParameters(resultProbe, expectedType,
                                          metavariableNames, assignment);
            // If anything's still unassigned, WHNF both sides and try
            // again. This handles Definition-headed types (e.g.
            // `Natural.divides(_, _)`) by unfolding them to their
            // underlying structure (`Exists(...)`) — metavariables
            // pushed under Lambda binders are now safe to assign,
            // because the unifier shifts them back to the outer scope.
            bool anyLeftUnassigned = false;
            for (const auto& name : leadingFreshNames) {
                if (!assignment.count(name)) {
                    anyLeftUnassigned = true; break;
                }
            }
            if (anyLeftUnassigned) {
                ExpressionPointer expectedTypeNormalised =
                    weakHeadNormalForm(environment_, expectedType);
                ExpressionPointer resultProbeNormalised =
                    weakHeadNormalForm(environment_, resultProbe);
                unifyConstructorParameters(resultProbeNormalised,
                                              expectedTypeNormalised,
                                              metavariableNames, assignment);
            }
        }

        // Walk trailing-arg Pis. For each, elaborate the corresponding
        // surface argument, infer its kernel type, and unify the
        // (metavariable-substituted) Pi domain against the inferred
        // type to fill in any leading values that backward inference
        // didn't resolve. Then descend through the Pi.
        std::vector<ExpressionPointer> elaboratedTrailingArguments;
        for (size_t j = 0; j < trailingArgumentsSurface.size(); ++j) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                throw ElaborateError(
                    "call to '" + diagnosticName
                    + "': too many arguments at line "
                    + std::to_string(line));
            }
            ExpressionPointer expectedDomain =
                substituteFreeVariables(pi->domain, assignment);
            ExpressionPointer kernelTrailingArgument = elaborateExpression(
                *trailingArgumentsSurface[j], localBinders,
                expectedDomain);
            ExpressionPointer inferredArgumentType =
                weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(
                        localBinders, kernelTrailingArgument));
            inferredArgumentType = closeOverLocalBinders(
                inferredArgumentType, localBinders,
                localBinders.size());
            // Structural attempt first; WHNF both sides as fallback
            // for Definition-headed mismatches. We pass a binder-type
            // stack so the unifier can apply Miller-pattern HO
            // unification when it descends into Pi/Lambda binders and
            // a metavariable head is applied to a local-binder
            // BoundVariable.
            std::vector<ExpressionPointer> binderStack;
            unifyConstructorParameters(expectedDomain,
                                          inferredArgumentType,
                                          metavariableNames, assignment,
                                          0, &binderStack);
            bool anyLeftUnassigned = false;
            for (const auto& name : leadingFreshNames) {
                if (!assignment.count(name)) {
                    anyLeftUnassigned = true; break;
                }
            }
            if (anyLeftUnassigned) {
                ExpressionPointer expectedDomainNormalised =
                    weakHeadNormalForm(environment_, expectedDomain);
                ExpressionPointer inferredArgumentTypeRenormalised =
                    weakHeadNormalForm(environment_,
                                        inferredArgumentType);
                binderStack.clear();
                unifyConstructorParameters(expectedDomainNormalised,
                                              inferredArgumentTypeRenormalised,
                                              metavariableNames, assignment,
                                              0, &binderStack);
            }
            elaboratedTrailingArguments.push_back(kernelTrailingArgument);
            std::string trailingArgumentFresh =
                "_callTrailingArgument_" + std::to_string(j);
            // Bind the trailing-arg placeholder to its elaborated
            // value so that subsequent expectedDomain substitutions for
            // later trailing args (and the final result-pattern
            // unification) don't leak `_callTrailingArgument_N`
            // placeholders into nested constructor inferences — those
            // placeholders would otherwise block assignments via the
            // `containsValueArgumentFreeVar` guard in
            // unifyConstructorParameters.
            assignment[trailingArgumentFresh] = kernelTrailingArgument;
            cursor = openBinder(pi->codomain, trailingArgumentFresh,
                                 FreeVariableOrigin::Internal);
        }

        // If any leading value still remains unassigned after forward
        // inference, retry the backward unification (now potentially
        // using newly-derived information).
        bool anyUnassigned = false;
        for (const auto& name : leadingFreshNames) {
            if (!assignment.count(name)) { anyUnassigned = true; break; }
        }
        if (anyUnassigned && expectedType) {
            ExpressionPointer resultPattern =
                substituteFreeVariables(cursor, assignment);
            ExpressionPointer expectedTypeNormalised =
                weakHeadNormalForm(environment_, expectedType);
            unifyConstructorParameters(resultPattern,
                                          expectedTypeNormalised,
                                          metavariableNames, assignment);
        }

        CallInferenceResult result;
        std::vector<std::string> unassigned;
        std::vector<std::pair<std::string, ExpressionPointer>> assigned;
        for (const auto& name : leadingFreshNames) {
            auto iterator = assignment.find(name);
            if (iterator == assignment.end()) {
                unassigned.push_back(name);
            } else {
                assigned.push_back({name, iterator->second});
                result.leadingValues.push_back(iterator->second);
            }
        }
        if (!unassigned.empty()) {
            std::string message =
                "could not infer all leading arguments of '"
                + diagnosticName + "':";
            for (const auto& name : unassigned) {
                // Names are like `_callLeadingArgument_2_Foo`; the
                // index after the prefix tells the user which
                // declaration parameter the elaborator gave up on.
                message += "\n    position ";
                size_t firstUnderscore = name.find('_', 1);
                size_t secondUnderscore = name.find(
                    '_', firstUnderscore + 1);
                if (firstUnderscore != std::string::npos
                    && secondUnderscore != std::string::npos) {
                    message += name.substr(
                        firstUnderscore + 1,
                        secondUnderscore - firstUnderscore - 1);
                } else {
                    message += "(?)";
                }
                message += " is unassigned";
            }
            if (!assigned.empty()) {
                message += "\n  inferred so far:";
                for (const auto& pair : assigned) {
                    message += "\n    ";
                    size_t firstUnderscore = pair.first.find('_', 1);
                    size_t secondUnderscore = pair.first.find(
                        '_', firstUnderscore + 1);
                    if (firstUnderscore != std::string::npos
                        && secondUnderscore != std::string::npos) {
                        message += "position ";
                        message += pair.first.substr(
                            firstUnderscore + 1,
                            secondUnderscore - firstUnderscore - 1);
                    } else {
                        message += pair.first;
                    }
                    message += " = ";
                    message += prettyPrintInLocalScope(
                        pair.second, localBinders);
                }
            }
            if (expectedType) {
                message += "\n  expected return type: ";
                message += prettyPrintInLocalScope(
                    expectedType, localBinders);
            }
            message += "\n  Provide the missing argument(s) explicitly "
                       "to disambiguate.";
            throwElaborate(message);
        }
        result.trailingValues = std::move(elaboratedTrailingArguments);
        return result;
    }

    // Constructor-specific wrapper around `inferLeadingArguments`. Handles
    // the universe-argument plumbing and assembles the final constructor
    // application.
    ExpressionPointer elaborateConstructorCallInferringParameters(
        const Constructor& constructor,
        const Inductive& inductive,
        const std::vector<SurfaceExpressionPointer>& valueArgumentsSurface,
        const std::vector<LevelPointer>& universeArguments,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {

        ExpressionPointer constructorType = substituteUniverseLevels(
            constructor.type, constructor.universeParameters,
            universeArguments);
        CallInferenceResult inferred = inferLeadingArguments(
            constructor.inductiveName,
            constructorType,
            inductive.numParameters,
            valueArgumentsSurface,
            localBinders,
            expectedType,
            "_constructorParameter_",
            line);

        const std::string& constructorName =
            inductive.constructorNames[constructor.constructorIndex];
        ExpressionPointer head = makeConstant(constructorName,
                                               universeArguments);
        for (auto& parameterValue : inferred.leadingValues) {
            head = makeApplication(std::move(head),
                                    std::move(parameterValue));
        }
        for (auto& valueArgument : inferred.trailingValues) {
            head = makeApplication(std::move(head),
                                    std::move(valueArgument));
        }
        return head;
    }

    ExpressionPointer elaborateNumericLiteral(
        const SurfaceNumericLiteral& numeric,
        int line, int column) {
        // Desugar `25` to successor(successor(...zero)) with 25 successors.
        // Requires Natural, zero, successor to be in the environment.
        if (environment_.lookup("Natural") == nullptr
            || environment_.lookup("zero") == nullptr
            || environment_.lookup("successor") == nullptr) {
            throw ElaborateError(
                "numeric literal at line " + std::to_string(line)
                + " requires Natural, zero, and successor to be in the "
                "environment (import Natural.basics)");
        }
        int value = std::stoi(numeric.digits);
        ExpressionPointer term = makeConstant("zero");
        for (int i = 0; i < value; ++i) {
            term = makeApplication(makeConstant("successor"),
                                    std::move(term));
        }
        (void)column;
        return term;
    }

    ExpressionPointer elaboratePiType(
        const SurfacePiType& piType,
        const std::vector<LocalBinder>& localBinders) {
        if (piType.binder.names.empty()) {
            // Anonymous: T → U.
            ExpressionPointer domain =
                elaborateExpression(*piType.binder.type, localBinders);
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back({"_", domain});
            ExpressionPointer codomain =
                elaborateExpression(*piType.codomain, extended);
            return makePi("_", std::move(domain), std::move(codomain));
        }
        // Multi-name binder: (x y z : T) → U becomes a chain of Pis.
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (const auto& name : piType.binder.names) {
            ExpressionPointer domainHere =
                elaborateExpression(*piType.binder.type, extended);
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        ExpressionPointer codomain =
            elaborateExpression(*piType.codomain, extended);
        ExpressionPointer result = codomain;
        for (int i = static_cast<int>(piType.binder.names.size()) - 1;
             i >= 0; --i) {
            result = makePi(piType.binder.names[i],
                            std::move(domainsPerName[i]),
                            std::move(result));
        }
        return result;
    }

    ExpressionPointer elaborateLambda(
        const SurfaceLambda& lambda,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType = nullptr) {
        if (lambda.binder.names.empty()) {
            throw ElaborateError("lambda binder must have at least one name");
        }
        // Pre-walk the expected Pi if present. Two things drop out:
        //   - per-name domain types (for untyped binders, used directly;
        //     for typed binders, double-checked against the annotation)
        //   - the expected body type after peeling lambda.binder.names
        //     Pi binders, for downstream constructor-parameter inference.
        std::vector<ExpressionPointer> expectedDomainsPerName;
        ExpressionPointer expectedBody = nullptr;
        if (expectedType) {
            ExpressionPointer cursor =
                weakHeadNormalForm(environment_, expectedType);
            bool ok = true;
            for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
                auto* pi = std::get_if<Pi>(&cursor->node);
                if (!pi) { ok = false; break; }
                expectedDomainsPerName.push_back(pi->domain);
                cursor = pi->codomain;
            }
            if (ok) {
                expectedBody = cursor;
            } else {
                expectedDomainsPerName.clear();
            }
        }
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
            const auto& name = lambda.binder.names[k];
            ExpressionPointer domainHere;
            if (lambda.binder.type) {
                domainHere =
                    elaborateExpression(*lambda.binder.type, extended);
            } else {
                // Untyped binder: read the domain from the expected
                // Pi. The kernel term is already in the right scope
                // (it came out of the Pi's domain in the surrounding
                // context); we just need to lift past the binders
                // we've added so far inside this lambda.
                if (k >= expectedDomainsPerName.size()) {
                    throw ElaborateError(
                        "lambda binder '" + name + "' has no type "
                        "annotation and no expected type to infer "
                        "from at this position");
                }
                domainHere = liftBoundVariables(
                    expectedDomainsPerName[k],
                    static_cast<int>(k), 0);
            }
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        ExpressionPointer body =
            elaborateExpression(*lambda.body, extended, expectedBody);
        // Diff-wrap the body if the expected codomain is an equality
        // and the body's type doesn't directly match. Catches
        // `function (rep) => congruenceOf(λ, P)` simplifications
        // where bare `P` would suffice given diff inference.
        if (expectedBody) {
            body = coerceToExpectedTypeViaDiff(
                extended, body, expectedBody);
            checkRedundantCongruenceOfWrapper(
                lambda.body, extended, expectedBody,
                "lambda body");
        }
        // Unused-name warning. Restricted to `suppose ... as`
        // statement-level intros — a `suppose P as h;` whose body
        // ignores `h` is almost always a refactor leftover. Function
        // lambdas (`function (x : T) (y : U) => body`) deliberately
        // do NOT trigger this warning, even when `y` goes unused —
        // C++'s `void foo(int)`-style omission isn't available in
        // this surface yet, and forcing the user to rename to `_y`
        // costs as much as just keeping `y`, so the warning would
        // produce noise without progress. Checked at the SURFACE
        // level (the user's body must textually reference the name)
        // because the elaborator may reference a binder on the
        // user's behalf — e.g. the bare-proposition-as-proof
        // coercion finds hypotheses by type, not by name.
        if (lambda.fromStatementIntro
            && lambda.binder.names.size() == 1) {
            warnIfSurfaceNameUnused(
                lambda.binder.names[0], *lambda.body,
                lambda.body->line, lambda.body->column,
                "`suppose ... as`");
        }
        ExpressionPointer result = body;
        for (int i = static_cast<int>(lambda.binder.names.size()) - 1;
             i >= 0; --i) {
            result = makeLambda(lambda.binder.names[i],
                                std::move(domainsPerName[i]),
                                std::move(result));
        }
        return result;
    }

    // -------- level elaboration --------

    LevelPointer elaborateLevel(const SurfaceLevel& level) {
        if (auto* numeric = std::get_if<SurfaceLevelNumeric>(&level.node)) {
            return makeLevelConst(numeric->value);
        }
        if (auto* name = std::get_if<SurfaceLevelName>(&level.node)) {
            if (currentUniverseParameters_.count(name->name) == 0) {
                throw ElaborateError(
                    "universe parameter '" + name->name
                    + "' is not declared (use .{...} on the declaration "
                    "to introduce it)");
            }
            return makeLevelParam(name->name);
        }
        if (auto* maxLevel = std::get_if<SurfaceLevelMax>(&level.node)) {
            return makeLevelMax(elaborateLevel(*maxLevel->left),
                                 elaborateLevel(*maxLevel->right));
        }
        if (auto* imaxLevel = std::get_if<SurfaceLevelImax>(&level.node)) {
            return makeLevelIMax(elaborateLevel(*imaxLevel->left),
                                  elaborateLevel(*imaxLevel->right));
        }
        if (auto* addLevel = std::get_if<SurfaceLevelAdd>(&level.node)) {
            LevelPointer base = elaborateLevel(*addLevel->base);
            for (int i = 0; i < addLevel->amount; ++i) {
                base = makeLevelSuccessor(std::move(base));
            }
            return base;
        }
        if (std::get_if<SurfaceLevelMeta>(&level.node)) {
            // Bare `Type` in source: generate a fresh universe parameter
            // name and let it be auto-bound to the enclosing declaration.
            return makeLevelParam(freshAutoBoundUniverseName());
        }
        throw ElaborateError("unhandled level variant");
    }

    // Resolves a binary arithmetic operator (`+`, `*`, ...) to a kernel
    // function call. For v1 the resolution table is hardcoded to the
    // Natural namespace: if both operands have type Natural, use
    // Natural.add / Natural.multiply. Otherwise an ElaborateError is
    // raised. A proper using-declaration-driven mechanism is the next
    // iteration.
    ExpressionPointer desugarArithmeticOperator(
        const std::string& operatorSymbol,
        const SurfaceExpression& leftSurface,
        const SurfaceExpression& rightSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {
        // First: if a local binder has the operator symbol as its
        // name (introduced via `((·) : G → G → G)`-style binders),
        // treat the operator as an application of that binder. This
        // lets group/ring theorems use `x · y` for the bound
        // operation without having to plumb it through the global
        // operator registry.
        for (size_t i = localBinders.size(); i > 0; --i) {
            if (localBinders[i - 1].name == operatorSymbol) {
                ExpressionPointer leftLocal =
                    elaborateExpression(leftSurface, localBinders);
                ExpressionPointer rightLocal =
                    elaborateExpression(rightSurface, localBinders);
                ExpressionPointer functionExpression =
                    elaborateIdentifier(
                        SurfaceIdentifier{operatorSymbol, {}},
                        localBinders, line, /*column=*/0);
                ExpressionPointer call = makeApplication(
                    std::move(functionExpression), std::move(leftLocal));
                call = makeApplication(std::move(call),
                                        std::move(rightLocal));
                return call;
            }
        }
        // `≥` and `>` desugar to the flipped `≤`/`<` against the same
        // carrier. We never register a separate function for them — the
        // existing `≤`/`<` registry entries are reused with the operand
        // order reversed. This keeps a single source of truth for the
        // order relation and lets calc chains mix the two notations.
        if (operatorSymbol == "≥") {
            return desugarArithmeticOperator(
                "≤", rightSurface, leftSurface, localBinders,
                expectedType, line);
        }
        if (operatorSymbol == ">") {
            return desugarArithmeticOperator(
                "<", rightSurface, leftSurface, localBinders,
                expectedType, line);
        }
        // Logical operators are dispatched first because their operand
        // type is a Proposition (a `Sort`, not a `Constant`), so the
        // numeric-operator dispatch below — which looks for a Constant
        // head on the inferred operand type — wouldn't see them.
        std::string logicalTarget;
        if (operatorSymbol == "∧") logicalTarget = "And";
        else if (operatorSymbol == "∨") logicalTarget = "Or";
        if (!logicalTarget.empty()) {
            if (environment_.lookup(logicalTarget) == nullptr) {
                throw ElaborateError(
                    "operator '" + operatorSymbol + "' resolves to '"
                    + logicalTarget + "' but that inductive is not in "
                    "scope (line " + std::to_string(line)
                    + "); import Logic.basics");
            }
            ExpressionPointer leftLogical =
                elaborateExpression(leftSurface, localBinders);
            ExpressionPointer rightLogical =
                elaborateExpression(rightSurface, localBinders);
            ExpressionPointer call = makeConstant(logicalTarget);
            call = makeApplication(std::move(call), std::move(leftLogical));
            call = makeApplication(std::move(call), std::move(rightLogical));
            return call;
        }
        // Use the outer expected type as a hint for the LEFT operand
        // only when it's a Constant head — e.g. `Rational`, `Integer`,
        // `Real`, `PAdic`. For arithmetic operators like `+`, `*`,
        // `-`, the result type equals the operand type, so the hint
        // is exactly the operand type. For `≤`, `<`, etc. the result
        // type is `Proposition` (a Sort, not a Constant), so the
        // guard skips them. Lets short-form `Quotient.mk(rep)` fire
        // on the LEFT of a homogeneous operator when the outer
        // context provides the carrier head.
        ExpressionPointer leftExpectedType = nullptr;
        if (expectedType
            && std::holds_alternative<Constant>(expectedType->node)) {
            leftExpectedType = expectedType;
        }
        ExpressionPointer leftKernel =
            elaborateExpression(leftSurface, localBinders,
                                 leftExpectedType);
        // Determine the operand type by inferring the type of the left
        // operand. Check the raw inferred type first: if a binder was
        // declared with a named type like `Integer` (which δ-reduces
        // to `Quotient(IntegerRepresentative, IntegerEquivalent)`),
        // we want to dispatch on `Integer`, not the unfolded form.
        // Only WHNF as a fallback for types that are themselves
        // computations (rare in practice but used by let-bindings
        // whose type-annotation is a reducible expression).
        ExpressionPointer leftTypeRaw =
            inferTypeInLocalContext(localBinders, leftKernel);
        // Propagate the left operand's type as expected type for the
        // right operand. This lets short-form `Quotient.mk(rep)` (with
        // R inferred from expected type) fire in operand position of
        // homogeneous operators like `+`, `*`, `≤`, `<` on Rational,
        // Real, etc. — mirrors the `=` desugaring's identical trick.
        ExpressionPointer leftTypeClosed = closeOverLocalBinders(
            leftTypeRaw, localBinders, localBinders.size());
        ExpressionPointer rightKernel =
            elaborateExpression(rightSurface, localBinders,
                                 leftTypeClosed);
        // Use `headConstantName` to extract the type head — peels through
        // Applications so parameterised types like `Set(T)` report `Set`
        // and `Quotient(IR, IE)` reports `Quotient`. Falls back to WHNF
        // for definitional aliases whose RHS exposes a different head.
        std::string operandTypeName = headConstantName(leftTypeRaw);
        std::string targetFunction;
        // First consult the user-declared registry: any
        // `operator (sym) on (T1, T2) := F;` registration wins. This is
        // the extensible path — Rational, Real, Complex, polynomial
        // rings, etc. all hook in here. Wildcard `_` registrations
        // (e.g. `∈` on `(_, Set)`) match any LHS or RHS type.
        ExpressionPointer rightTypeRaw =
            inferTypeInLocalContext(localBinders, rightKernel);
        std::string rightTypeName = headConstantName(rightTypeRaw);
        std::string registered = environment_.lookupOperator(
            operatorSymbol, operandTypeName, rightTypeName);
        if (!registered.empty()) {
            targetFunction = registered;
        }
        // Fallback: if the raw head Constant didn't match anything,
        // try operand-type names from the registry whose definition
        // δ-reduces to the operand's actual type. This catches
        // `Quotient.mk(IntegerRepresentative, IntegerEquivalent, _)`
        // (raw type head: `Quotient`) being treated as `Integer`
        // (whose definition body is exactly that `Quotient(...)`).
        if (targetFunction.empty()) {
            ExpressionPointer operandLeftWHNF = weakHeadNormalForm(
                environment_, leftTypeRaw);
            ExpressionPointer operandRightWHNF = weakHeadNormalForm(
                environment_, rightTypeRaw);
            for (const auto& [key, funcName]
                 : environment_.operatorRegistry) {
                const auto& [opSym, leftReg, rightReg] = key;
                if (opSym != operatorSymbol) continue;
                const Declaration* leftDecl =
                    environment_.lookup(leftReg);
                const Declaration* rightDecl =
                    environment_.lookup(rightReg);
                auto* leftDef = leftDecl
                    ? std::get_if<Definition>(leftDecl) : nullptr;
                auto* rightDef = rightDecl
                    ? std::get_if<Definition>(rightDecl) : nullptr;
                if (!leftDef || !rightDef) continue;
                ExpressionPointer leftRegBodyWHNF = weakHeadNormalForm(
                    environment_, leftDef->body);
                ExpressionPointer rightRegBodyWHNF = weakHeadNormalForm(
                    environment_, rightDef->body);
                if (structurallyEqual(leftRegBodyWHNF, operandLeftWHNF)
                    && structurallyEqual(rightRegBodyWHNF,
                                            operandRightWHNF)) {
                    targetFunction = funcName;
                    break;
                }
            }
        }
        // For `<` we wrap the left operand in `successor`, since
        // `a < b` is defined as `LessOrEqual(successor(a), b)`. This is
        // special enough that we leave it built-in.
        bool wrapLeftInSuccessor = false;
        if (targetFunction.empty()) {
            if (operandTypeName == "Natural") {
                if (operatorSymbol == "≤") targetFunction = "LessOrEqual";
                else if (operatorSymbol == "<") {
                    targetFunction = "LessOrEqual";
                    wrapLeftInSuccessor = true;
                }
                else if (operatorSymbol == "∣") targetFunction = "Natural.divides";
            }
        }
        if (targetFunction.empty()) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' is not supported for "
                "operand type '" + operandTypeName + "' (line "
                + std::to_string(line)
                + "); supported: +, *, ≤, <, ∣ on Natural; +, *, - on "
                "Integer; ∧, ∨ on Proposition");
        }
        if (environment_.lookup(targetFunction) == nullptr) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' resolves to '"
                + targetFunction + "' but that function is not in scope "
                "(line " + std::to_string(line) + ")");
        }
        if (wrapLeftInSuccessor) {
            if (environment_.lookup("successor") == nullptr) {
                throw ElaborateError(
                    "operator '<' on Natural requires `successor` in scope "
                    "(line " + std::to_string(line) + ")");
            }
            leftKernel = makeApplication(
                makeConstant("successor"), std::move(leftKernel));
        }
        ExpressionPointer call = makeConstant(targetFunction);
        // Fill any leading implicit binders the dispatch function may
        // have. Two patterns are common:
        //   (a) `Set.member {T : Type(0)} (x : T) (S : Set(T))` —
        //       the implicit carrier is the LEFT operand's type T.
        //   (b) `Set.subset {T : Type(0)} (A : Set(T)) (B : Set(T))` —
        //       the implicit carrier is the *parameter* of the LEFT
        //       operand's type `Set(T)`, not `Set(T)` itself.
        // We recover the fillers by unifying the LEFT operand's type
        // against the target function's first-explicit-argument type
        // template (which has BoundVariable references to the implicit
        // binders). Works for both patterns above and any
        // structurally-decomposable shape — in particular, it doesn't
        // trip when the LEFT operand's type is itself a parameterised
        // alias like `Real = Quotient(_, _)`.
        int implicitCount =
            environment_.implicitArgumentCount(targetFunction);
        if (implicitCount > 0) {
            std::vector<ExpressionPointer> implicitBindings(implicitCount);
            bool inferredByUnification = false;
            if (const Declaration* targetDecl =
                    environment_.lookup(targetFunction)) {
                ExpressionPointer cursor = declarationType(*targetDecl);
                for (int i = 0; i < implicitCount && cursor; ++i) {
                    auto* pi = std::get_if<Pi>(&cursor->node);
                    if (!pi) { cursor = nullptr; break; }
                    cursor = pi->codomain;
                }
                if (cursor) {
                    if (auto* firstExplicit =
                            std::get_if<Pi>(&cursor->node)) {
                        if (matchAgainstPattern(
                                firstExplicit->domain, leftTypeClosed,
                                implicitCount, implicitBindings)) {
                            inferredByUnification = true;
                            for (const auto& binding : implicitBindings) {
                                if (!binding) {
                                    inferredByUnification = false;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if (inferredByUnification) {
                // bindings[0] is the INNERMOST implicit (smallest BV
                // index from inside). Application order is outermost-
                // first, so apply in reverse.
                for (int i = implicitCount - 1; i >= 0; --i) {
                    call = makeApplication(std::move(call),
                                             implicitBindings[i]);
                }
            } else {
                // Fall back to the legacy single-filler heuristic for
                // safety. If this fires, the kernel typecheck will
                // catch a mismatch — better than silently building a
                // wrong term, no worse than the prior behaviour.
                ExpressionPointer implicitFiller = leftTypeClosed;
                auto* leftTypeApp =
                    std::get_if<Application>(&leftTypeClosed->node);
                if (leftTypeApp) {
                    implicitFiller = leftTypeApp->argument;
                }
                for (int i = 0; i < implicitCount; ++i) {
                    call = makeApplication(std::move(call),
                                             implicitFiller);
                }
            }
        }
        call = makeApplication(std::move(call), std::move(leftKernel));
        call = makeApplication(std::move(call), std::move(rightKernel));
        return call;
    }

    // Desugars `reflexivity(subject)` into
    // `reflexivity.{u}(typeOfSubject, subject)` where u is the subject's
    // type universe. Mirrors how the constructor's signature makes the
    // carrier type and its universe inferable from the subject.
    ExpressionPointer desugarReflexivity(
        SurfaceExpressionPointer subjectSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {
        ExpressionPointer subjectKernel =
            elaborateExpression(*subjectSurface, localBinders);
        ExpressionPointer subjectTypeOpened =
            inferTypeInLocalContext(localBinders, subjectKernel);
        ExpressionPointer subjectType = closeOverLocalBinders(
            subjectTypeOpened, localBinders, localBinders.size());
        LevelPointer carrierUniverseLevel =
            typeUniverseOf(localBinders, subjectKernel);
        ExpressionPointer call =
            makeConstant("reflexivity", {carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(subjectType));
        call = makeApplication(std::move(call), std::move(subjectKernel));
        (void)line; (void)column;
        return call;
    }

    // Helper: given a kernel term whose type (already weak-head-normalised)
    // is `Equality.{u}(A, x, y)`, extracts the four components. Throws
    // ElaborateError if the type doesn't have that shape.
    struct EqualityComponents {
        ExpressionPointer carrierType;
        ExpressionPointer leftEndpoint;
        ExpressionPointer rightEndpoint;
        LevelPointer carrierUniverseLevel;
    };
    EqualityComponents extractEqualityComponents(
        ExpressionPointer equalityType, const char* contextLabel,
        int line) {
        // WHNF the type so a β-redex (e.g. the predicate body of an
        // Exists destructured via `obtain ⟨k, eq⟩` — the binder's
        // type starts as `(λ k'. P k')(k)`) reduces to the
        // applied-`Equality.{u}` form we expect to destructure below.
        equalityType =
            weakHeadNormalForm(environment_, equalityType);
        auto* outerApp = std::get_if<Application>(&equalityType->node);
        if (!outerApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer rightEndpoint = outerApp->argument;
        auto* middleApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!middleApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer leftEndpoint = middleApp->argument;
        auto* innerApp =
            std::get_if<Application>(&middleApp->function->node);
        if (!innerApp) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type is not a fully applied Equality "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer carrierType = innerApp->argument;
        auto* equalityConstant =
            std::get_if<Constant>(&innerApp->function->node);
        if (!equalityConstant
            || equalityConstant->name != "Equality"
            || equalityConstant->universeArguments.size() != 1) {
            throw ElaborateError(
                std::string(contextLabel)
                + ": argument's type isn't an Equality.{u} (line "
                + std::to_string(line) + ")");
        }
        return {carrierType, leftEndpoint, rightEndpoint,
                equalityConstant->universeArguments[0]};
    }

    // Desugars `Equality.symmetry(equalityProof)` to the full call with
    // the carrier type and endpoint values inferred from the proof's
    // type.
    ExpressionPointer desugarEqualitySymmetry(
        SurfaceExpressionPointer equalityProofSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {
        ExpressionPointer equalityProofKernel =
            elaborateExpression(*equalityProofSurface, localBinders);
        ExpressionPointer equalityProofType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          equalityProofKernel));
        EqualityComponents components = extractEqualityComponents(
            equalityProofType, "Equality.symmetry", line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            components.carrierType, localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            components.leftEndpoint, localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            components.rightEndpoint, localBinders, localBinders.size());
        ExpressionPointer call =
            makeConstant("Equality.symmetry",
                          {components.carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        (void)column;
        return call;
    }

    // Desugars `Equality.transitivity(firstEquality, secondEquality)`
    // to the full call, with the carrier type and the three endpoints
    // inferred from the two argument equalities' types.
    ExpressionPointer desugarEqualityTransitivity(
        SurfaceExpressionPointer firstEqualitySurface,
        SurfaceExpressionPointer secondEqualitySurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        // If the surrounding context provided an expected type
        // `Equality(carrier, A, C)`, synthesize `Equality(carrier, A, A)`
        // as the expected type for the first argument so that desugars
        // like rewrite (which need an expected type) can fire there too.
        // Otherwise the first argument elaborates without an expected
        // type, exactly as before.
        ExpressionPointer expectedForFirst;
        if (expectedType) {
            ExpressionPointer expectedOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            ExpressionPointer expectedWhnf = weakHeadNormalForm(
                environment_, expectedOpened);
            EqualityComponents outerComponents;
            try {
                outerComponents = extractEqualityComponents(
                    expectedWhnf,
                    "Equality.transitivity (outer expected)", line);
                ExpressionPointer outerCarrier = closeOverLocalBinders(
                    outerComponents.carrierType,
                    localBinders, localBinders.size());
                ExpressionPointer outerLeft = closeOverLocalBinders(
                    outerComponents.leftEndpoint,
                    localBinders, localBinders.size());
                expectedForFirst = makeConstant(
                    "Equality",
                    {outerComponents.carrierUniverseLevel});
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerCarrier);
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerLeft);
                expectedForFirst = makeApplication(
                    std::move(expectedForFirst), outerLeft);
            } catch (const ElaborateError&) {
                // Outer expected type isn't an Equality — proceed
                // without synthesizing.
            }
        }
        ExpressionPointer firstEqualityKernel =
            elaborateExpression(*firstEqualitySurface, localBinders,
                                  expectedForFirst);
        ExpressionPointer firstEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          firstEqualityKernel));
        EqualityComponents firstComponents = extractEqualityComponents(
            firstEqualityType,
            "Equality.transitivity (first argument)", line);
        // Build the closed-over endpoints early so we can compose a
        // synthetic expected type for the second argument.
        ExpressionPointer carrierTypeForExpected =
            closeOverLocalBinders(firstComponents.carrierType,
                                    localBinders, localBinders.size());
        ExpressionPointer middleForExpected =
            closeOverLocalBinders(firstComponents.rightEndpoint,
                                    localBinders, localBinders.size());
        ExpressionPointer expectedForSecond = makeConstant(
            "Equality",
            {firstComponents.carrierUniverseLevel});
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), carrierTypeForExpected);
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), middleForExpected);
        expectedForSecond = makeApplication(
            std::move(expectedForSecond), middleForExpected);
        ExpressionPointer secondEqualityKernel =
            elaborateExpression(*secondEqualitySurface, localBinders,
                                  expectedForSecond);
        ExpressionPointer secondEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          secondEqualityKernel));
        EqualityComponents secondComponents = extractEqualityComponents(
            secondEqualityType,
            "Equality.transitivity (second argument)", line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            firstComponents.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            firstComponents.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer middleEndpoint = closeOverLocalBinders(
            firstComponents.rightEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            secondComponents.rightEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer call = makeConstant(
            "Equality.transitivity",
            {firstComponents.carrierUniverseLevel});
        call = makeApplication(std::move(call), std::move(carrierType));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call),
                                std::move(middleEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(firstEqualityKernel));
        call = makeApplication(std::move(call),
                                std::move(secondEqualityKernel));
        (void)column;
        return call;
    }

    // Desugars `congruenceOf(f, h)` into a full call to
    // `Equality.congruence.{u, v}(A, B, f, x, y, h)` by inferring the
    // type arguments and universes from the kernel types of f and h.
    // Requires `Equality.congruence` to be in the environment.
    // Walks `expression` looking for subterms structurally equal to
    // `target`. Each match is replaced by `BoundVariable(currentDepth)`,
    // and every other BoundVariable referring to outer scope is shifted
    // up by 1 — preparing the result to be the body of a new outer
    // Lambda binder. Counts matches so the caller can require exactly
    // one. `target` is shifted as we descend into binders so structural
    // comparison stays correct.

    // Recursive WHNF through Application spines. WHNFs the current
    // expression, then — if the result is an Application — recursively
    // normalizes its function and argument. This exposes structural
    // shape that plain `weakHeadNormalForm` leaves alone (it only
    // reduces the outermost head). Used by `claim by substituting`'s
    // search as a fallback when the surface goal has no occurrences
    // of the equation's endpoint, but a deeper reduction would expose
    // one — e.g. under `unfold X in body`, where `X(args)` in the
    // surface goal δ-unfolds to a `cases scrutinee { … }` body whose
    // scrutinee is the substitution target.
    ExpressionPointer deepWhnfThroughApplications(
        ExpressionPointer expression) {
        expression = weakHeadNormalForm(environment_, expression);
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer function =
                deepWhnfThroughApplications(application->function);
            ExpressionPointer argument =
                deepWhnfThroughApplications(application->argument);
            if (function.get() != application->function.get()
                || argument.get() != application->argument.get()) {
                return makeApplication(std::move(function),
                                        std::move(argument));
            }
        }
        return expression;
    }

    // Deep beta-only reduction: rewrites every (λx. body)(arg) redex
    // anywhere in the expression — never δ-unfolds Constants, so
    // user-visible names stay intact. Used as a fallback combo by
    // `rewrite(eq, term)` to catch redexes hiding inside the term's
    // type — e.g. `sequenceFunction(λn. …, m)` from Quotient.lift
    // bodies in real-analysis proofs, where the user's stated motive
    // sees the β-reduced form but the inferred type doesn't.
    ExpressionPointer deepBetaReduce(ExpressionPointer expression) {
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer function =
                deepBetaReduce(application->function);
            ExpressionPointer argument =
                deepBetaReduce(application->argument);
            if (auto* lambda = std::get_if<Lambda>(&function->node)) {
                return deepBetaReduce(
                    substitute(lambda->body, 0, argument));
            }
            return makeApplication(std::move(function),
                                    std::move(argument));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                deepBetaReduce(lambda->domain),
                deepBetaReduce(lambda->body));
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                deepBetaReduce(pi->domain),
                deepBetaReduce(pi->codomain));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                deepBetaReduce(let->type),
                deepBetaReduce(let->value),
                deepBetaReduce(let->body));
        }
        return expression;
    }

    // Abstract every occurrence of `target` in `expression`, like
    // `abstractStructuralOccurrence`, but WHNF the expression at each
    // recursion level first. This exposes target subterms (like
    // `Logic.classical_decidable(P)`) that are hidden behind a chain
    // of δ-unfoldings in the goal — e.g., `bisectionRight(…, succ(n))`
    // → `right(bisectionIntervals(…, succ(n)))` → `right(bisectionStep(…))`
    // → `right(bisectionStepWithDec(…, classical_decidable(…)))`.
    //
    // Each level WHNFs only the head, so we don't pay for fully
    // normalising the goal up front (which would expand bisection
    // proofs to unmanageable sizes). When recursion passes through a
    // binder, the BoundVariable depth advances; references to the
    // freshly introduced motive binder (BV(currentDepth)) shift their
    // free occurrences upward to leave room, mirroring
    // `abstractStructuralOccurrence`.
    //
    // WHNF failures (fuel exhaustion, etc.) leave that subterm in its
    // current form and continue.
    // Recursively replace every reference to a let-binder in
    // `expression` with the binder's value. Used by `decide` so the
    // user's proposition (which references in-scope `let X := V`
    // bindings symbolically) lines up with the goal's structure, which
    // typically predates the let-bindings and has V inlined.
    ExpressionPointer zetaUnfoldLetBinders(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders,
        int currentDepth) {
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= currentDepth) {
                int localOffset = index - currentDepth;
                int arrayIndex =
                    static_cast<int>(localBinders.size()) - 1 - localOffset;
                if (arrayIndex >= 0
                    && arrayIndex
                       < static_cast<int>(localBinders.size())
                    && localBinders[arrayIndex].value) {
                    // The let's value was elaborated in a scope that
                    // contained the localBinders BELOW it (indices 0
                    // ..arrayIndex-1) but not the ones ABOVE it. Shift
                    // its BVs up by the number of binders above it
                    // plus the current in-expression depth to land in
                    // our scope. Recursively unfold the value too so
                    // chained let-bindings collapse fully.
                    // The let's value V was elaborated in a smaller
                    // scope (the binders below it, size = arrayIndex).
                    // Lift V to interpret its BVs in the current
                    // localBinders scope; recursively unfold any
                    // chained let-references it contains; then shift
                    // for the in-expression depth.
                    int bindersIntroducedSince =
                        static_cast<int>(localBinders.size())
                        - arrayIndex;
                    ExpressionPointer valueInCurrentScope = shift(
                        localBinders[arrayIndex].value,
                        bindersIntroducedSince);
                    ExpressionPointer unfolded = zetaUnfoldLetBinders(
                        valueInCurrentScope, localBinders,
                        /*currentDepth=*/0);
                    return shift(unfolded, currentDepth);
                }
            }
            return expression;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                zetaUnfoldLetBinders(pi->domain, localBinders, currentDepth),
                zetaUnfoldLetBinders(pi->codomain, localBinders,
                                      currentDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                zetaUnfoldLetBinders(lambda->domain, localBinders,
                                      currentDepth),
                zetaUnfoldLetBinders(lambda->body, localBinders,
                                      currentDepth + 1));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                zetaUnfoldLetBinders(application->function, localBinders,
                                      currentDepth),
                zetaUnfoldLetBinders(application->argument, localBinders,
                                      currentDepth));
        }
        if (auto* letNode = std::get_if<Let>(&expression->node)) {
            return makeLet(letNode->displayHint,
                zetaUnfoldLetBinders(letNode->type, localBinders,
                                      currentDepth),
                zetaUnfoldLetBinders(letNode->value, localBinders,
                                      currentDepth),
                zetaUnfoldLetBinders(letNode->body, localBinders,
                                      currentDepth + 1));
        }
        return expression;
    }

    // Return the head constant name of an Application chain, or empty
    // string if the head isn't a Constant. `f(a, b, c)` returns "f".
    std::string applicationHeadConstantName(
        ExpressionPointer expression) const {
        ExpressionPointer cursor = expression;
        while (auto* app = std::get_if<Application>(&cursor->node)) {
            cursor = app->function;
        }
        if (auto* c = std::get_if<Constant>(&cursor->node)) {
            return c->name;
        }
        return std::string();
    }

    // Does `expression` syntactically reference `targetHeadName` as a
    // Constant somewhere? Used to seed unfoldExposesHead.
    bool expressionReferencesConstant(
        ExpressionPointer expression,
        const std::string& targetHeadName,
        std::unordered_set<std::string>& visiting) {
        if (auto* c = std::get_if<Constant>(&expression->node)) {
            if (c->name == targetHeadName) return true;
            return unfoldExposesHead(c->name, targetHeadName, visiting);
        }
        if (auto* app =
                std::get_if<Application>(&expression->node)) {
            return expressionReferencesConstant(
                       app->function, targetHeadName, visiting)
                || expressionReferencesConstant(
                       app->argument, targetHeadName, visiting);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return expressionReferencesConstant(
                       pi->domain, targetHeadName, visiting)
                || expressionReferencesConstant(
                       pi->codomain, targetHeadName, visiting);
        }
        if (auto* lam = std::get_if<Lambda>(&expression->node)) {
            return expressionReferencesConstant(
                       lam->domain, targetHeadName, visiting)
                || expressionReferencesConstant(
                       lam->body, targetHeadName, visiting);
        }
        if (auto* letNode = std::get_if<Let>(&expression->node)) {
            return expressionReferencesConstant(
                       letNode->type, targetHeadName, visiting)
                || expressionReferencesConstant(
                       letNode->value, targetHeadName, visiting)
                || expressionReferencesConstant(
                       letNode->body, targetHeadName, visiting);
        }
        return false;
    }

    // Does WHNF-unfolding `constantName` produce a term that
    // syntactically (transitively, through other transparent
    // definitions) references `targetHeadName`? Memoised: each
    // constant is walked once per target. Used by the `decide` walker
    // to skip Applications whose head is provably irrelevant
    // (Real.LessOrEqual, Set.member, etc., when the target is
    // Logic.classical_decidable).
    //
    // The `visiting` set guards against cycles in mutually recursive
    // definitions — a constant currently being computed contributes
    // `false` to its own caller to avoid an infinite loop; the cached
    // result then reflects only what was reachable WITHOUT the cycle.
    bool unfoldExposesHead(
        const std::string& constantName,
        const std::string& targetHeadName,
        std::unordered_set<std::string>& visiting) {
        if (constantName == targetHeadName) return true;
        const std::string cacheKey =
            constantName + "|" + targetHeadName;
        auto cached = unfoldExposesHeadCache_.find(cacheKey);
        if (cached != unfoldExposesHeadCache_.end()) {
            return cached->second;
        }
        if (visiting.count(constantName)) return false;
        visiting.insert(constantName);
        bool result = false;
        const Declaration* declaration =
            environment_.lookup(constantName);
        if (declaration) {
            if (auto* def = std::get_if<Definition>(declaration)) {
                // Opaque definitions can't be δ-unfolded by WHNF, so
                // their body never gets exposed.
                if (def->opacity == Opacity::Transparent) {
                    result = expressionReferencesConstant(
                        def->body, targetHeadName, visiting);
                }
            }
        }
        visiting.erase(constantName);
        unfoldExposesHeadCache_[cacheKey] = result;
        return result;
    }

    ExpressionPointer abstractStructuralOccurrenceWithWHNF(
        ExpressionPointer expression,
        ExpressionPointer target,
        const std::string& targetHeadName,
        int currentDepth,
        int& occurrenceCount,
        int& whnfFuel) {
        // We can't early-stop after the first match: the motive must
        // abstract EVERY occurrence so motive(constructor) reduces
        // uniformly when the kernel ι-reduces in each arm.
        ExpressionPointer shiftedTarget =
            currentDepth == 0 ? target : shift(target, currentDepth);
        // Try structural match on the un-reduced expression first; if it
        // matches, no need to WHNF (which can be expensive and may not
        // change the head). For Application-headed expressions whose
        // head is the target's head (e.g. both are `classical_decidable`
        // applications), fall back to full definitional equality —
        // kernel WHNF often leaves the term in an intermediate form
        // (Let-binders, partial β-substitutions, recursor wrappings)
        // that doesn't match structurally but IS the same proposition.
        if (structurallyEqual(expression, shiftedTarget)) {
            occurrenceCount++;
            return makeBoundVariable(currentDepth);
        }
        if (!targetHeadName.empty()) {
            std::string thisHeadName =
                applicationHeadConstantName(expression);
            if (thisHeadName == targetHeadName) {
                // Open the local binders so isDefinitionallyEqual can
                // walk through let-binder ζ-reductions etc. The caller
                // passed expressions in closed (BoundVariable) form
                // against this localBinders scope.
                // (We use a fresh empty context since the comparison
                // is at depth `currentDepth` and the kernel's defeq
                // doesn't need extra context for closed expressions —
                // it can handle BoundVariable refs directly.)
                Context emptyContext;
                if (isDefinitionallyEqual(
                        environment_, emptyContext,
                        expression, shiftedTarget)) {
                    occurrenceCount++;
                    return makeBoundVariable(currentDepth);
                }
            }
        }
        // For Application nodes, conditionally WHNF: δ-unfolding may
        // expose the target as a subterm. Only WHNF if the head's
        // definition transitively references `targetHeadName` —
        // otherwise we'd waste fuel expanding propositional chains
        // (Real.LessOrEqual, Set.member, etc.) that can never produce
        // a `Logic.classical_decidable(…)` subterm.
        ExpressionPointer working = expression;
        if (whnfFuel > 0
            && std::get_if<Application>(&expression->node)) {
            std::string headName =
                applicationHeadConstantName(expression);
            // Always WHNF an Application whose head isn't a Constant —
            // that's a β-redex (Application of Lambda) and reducing it
            // is essentially free; if we don't, the head-relevance gate
            // never gets a chance to fire on the result. For
            // Constant-headed Applications, only WHNF if the head's
            // definition transitively references the target's head.
            bool maybeRelevant = headName.empty();
            if (!maybeRelevant && !targetHeadName.empty()) {
                std::unordered_set<std::string> visiting;
                maybeRelevant = unfoldExposesHead(
                    headName, targetHeadName, visiting);
            }
            if (maybeRelevant) {
                ExpressionPointer reduced;
                try {
                    reduced = weakHeadNormalForm(environment_, expression);
                } catch (const TypeError&) {
                    reduced = expression;
                }
                if (!structurallyEqual(reduced, expression)) {
                    whnfFuel--;
                    working = reduced;
                    if (structurallyEqual(working, shiftedTarget)) {
                        occurrenceCount++;
                        return makeBoundVariable(currentDepth);
                    }
                }
            }
        }
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&working->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= currentDepth) {
                return makeBoundVariable(index + 1);
            }
            return working;
        }
        if (auto* pi = std::get_if<Pi>(&working->node)) {
            // Skip WHNF in the domain: domains are types (propositions
            // or sorts), not the user-value path where
            // `classical_decidable(P)` lives. Use the cheap structural
            // walker for the domain so any literal occurrence there
            // still gets abstracted.
            ExpressionPointer newDomain = abstractStructuralOccurrence(
                pi->domain, target, currentDepth, occurrenceCount);
            return makePi(pi->displayHint, newDomain,
                abstractStructuralOccurrenceWithWHNF(
                    pi->codomain, target, targetHeadName,
                    currentDepth + 1, occurrenceCount, whnfFuel));
        }
        if (auto* lambda = std::get_if<Lambda>(&working->node)) {
            // Same domain-skip as for Pi.
            ExpressionPointer newDomain = abstractStructuralOccurrence(
                lambda->domain, target, currentDepth, occurrenceCount);
            return makeLambda(lambda->displayHint, newDomain,
                abstractStructuralOccurrenceWithWHNF(
                    lambda->body, target, targetHeadName,
                    currentDepth + 1, occurrenceCount, whnfFuel));
        }
        if (auto* application =
                std::get_if<Application>(&working->node)) {
            return makeApplication(
                abstractStructuralOccurrenceWithWHNF(
                    application->function, target, targetHeadName,
                    currentDepth, occurrenceCount, whnfFuel),
                abstractStructuralOccurrenceWithWHNF(
                    application->argument, target, targetHeadName,
                    currentDepth, occurrenceCount, whnfFuel));
        }
        if (auto* letNode = std::get_if<Let>(&working->node)) {
            // ζ-substitute the let's value into the body before
            // recursing — otherwise the body's BV(0) references to the
            // let-binder don't match the target's literal form.
            ExpressionPointer substituted = substitute(
                letNode->body, 0, letNode->value);
            return abstractStructuralOccurrenceWithWHNF(
                substituted, target, targetHeadName,
                currentDepth, occurrenceCount, whnfFuel);
        }
        return working;
    }

    ExpressionPointer abstractStructuralOccurrence(
        ExpressionPointer expression,
        ExpressionPointer target,
        int currentDepth,
        int& occurrenceCount) {
        ExpressionPointer shiftedTarget =
            currentDepth == 0 ? target : shift(target, currentDepth);
        if (structurallyEqual(expression, shiftedTarget)) {
            occurrenceCount++;
            return makeBoundVariable(currentDepth);
        }
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int index = boundVariable->deBruijnIndex;
            if (index >= currentDepth) {
                return makeBoundVariable(index + 1);
            }
            return expression;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                abstractStructuralOccurrence(pi->domain, target,
                                              currentDepth, occurrenceCount),
                abstractStructuralOccurrence(pi->codomain, target,
                                              currentDepth + 1,
                                              occurrenceCount));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                abstractStructuralOccurrence(lambda->domain, target,
                                              currentDepth, occurrenceCount),
                abstractStructuralOccurrence(lambda->body, target,
                                              currentDepth + 1,
                                              occurrenceCount));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                abstractStructuralOccurrence(application->function, target,
                                              currentDepth, occurrenceCount),
                abstractStructuralOccurrence(application->argument, target,
                                              currentDepth, occurrenceCount));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                abstractStructuralOccurrence(let->type, target,
                                              currentDepth, occurrenceCount),
                abstractStructuralOccurrence(let->value, target,
                                              currentDepth, occurrenceCount),
                abstractStructuralOccurrence(let->body, target,
                                              currentDepth + 1,
                                              occurrenceCount));
        }
        // Sort, FreeVariable, Constant — no children, return as-is.
        return expression;
    }

    // `rewrite(lemma)` where `lemma : Equality.{u}(T', x, y)` and the
    // current goal is `Equality.{v}(T, A, B)`: builds the proof
    //   `Equality.congruence.{u, v}(T', T, λ z ⇒ A[z/x], x, y, lemma)`
    // — locating the unique structural occurrence of `x` inside `A` and
    // replacing it with the binder of an inserted Lambda. Errors if `x`
    // doesn't appear or appears more than once (the user would have to
    // disambiguate via explicit `congruenceOf`).
    // `rewrite(equalityProof, term)` — term-level form. Given
    // `equalityProof : Equality(A, x, y)` and `term : P(x)` for some
    // Proposition-valued `P`, returns a term of type `P(y)`. Implemented
    // as `Equality.transport_proposition(A, λz. P[x↦z], x, y,
    // equalityProof, term)`. The motive is recovered by locating the
    // unique structural occurrence of `x` in `term`'s inferred type and
    // abstracting it.
    //
    // Distinguished from the 1-arg `rewrite(equalityProof)` (calc-step
    // form) by argument count. The two have different return types and
    // operate in different positions: term-level transport produces a
    // proof witness; calc-step rewrite produces an equality between two
    // calc endpoints.
    ExpressionPointer desugarRewriteTerm(
        SurfaceExpressionPointer equalityProofSurface,
        SurfaceExpressionPointer termSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int /*column*/) {
        Frame frame(*this,
            "rewrite (term-level) at line " + std::to_string(line));
        ExpressionPointer equalityProofKernel = elaborateExpression(
            *equalityProofSurface, localBinders);
        ExpressionPointer equalityProofTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, equalityProofKernel));
        EqualityComponents lemmaComponentsOpened =
            extractEqualityComponents(
                equalityProofTypeOpened, "rewrite (equality proof)",
                line);
        ExpressionPointer carrierType = closeOverLocalBinders(
            lemmaComponentsOpened.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer leftEndpoint = closeOverLocalBinders(
            lemmaComponentsOpened.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer rightEndpoint = closeOverLocalBinders(
            lemmaComponentsOpened.rightEndpoint,
            localBinders, localBinders.size());

        ExpressionPointer termKernel = elaborateExpression(
            *termSurface, localBinders);
        // Deliberately DON'T weak-head-normalise term's inferred type
        // here: definitions like `Rational.LessThan(x, y) :=
        // And(LessOrEqual(x, y), Not(x = y))` unfold to a Constant
        // head whose argument appears twice (once on each conjunct),
        // and `Rational.IsNonneg(Quotient.mk(rep))` unfolds via
        // `Quotient.lift` so the `Quotient.mk` head disappears.
        // Either kills the structural-occurrence search. Keeping the
        // unreduced form gives us the user-visible motive shape, with
        // the rewrite endpoint exactly where they expect it. If no
        // match is found at this level we fall back to WHNF — that
        // covers sites where the term's type is genuinely behind a
        // definition that must be peeled.
        ExpressionPointer termTypeUnreduced =
            inferTypeInLocalContext(localBinders, termKernel);
        ExpressionPointer termTypeUnreducedClosed = closeOverLocalBinders(
            termTypeUnreduced, localBinders, localBinders.size());

        // Try six combinations of (term type, left endpoint) ×
        // (unreduced, head-beta/WHNF, deep-beta) in priority order.
        // WHNF-ing the left endpoint catches `congruenceOf(λr. P(r),
        // eq)` whose stated type's lhs is the unreduced beta-redex
        // `Application(λ, x)` while the term's inferred type carries
        // the beta-reduced `P(x)`. WHNF-ing the term type catches
        // definitions like `Rational.IsNonneg(...)` that wrap the
        // underlying claim. Deep-beta-reducing the term type catches
        // internal redexes (e.g. `sequenceFunction(λn. …, m)` from
        // Quotient.lift bodies in real analysis) that WHNF leaves
        // alone because it only reduces at the head.
        auto trySearch = [&](const ExpressionPointer& termTypeClosed,
                             const ExpressionPointer& lhs)
            -> std::pair<int, ExpressionPointer> {
            int count = 0;
            ExpressionPointer body = abstractStructuralOccurrence(
                termTypeClosed, lhs, /*currentDepth=*/0, count);
            return {count, std::move(body)};
        };

        // Beta-only reduction at the spine head. Required for
        // `congruenceOf(λr. P(r), eq)`: the equality's stated type
        // carries the unreduced beta-redex `(λr. P(r))(x)` as its
        // left endpoint, while the term's inferred type has the
        // beta-reduced `P(x)`. We can't use weakHeadNormalForm here
        // because that would δ-unfold any subsequent Constant head
        // (e.g. `Rational.padic_absolute_value`, which is defined as
        // a `Quotient.lift`) and lose the user-visible shape we want
        // to match against the term's type.
        auto betaReduceHead =
            [](ExpressionPointer e) -> ExpressionPointer {
            while (std::holds_alternative<Application>(e->node)) {
                std::vector<ExpressionPointer> args;
                ExpressionPointer head = e;
                while (auto* app = std::get_if<Application>(&head->node)) {
                    args.push_back(app->argument);
                    head = app->function;
                }
                std::reverse(args.begin(), args.end());
                if (auto* lambda = std::get_if<Lambda>(&head->node)) {
                    ExpressionPointer reduced =
                        substitute(lambda->body, 0, args[0]);
                    for (size_t i = 1; i < args.size(); ++i) {
                        reduced = makeApplication(reduced, args[i]);
                    }
                    e = reduced;
                } else {
                    break;
                }
            }
            return e;
        };

        ExpressionPointer leftEndpointBetaOpened =
            betaReduceHead(lemmaComponentsOpened.leftEndpoint);
        ExpressionPointer leftEndpointWhnf = closeOverLocalBinders(
            leftEndpointBetaOpened, localBinders, localBinders.size());

        // Try each (term form, endpoint form) combo in priority order
        // and remember each occurrence count for the failure
        // diagnostic. The body that wins is the FIRST combo that
        // returns exactly one occurrence — preferring the user's
        // surface shape (unreduced × unreduced) when possible — so a
        // success doesn't drift to a more-reduced form than needed.
        struct ComboAttempt {
            const char* label;
            int count = -1;  // -1 = not attempted
        };
        ComboAttempt attempts[6] = {
            {"unreduced term × unreduced endpoint"},
            {"unreduced term × β-reduced endpoint"},
            {"WHNF term × unreduced endpoint"},
            {"WHNF term × β-reduced endpoint"},
            {"deep-β term × unreduced endpoint"},
            {"deep-β term × β-reduced endpoint"},
        };
        int occurrenceCount = 0;
        ExpressionPointer abstractedBody;
        bool found = false;

        auto runAttempt =
            [&](int slot,
                const ExpressionPointer& termClosed,
                const ExpressionPointer& lhs) {
            if (found) return;
            auto [count, body] = trySearch(termClosed, lhs);
            attempts[slot].count = count;
            if (count == 1) {
                occurrenceCount = count;
                abstractedBody = std::move(body);
                found = true;
            }
        };

        runAttempt(0, termTypeUnreducedClosed, leftEndpoint);
        runAttempt(1, termTypeUnreducedClosed, leftEndpointWhnf);

        ExpressionPointer termTypeWhnfClosed;
        if (!found) {
            ExpressionPointer termTypeWhnf = weakHeadNormalForm(
                environment_, termTypeUnreduced);
            termTypeWhnfClosed = closeOverLocalBinders(
                termTypeWhnf, localBinders, localBinders.size());
            runAttempt(2, termTypeWhnfClosed, leftEndpoint);
            runAttempt(3, termTypeWhnfClosed, leftEndpointWhnf);
        }

        ExpressionPointer termTypeDeepBetaClosed;
        if (!found) {
            ExpressionPointer termTypeDeepBeta =
                deepBetaReduce(termTypeUnreduced);
            termTypeDeepBetaClosed = closeOverLocalBinders(
                termTypeDeepBeta, localBinders, localBinders.size());
            runAttempt(4, termTypeDeepBetaClosed, leftEndpoint);
            runAttempt(5, termTypeDeepBetaClosed, leftEndpointWhnf);
        }

        // If no combo found exactly one occurrence, build a diagnostic
        // that breaks down each attempt's count so the user can tell
        // whether they have a 0-occurrence (mismatch), a >1-occurrence
        // (ambiguity), or both depending on normalisation level.
        auto buildFailureBreakdown = [&]() {
            std::string breakdown;
            for (const ComboAttempt& a : attempts) {
                if (a.count < 0) continue;
                breakdown += "\n      ";
                breakdown += a.label;
                breakdown += ": ";
                if (a.count == 0) {
                    breakdown += "0 occurrences";
                } else {
                    breakdown += std::to_string(a.count) +
                                 " occurrences";
                }
            }
            return breakdown;
        };

        // Use the unreduced form for the diagnostic display.
        ExpressionPointer termTypeOpened = termTypeUnreduced;
        if (!found) {
            // Decide whether the dominant failure mode was "0 occurrences"
            // or "too many" so the headline matches what the user will
            // most likely act on.
            bool sawZeroOnly = true;
            int maxCount = 0;
            for (const ComboAttempt& a : attempts) {
                if (a.count <= 0) continue;
                sawZeroOnly = false;
                if (a.count > maxCount) maxCount = a.count;
            }
            std::string headline;
            if (sawZeroOnly) {
                headline =
                    "rewrite(eq, term): the equality's left endpoint "
                    "does not appear (structurally) in term's type "
                    "(`"
                    + prettyPrintInLocalScope(termTypeOpened,
                                                localBinders)
                    + "`).";
            } else {
                headline =
                    "rewrite(eq, term): the equality's left endpoint "
                    "appears "
                    + std::to_string(maxCount)
                    + " time(s) in term's type — `rewrite` needs "
                      "exactly one. Use explicit "
                      "Equality.transport_proposition(...) to "
                      "disambiguate the position. (`"
                    + prettyPrintInLocalScope(termTypeOpened,
                                                localBinders)
                    + "`)";
            }
            throwElaborate(headline
                + "\n  Occurrence search:"
                + buildFailureBreakdown());
        }
        ExpressionPointer motiveLambda = makeLambda(
            "_rewriteHole", carrierType, std::move(abstractedBody));

        ExpressionPointer call = makeConstant(
            "Equality.transport_proposition",
            {lemmaComponentsOpened.carrierUniverseLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), std::move(motiveLambda));
        call = makeApplication(std::move(call), std::move(leftEndpoint));
        call = makeApplication(std::move(call), std::move(rightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        call = makeApplication(std::move(call), std::move(termKernel));
        return call;
    }

    ExpressionPointer desugarRewrite(
        SurfaceExpressionPointer lemmaSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "rewrite at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "rewrite needs an expected type from context — use it "
                "in a calc step, where the step's `previous = next` "
                "equality provides the target");
        }
        // The 1-arg rewrite wraps via Equality.congruence. If that name
        // isn't declared (small test modules sometimes omit it), bail
        // out so the caller can fall through to its own diagnostic,
        // rather than handing the kernel a term that mentions an
        // undefined constant.
        if (!environment_.lookup("Equality.congruence")) {
            throwElaborate(
                "rewrite: Equality.congruence is not declared in "
                "scope; cannot synthesise the calc-step congruence "
                "wrap");
        }
        EqualityComponents goalComponents =
            extractEqualityComponents(expectedType, "rewrite (goal)", line);

        // Elaborate the lemma; close its inferred type's components back
        // to BoundVariables so they live in the same scope as
        // `expectedType` (which arrived in closed form).
        ExpressionPointer lemmaKernel =
            elaborateExpression(*lemmaSurface, localBinders);
        ExpressionPointer lemmaTypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, lemmaKernel));
        EqualityComponents lemmaComponentsOpened =
            extractEqualityComponents(lemmaTypeOpened, "rewrite (lemma)",
                                       line);
        ExpressionPointer lemmaCarrier = closeOverLocalBinders(
            lemmaComponentsOpened.carrierType,
            localBinders, localBinders.size());
        ExpressionPointer lemmaLeft = closeOverLocalBinders(
            lemmaComponentsOpened.leftEndpoint,
            localBinders, localBinders.size());
        ExpressionPointer lemmaRight = closeOverLocalBinders(
            lemmaComponentsOpened.rightEndpoint,
            localBinders, localBinders.size());

        // Locate the unique occurrence of `lemmaLeft` inside the goal's
        // left endpoint, replacing it with BoundVariable(0) and shifting
        // outer references up by 1. If the forward direction doesn't
        // find a match, automatically try the reverse direction (as if
        // the user wrote `rewrite(Equality.symmetry(lemma))`).
        int occurrenceCount = 0;
        ExpressionPointer abstractedBody = abstractStructuralOccurrence(
            goalComponents.leftEndpoint, lemmaLeft,
            /*currentDepth=*/0, occurrenceCount);
        bool reversed = false;
        if (occurrenceCount == 0) {
            int reverseOccurrenceCount = 0;
            ExpressionPointer reverseAbstractedBody =
                abstractStructuralOccurrence(
                    goalComponents.leftEndpoint, lemmaRight,
                    /*currentDepth=*/0, reverseOccurrenceCount);
            if (reverseOccurrenceCount > 0) {
                occurrenceCount = reverseOccurrenceCount;
                abstractedBody = std::move(reverseAbstractedBody);
                reversed = true;
            } else {
                throwElaborate(
                    "rewrite: neither endpoint of the lemma appears "
                    "(structurally) in the goal's left side");
            }
        }
        if (occurrenceCount > 1) {
            throwElaborate(
                "rewrite: the lemma's left endpoint appears "
                + std::to_string(occurrenceCount)
                + " times in the goal's left side — use explicit "
                "`congruenceOf(function (z) => …, lemma)` to "
                "disambiguate the position");
        }
        ExpressionPointer abstractionLambda = makeLambda(
            "_rewriteHole", lemmaCarrier, abstractedBody);

        // Build `Equality.congruence.{u, v}(lemmaT, goalT, λ,
        //                                    lemmaLeft, lemmaRight,
        //                                    lemma)`.
        // When reversed, swap the endpoints and wrap the lemma in
        // Equality.symmetry so the resulting term still type-checks.
        ExpressionPointer effectiveLemma = lemmaKernel;
        ExpressionPointer effectiveLeft = lemmaLeft;
        ExpressionPointer effectiveRight = lemmaRight;
        if (reversed) {
            ExpressionPointer symmetryCall = makeConstant(
                "Equality.symmetry",
                {lemmaComponentsOpened.carrierUniverseLevel});
            symmetryCall = makeApplication(
                std::move(symmetryCall), lemmaCarrier);
            symmetryCall = makeApplication(
                std::move(symmetryCall), lemmaLeft);
            symmetryCall = makeApplication(
                std::move(symmetryCall), lemmaRight);
            symmetryCall = makeApplication(
                std::move(symmetryCall), std::move(effectiveLemma));
            effectiveLemma = std::move(symmetryCall);
            std::swap(effectiveLeft, effectiveRight);
        }
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {lemmaComponentsOpened.carrierUniverseLevel,
             goalComponents.carrierUniverseLevel});
        call = makeApplication(std::move(call), lemmaCarrier);
        call = makeApplication(std::move(call), goalComponents.carrierType);
        call = makeApplication(std::move(call), std::move(abstractionLambda));
        call = makeApplication(std::move(call), std::move(effectiveLeft));
        call = makeApplication(std::move(call), std::move(effectiveRight));
        call = makeApplication(std::move(call), std::move(effectiveLemma));
        return call;
    }

    // ---- simplify --------------------------------------------------------
    //
    // `simplify(L1, L2, …, Ln)` in calc context: discharges the current
    // step's `a = b` by repeatedly rewriting `a` (or arbitrary subterms of
    // it) using any of the supplied lemmas, until the resulting term is
    // definitionally equal to `b`. Each lemma is a polymorphic equality:
    // `(p1 : T1) → … → (pk : Tk) → Equality.{u}(C, LHS, RHS)`. simplify
    // picks the first subterm of the current term that any lemma's LHS
    // pattern unifies with (Pi binders treated as metavariables), then
    // applies that lemma's RHS at the matched site via `Equality.congruence`
    // — same shape as `rewrite(L)` but with the lemma instantiated
    // automatically.
    //
    // V1 limitations:
    //   * Pattern matching is first-order: linear, no higher-order vars,
    //     no descent under binders. The lemma's LHS may not itself contain
    //     a Lambda/Pi/Let; the search through the goal also does not enter
    //     binders.
    //   * Only forward direction (LHS → RHS). The user must pass a
    //     symmetric lemma if they need a reverse rewrite.
    //   * Termination is bounded by a fixed iteration limit; non-confluent
    //     rule sets (e.g. naked commutativity) can hit the bound.

    // First-order match. `pattern` lives in a scope with `numPatternBinders`
    // leading Pi binders (the lemma's universal quantifiers); pattern uses
    // BoundVariable(0..numPatternBinders-1) to refer to them. Higher-indexed
    // BoundVariables refer to scope above the lemma's type — for a
    // top-level lemma these don't occur.
    //
    // On success, `bindings[i]` is the term substituted for the i-th
    // pattern binder. Bindings are populated as the match descends; if a
    // metavariable appears twice in the pattern, the second occurrence is
    // required to match the term already recorded (linearity).
    bool tryFirstOrderMatch(
        ExpressionPointer pattern,
        ExpressionPointer term,
        int numPatternBinders,
        std::vector<ExpressionPointer>& bindings) {
        if (auto* boundVar =
                std::get_if<BoundVariable>(&pattern->node)) {
            int idx = boundVar->deBruijnIndex;
            if (idx < numPatternBinders) {
                if (bindings[idx]) {
                    return structurallyEqual(bindings[idx], term);
                }
                bindings[idx] = term;
                return true;
            }
            // Reference outside the lemma's universal quantifiers — must
            // be a literal match against an outer BoundVariable in the
            // term (after adjusting for the binder offset).
            auto* termVar =
                std::get_if<BoundVariable>(&term->node);
            if (!termVar) return false;
            return termVar->deBruijnIndex == idx - numPatternBinders;
        }
        if (auto* application =
                std::get_if<Application>(&pattern->node)) {
            auto* termApp =
                std::get_if<Application>(&term->node);
            if (!termApp) return false;
            return tryFirstOrderMatch(application->function,
                                       termApp->function,
                                       numPatternBinders, bindings)
                && tryFirstOrderMatch(application->argument,
                                       termApp->argument,
                                       numPatternBinders, bindings);
        }
        if (std::get_if<Constant>(&pattern->node)
            || std::get_if<Sort>(&pattern->node)
            || std::get_if<FreeVariable>(&pattern->node)) {
            return structurallyEqual(pattern, term);
        }
        // Pi/Lambda/Let — v1 doesn't match under binders.
        return false;
    }

    // Substitute the pattern's metavariables with their matched
    // expressions. `pattern` may reference Bound(0..numPatternBinders-1)
    // (substituted) and Bound(k >= numPatternBinders) (shifted down by
    // numPatternBinders to refer to the surrounding outer scope).
    ExpressionPointer instantiatePattern(
        ExpressionPointer pattern,
        const std::vector<ExpressionPointer>& bindings,
        int numPatternBinders,
        int currentDepth = 0) {
        if (auto* boundVar =
                std::get_if<BoundVariable>(&pattern->node)) {
            int idx = boundVar->deBruijnIndex;
            if (idx < currentDepth) {
                return pattern;  // bound locally inside the pattern
            }
            int effective = idx - currentDepth;
            if (effective < numPatternBinders) {
                ExpressionPointer binding = bindings[effective];
                if (currentDepth > 0) {
                    binding = shift(binding, currentDepth);
                }
                return binding;
            }
            return makeBoundVariable(
                idx - numPatternBinders);
        }
        if (auto* application =
                std::get_if<Application>(&pattern->node)) {
            return makeApplication(
                instantiatePattern(application->function, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(application->argument, bindings,
                                    numPatternBinders, currentDepth));
        }
        if (auto* pi = std::get_if<Pi>(&pattern->node)) {
            return makePi(pi->displayHint,
                instantiatePattern(pi->domain, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(pi->codomain, bindings,
                                    numPatternBinders, currentDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&pattern->node)) {
            return makeLambda(lambda->displayHint,
                instantiatePattern(lambda->domain, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(lambda->body, bindings,
                                    numPatternBinders, currentDepth + 1));
        }
        if (auto* let = std::get_if<Let>(&pattern->node)) {
            return makeLet(let->displayHint,
                instantiatePattern(let->type, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(let->value, bindings,
                                    numPatternBinders, currentDepth),
                instantiatePattern(let->body, bindings,
                                    numPatternBinders, currentDepth + 1));
        }
        // Constant / Sort / FreeVariable — pure leaves.
        return pattern;
    }

    // A prepared simplify lemma: its kernel-level reference plus the
    // shape data needed to match-and-apply.
    struct SimplifyLemma {
        ExpressionPointer lemmaReference;     // kernel value: the lemma
        int numBinders;                        // count of universal Pis
        std::vector<ExpressionPointer> binderTypes;  // domain of each Pi
        ExpressionPointer carrier;             // T in Equality.{u}(T, …, …)
        ExpressionPointer leftPattern;         // LHS, Bound(0..n-1) = metas
        ExpressionPointer rightPattern;        // RHS, same convention
        LevelPointer carrierUniverseLevel;
    };

    // Walk `term` looking for the first subterm (Application spine,
    // leaving binders alone) where any lemma's LHS pattern matches. On
    // success, returns the lemma's index and populates `bindings`. The
    // returned `matchedSubterm` is the subterm where the match landed.
    bool findFirstSimplifyMatch(
        ExpressionPointer term,
        const std::vector<SimplifyLemma>& lemmas,
        size_t& matchedLemmaIndex,
        std::vector<ExpressionPointer>& bindings,
        ExpressionPointer& matchedSubterm) {
        for (size_t i = 0; i < lemmas.size(); ++i) {
            std::vector<ExpressionPointer> attempt(
                lemmas[i].numBinders, nullptr);
            if (tryFirstOrderMatch(lemmas[i].leftPattern, term,
                                    lemmas[i].numBinders, attempt)) {
                bool complete = true;
                for (const auto& b : attempt) {
                    if (!b) { complete = false; break; }
                }
                if (complete) {
                    matchedLemmaIndex = i;
                    bindings = std::move(attempt);
                    matchedSubterm = term;
                    return true;
                }
            }
        }
        if (auto* application =
                std::get_if<Application>(&term->node)) {
            if (findFirstSimplifyMatch(application->function, lemmas,
                                         matchedLemmaIndex, bindings,
                                         matchedSubterm)) {
                return true;
            }
            return findFirstSimplifyMatch(application->argument, lemmas,
                                            matchedLemmaIndex, bindings,
                                            matchedSubterm);
        }
        // Don't descend into Pi/Lambda/Let bodies in v1 — the captured
        // binders would make any match references invalid in the outer
        // proof. Constants/Sorts/Bound/FreeVariable are leaves.
        return false;
    }

    // Prepare the kernel-level proof witness for one rewrite step.
    // `goalCarrier` is the carrier of the calc step's equality; `current`
    // is the term we're rewriting (LHS of the residual `current = target`
    // step); `newCurrent` is the result after this rewrite. The returned
    // expression has type `Equality.{v}(goalCarrier, current, newCurrent)`.
    ExpressionPointer buildSingleSimplifyStep(
        const SimplifyLemma& lemma,
        const std::vector<ExpressionPointer>& bindings,
        ExpressionPointer current,
        ExpressionPointer matchedSubterm,
        ExpressionPointer newCurrent,
        ExpressionPointer goalCarrier,
        LevelPointer goalCarrierUniverseLevel,
        ExpressionPointer instantiatedRight) {
        // Instantiated lemma value: lemma applied to each bound argument
        // in declaration order.
        ExpressionPointer instantiatedLemma = lemma.lemmaReference;
        for (int i = lemma.numBinders - 1; i >= 0; --i) {
            instantiatedLemma = makeApplication(
                std::move(instantiatedLemma), bindings[i]);
        }
        ExpressionPointer instantiatedCarrier =
            instantiatePattern(lemma.carrier, bindings,
                                lemma.numBinders);
        // Abstract the matched subterm out of `current`, building the
        // motive lambda for Equality.congruence.
        int occurrenceCount = 0;
        ExpressionPointer abstractedBody = abstractStructuralOccurrence(
            current, matchedSubterm, 0, occurrenceCount);
        if (occurrenceCount == 0) {
            throw ElaborateError(
                "simplify: internal — matched subterm not located "
                "structurally after match");
        }
        // Multiple matches: rewrite still produces a valid proof
        // (Equality.congruence will replace every Bound(0) in the
        // motive simultaneously), so we don't need to fail here.
        ExpressionPointer motiveLambda = makeLambda(
            "_simplifyHole", instantiatedCarrier,
            std::move(abstractedBody));
        // Equality.congruence's `x` and `y` are the lemma's endpoints
        // (matchedSubterm and instantiatedRight). The motive carries
        // the surrounding context: `motive(x) = matchedSubterm`-shaped
        // = current; `motive(y) = instantiatedRight`-shaped = newCurrent.
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {lemma.carrierUniverseLevel, goalCarrierUniverseLevel});
        call = makeApplication(std::move(call), instantiatedCarrier);
        call = makeApplication(std::move(call), goalCarrier);
        call = makeApplication(std::move(call), std::move(motiveLambda));
        call = makeApplication(std::move(call), matchedSubterm);
        call = makeApplication(std::move(call), instantiatedRight);
        call = makeApplication(std::move(call),
                                std::move(instantiatedLemma));
        (void)current;
        (void)newCurrent;
        return call;
    }

    ExpressionPointer desugarSimplify(
        const std::vector<SurfaceExpressionPointer>& lemmaSurfaces,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "simplify at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "simplify needs an expected type from context — use it "
                "in a calc step or as the body of a theorem with a "
                "declared equality conclusion");
        }
        EqualityComponents goal =
            extractEqualityComponents(expectedType, "simplify (goal)",
                                       line);

        // Prepare each lemma: elaborate to a kernel reference, close
        // its inferred type over localBinders (so references to outer
        // binders end up as BoundVariables — required for matching
        // against the closed-form goal), peel the Pi chain, then
        // extract the underlying Equality. Closing first ensures the
        // Pi binders end up at Bound(0..numBinders-1) (the matcher's
        // metavariable range) while localBinders refs land at higher
        // indices, where the matcher treats them as outer references.
        std::vector<SimplifyLemma> lemmas;
        lemmas.reserve(lemmaSurfaces.size());
        for (const auto& lemmaSurface : lemmaSurfaces) {
            SimplifyLemma prepared;
            prepared.lemmaReference =
                elaborateExpression(*lemmaSurface, localBinders);
            ExpressionPointer lemmaTypeOpened = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders,
                                          prepared.lemmaReference));
            ExpressionPointer lemmaTypeClosed = closeOverLocalBinders(
                lemmaTypeOpened, localBinders, localBinders.size());
            int numBinders = 0;
            ExpressionPointer cursor = lemmaTypeClosed;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                prepared.binderTypes.push_back(pi->domain);
                cursor = pi->codomain;
                ++numBinders;
            }
            prepared.numBinders = numBinders;
            EqualityComponents components =
                extractEqualityComponents(cursor, "simplify (lemma)",
                                           line);
            prepared.carrier = components.carrierType;
            prepared.leftPattern = components.leftEndpoint;
            prepared.rightPattern = components.rightEndpoint;
            prepared.carrierUniverseLevel =
                components.carrierUniverseLevel;
            lemmas.push_back(std::move(prepared));
        }

        // Iterate. At each step, look for any matching subterm; on
        // success, build the rewrite proof step and update the running
        // `current` value. Stop when `current` is definitionally equal
        // to the target, or when no lemma fires. `intermediates[i]` is
        // the running term BEFORE proofSteps[i]; intermediates.back()
        // is the final term after all steps.
        ExpressionPointer originalLeft = goal.leftEndpoint;
        ExpressionPointer current = goal.leftEndpoint;
        ExpressionPointer target = goal.rightEndpoint;
        std::vector<ExpressionPointer> proofSteps;
        std::vector<ExpressionPointer> intermediates;
        intermediates.push_back(current);
        const int iterationLimit = 200;

        // Build a context for definitional-equality checks, using the
        // localBinders (opened over fresh internal FreeVariables).
        auto checkDefinitionallyEqual =
            [&](ExpressionPointer left,
                ExpressionPointer right) -> bool {
            Context context = buildContextFromLocalBinders(localBinders);
            ExpressionPointer leftOpened = openOverLocalBinders(
                left, localBinders, localBinders.size());
            ExpressionPointer rightOpened = openOverLocalBinders(
                right, localBinders, localBinders.size());
            return isDefinitionallyEqual(environment_, context,
                                          leftOpened, rightOpened);
        };

        for (int iteration = 0; iteration < iterationLimit; ++iteration) {
            if (checkDefinitionallyEqual(current, target)) break;

            size_t matchedLemmaIndex = 0;
            std::vector<ExpressionPointer> bindings;
            ExpressionPointer matchedSubterm;
            if (!findFirstSimplifyMatch(current, lemmas,
                                          matchedLemmaIndex, bindings,
                                          matchedSubterm)) {
                throwElaborate(
                    "simplify: no lemma's left-hand side matches a "
                    "subterm of the current goal, and the goal is not "
                    "yet equal to its target — the rule set is "
                    "insufficient for this step");
            }
            const SimplifyLemma& matched = lemmas[matchedLemmaIndex];
            ExpressionPointer instantiatedRight = instantiatePattern(
                matched.rightPattern, bindings, matched.numBinders);
            // Replace the matched subterm with `instantiatedRight`. We
            // do this structurally — `abstractStructuralOccurrence`
            // would replace EVERY occurrence; we want the rewrite to
            // happen at the same set of positions that the proof step
            // covers (also "every occurrence"), so this is consistent.
            int occurrenceCount = 0;
            ExpressionPointer holed = abstractStructuralOccurrence(
                current, matchedSubterm, 0, occurrenceCount);
            ExpressionPointer newCurrent =
                substitute(holed, 0, instantiatedRight);
            ExpressionPointer step = buildSingleSimplifyStep(
                matched, bindings, current, matchedSubterm,
                newCurrent, goal.carrierType,
                goal.carrierUniverseLevel, instantiatedRight);
            proofSteps.push_back(std::move(step));
            current = std::move(newCurrent);
            intermediates.push_back(current);
        }

        if (!checkDefinitionallyEqual(current, target)) {
            throwElaborate(
                "simplify: hit iteration limit before reaching the "
                "target; the rule set may be non-confluent (e.g. "
                "naked commutativity)");
        }

        // Compose the proof. If no rewrites fired, the LHS was already
        // definitionally equal to the RHS — emit reflexivity at the
        // calc step's LHS (well-typed because expectedType is opaque
        // up to definitional equality).
        if (proofSteps.empty()) {
            ExpressionPointer reflexivityCall = makeConstant(
                "reflexivity",
                {goal.carrierUniverseLevel});
            reflexivityCall = makeApplication(
                std::move(reflexivityCall), goal.carrierType);
            reflexivityCall = makeApplication(
                std::move(reflexivityCall), goal.leftEndpoint);
            return reflexivityCall;
        }
        // Chain transitivities left-fold style. We tracked the
        // intermediate terms as we went, so we don't need to extract
        // them from the proof types (which would arrive in opened
        // form and require re-closing). The signature is
        //   Equality.transitivity.{u} (T : Type u) (x y z : T)
        //       (xEqY : Equality(T, x, y))
        //       (yEqZ : Equality(T, y, z))
        //   : Equality(T, x, z).
        ExpressionPointer composed = proofSteps[0];
        for (size_t i = 1; i < proofSteps.size(); ++i) {
            ExpressionPointer call = makeConstant(
                "Equality.transitivity",
                {goal.carrierUniverseLevel});
            call = makeApplication(std::move(call), goal.carrierType);
            call = makeApplication(std::move(call), originalLeft);
            call = makeApplication(std::move(call), intermediates[i]);
            call = makeApplication(std::move(call),
                                    intermediates[i + 1]);
            call = makeApplication(std::move(call), composed);
            call = makeApplication(std::move(call), proofSteps[i]);
            composed = std::move(call);
        }
        return composed;
    }

    // ---- absurd ---------------------------------------------------------
    //
    // `absurd(witness)` — discharges any goal from a contradictory
    // witness. Recognized shapes for `witness`'s type:
    //   * `False`                                  — used directly.
    //   * `successor(K) ≤ zero`                    — applies
    //                                                Natural.not_less_or_equal_successor_zero.
    //   * `successor(K) = zero` / `zero = successor(K)` — applies
    //                                                Natural.successor_not_zero /
    //                                                Natural.zero_not_successor.
    // Then emits `False.eliminate_proposition(GOAL, falseProof)` where
    // GOAL comes from the expected type at the call site. Adding more
    // shapes is mechanical — register the pattern + matching lemma name
    // below.
    ExpressionPointer desugarAbsurd(
        SurfaceExpressionPointer witnessSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "absurd at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "absurd needs an expected type from context — use it "
                "in a position with a known goal");
        }

        ExpressionPointer witnessKernel =
            elaborateExpression(*witnessSurface, localBinders);
        ExpressionPointer witnessTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, witnessKernel));
        ExpressionPointer witnessType = closeOverLocalBinders(
            witnessTypeOpened, localBinders, localBinders.size());

        ExpressionPointer falseProof;

        // Shape: witness is already a proof of False.
        if (auto* constant =
                std::get_if<Constant>(&witnessType->node)) {
            if (constant->name == "False") {
                falseProof = witnessKernel;
            }
        }

        // Shape: `LessOrEqual(successor(K), zero)`. The type is built
        // as `App(App(LessOrEqual, successor(K)), zero)`. Both
        // endpoints are WHNF'd so that definitional reductions like
        // `successor(k) + b → successor(k + b)` expose the
        // constructor.
        if (!falseProof) {
            auto* outerApp =
                std::get_if<Application>(&witnessType->node);
            if (outerApp) {
                ExpressionPointer rhsNormalised = weakHeadNormalForm(
                    environment_, outerApp->argument);
                auto* zeroConstant = std::get_if<Constant>(
                    &rhsNormalised->node);
                bool rhsIsZero = zeroConstant
                    && zeroConstant->name == "zero";
                auto* innerApp = std::get_if<Application>(
                    &outerApp->function->node);
                if (rhsIsZero && innerApp) {
                    auto* head = std::get_if<Constant>(
                        &innerApp->function->node);
                    if (head && head->name == "LessOrEqual") {
                        ExpressionPointer lhsNormalised =
                            weakHeadNormalForm(
                                environment_, innerApp->argument);
                        auto* succApp = std::get_if<Application>(
                            &lhsNormalised->node);
                        if (succApp) {
                            auto* succHead = std::get_if<Constant>(
                                &succApp->function->node);
                            if (succHead
                                && succHead->name == "successor") {
                                ExpressionPointer kValue =
                                    succApp->argument;
                                ExpressionPointer call = makeConstant(
                                    "Natural.not_less_or_equal_successor_zero",
                                    {});
                                call = makeApplication(
                                    std::move(call), kValue);
                                call = makeApplication(
                                    std::move(call), witnessKernel);
                                falseProof = std::move(call);
                            }
                        }
                    }
                }
            }
        }

        // Shapes: `successor(K) = zero` or `zero = successor(K)` on
        // `Natural`. We extract via extractEqualityComponents and
        // dispatch based on which side is `successor(_)`.
        if (!falseProof) {
            EqualityComponents components;
            bool hasComponents = false;
            try {
                components = extractEqualityComponents(
                    witnessType, "absurd", line);
                hasComponents = true;
            } catch (const ElaborateError&) {
                hasComponents = false;
            }
            if (hasComponents) {
                auto* carrierConstant = std::get_if<Constant>(
                    &components.carrierType->node);
                bool carrierIsNatural = carrierConstant
                    && carrierConstant->name == "Natural";
                auto isSuccessor = [&](ExpressionPointer expression,
                                       ExpressionPointer& inner)
                                       -> bool {
                    ExpressionPointer normalised =
                        weakHeadNormalForm(environment_, expression);
                    auto* application = std::get_if<Application>(
                        &normalised->node);
                    if (!application) return false;
                    auto* head = std::get_if<Constant>(
                        &application->function->node);
                    if (!head || head->name != "successor") {
                        return false;
                    }
                    inner = application->argument;
                    return true;
                };
                auto isZero = [&](ExpressionPointer expression)
                                  -> bool {
                    ExpressionPointer normalised =
                        weakHeadNormalForm(environment_, expression);
                    auto* constant = std::get_if<Constant>(
                        &normalised->node);
                    return constant && constant->name == "zero";
                };
                ExpressionPointer kValue;
                if (carrierIsNatural
                    && isSuccessor(components.leftEndpoint, kValue)
                    && isZero(components.rightEndpoint)) {
                    ExpressionPointer call = makeConstant(
                        "Natural.successor_not_zero", {});
                    call = makeApplication(std::move(call), kValue);
                    call = makeApplication(std::move(call),
                                            witnessKernel);
                    falseProof = std::move(call);
                } else if (carrierIsNatural
                    && isZero(components.leftEndpoint)
                    && isSuccessor(components.rightEndpoint,
                                    kValue)) {
                    ExpressionPointer call = makeConstant(
                        "Natural.zero_not_successor", {});
                    call = makeApplication(std::move(call), kValue);
                    call = makeApplication(std::move(call),
                                            witnessKernel);
                    falseProof = std::move(call);
                }
            }
        }

        if (!falseProof) {
            throwElaborate(
                "absurd: argument's type is not `False` and doesn't "
                "match a recognized contradiction shape "
                "(supported: succ(K) ≤ zero, succ(K) = zero, "
                "zero = succ(K)). Use `False.eliminate_proposition` "
                "directly if you already have a False proof from "
                "some other source.");
        }

        // Dispatch between `False.eliminate_proposition` (for goals in
        // Proposition) and `False.eliminate.{u}` (for goals in
        // Type u = Sort u+1). The goal's universe level is the level
        // of the Sort returned by inferType(expectedType).
        Context openedContext = buildContextFromLocalBinders(localBinders);
        ExpressionPointer goalSort = weakHeadNormalForm(
            environment_,
            inferType(environment_, openedContext,
                       openOverLocalBinders(
                           expectedType, localBinders,
                           localBinders.size())));
        auto* sortNode = std::get_if<Sort>(&goalSort->node);
        if (!sortNode) {
            throwElaborate(
                "absurd: internal — goal type's kind isn't a Sort");
        }
        std::optional<int> levelConstant =
            levelAsConstant(sortNode->level);

        if (levelConstant && *levelConstant == 0) {
            ExpressionPointer call = makeConstant(
                "False.eliminate_proposition", {});
            call = makeApplication(std::move(call), expectedType);
            call = makeApplication(std::move(call),
                                    std::move(falseProof));
            return call;
        }
        if (!levelConstant) {
            throwElaborate(
                "absurd: goal's universe isn't a concrete level — "
                "v1 only dispatches against Proposition or "
                "Type N for explicit N");
        }
        // Type N case: pass N as the universe arg to False.eliminate.
        ExpressionPointer call = makeConstant(
            "False.eliminate",
            {makeLevelConst(*levelConstant - 1)});
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(falseProof));
        return call;
    }

    // Pick the unique overload candidate that matches the user-supplied
    // argument types. Errors if zero or multiple candidates match.
    // Matching is by Constant-head name of each parameter type (raw,
    // not WHNF'd — so a parameter declared as `Rational` matches an
    // argument of type `Rational` even though Rational δ-reduces to
    // `Quotient(...)`. WHNF is used as a fallback when the raw form
    // isn't a Constant.) Partial application of an overloaded name is
    // not supported: if `f` has only 2-ary overloads, `f(p)` is an
    // error — wrap in `function (q) => f(p, q)` instead.
    ExpressionPointer resolveOverloadedCall(
        const std::string& aliasName,
        const std::vector<std::string>& candidateNames,
        const std::vector<SurfaceExpressionPointer>& argumentSurfaces,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "overload '" + aliasName + "' resolution at line "
            + std::to_string(line));
        // Elaborate arguments and infer their head-type names.
        // When the argument surface is a SurfaceAscription
        // `(expr : T)`, derive the head name from T directly rather
        // than from inferType on the elaborated kernel term. The
        // ascription is the user's explicit label, and inferType
        // unfolds carrier aliases (e.g. `Real` -> `Quotient(...)`),
        // which would lose the label needed to pick the carrier-
        // specific overload. Concretely: `abs((Quotient.mk(rep) :
        // Real))` would otherwise match the Quotient head (no
        // candidate) instead of Real.
        std::vector<ExpressionPointer> argumentKernels;
        std::vector<std::string> argumentTypeNames;
        for (const auto& argumentSurface : argumentSurfaces) {
            ExpressionPointer argumentKernel =
                elaborateExpression(*argumentSurface, localBinders);
            argumentKernels.push_back(argumentKernel);
            std::string typeName;
            if (auto* ascription = std::get_if<SurfaceAscription>(
                    &argumentSurface->node)) {
                ExpressionPointer ascribedType = elaborateExpression(
                    *ascription->type, localBinders);
                typeName = headConstantName(ascribedType);
            } else {
                ExpressionPointer argumentTypeRaw =
                    inferTypeInLocalContext(localBinders, argumentKernel);
                typeName = headConstantName(argumentTypeRaw);
            }
            argumentTypeNames.push_back(std::move(typeName));
        }
        // Find candidates whose first N parameter-type names match.
        std::vector<std::string> matches;
        for (const auto& candidateName : candidateNames) {
            const Declaration* declaration =
                environment_.lookup(candidateName);
            if (!declaration) continue;
            ExpressionPointer signature = declarationType(*declaration);
            if (!signatureAcceptsArgumentTypes(signature,
                                                  argumentTypeNames)) {
                continue;
            }
            matches.push_back(candidateName);
        }
        if (matches.empty()) {
            std::string message =
                "no overload of '" + aliasName + "' matches arguments "
                "of types (";
            for (size_t i = 0; i < argumentTypeNames.size(); ++i) {
                if (i > 0) message += ", ";
                message += argumentTypeNames[i];
            }
            message += "); candidates:";
            for (const auto& candidate : candidateNames) {
                message += "\n  " + candidate;
            }
            throwElaborate(message);
        }
        if (matches.size() > 1) {
            std::string message =
                "ambiguous overload of '" + aliasName
                + "' on argument types (";
            for (size_t i = 0; i < argumentTypeNames.size(); ++i) {
                if (i > 0) message += ", ";
                message += argumentTypeNames[i];
            }
            message += "); multiple candidates match:";
            for (const auto& match : matches) {
                message += "\n  " + match;
            }
            message += "\nuse the fully-qualified name to disambiguate";
            throwElaborate(message);
        }
        // Build a SurfaceApplication of the chosen candidate and
        // re-elaborate it — that reuses universe-inference, leading-
        // argument inference, etc.
        SurfaceExpressionPointer resolvedHead = makeSurfaceIdentifier(
            matches[0], /*universeArgs=*/{}, line, column);
        SurfaceExpressionPointer resolvedCall = makeSurfaceApplication(
            std::move(resolvedHead),
            argumentSurfaces,
            line, column);
        return elaborateExpression(*resolvedCall, localBinders,
                                     expectedType);
    }

    // Extract a Constant head name from a type expression. Tries the
    // raw form first (so user-declared type aliases like `Rational`
    // don't get unfolded), falls back to WHNF.
    std::string headConstantName(ExpressionPointer typeExpression) {
        ExpressionPointer cursor = typeExpression;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            cursor = application->function;
        }
        if (auto* constant = std::get_if<Constant>(&cursor->node)) {
            return constant->name;
        }
        ExpressionPointer reduced = weakHeadNormalForm(
            environment_, typeExpression);
        while (auto* application =
                   std::get_if<Application>(&reduced->node)) {
            reduced = weakHeadNormalForm(environment_,
                                          application->function);
        }
        if (auto* constant = std::get_if<Constant>(&reduced->node)) {
            return constant->name;
        }
        return "<unknown>";
    }

    // Walk `signature`'s Pi chain; check that the first N domains have
    // the head-name listed in `argumentTypeNames`. Requires the chain
    // to have AT LEAST N Pis — partial application of an overloaded
    // name is not allowed (we want exact-arity calls).
    bool signatureAcceptsArgumentTypes(
        ExpressionPointer signature,
        const std::vector<std::string>& argumentTypeNames) {
        ExpressionPointer cursor = signature;
        for (const auto& expectedName : argumentTypeNames) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) return false;
            std::string actualName = headConstantName(pi->domain);
            if (actualName != expectedName) return false;
            cursor = pi->codomain;
        }
        return true;
    }

    // Helper: decompose `expectedType` (or any type expression) as
    // `Quotient(T, R)` and return T, R, and the universe level u such
    // that T : Type(u). Returns nullopt if the expression isn't a
    // Quotient application.
    struct QuotientDecomposition {
        ExpressionPointer carrierType;
        ExpressionPointer relation;
        LevelPointer universeLevel;
    };
    bool tryDecomposeQuotient(
        ExpressionPointer typeExpression,
        QuotientDecomposition& result) {
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, typeExpression);
        auto* outerApp = std::get_if<Application>(&cursor->node);
        if (!outerApp) return false;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return false;
        auto* quotientConstant =
            std::get_if<Constant>(&innerApp->function->node);
        if (!quotientConstant || quotientConstant->name != "Quotient")
            return false;
        if (quotientConstant->universeArguments.size() != 1)
            return false;
        result.carrierType = innerApp->argument;
        result.relation = outerApp->argument;
        result.universeLevel = quotientConstant->universeArguments[0];
        return true;
    }

    // `Quotient.mk(rep)` — desugars to `Quotient.mk.{u}(T, R, rep)`,
    // recovering `T` from `rep`'s inferred type and `R` (plus
    // confirming `T`) from the expected type when available.
    ExpressionPointer desugarQuotientMk(
        SurfaceExpressionPointer representativeSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.mk(rep) at line " + std::to_string(line));
        ExpressionPointer representativeKernel =
            elaborateExpression(*representativeSurface, localBinders);
        ExpressionPointer representativeTypeOpened =
            inferTypeInLocalContext(localBinders, representativeKernel);
        ExpressionPointer representativeType = closeOverLocalBinders(
            representativeTypeOpened, localBinders, localBinders.size());
        LevelPointer universeLevel =
            typeUniverseOf(localBinders, representativeKernel);

        ExpressionPointer relation;
        if (expectedType) {
            QuotientDecomposition decomp;
            if (tryDecomposeQuotient(expectedType, decomp)) {
                relation = decomp.relation;
            }
        }
        if (!relation) {
            throwElaborate(
                "Quotient.mk(rep): cannot infer the equivalence "
                "relation `R`. The short form needs an expected type "
                "of shape `Quotient(T, R)` from context. Common spots "
                "this fails: operand of unary `-`, immediate body of "
                "`function (rep) =>` inside `Quotient.lift`, or any "
                "position with no propagated expected type. Fall back "
                "to the explicit 3-arg form: `Quotient.mk(T, R, rep)`. "
                "Needed an expected type of the form "
                "`Quotient(T, R)` in context");
        }
        ExpressionPointer call = makeConstant(
            "Quotient.mk", {universeLevel});
        call = makeApplication(std::move(call), representativeType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call),
                                std::move(representativeKernel));
        return call;
    }

    // `Quotient.sound(x, y, proof)` — desugars to
    // `Quotient.sound.{u}(T, R, x, y, proof)`. Recovers `T` from `x`'s
    // type and `R` by walking `proof`'s type as `R(x, y)` to extract
    // the head `R`.
    ExpressionPointer desugarQuotientSound(
        SurfaceExpressionPointer xSurface,
        SurfaceExpressionPointer ySurface,
        SurfaceExpressionPointer proofSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.sound at line " + std::to_string(line));
        // Prefer pulling `T` and `R` from the expected type. Its
        // shape (after WHNF/δ-reduction) is
        // `Equality(Quotient(T, R), mk(T, R, x), mk(T, R, y))`, which
        // pins down `R` as the user wrote it — important when `R`
        // δ-reduces (`IntegerEquivalent → λ rep1 rep2. (...)`) and we'd
        // otherwise infer the reduced form from the proof's type.
        ExpressionPointer carrierType;
        ExpressionPointer relation;
        LevelPointer universeLevel;
        if (expectedType) {
            ExpressionPointer expectedOpened = weakHeadNormalForm(
                environment_, expectedType);
            // Expect Equality(Q, ..., ...) → extract Q.
            if (auto* eqOuter =
                    std::get_if<Application>(&expectedOpened->node)) {
                if (auto* eqMid =
                        std::get_if<Application>(
                            &eqOuter->function->node)) {
                    if (auto* eqInner =
                            std::get_if<Application>(
                                &eqMid->function->node)) {
                        QuotientDecomposition decomp;
                        if (tryDecomposeQuotient(eqInner->argument, decomp)) {
                            carrierType = closeOverLocalBinders(
                                decomp.carrierType, localBinders,
                                localBinders.size());
                            relation = closeOverLocalBinders(
                                decomp.relation, localBinders,
                                localBinders.size());
                            universeLevel = decomp.universeLevel;
                        }
                    }
                }
            }
        }

        ExpressionPointer xKernel = elaborateExpression(
            *xSurface, localBinders);
        ExpressionPointer yKernel = elaborateExpression(
            *ySurface, localBinders);
        ExpressionPointer proofKernel = elaborateExpression(
            *proofSurface, localBinders);

        if (!carrierType) {
            ExpressionPointer xTypeOpened =
                inferTypeInLocalContext(localBinders, xKernel);
            carrierType = closeOverLocalBinders(
                xTypeOpened, localBinders, localBinders.size());
            universeLevel = typeUniverseOf(localBinders, xKernel);
        }
        if (!relation) {
            // Fallback: pull `R` from proof's type as `R(x, y)`.
            ExpressionPointer proofTypeOpened = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, proofKernel));
            if (auto* outer = std::get_if<Application>(
                    &proofTypeOpened->node)) {
                if (auto* inner = std::get_if<Application>(
                        &outer->function->node)) {
                    relation = closeOverLocalBinders(
                        inner->function, localBinders,
                        localBinders.size());
                }
            }
        }
        if (!relation) {
            throwElaborate(
                "Quotient.sound(x, y, proof): cannot infer the "
                "equivalence relation `R` — provide an expected type "
                "of the form `Equality(Quotient(T, R), …, …)` or use "
                "the explicit `Quotient.sound(T, R, x, y, proof)` form");
        }
        ExpressionPointer call = makeConstant(
            "Quotient.sound", {universeLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call), std::move(xKernel));
        call = makeApplication(std::move(call), std::move(yKernel));
        call = makeApplication(std::move(call), std::move(proofKernel));
        return call;
    }

    // `And.eliminate(handler, conjunction)` — short form. Desugars to
    // the verbose `And.eliminate(A, B, Goal, handler, conjunction)`.
    ExpressionPointer desugarAndEliminate(
        SurfaceExpressionPointer handlerSurface,
        SurfaceExpressionPointer conjSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "And.eliminate at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "And.eliminate(handler, conjunction): short form needs "
                "an expected goal type from context; use the 5-arg "
                "verbose form when no expected type is available");
        }
        ExpressionPointer conjKernel = elaborateExpression(
            *conjSurface, localBinders);
        ExpressionPointer conjType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, conjKernel));
        auto* outerApp = std::get_if<Application>(&conjType->node);
        auto* innerApp = outerApp
            ? std::get_if<Application>(&outerApp->function->node)
            : nullptr;
        auto* head = innerApp
            ? std::get_if<Constant>(&innerApp->function->node)
            : nullptr;
        if (!head || head->name != "And") {
            throwElaborate(
                "And.eliminate(handler, conjunction): second argument's "
                "type must be `And(A, B)`, got `"
                + prettyPrintInLocalScope(conjType, localBinders) + "`");
        }
        ExpressionPointer aProp = innerApp->argument;
        ExpressionPointer bProp = outerApp->argument;
        // Handler's expected type: A → B → Goal. The Pi binders are
        // independent of the codomain, so expectedType (already
        // closed at the call's depth) needs no lifting in the
        // current Pi-codomain position when the surface elaborator
        // matches a Lambda against it.
        ExpressionPointer handlerExpected = makePi("leftProof", aProp,
            makePi("rightProof", bProp, expectedType));
        ExpressionPointer handlerKernel = elaborateExpression(
            *handlerSurface, localBinders, handlerExpected);
        ExpressionPointer aClosed = closeOverLocalBinders(
            aProp, localBinders, localBinders.size());
        ExpressionPointer bClosed = closeOverLocalBinders(
            bProp, localBinders, localBinders.size());
        ExpressionPointer call = makeConstant("And.eliminate", {});
        call = makeApplication(std::move(call), std::move(aClosed));
        call = makeApplication(std::move(call), std::move(bClosed));
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(handlerKernel));
        call = makeApplication(std::move(call), std::move(conjKernel));
        return call;
    }

    // `Or.eliminate(handleLeft, handleRight, disjunction)` — short
    // form. Desugars to `Or.eliminate(A, B, Goal, handleLeft,
    // handleRight, disjunction)`.
    ExpressionPointer desugarOrEliminate(
        SurfaceExpressionPointer handleLeftSurface,
        SurfaceExpressionPointer handleRightSurface,
        SurfaceExpressionPointer disjSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Or.eliminate at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "Or.eliminate(hL, hR, disj): short form needs an "
                "expected goal type from context; use the 6-arg "
                "verbose form when no expected type is available");
        }
        ExpressionPointer disjKernel = elaborateExpression(
            *disjSurface, localBinders);
        ExpressionPointer disjType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, disjKernel));
        auto* outerApp = std::get_if<Application>(&disjType->node);
        auto* innerApp = outerApp
            ? std::get_if<Application>(&outerApp->function->node)
            : nullptr;
        auto* head = innerApp
            ? std::get_if<Constant>(&innerApp->function->node)
            : nullptr;
        if (!head || head->name != "Or") {
            throwElaborate(
                "Or.eliminate(hL, hR, disj): third argument's type "
                "must be `Or(A, B)`, got `"
                + prettyPrintInLocalScope(disjType, localBinders) + "`");
        }
        ExpressionPointer aProp = innerApp->argument;
        ExpressionPointer bProp = outerApp->argument;
        // Each handler has type A → Goal / B → Goal.
        ExpressionPointer handleLeftExpected = makePi("leftProof",
            aProp, expectedType);
        ExpressionPointer handleRightExpected = makePi("rightProof",
            bProp, expectedType);
        ExpressionPointer handleLeftKernel = elaborateExpression(
            *handleLeftSurface, localBinders, handleLeftExpected);
        ExpressionPointer handleRightKernel = elaborateExpression(
            *handleRightSurface, localBinders, handleRightExpected);
        ExpressionPointer aClosed = closeOverLocalBinders(
            aProp, localBinders, localBinders.size());
        ExpressionPointer bClosed = closeOverLocalBinders(
            bProp, localBinders, localBinders.size());
        ExpressionPointer call = makeConstant("Or.eliminate", {});
        call = makeApplication(std::move(call), std::move(aClosed));
        call = makeApplication(std::move(call), std::move(bClosed));
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(handleLeftKernel));
        call = makeApplication(std::move(call), std::move(handleRightKernel));
        call = makeApplication(std::move(call), std::move(disjKernel));
        return call;
    }

    // `Exists.eliminate(handler, witness)` — short form. Desugars to
    // the verbose `Exists.eliminate(A, P, Goal, handler, witness)` by
    // recovering A and P from `witness`'s type (`Exists(A, P)`) and
    // Goal from the call-site expectedType.
    //
    // The handler must have type `(w : A) → P(w) → Goal`. We build
    // that Pi-chain as the expected type for the handler so the
    // user-side lambda can be type-driven (no need to annotate the
    // binders).
    //
    // Subtle: the contract of `expectedType` here is *closed* form
    // — BoundVariable indices already account for the call-site's
    // enclosing Pi/Lambda binders. `aType` / `predicate` extracted
    // from the witness's *inferred* type are in *opened* form
    // (Internal FreeVariables, since `inferTypeInLocalContext`
    // opens). Mixing the two without conversion produces dangling
    // BoundVariables or unbound FreeVariables in the assembled
    // call. See the close/no-close discipline at the end.
    ExpressionPointer desugarExistsEliminate(
        SurfaceExpressionPointer handlerSurface,
        SurfaceExpressionPointer witnessSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Exists.eliminate at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "Exists.eliminate(handler, witness): short form needs "
                "an expected goal type from context (e.g. inside a "
                "theorem body); use the 5-arg verbose form "
                "Exists.eliminate(A, P, Goal, handler, witness) "
                "when no expected type is available");
        }
        ExpressionPointer witnessKernel = elaborateExpression(
            *witnessSurface, localBinders);
        ExpressionPointer witnessType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, witnessKernel));
        // witnessType should be `App(App(Const("Exists"), A), P)`.
        auto* outerApp = std::get_if<Application>(&witnessType->node);
        auto* innerApp = outerApp
            ? std::get_if<Application>(&outerApp->function->node)
            : nullptr;
        auto* head = innerApp
            ? std::get_if<Constant>(&innerApp->function->node)
            : nullptr;
        if (!head || head->name != "Exists") {
            throwElaborate(
                "Exists.eliminate(handler, witness): second argument's "
                "type must be `Exists(A, P)`, got `"
                + prettyPrintInLocalScope(witnessType, localBinders)
                + "`");
        }
        ExpressionPointer aType = innerApp->argument;
        ExpressionPointer predicate = outerApp->argument;
        // Build handler's expected type:
        //   Pi w : A. Pi _ : (predicate w). expectedType
        // aType, predicate, expectedType are all in OPENED form
        // (FreeVariable for outer local binders). Inside the outer
        // Pi the codomain references the binder via BV(0); to
        // construct `predicate w` we apply the (BV-free) predicate
        // to BV(0). expectedType doesn't mention the new binders.
        ExpressionPointer predicateAppliedToW = makeApplication(
            predicate, makeBoundVariable(0));
        ExpressionPointer innerPi = makePi("_",
            std::move(predicateAppliedToW), expectedType);
        ExpressionPointer handlerExpected = makePi("w",
            aType, std::move(innerPi));
        ExpressionPointer handlerKernel = elaborateExpression(
            *handlerSurface, localBinders, handlerExpected);
        // Universe argument: Exists's first universe is the carrier's
        // level. Compute it from A's type.
        LevelPointer carrierLevel;
        try {
            ExpressionPointer aTypeOfType = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, aType));
            auto* aTypeSort = std::get_if<Sort>(&aTypeOfType->node);
            if (!aTypeSort) {
                throwElaborate(
                    "Exists.eliminate: cannot determine the carrier "
                    "type's universe");
            }
            carrierLevel = predecessorOfSortLevel(aTypeSort->level);
        } catch (const TypeError&) {
            throwElaborate(
                "Exists.eliminate: cannot infer the carrier universe");
        }
        // Asymmetric form discipline:
        //   * `expectedType` is in CLOSED form — the caller computed
        //     it at the call site's scope and its BoundVariables
        //     already index the surrounding theorem binders. Use it
        //     directly. Closing it again would bump every BV by
        //     `localBinders.size()`, producing dangling indices.
        //   * `aType` / `predicate` came out of
        //     `inferTypeInLocalContext` and so are in OPENED form
        //     (Internal FreeVariables for the same binders). Close
        //     them to match.
        //   * `handlerKernel` / `witnessKernel` came back from
        //     `elaborateExpression`, which produces CLOSED form, so
        //     they need no transformation.
        ExpressionPointer aClosed = closeOverLocalBinders(
            aType, localBinders, localBinders.size());
        ExpressionPointer pClosed = closeOverLocalBinders(
            predicate, localBinders, localBinders.size());
        ExpressionPointer call = makeConstant(
            "Exists.eliminate", {carrierLevel});
        call = makeApplication(std::move(call), std::move(aClosed));
        call = makeApplication(std::move(call), std::move(pClosed));
        call = makeApplication(std::move(call), expectedType);
        call = makeApplication(std::move(call), std::move(handlerKernel));
        call = makeApplication(std::move(call), std::move(witnessKernel));
        return call;
    }

    // `Quotient.lift(f, h, q)` — desugars to
    // `Quotient.lift.{u, v}(T, R, U, f, h, q)`. Recovers everything
    // from the argument types: `T → U` is `f`'s Pi signature; `R`
    // appears in `q`'s type as `Quotient(T, R)`.
    ExpressionPointer desugarQuotientLift(
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer hSurface,
        SurfaceExpressionPointer qSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.lift at line " + std::to_string(line));
        // Elaborate `q` first to get T from its `Quotient(T, R)` type;
        // then we can build `T → U` as the expected type for `f`, which
        // lets the lambda body's `Quotient.mk` etc. back-infer when
        // they appear in a position whose carrier matches U.
        ExpressionPointer qKernel = elaborateExpression(
            *qSurface, localBinders);
        ExpressionPointer qTypeForT = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, qKernel));
        QuotientDecomposition decompForT;
        if (!tryDecomposeQuotient(qTypeForT, decompForT)) {
            throwElaborate(
                "Quotient.lift(f, h, q): third argument's type must "
                "be `Quotient(T, R)`");
        }
        ExpressionPointer fExpected = nullptr;
        if (expectedType) {
            // Build `T → U` (with U = expectedType) as f's expected
            // type — provided expectedType is a closed expression.
            fExpected = makePi("_", decompForT.carrierType, expectedType);
        }
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders, fExpected);
        ExpressionPointer fTypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, fKernel));
        auto* fPi = std::get_if<Pi>(&fTypeOpened->node);
        if (!fPi) {
            throwElaborate(
                "Quotient.lift(f, h, q): first argument must be a "
                "function `T → U`");
        }
        ExpressionPointer carrierType = closeOverLocalBinders(
            fPi->domain, localBinders, localBinders.size());
        ExpressionPointer targetType = closeOverLocalBinders(
            fPi->codomain, localBinders, localBinders.size());
        // Compute the carrier and target universe levels.
        LevelPointer uLevel;
        LevelPointer vLevel;
        {
            ExpressionPointer carrierTypeOfType = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, carrierType));
            auto* sortNode =
                std::get_if<Sort>(&carrierTypeOfType->node);
            if (!sortNode) {
                throwElaborate(
                    "Quotient.lift: cannot determine carrier universe");
            }
            uLevel = predecessorOfSortLevel(sortNode->level);
            ExpressionPointer targetTypeOfType = weakHeadNormalForm(
                environment_,
                inferTypeInLocalContext(localBinders, targetType));
            auto* targetSortNode =
                std::get_if<Sort>(&targetTypeOfType->node);
            if (!targetSortNode) {
                throwElaborate(
                    "Quotient.lift: cannot determine target universe");
            }
            vLevel = predecessorOfSortLevel(targetSortNode->level);
        }
        // R from `q`'s type (already decomposed above).
        ExpressionPointer relation = closeOverLocalBinders(
            decompForT.relation, localBinders, localBinders.size());
        // Elaborate `h` after we know all the pieces.
        ExpressionPointer hKernel = elaborateExpression(
            *hSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.lift", {uLevel, vLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call), targetType);
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(hKernel));
        call = makeApplication(std::move(call), std::move(qKernel));
        return call;
    }

    // `Quotient.induct(motive, f, q)` — desugars to
    // `Quotient.induct.{u}(T, R, motive, f, q)`. Recovers T, R from
    // `motive`'s domain `Quotient(T, R)`.
    ExpressionPointer desugarQuotientInduct(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer qSurface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer /*expectedType*/,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.induct at line " + std::to_string(line));
        ExpressionPointer motiveKernel = elaborateExpression(
            *motiveSurface, localBinders);
        ExpressionPointer motiveTypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, motiveKernel));
        auto* motivePi = std::get_if<Pi>(&motiveTypeOpened->node);
        if (!motivePi) {
            throwElaborate(
                "Quotient.induct(motive, f, q): motive must be a "
                "function `Quotient(T, R) → Proposition`");
        }
        QuotientDecomposition decomp;
        if (!tryDecomposeQuotient(motivePi->domain, decomp)) {
            throwElaborate(
                "Quotient.induct(motive, f, q): motive's domain must "
                "be a `Quotient(T, R)` type");
        }
        ExpressionPointer carrierType = closeOverLocalBinders(
            decomp.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation = closeOverLocalBinders(
            decomp.relation, localBinders, localBinders.size());
        LevelPointer uLevel = decomp.universeLevel;
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders);
        ExpressionPointer qKernel = elaborateExpression(
            *qSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.induct", {uLevel});
        call = makeApplication(std::move(call), carrierType);
        call = makeApplication(std::move(call), relation);
        call = makeApplication(std::move(call), std::move(motiveKernel));
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(qKernel));
        return call;
    }

    // `Quotient.induct_two(motive, f, q1, q2)` — recovers T1, R1, T2,
    // R2 from `q1` and `q2`'s types (each of the form `Quotient(Ti, Ri)`)
    // and emits `Quotient.induct_two.{u, v}(T1, R1, T2, R2, motive, f,
    // q1, q2)`.
    ExpressionPointer desugarQuotientInductTwo(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer q1Surface,
        SurfaceExpressionPointer q2Surface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer /*expectedType*/,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.induct_two at line " + std::to_string(line));
        ExpressionPointer q1Kernel = elaborateExpression(
            *q1Surface, localBinders);
        ExpressionPointer q2Kernel = elaborateExpression(
            *q2Surface, localBinders);
        ExpressionPointer q1TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q1Kernel));
        ExpressionPointer q2TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q2Kernel));
        QuotientDecomposition d1, d2;
        if (!tryDecomposeQuotient(q1TypeOpened, d1)) {
            throwElaborate(
                "Quotient.induct_two: q1's type must be `Quotient(T, R)`");
        }
        if (!tryDecomposeQuotient(q2TypeOpened, d2)) {
            throwElaborate(
                "Quotient.induct_two: q2's type must be `Quotient(T, R)`");
        }
        ExpressionPointer carrierType1 = closeOverLocalBinders(
            d1.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation1 = closeOverLocalBinders(
            d1.relation, localBinders, localBinders.size());
        ExpressionPointer carrierType2 = closeOverLocalBinders(
            d2.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation2 = closeOverLocalBinders(
            d2.relation, localBinders, localBinders.size());
        ExpressionPointer motiveKernel = elaborateExpression(
            *motiveSurface, localBinders);
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.induct_two", {d1.universeLevel, d2.universeLevel});
        call = makeApplication(std::move(call), carrierType1);
        call = makeApplication(std::move(call), relation1);
        call = makeApplication(std::move(call), carrierType2);
        call = makeApplication(std::move(call), relation2);
        call = makeApplication(std::move(call), std::move(motiveKernel));
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(q1Kernel));
        call = makeApplication(std::move(call), std::move(q2Kernel));
        return call;
    }

    // `Quotient.induct_three(motive, f, q1, q2, q3)` — recovers T1, R1,
    // T2, R2, T3, R3 from `q1`, `q2`, `q3`'s types and emits
    // `Quotient.induct_three.{u, v, w}(T1, R1, T2, R2, T3, R3, motive,
    //                                    f, q1, q2, q3)`.
    ExpressionPointer desugarQuotientInductThree(
        SurfaceExpressionPointer motiveSurface,
        SurfaceExpressionPointer fSurface,
        SurfaceExpressionPointer q1Surface,
        SurfaceExpressionPointer q2Surface,
        SurfaceExpressionPointer q3Surface,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer /*expectedType*/,
        int line, int /*column*/) {
        Frame frame(*this,
            "Quotient.induct_three at line " + std::to_string(line));
        ExpressionPointer q1Kernel = elaborateExpression(
            *q1Surface, localBinders);
        ExpressionPointer q2Kernel = elaborateExpression(
            *q2Surface, localBinders);
        ExpressionPointer q3Kernel = elaborateExpression(
            *q3Surface, localBinders);
        ExpressionPointer q1TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q1Kernel));
        ExpressionPointer q2TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q2Kernel));
        ExpressionPointer q3TypeOpened = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, q3Kernel));
        QuotientDecomposition d1, d2, d3;
        if (!tryDecomposeQuotient(q1TypeOpened, d1)) {
            throwElaborate(
                "Quotient.induct_three: q1's type must be `Quotient(T, R)`");
        }
        if (!tryDecomposeQuotient(q2TypeOpened, d2)) {
            throwElaborate(
                "Quotient.induct_three: q2's type must be `Quotient(T, R)`");
        }
        if (!tryDecomposeQuotient(q3TypeOpened, d3)) {
            throwElaborate(
                "Quotient.induct_three: q3's type must be `Quotient(T, R)`");
        }
        ExpressionPointer carrierType1 = closeOverLocalBinders(
            d1.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation1 = closeOverLocalBinders(
            d1.relation, localBinders, localBinders.size());
        ExpressionPointer carrierType2 = closeOverLocalBinders(
            d2.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation2 = closeOverLocalBinders(
            d2.relation, localBinders, localBinders.size());
        ExpressionPointer carrierType3 = closeOverLocalBinders(
            d3.carrierType, localBinders, localBinders.size());
        ExpressionPointer relation3 = closeOverLocalBinders(
            d3.relation, localBinders, localBinders.size());
        ExpressionPointer motiveKernel = elaborateExpression(
            *motiveSurface, localBinders);
        ExpressionPointer fKernel = elaborateExpression(
            *fSurface, localBinders);
        ExpressionPointer call = makeConstant(
            "Quotient.induct_three",
            {d1.universeLevel, d2.universeLevel, d3.universeLevel});
        call = makeApplication(std::move(call), carrierType1);
        call = makeApplication(std::move(call), relation1);
        call = makeApplication(std::move(call), carrierType2);
        call = makeApplication(std::move(call), relation2);
        call = makeApplication(std::move(call), carrierType3);
        call = makeApplication(std::move(call), relation3);
        call = makeApplication(std::move(call), std::move(motiveKernel));
        call = makeApplication(std::move(call), std::move(fKernel));
        call = makeApplication(std::move(call), std::move(q1Kernel));
        call = makeApplication(std::move(call), std::move(q2Kernel));
        call = makeApplication(std::move(call), std::move(q3Kernel));
        return call;
    }

    // Given a `Sort u`-shape level, return the predecessor `u-1`. Used
    // by the quotient desugars to back out the universe parameter from
    // a type's type.
    LevelPointer predecessorOfSortLevel(LevelPointer sortLevel) {
        if (auto* successor =
                std::get_if<LevelSuccessor>(&sortLevel->node)) {
            return successor->base;
        }
        if (auto* constant =
                std::get_if<LevelConst>(&sortLevel->node)) {
            if (constant->value >= 1) {
                return makeLevelConst(constant->value - 1);
            }
        }
        throwElaborate(
            "internal: cannot derive universe predecessor from sort level");
        return nullptr;  // unreachable
    }

    ExpressionPointer desugarCongruenceOf(
        SurfaceExpressionPointer functionSurface,
        SurfaceExpressionPointer equalityProofSurface,
        const std::vector<LocalBinder>& localBinders,
        int line, int column) {

        // Elaborate the equality proof first so we know the domain
        // type (from its Equality structure); that lets us accept an
        // untyped lambda for the function argument (bidirectional
        // elaboration of `fun x => body`).
        ExpressionPointer equalityProofKernel =
            elaborateExpression(*equalityProofSurface, localBinders);
        ExpressionPointer equalityProofType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          equalityProofKernel));

        // Pre-extract the domain type from the proof's Equality type
        // so we can hand it to an untyped lambda's elaboration. We use
        // the closed form (BoundVariables for our local binders) so
        // the lambda we construct slots into the surrounding context
        // correctly.
        EqualityComponents proofComponents = extractEqualityComponents(
            equalityProofType, "congruenceOf", line);
        ExpressionPointer domainTypeForLambda = closeOverLocalBinders(
            proofComponents.carrierType,
            localBinders, localBinders.size());

        // Elaborate the function. If it's an untyped single-binder
        // lambda, fill the domain from domainTypeForLambda; otherwise
        // elaborate normally.
        ExpressionPointer functionKernel;
        auto* functionSurfaceLambda =
            std::get_if<SurfaceLambda>(&functionSurface->node);
        if (functionSurfaceLambda
            && !functionSurfaceLambda->binder.type
            && functionSurfaceLambda->binder.names.size() == 1) {
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back(
                {functionSurfaceLambda->binder.names[0],
                 domainTypeForLambda});
            ExpressionPointer lambdaBody = elaborateExpression(
                *functionSurfaceLambda->body, extended);
            functionKernel =
                makeLambda(functionSurfaceLambda->binder.names[0],
                            domainTypeForLambda,
                            std::move(lambdaBody));
        } else {
            functionKernel =
                elaborateExpression(*functionSurface, localBinders);
        }

        // The function's type should be a Pi (A → B). Extract A (the
        // domain) and B (the codomain).
        ExpressionPointer functionType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders, functionKernel));
        auto* functionPi = std::get_if<Pi>(&functionType->node);
        if (!functionPi) {
            throw ElaborateError(
                "congruenceOf: first argument must be a function "
                "(line " + std::to_string(line) + ")");
        }
        ExpressionPointer domainType = functionPi->domain;
        ExpressionPointer codomainType = functionPi->codomain;
        ExpressionPointer leftEndpoint = proofComponents.leftEndpoint;
        ExpressionPointer rightEndpoint = proofComponents.rightEndpoint;

        // Compute universe levels for the domain and codomain types.
        LevelPointer domainUniverseLevel =
            typeUniverseOf(localBinders, leftEndpoint);
        // For the codomain universe level, we need the universe of
        // codomainType. But codomainType lives in a context with one
        // extra binder (the Pi's binder). We re-infer by elaborating
        // in extended context. For non-dependent codomains, the level
        // result has no BoundVariables so it's safe to return as-is.
        std::vector<LocalBinder> piExtended = localBinders;
        piExtended.push_back({functionPi->displayHint, functionPi->domain});
        LevelPointer codomainUniverseLevel;
        {
            ExpressionPointer typeOfCodomain =
                inferTypeInLocalContext(piExtended, codomainType);
            auto* sortNode = std::get_if<Sort>(&typeOfCodomain->node);
            if (!sortNode) {
                throw ElaborateError(
                    "congruenceOf: cannot determine codomain universe");
            }
            LevelPointer sortLevel = sortNode->level;
            if (auto* successorLevel =
                    std::get_if<LevelSuccessor>(&sortLevel->node)) {
                codomainUniverseLevel = successorLevel->base;
            } else if (auto* constant =
                            std::get_if<LevelConst>(&sortLevel->node)) {
                if (constant->value >= 1) {
                    codomainUniverseLevel =
                        makeLevelConst(constant->value - 1);
                } else {
                    throw ElaborateError(
                        "congruenceOf: cannot derive universe predecessor");
                }
            } else {
                throw ElaborateError(
                    "congruenceOf: cannot derive universe predecessor");
            }
        }

        // The endpoints and the domain/codomain came out of the
        // inferred type, which lives in the opened form with
        // FreeVariables for our local binders. Close them back to
        // BoundVariables so they make sense in the calling context —
        // otherwise a stray FreeVariable referring to e.g. a
        // theorem-level binder leaks into the result term and the
        // kernel rejects it as an unbound internal variable.
        ExpressionPointer closedDomainType = closeOverLocalBinders(
            domainType, localBinders, localBinders.size());
        ExpressionPointer closedCodomainType = closeOverLocalBinders(
            codomainType, localBinders, localBinders.size());
        ExpressionPointer closedLeftEndpoint = closeOverLocalBinders(
            leftEndpoint, localBinders, localBinders.size());
        ExpressionPointer closedRightEndpoint = closeOverLocalBinders(
            rightEndpoint, localBinders, localBinders.size());

        // Build Equality.congruence.{u, v}(A, B, f, x, y, proof).
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {domainUniverseLevel, codomainUniverseLevel});
        call = makeApplication(std::move(call),
                                std::move(closedDomainType));
        call = makeApplication(std::move(call),
                                std::move(closedCodomainType));
        call = makeApplication(std::move(call), std::move(functionKernel));
        call = makeApplication(std::move(call),
                                std::move(closedLeftEndpoint));
        call = makeApplication(std::move(call),
                                std::move(closedRightEndpoint));
        call = makeApplication(std::move(call),
                                std::move(equalityProofKernel));
        (void)column;
        return call;
    }

    // Open the innermost `count` local binders of `term` into FreeVariables
    // (one per binder, by name, with Internal origin so they don't collide
    // with user names). Returns the opened term suitable for inferType when
    // paired with a matching Context built from the same binders.
    ExpressionPointer openOverLocalBinders(
        ExpressionPointer term,
        const std::vector<LocalBinder>& localBinders,
        size_t count) {
        for (size_t i = count; i > 0; --i) {
            term = openBinder(term,
                              openingNameFor(localBinders, i - 1),
                              FreeVariableOrigin::Internal);
        }
        return term;
    }

    // Inverse of openOverLocalBinders: converts the Internal-origin
    // FreeVariables introduced by opening back into BoundVariables so the
    // term can be embedded in a context with the same binders. Closes
    // outermost-first (the reverse order of opening), so the resulting
    // BoundVariable indices line up.
    ExpressionPointer closeOverLocalBinders(
        ExpressionPointer term,
        const std::vector<LocalBinder>& localBinders,
        size_t count) {
        for (size_t i = 0; i < count; ++i) {
            term = closeBinder(term,
                                openingNameFor(localBinders, i),
                                FreeVariableOrigin::Internal);
        }
        return term;
    }

    // Build the kernel Context corresponding to `localBinders`: for each
    // binder, open its type over earlier binders and (when the binder is
    // a let-binding with a value) its value too. Centralizes the
    // ~13 ad-hoc loops that previously built this by hand; their value
    // propagation is what enables isDefinitionallyEqual to ζ-reduce
    // FreeVariables back to let-bound values.
    Context buildContextFromLocalBinders(
        const std::vector<LocalBinder>& localBinders) {
        Context result;
        result.reserve(localBinders.size());
        for (size_t i = 0; i < localBinders.size(); ++i) {
            ExpressionPointer openedType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            ExpressionPointer openedValue = nullptr;
            if (localBinders[i].value) {
                openedValue = openOverLocalBinders(
                    localBinders[i].value, localBinders, i);
            }
            result.push_back({openingNameFor(localBinders, i), openedType,
                              FreeVariableOrigin::Internal, openedValue});
        }
        return result;
    }

    // ζ-unfold every reference to a let-bound binder in `term` (a term
    // in closed-over-localBinders form), replacing it with the let's
    // value. Returns `term` unchanged when no let-binders are in scope.
    //
    // The auto-prover's structural matchers (tryLemmaIndexLookup,
    // tryClassifyDiff) walk terms by syntactic shape rather than
    // calling isDefinitionallyEqual on sub-positions, so they don't
    // benefit from the kernel-level δ-reduction on let-bound
    // FreeVariables. Calling this helper on cursors before matching
    // exposes the underlying expressions so library lemmas about V
    // match goals stated in terms of X (the let-name).
    ExpressionPointer zetaUnfoldLetBinders(
        ExpressionPointer term,
        const std::vector<LocalBinder>& localBinders) {
        std::map<std::string, ExpressionPointer> assignment;
        for (size_t i = 0; i < localBinders.size(); ++i) {
            if (localBinders[i].value) {
                assignment[openingNameFor(localBinders, i)] =
                    openOverLocalBinders(
                        localBinders[i].value, localBinders, i);
            }
        }
        if (assignment.empty()) return term;
        ExpressionPointer opened = openOverLocalBinders(
            term, localBinders, localBinders.size());
        ExpressionPointer substituted =
            substituteFreeVariables(opened, assignment);
        return closeOverLocalBinders(
            substituted, localBinders, localBinders.size());
    }

    // Walks `expression` and replaces every FreeVariable whose name is a
    // key in `assignment` with the corresponding replacement, lifting the
    // replacement by the number of binders we've descended into. Used to
    // substitute inferred constructor-parameter values back into Pi
    // domains and result types during parameter inference.
    ExpressionPointer substituteFreeVariables(
        ExpressionPointer expression,
        const std::map<std::string, ExpressionPointer>& assignment,
        int binderDepth = 0) {
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&expression->node)) {
            auto iterator = assignment.find(freeVariable->name);
            if (iterator != assignment.end()) {
                return shift(iterator->second, binderDepth);
            }
            return expression;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                substituteFreeVariables(pi->domain, assignment,
                                          binderDepth),
                substituteFreeVariables(pi->codomain, assignment,
                                          binderDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                substituteFreeVariables(lambda->domain, assignment,
                                          binderDepth),
                substituteFreeVariables(lambda->body, assignment,
                                          binderDepth + 1));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                substituteFreeVariables(application->function, assignment,
                                          binderDepth),
                substituteFreeVariables(application->argument, assignment,
                                          binderDepth));
        }
        return expression;
    }

    // Returns true if `expression` contains an Internal-origin
    // FreeVariable whose name starts with `_constructorValueArgument_`
    // or `_callTrailingArgument_` — both are trailing-arg placeholders
    // opened during the backward-inference result-type probe. Targets
    // that mention any such placeholder aren't substituted away later
    // and would leak into the assembled kernel term, so the unifier
    // rejects them.
    bool containsValueArgumentFreeVar(ExpressionPointer expression) {
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&expression->node)) {
            const std::string& name = freeVariable->name;
            if (freeVariable->origin != FreeVariableOrigin::Internal) {
                return false;
            }
            static const char* placeholderPrefixes[] = {
                "_constructorValueArgument_",
                "_callTrailingArgument_",
            };
            for (const char* prefix : placeholderPrefixes) {
                size_t length = std::char_traits<char>::length(prefix);
                if (name.size() >= length
                    && name.compare(0, length, prefix) == 0) {
                    return true;
                }
            }
            return false;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return containsValueArgumentFreeVar(pi->domain)
                || containsValueArgumentFreeVar(pi->codomain);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return containsValueArgumentFreeVar(lambda->domain)
                || containsValueArgumentFreeVar(lambda->body);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return containsValueArgumentFreeVar(application->function)
                || containsValueArgumentFreeVar(application->argument);
        }
        return false;
    }

    // Walks `pattern` and `target` in parallel. Whenever pattern is a
    // FreeVariable whose name is in `metavariableNames` (and isn't yet
    // assigned), records `assignment[name] = target`. For Pi/Lambda/
    // Application, recurses into matching positions. For mismatches
    // (different shapes, different Constants, etc.), simply stops at
    // that subterm — we don't error out, since the caller may still
    // be able to fill the metavariable from other unification sources.
    //
    // Limitation: we only record assignments when binderDepth == 0,
    // because the captured `target` would otherwise live in a binder
    // context that doesn't match where the assignment is later used.
    // For the common cases (parameters appearing at the top level of
    // value-arg domains or as direct args of the result type's
    // applications), this is sufficient.
    // Walks a term and returns true if it references any BoundVariable
    // whose index is < threshold (i.e. it captures a binder we
    // descended into). Used to gate metavariable assignment under
    // binders: we can lift target up to the outer scope only when no
    // such "captured" references are present.
    bool referencesBoundBelowThreshold(ExpressionPointer expression,
                                        int threshold,
                                        int currentDepth = 0) {
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int effectiveIndex =
                boundVariable->deBruijnIndex - currentDepth;
            return effectiveIndex >= 0 && effectiveIndex < threshold;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesBoundBelowThreshold(pi->domain, threshold,
                                                  currentDepth)
                || referencesBoundBelowThreshold(pi->codomain, threshold,
                                                  currentDepth + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return referencesBoundBelowThreshold(lambda->domain, threshold,
                                                  currentDepth)
                || referencesBoundBelowThreshold(lambda->body, threshold,
                                                  currentDepth + 1);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return referencesBoundBelowThreshold(
                       application->function, threshold, currentDepth)
                || referencesBoundBelowThreshold(
                       application->argument, threshold, currentDepth);
        }
        return false;
    }

    void unifyConstructorParameters(
        ExpressionPointer pattern,
        ExpressionPointer target,
        const std::set<std::string>& metavariableNames,
        std::map<std::string, ExpressionPointer>& assignment,
        int binderDepth = 0,
        std::vector<ExpressionPointer>* binderTypeStack = nullptr) {
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&pattern->node)) {
            if (metavariableNames.count(freeVariable->name)
                && !assignment.count(freeVariable->name)
                && !containsValueArgumentFreeVar(target)
                && !referencesBoundBelowThreshold(target, binderDepth)) {
                // Lift the target up to the outer scope by shifting it
                // down by `binderDepth`. Safe because we just verified
                // the target has no references that would be captured.
                ExpressionPointer lifted = binderDepth == 0
                    ? target
                    : shift(target, -binderDepth);
                assignment[freeVariable->name] = lifted;
            }
            return;
        }
        if (auto* patternPi = std::get_if<Pi>(&pattern->node)) {
            if (auto* targetPi = std::get_if<Pi>(&target->node)) {
                unifyConstructorParameters(
                    patternPi->domain, targetPi->domain,
                    metavariableNames, assignment, binderDepth,
                    binderTypeStack);
                if (binderTypeStack)
                    binderTypeStack->push_back(patternPi->domain);
                unifyConstructorParameters(
                    patternPi->codomain, targetPi->codomain,
                    metavariableNames, assignment, binderDepth + 1,
                    binderTypeStack);
                if (binderTypeStack) binderTypeStack->pop_back();
            }
            return;
        }
        if (auto* patternLambda =
                std::get_if<Lambda>(&pattern->node)) {
            if (auto* targetLambda =
                    std::get_if<Lambda>(&target->node)) {
                unifyConstructorParameters(
                    patternLambda->domain, targetLambda->domain,
                    metavariableNames, assignment, binderDepth,
                    binderTypeStack);
                if (binderTypeStack)
                    binderTypeStack->push_back(patternLambda->domain);
                unifyConstructorParameters(
                    patternLambda->body, targetLambda->body,
                    metavariableNames, assignment, binderDepth + 1,
                    binderTypeStack);
                if (binderTypeStack) binderTypeStack->pop_back();
            }
            return;
        }
        if (auto* patternApplication =
                std::get_if<Application>(&pattern->node)) {
            ExpressionPointer patternHead = patternApplication->function;
            while (auto* nestedApp =
                       std::get_if<Application>(&patternHead->node)) {
                patternHead = nestedApp->function;
            }
            if (auto* headFreeVariable =
                    std::get_if<FreeVariable>(&patternHead->node)) {
                if (metavariableNames.count(headFreeVariable->name)) {
                    // Miller-pattern higher-order unification: if the
                    // pattern is `metavar(Bound(k))` with k < binderDepth
                    // (referring to a binder we descended into), and
                    // the target doesn't reference any DEEPER binders
                    // (those would also be captured), solve the
                    // metavariable by abstracting target over Bound(k).
                    // For now we handle only the unary case — enough for
                    // motive-style implicit predicates like
                    // `{P : T → Prop}` in `strong_induction`.
                    if (binderTypeStack
                        && !assignment.count(
                               headFreeVariable->name)) {
                        auto* singleArgBound =
                            std::get_if<BoundVariable>(
                                &patternApplication->argument->node);
                        if (singleArgBound) {
                            int k = singleArgBound->deBruijnIndex;
                            if (k >= 0 && k < binderDepth) {
                                int captureThreshold = binderDepth;
                                // Bound(k) IS allowed (we abstract it
                                // away); reject only other captures.
                                if (!referencesOtherBoundsBelowThreshold(
                                        target, captureThreshold, k)
                                    && !containsValueArgumentFreeVar(
                                           target)) {
                                    // Build Lambda(_, T_k, body) where
                                    // body abstracts over Bound(k).
                                    // T_k is the binder at depth k
                                    // from the innermost in the stack.
                                    int stackPosition =
                                        static_cast<int>(
                                            binderTypeStack->size())
                                        - 1 - k;
                                    if (stackPosition >= 0
                                        && !referencesBoundBelowThreshold(
                                               (*binderTypeStack)
                                                   [stackPosition],
                                               stackPosition)) {
                                        ExpressionPointer kType =
                                            (*binderTypeStack)
                                                [stackPosition];
                                        // The binder type was captured
                                        // in a scope with `stackPosition`
                                        // earlier descended binders.
                                        // Shift down so it lives in
                                        // the outer scope. The guard
                                        // above rejects types whose
                                        // Bound vars reference those
                                        // earlier descended binders —
                                        // those can't be expressed in
                                        // the outer scope.
                                        ExpressionPointer kTypeOuter =
                                            stackPosition == 0
                                                ? kType
                                                : shift(kType,
                                                         -stackPosition);
                                        ExpressionPointer abstracted =
                                            abstractOverBoundVariable(
                                                target, k);
                                        // `abstracted` is in scope
                                        // {outer + descended binders +
                                        //  Lambda binder}. We need it
                                        // in {outer + Lambda binder},
                                        // which means shifting indices
                                        // that reference the outer
                                        // scope (Bound(>=binderDepth+1)
                                        // after abstraction) down by
                                        // `binderDepth`, while leaving
                                        // Bound(0) (the Lambda binder)
                                        // alone. References to the
                                        // descended binders themselves
                                        // (Bound(1..binderDepth)) have
                                        // been ruled out by the
                                        // `referencesOtherBoundsBelow…`
                                        // check above.
                                        ExpressionPointer body =
                                            shift(abstracted,
                                                  -binderDepth,
                                                  binderDepth + 1);
                                        ExpressionPointer solution =
                                            makeLambda(
                                                "_motiveBinder",
                                                kTypeOuter,
                                                body);
                                        assignment[
                                            headFreeVariable->name] =
                                            solution;
                                    }
                                }
                            }
                        }
                    }
                    return;
                }
            }
            if (auto* targetApplication =
                    std::get_if<Application>(&target->node)) {
                // Require the heads (after walking the function chain)
                // to be structurally equivalent. Without this check,
                // pointwise recursion of two same-arity but
                // semantically-different applications (e.g.
                // `Natural.divides(_, _)` vs `Exists(Natural, _)`)
                // would assign metavariables to wrong-typed targets.
                ExpressionPointer targetHead = targetApplication->function;
                while (auto* nestedApp =
                           std::get_if<Application>(&targetHead->node)) {
                    targetHead = nestedApp->function;
                }
                if (!headsMatch(patternHead, targetHead)) {
                    return;
                }
                unifyConstructorParameters(
                    patternApplication->function,
                    targetApplication->function,
                    metavariableNames, assignment, binderDepth);
                unifyConstructorParameters(
                    patternApplication->argument,
                    targetApplication->argument,
                    metavariableNames, assignment, binderDepth);
            }
            return;
        }
    }

    // Heads match when both are the same Constant (same name + universe
    // arguments), the same BoundVariable index, or the same Sort. A
    // FreeVariable head means a metavariable case — handled separately.
    bool headsMatch(ExpressionPointer left, ExpressionPointer right) {
        if (auto* leftConstant = std::get_if<Constant>(&left->node)) {
            if (auto* rightConstant =
                    std::get_if<Constant>(&right->node)) {
                return leftConstant->name == rightConstant->name;
            }
            return false;
        }
        if (auto* leftBound = std::get_if<BoundVariable>(&left->node)) {
            if (auto* rightBound =
                    std::get_if<BoundVariable>(&right->node)) {
                return leftBound->deBruijnIndex
                    == rightBound->deBruijnIndex;
            }
            return false;
        }
        if (std::get_if<Sort>(&left->node)) {
            return std::get_if<Sort>(&right->node) != nullptr;
        }
        if (auto* leftFree = std::get_if<FreeVariable>(&left->node)) {
            if (auto* rightFree =
                    std::get_if<FreeVariable>(&right->node)) {
                return leftFree->name == rightFree->name
                    && leftFree->origin == rightFree->origin;
            }
            return false;
        }
        return false;
    }

    // Calls the kernel's inferType on `term` interpreted under the given
    // local binder stack. Builds a kernel Context with FreeVariables for
    // each binder and opens the term to refer to them.
    ExpressionPointer inferTypeInLocalContext(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term) {
        ExpressionPointer openedTerm = openOverLocalBinders(
            term, localBinders, localBinders.size());
        Context context = buildContextFromLocalBinders(localBinders);
        return inferType(environment_, context, openedTerm);
    }

    // For a term whose type is in some universe — i.e. the type's type is
    // a Sort N — returns the level u such that the term has type Type(u)
    // (i.e. u = N - 1). Throws if the predecessor cannot be computed
    // syntactically (e.g. a polymorphic Sort whose level is not a
    // LevelSuccessor or a concrete LevelConst).
    LevelPointer typeUniverseOf(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer term) {
        ExpressionPointer typeOfTerm =
            inferTypeInLocalContext(localBinders, term);
        ExpressionPointer typeOfType =
            inferTypeInLocalContext(localBinders, typeOfTerm);
        auto* sortNode = std::get_if<Sort>(&typeOfType->node);
        if (!sortNode) {
            throw ElaborateError(
                "internal: expected a Sort when computing universe level");
        }
        LevelPointer sortLevel = sortNode->level;
        if (auto* successorLevel =
                std::get_if<LevelSuccessor>(&sortLevel->node)) {
            return successorLevel->base;
        }
        if (auto* constant = std::get_if<LevelConst>(&sortLevel->node)) {
            if (constant->value >= 1) {
                return makeLevelConst(constant->value - 1);
            }
        }
        throw ElaborateError(
            "cannot determine universe level for desugaring; the type's "
            "Sort isn't a syntactic successor — use the explicit "
            "Equality.{u}(...) form");
    }

    static const std::vector<std::string>& declarationUniverseParameters(
        const Declaration& declaration) {
        static const std::vector<std::string> empty;
        if (auto* axiom = std::get_if<Axiom>(&declaration))
            return axiom->universeParameters;
        if (auto* definition = std::get_if<Definition>(&declaration))
            return definition->universeParameters;
        if (auto* inductive = std::get_if<Inductive>(&declaration))
            return inductive->universeParameters;
        if (auto* constructor = std::get_if<Constructor>(&declaration))
            return constructor->universeParameters;
        if (auto* recursor = std::get_if<Recursor>(&declaration))
            return recursor->universeParameters;
        return empty;
    }

    static ExpressionPointer declarationType(
        const Declaration& declaration) {
        if (auto* axiom = std::get_if<Axiom>(&declaration))
            return axiom->type;
        if (auto* definition = std::get_if<Definition>(&declaration))
            return definition->type;
        if (auto* inductive = std::get_if<Inductive>(&declaration))
            return inductive->kind;
        if (auto* constructor = std::get_if<Constructor>(&declaration))
            return constructor->type;
        if (auto* recursor = std::get_if<Recursor>(&declaration))
            return recursor->type;
        return nullptr;
    }

    // Unifies a single level expression with a concrete level, collecting
    // assignments for universe-parameter names. The "expected" side comes
    // from the signature being instantiated (may contain LevelParams that
    // are unsolved); the "actual" side is the level inferred from the
    // user's argument. Only handles cases we encounter in practice
    // (LevelParam, LevelSuccessor, LevelConst, LevelMax of constant-or-
    // parameter).
    void unifyLevels(
        LevelPointer expected, LevelPointer actual,
        std::map<std::string, LevelPointer>& assignment) {
        if (auto* parameter = std::get_if<LevelParam>(&expected->node)) {
            auto iterator = assignment.find(parameter->name);
            if (iterator == assignment.end()) {
                assignment[parameter->name] = actual;
            }
            return;
        }
        if (auto* expectedSuccessor =
                std::get_if<LevelSuccessor>(&expected->node)) {
            if (auto* actualSuccessor =
                    std::get_if<LevelSuccessor>(&actual->node)) {
                unifyLevels(expectedSuccessor->base,
                             actualSuccessor->base,
                             assignment);
                return;
            }
            if (auto* actualConstant =
                    std::get_if<LevelConst>(&actual->node)) {
                if (actualConstant->value >= 1) {
                    unifyLevels(expectedSuccessor->base,
                                 makeLevelConst(actualConstant->value - 1),
                                 assignment);
                    return;
                }
            }
        }
        // Other cases (max, imax, mismatched constants): no assignment.
    }

    void unifyTypes(
        ExpressionPointer expected, ExpressionPointer actual,
        std::map<std::string, LevelPointer>& assignment) {
        // Walk Pi chains in parallel. We don't try to match Pi domains
        // (they may contain BoundVariables in the expected side that
        // don't substitute trivially); the codomain typically carries
        // the universe info we care about.
        if (auto* expectedPi = std::get_if<Pi>(&expected->node)) {
            if (auto* actualPi = std::get_if<Pi>(&actual->node)) {
                unifyTypes(expectedPi->codomain, actualPi->codomain,
                            assignment);
                return;
            }
        }
        auto* expectedSort = std::get_if<Sort>(&expected->node);
        auto* actualSort = std::get_if<Sort>(&actual->node);
        if (expectedSort && actualSort) {
            unifyLevels(expectedSort->level, actualSort->level,
                         assignment);
            return;
        }
        // Constant heads with universe-arguments lined up (e.g.,
        // Equality.{u}
        // applied to a value vs Equality.{0} applied to the same).
        if (auto* expectedConstant =
                std::get_if<Constant>(&expected->node)) {
            if (auto* actualConstant =
                    std::get_if<Constant>(&actual->node)) {
                if (expectedConstant->name == actualConstant->name) {
                    size_t commonCount = std::min(
                        expectedConstant->universeArguments.size(),
                        actualConstant->universeArguments.size());
                    for (size_t i = 0; i < commonCount; ++i) {
                        unifyLevels(
                            expectedConstant->universeArguments[i],
                            actualConstant->universeArguments[i],
                            assignment);
                    }
                }
            }
        }
        if (auto* expectedApplication =
                std::get_if<Application>(&expected->node)) {
            if (auto* actualApplication =
                    std::get_if<Application>(&actual->node)) {
                unifyTypes(expectedApplication->function,
                            actualApplication->function, assignment);
            }
        }
    }

    // Stage 2 universe inference: when the user writes `Equality(A, x, y)`
    // without `.{u}`, look at the declaration's universe parameters and
    // value-argument types to derive the universe instantiation. Returns
    // the inferred universe arguments in declaration order. Universe
    // parameters that cannot be derived are defaulted to LevelConst(0).
    //
    // `skipLeadingPis` skips that many Pi binders before aligning the
    // value arguments with the remaining Pis. This lets the same routine
    // serve declarations with an implicit-arg prefix the user did NOT
    // pass — the caller infers those implicits separately.
    std::vector<LevelPointer> inferUniverseArguments(
        const Declaration& declaration,
        const std::vector<ExpressionPointer>& valueArguments,
        const std::vector<LocalBinder>& localBinders,
        int skipLeadingPis = 0) {

        const std::vector<std::string>& universeParameters =
            declarationUniverseParameters(declaration);
        if (universeParameters.empty()) return {};

        std::map<std::string, LevelPointer> assignment;
        ExpressionPointer cursor = declarationType(declaration);
        for (int s = 0; s < skipLeadingPis && cursor != nullptr; ++s) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) { cursor = nullptr; break; }
            // Open the binder with a fresh Internal FreeVariable so the
            // codomain refers to a free name rather than a loose BVar.
            std::string skipName =
                "_inferUniverseSkip_" + std::to_string(s);
            cursor = openBinder(pi->codomain, skipName,
                                  FreeVariableOrigin::Internal);
        }
        for (size_t i = 0;
             i < valueArguments.size() && cursor != nullptr; ++i) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) break;
            if (!valueArguments[i]) {
                cursor = pi->codomain;
                continue;
            }
            ExpressionPointer expectedDomain =
                weakHeadNormalForm(environment_, pi->domain);
            ExpressionPointer actualType;
            try {
                actualType = weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(localBinders,
                                              valueArguments[i]));
            } catch (const TypeError&) {
                cursor = pi->codomain;
                continue;
            } catch (const ElaborateError&) {
                cursor = pi->codomain;
                continue;
            }
            unifyTypes(expectedDomain, actualType, assignment);
            cursor = pi->codomain;
        }

        std::vector<LevelPointer> result;
        for (const auto& name : universeParameters) {
            auto iterator = assignment.find(name);
            if (iterator != assignment.end()) {
                result.push_back(iterator->second);
            } else {
                result.push_back(makeLevelConst(0));
            }
        }
        return result;
    }

    static size_t universeParameterCount(const Declaration& declaration) {
        if (auto* axiom = std::get_if<Axiom>(&declaration))
            return axiom->universeParameters.size();
        if (auto* definition = std::get_if<Definition>(&declaration))
            return definition->universeParameters.size();
        if (auto* inductive = std::get_if<Inductive>(&declaration))
            return inductive->universeParameters.size();
        if (auto* constructor = std::get_if<Constructor>(&declaration))
            return constructor->universeParameters.size();
        if (auto* recursor = std::get_if<Recursor>(&declaration))
            return recursor->universeParameters.size();
        return 0;
    }

    // ---- universe metavariable state ----
    // Each call to a declaration handler resets these. As elaboration
    // proceeds, each bare `Type` in the source generates a fresh
    // universe parameter name; the name is appended both to the
    // ordered/set views of "available universe parameters" (so internal
    // self-references can use it) and to autoBoundUniverseParameters_,
    // which is folded into the kernel declaration's universe parameter
    // list at the end of the handler.
    std::string freshAutoBoundUniverseName() {
        std::string name =
            "_auto_u_" + std::to_string(metavarCounter_++);
        autoBoundUniverseParameters_.push_back(name);
        currentUniverseParametersOrdered_.push_back(name);
        currentUniverseParameters_.insert(name);
        return name;
    }
    void resetAutoBoundState() {
        autoBoundUniverseParameters_.clear();
        metavarCounter_ = 0;
    }
    std::vector<std::string> finalUniverseParameters(
        const std::vector<std::string>& userDeclared) {
        std::vector<std::string> result = userDeclared;
        for (const auto& name : autoBoundUniverseParameters_) {
            result.push_back(name);
        }
        return result;
    }

    Environment& environment_;
    std::vector<std::string>& importedModules_;
    std::string moduleName_;
    bool reportRedundantBy_ = false;
    bool reportRedundantCalcSteps_ = false;
    std::string currentDeclarationName_;
    // Stack of expected types active on the current elaboration call
    // chain. The top of the stack is what the `goal` keyword resolves
    // to. Pushed at the entry to elaborateExpression whenever the
    // call carries a non-null expectedType; popped on return via the
    // GoalScope RAII guard.
    std::vector<ExpressionPointer> goalStack_;
    // `unfold X in <body>` flips X's opacity from Opaque to
    // Transparent and records the original opacity here. The list is
    // drained at the end of each top-level definition / theorem so
    // the kernel's final typecheck (inside addDefinition) also sees
    // the unfolded view. One theorem's `unfold` doesn't leak to the
    // next.
    std::vector<std::pair<std::string, Opacity>>
        pendingOpacityRestores_;
    // Conventions registered via `convention p [q ...] : T [with …];`
    // declarations. Keyed by name. When a subsequent declaration's
    // signature or body mentions a key as a free identifier, the
    // elaborator auto-prepends `{p : T}` and one implicit binder per
    // side-condition. v1: file-local (cleared at module start would be
    // ideal but for now lives for the entire elaborator instance, which
    // matches the per-module verifier invocation).
    struct ConventionEntry {
        SurfaceExpressionPointer type;
        std::vector<SurfaceConventionProposition> propositions;
    };
    std::unordered_map<std::string, ConventionEntry> conventionRegistry_;
    // Memoized result of "does definition X's body transitively
    // reference constant Y as a head?" — used by the `decide`
    // elaborator's WHNF walker to skip Applications whose head
    // can't δ-unfold to expose the target. Keyed by
    // "<X>|<Y>" (a flat string so std::unordered_map works).
    mutable std::unordered_map<std::string, bool>
        unfoldExposesHeadCache_;
    // Phase 3 lemma index. Each registered rewrite lemma — anything of
    // shape `Π x₁ … xₙ. Equality.{u}(carrier, LHS, RHS)` with no
    // universe parameters — is keyed by `spineHash(LHS)` (and again by
    // `spineHash(RHS)` so a reverse-direction lookup works without a
    // separate scan). At calc-step classify time we hash the diff,
    // pull candidates from the bucket, run a small first-order matcher,
    // substitute the matched bindings into the lemma's RHS, and verify
    // structural equality against the other endpoint. This subsumes
    // the bespoke commutativity/associativity/identity classifiers and
    // additionally fires on any user-written rewrite lemma whose LHS
    // matches the diff.
    struct RewriteLemma {
        std::string lemmaName;
        int binderCount = 0;
        // LHS / RHS in closed-over-binders form: BoundVariable(0..n-1)
        // refer to the lemma's binders, BV(0) being the *innermost*.
        ExpressionPointer lhs;
        ExpressionPointer rhs;
        // Each binder's type, lifted into the conclusion's frame so
        // `instantiateLemmaBinders` can substitute the metavariable
        // bindings directly. `binderTypes[i]` is the type of the
        // binder with conclusion-frame de Bruijn index i (0 =
        // innermost, n-1 = outermost). Used to discharge propositional
        // preconditions when pattern matching the LHS/RHS leaves some
        // binders unbound (e.g. `primality` / positivity proofs on
        // `padic_valuation_multiplicative`).
        std::vector<ExpressionPointer> binderTypes;
        // Set when this entry indexes the lemma's RHS (so a hash hit
        // means we matched the wrong side and must emit
        // `Equality.symmetry`).
        bool reverseDirection = false;
    };
    std::unordered_multimap<uint64_t, RewriteLemma> lemmaIndex_;
    // Context frames describing what the elaborator is currently doing.
    // Each frame is a short phrase like "while elaborating cases at
    // line 42". `Frame` is an RAII guard that pushes on construction
    // and pops on destruction; `throwElaborate` (and the kernel-error
    // catch path) prepends the frames to the diagnostic so the user
    // sees a breadcrumb trail from their source line to the failure.
    std::vector<FrameSnapshot> contextFrames_;
    // Ordered list of universe parameters of the current declaration —
    // ordered so we can auto-fill universe arguments at self-reference
    // sites (the user writes `Equality(A, x, x)` inside reflexivity's
    // constructor type; we elaborate it as `Equality.{u}(A, x, x)`).
    // Auto-bound names are appended as bare `Type` is encountered.
    std::vector<std::string> currentUniverseParametersOrdered_;
    std::set<std::string> currentUniverseParameters_;
    std::vector<std::string> autoBoundUniverseParameters_;
    int metavarCounter_ = 0;
};

}  // namespace

ExpressionPointer elaborateExpression(const SurfaceExpression& expression,
                                       const Environment& environment) {
    Environment local = environment;  // can't pass const Environment&
    std::vector<std::string> imports;
    Elaborator elaborator(local, imports);
    return elaborator.runExpression(expression);
}

void elaborateModule(const SurfaceModule& module,
                     Environment& environment,
                     std::vector<std::string>& importedModules,
                     bool reportRedundantBy,
                     bool reportRedundantCalcSteps) {
    Elaborator elaborator(environment, importedModules);
    elaborator.setReportRedundantBy(reportRedundantBy);
    elaborator.setReportRedundantCalcSteps(reportRedundantCalcSteps);
    elaborator.runModule(module);
}
