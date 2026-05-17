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
struct LocalBinder {
    std::string name;
    ExpressionPointer type;
};

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

    struct Frame {
        Elaborator& elaborator;
        Frame(Elaborator& target, std::string description)
            : elaborator(target) {
            elaborator.contextFrames_.push_back(std::move(description));
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
            term = openBinder(term, localBinders[i - 1].name,
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
        // to inner failure.
        for (auto iterator = contextFrames_.rbegin();
             iterator != contextFrames_.rend(); ++iterator) {
            result += *iterator;
            result += "\n  ";
        }
        result += message;
        return result;
    }

    [[noreturn]] void throwElaborate(const std::string& message) const {
        throw ElaborateError(formatErrorWithContext(message));
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
    // definition).
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
        // Pull the function's type and verify it's T1 → T2 → R.
        ExpressionPointer functionType = declarationType(*functionDecl);
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, functionType);
        auto* leftPi = std::get_if<Pi>(&cursor->node);
        if (!leftPi) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + "' must take at least two arguments");
        }
        if (!typeHasHeadName(leftPi->domain, declaration.leftTypeName)) {
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
        if (!typeHasHeadName(rightPi->domain, declaration.rightTypeName)) {
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
        // SurfaceHammer, SurfaceSorry, SurfaceRing, calc, by_induction,
        // and a handful of other leaf/specialised nodes have no
        // children we care about for convention detection. We default
        // to ignoring them — at worst the convention doesn't fire for
        // those forms.
    }

    void elaborateDefinition(const SurfaceDefinitionDeclaration& origDecl) {
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
                          std::move(fullType), std::move(fullBody));
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
                    {outerBinderStack[i].name, openedType,
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
                          std::move(fullType), std::move(fullBody));
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

        // Desugar non-bare patterns in non-scrutinee positions: replace
        // each with a fresh bare name and wrap the body in a `cases
        // freshName { originalPattern => body }`. This lets users write
        // `| Foo.make(a, b), Bar.make(c, d) => …` even though the
        // recursor-style elaboration below only handles a constructor
        // pattern in the first position. The wrapping order is
        // last-to-first so the innermost `cases` is the latest pattern
        // — pattern-bound names in each position remain in scope for
        // the original body.
        SurfacePatternCase desugaredCase = *matchedCase;
        {
            SurfaceExpressionPointer wrappedBody = desugaredCase.body;
            for (size_t reverseIndex =
                     desugaredCase.patterns.size();
                 reverseIndex > 1; --reverseIndex) {
                size_t patternIndex = reverseIndex - 1;
                const SurfacePattern& pattern =
                    *desugaredCase.patterns[patternIndex];
                if (std::get_if<SurfacePatternBareName>(&pattern.node)) {
                    continue;
                }
                std::string freshName =
                    "_patternMatchArg_" + std::to_string(patternIndex);
                int line = pattern.line;
                int column = pattern.column;
                SurfaceCasesClause clause;
                clause.pattern = desugaredCase.patterns[patternIndex];
                clause.body = wrappedBody;
                clause.line = line;
                clause.column = column;
                std::vector<SurfaceCasesClause> clauses;
                clauses.push_back(std::move(clause));
                SurfaceExpressionPointer scrutinee = makeSurfaceIdentifier(
                    freshName, {}, line, column);
                wrappedBody = makeSurfaceCases(
                    std::move(scrutinee),
                    std::move(clauses),
                    line, column);
                desugaredCase.patterns[patternIndex] =
                    makeSurfacePatternBareName(freshName, line, column);
            }
            desugaredCase.body = std::move(wrappedBody);
            matchedCase = &desugaredCase;
        }

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
        struct LambdaBinder {
            std::string name;
            ExpressionPointer type;
        };
        std::vector<LambdaBinder> lambdaBinders;
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
        std::vector<size_t> otherFunctionArgumentPositions;
        for (size_t i = 1; i < matchedCase->patterns.size(); ++i) {
            const SurfacePattern& pattern = *matchedCase->patterns[i];
            auto* bareName = std::get_if<SurfacePatternBareName>(
                &pattern.node);
            if (!bareName) {
                throw ElaborateError(
                    "non-scrutinee pattern positions must be variable "
                    "patterns (e.g. 'm' or '_')");
            }
            auto* pi = std::get_if<Pi>(&motiveAtCase->node);
            if (!pi) {
                throw ElaborateError(
                    "pattern case for '" + constructorName + "' has too "
                    "many positions for the function signature");
            }
            otherFunctionArgumentPositions.push_back(lambdaBinders.size());
            lambdaBinders.push_back({bareName->name, pi->domain});
            motiveAtCase = pi->codomain;
            binderDepth++;
        }

        // Translate the body: rewrite recursive calls. The user types
        // out the outer binders in any recursive call, so we tell the
        // rewriter to skip past them before looking for the scrutinee.
        SurfaceExpressionPointer rewrittenBody = rewriteRecursiveCalls(
            matchedCase->body, declaration.name, recursiveArgToHypothesis,
            static_cast<int>(outerBinderStack.size()));

        // The expected body type is what's left of the motive after
        // all the non-scrutinee Pi peels.
        ExpressionPointer expectedBodyType = motiveAtCase;

        // Elaborate the body with all binders in scope (outer + case).
        std::vector<LocalBinder> bodyStack = outerBinderStack;
        for (const auto& binder : lambdaBinders) {
            bodyStack.push_back({binder.name, binder.type});
        }
        ExpressionPointer bodyKernel =
            elaborateExpression(*rewrittenBody, bodyStack,
                                 expectedBodyType);

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
            Context bodyContext;
            for (size_t i = 0; i < bodyStack.size(); ++i) {
                ExpressionPointer openedType = openOverLocalBinders(
                    bodyStack[i].type, bodyStack, i);
                bodyContext.push_back({bodyStack[i].name, openedType,
                                          FreeVariableOrigin::Internal});
            }
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
            return makeSurfaceCases(std::move(rewrittenScrutinee),
                                     std::move(rewrittenClauses),
                                     node.line, node.column);
        }
        if (auto* calc = std::get_if<SurfaceCalc>(&node.node)) {
            auto rewrittenInitial = rewriteRecursiveCalls(
                calc->initialExpression, thisDeclName,
                recursiveArgToHypothesis, outerBinderCount);
            std::vector<SurfaceCalcStep> rewrittenSteps;
            for (const auto& step : calc->steps) {
                SurfaceCalcStep rewrittenStep;
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

    ExpressionPointer elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType = nullptr) {

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
                        bool universesOk =
                            declarationUniverseParams->empty()
                            || (headIdentifier->universeArgs.size()
                                == declarationUniverseParams->size());
                        if (numLeadingToInfer > 0 && universesOk) {
                            // When the declaration uses explicit
                            // `{x : T}` binders, the user has
                            // committed to inference — any failure is
                            // a real error. When inference is engaged
                            // only via arity-based heuristics (the
                            // declaration has no implicit markers),
                            // we fall back to partial application so
                            // intentional under-application still
                            // works.
                            bool explicitImplicitMode =
                                declaredImplicitCount > 0;
                            auto runInference = [&]() {
                                std::vector<LevelPointer> universeArguments;
                                if (!headIdentifier->universeArgs.empty()) {
                                    for (const auto& level :
                                         headIdentifier->universeArgs) {
                                        universeArguments.push_back(
                                            elaborateLevel(*level));
                                    }
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
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back({let->name, letType});
            // Propagate expectedType to body (shifted for new binder).
            ExpressionPointer bodyExpectedType =
                expectedType ? shift(expectedType, 1) : nullptr;
            ExpressionPointer letBody =
                elaborateExpression(*let->body, extended,
                                     bodyExpectedType);
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
                    Context coercionContext;
                    for (size_t i = 0; i < localBinders.size(); ++i) {
                        ExpressionPointer openedBinderType =
                            openOverLocalBinders(localBinders[i].type,
                                                  localBinders, i);
                        coercionContext.push_back(
                            {localBinders[i].name, openedBinderType,
                             FreeVariableOrigin::Internal});
                    }
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
                localBinders, expression.line);
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
                ExpressionPointer operandKernel =
                    elaborateExpression(*unary->operand, localBinders);
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
        if (std::get_if<SurfaceHammer>(&expression.node)) {
            return elaborateHammerPlaceholder(localBinders, expectedType,
                                                expression.line,
                                                expression.column);
        }
        if (std::get_if<SurfaceSorry>(&expression.node)) {
            return elaborateSorry(localBinders, expectedType,
                                   expression.line, expression.column);
        }
        if (std::get_if<SurfaceRing>(&expression.node)) {
            return elaborateRing(localBinders, expectedType,
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
        throw ElaborateError("unhandled surface expression variant");
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
        ExpressionPointer /*expectedType*/,
        int line, int /*column*/) {
        Frame frame(*this,
            "calc block at line " + std::to_string(line));
        ExpressionPointer previousKernel = elaborateExpression(
            *calc.initialExpression, localBinders);
        ExpressionPointer carrierTypeOpen =
            inferTypeInLocalContext(localBinders, previousKernel);
        ExpressionPointer carrierType = closeOverLocalBinders(
            carrierTypeOpen, localBinders, localBinders.size());
        LevelPointer carrierLevel =
            typeUniverseOf(localBinders, previousKernel);
        std::vector<ExpressionPointer> stepProofKernels;
        std::vector<ExpressionPointer> endpointKernels;
        endpointKernels.push_back(previousKernel);
        for (size_t k = 0; k < calc.steps.size(); ++k) {
            const auto& step = calc.steps[k];
            Frame stepFrame(*this,
                "calc step " + std::to_string(k + 1)
                + " at line " + std::to_string(step.line));
            ExpressionPointer nextKernel = elaborateExpression(
                *step.nextExpression, localBinders, carrierType);
            ExpressionPointer stepEqualityType = makeApplication(
                makeApplication(
                    makeApplication(
                        makeConstant("Equality", {carrierLevel}),
                        carrierType),
                    previousKernel),
                nextKernel);
            ExpressionPointer stepProofKernel;
            if (step.stepProof) {
                stepProofKernel = elaborateExpression(
                    *step.stepProof, localBinders, stepEqualityType);
            } else {
                // No `by <proof>` — run the auto-prover. v0: try
                // reflexivity (definitional equality) only. Future
                // iterations add commutativity/associativity/local-
                // hypothesis recognition via a single-position diff.
                stepProofKernel = autoProveCalcStep(
                    localBinders, previousKernel, nextKernel,
                    carrierType, carrierLevel, stepEqualityType,
                    step.line, step.column);
                if (!stepProofKernel) {
                    throwElaborate(
                        "calc step has no `by <proof>` and the "
                        "auto-prover couldn't close it. Add `by "
                        "<reason>` to disambiguate.");
                }
            }
            // Verify the proof actually has the equality type the step
            // claims — bare identifier proofs don't get checked against
            // expectedType during elaboration, so a wrong proof would
            // otherwise leak through to a confusing kernel error later.
            ExpressionPointer stepProofType = inferTypeInLocalContext(
                localBinders, stepProofKernel);
            ExpressionPointer stepEqualityTypeOpened = openOverLocalBinders(
                stepEqualityType, localBinders, localBinders.size());
            Context stepContext;
            for (size_t i = 0; i < localBinders.size(); ++i) {
                ExpressionPointer openedType = openOverLocalBinders(
                    localBinders[i].type, localBinders, i);
                stepContext.push_back({localBinders[i].name, openedType,
                                          FreeVariableOrigin::Internal});
            }
            if (!isDefinitionallyEqual(environment_, stepContext,
                                        stepProofType,
                                        stepEqualityTypeOpened)) {
                // Auto-rewrite fallback. If the user wrote a bare
                // expression of equality type as the step proof
                // (most commonly a hypothesis name like `IH`), and
                // it doesn't match the expected step equality, try
                // re-elaborating it as `rewrite(<surface>)`. The
                // existing rewrite desugaring finds the unique
                // occurrence of the proof's LHS in the goal's LHS
                // and wraps the proof in `Equality.congruence`.
                // Lets the user write `by IH` instead of
                // `by rewrite(IH)`. Only fires when a surface proof
                // was supplied — when stepProof is nullptr the
                // auto-prover above has already run.
                ExpressionPointer rewriteAttempt;
                if (step.stepProof) {
                    try {
                        rewriteAttempt = desugarRewrite(
                            step.stepProof, localBinders,
                            stepEqualityType,
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
                                                stepEqualityTypeOpened)) {
                        stepProofKernel = rewriteAttempt;
                        stepProofType = rewriteType;
                    }
                }
            }
            if (!isDefinitionallyEqual(environment_, stepContext,
                                        stepProofType,
                                        stepEqualityTypeOpened)) {
                TypeError error(
                    "calc step proof's type does not match the equality "
                    "claimed by this step");
                error.expectedType = stepEqualityTypeOpened;
                error.actualType = stepProofType;
                rethrowKernelError(error);
            }
            stepProofKernels.push_back(stepProofKernel);
            endpointKernels.push_back(nextKernel);
            previousKernel = nextKernel;
        }
        // One-step calc: the proof already has the desired type.
        if (stepProofKernels.size() == 1) {
            return stepProofKernels[0];
        }
        // Left-fold transitivity. After step k (0-indexed, k ≥ 1) the
        // running proof spans endpoints[0] → endpoints[k+1] via the
        // running middle endpoints[k].
        ExpressionPointer running = stepProofKernels[0];
        for (size_t k = 1; k < stepProofKernels.size(); ++k) {
            ExpressionPointer call = makeConstant(
                "Equality.transitivity", {carrierLevel});
            call = makeApplication(std::move(call), carrierType);
            call = makeApplication(std::move(call), endpointKernels[0]);
            call = makeApplication(std::move(call), endpointKernels[k]);
            call = makeApplication(std::move(call), endpointKernels[k + 1]);
            call = makeApplication(std::move(call), std::move(running));
            call = makeApplication(std::move(call), stepProofKernels[k]);
            running = std::move(call);
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
        // Peel leading Pi binders.
        int binderCount = 0;
        ExpressionPointer cursor = typeExpr;
        while (auto* pi = std::get_if<Pi>(&cursor->node)) {
            ++binderCount;
            cursor = pi->codomain;
        }
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
        forwardEntry.reverseDirection = false;
        lemmaIndex_.emplace(spineHash(lhs),
                              std::move(forwardEntry));
        RewriteLemma reverseEntry;
        reverseEntry.lemmaName = theoremName;
        reverseEntry.binderCount = binderCount;
        reverseEntry.lhs = lhs;
        reverseEntry.rhs = rhs;
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
        // Strategy 1: reflexivity for definitionally-equal endpoints.
        Context openedContext;
        for (size_t i = 0; i < localBinders.size(); ++i) {
            ExpressionPointer openedType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            openedContext.push_back({localBinders[i].name, openedType,
                                       FreeVariableOrigin::Internal});
        }
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
                ExpressionPointer varType = inferTypeInLocalContext(
                    localBinders, currentLeft);
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
                ExpressionPointer outerType =
                    inferTypeInLocalContext(localBinders, outerLeft);
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
    bool matchAgainstPattern(
        ExpressionPointer pattern,
        ExpressionPointer subject,
        int binderCount,
        std::vector<ExpressionPointer>& bindings) {
        if (auto* patternBV =
                std::get_if<BoundVariable>(&pattern->node)) {
            if (patternBV->deBruijnIndex < binderCount) {
                int slot = patternBV->deBruijnIndex;
                if (!bindings[slot]) {
                    bindings[slot] = subject;
                    return true;
                }
                return structurallyEqual(bindings[slot], subject);
            }
        }
        if (pattern->node.index() != subject->node.index()) {
            return false;
        }
        if (auto* p = std::get_if<BoundVariable>(&pattern->node)) {
            auto* s = std::get_if<BoundVariable>(&subject->node);
            // Pattern BVs with index >= binderCount refer to binders
            // outside the lemma — shouldn't occur in a well-formed
            // top-level lemma, but be defensive: require equal index.
            return p->deBruijnIndex == s->deBruijnIndex;
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
            return matchAgainstPattern(p->function, s->function,
                                          binderCount, bindings)
                && matchAgainstPattern(p->argument, s->argument,
                                          binderCount, bindings);
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
        // Pi / Lambda / Let are rare in lemma LHSs and require binder-
        // index bookkeeping we haven't wired up. Bail conservatively.
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
            bool allBound = true;
            for (const auto& binding : bindings) {
                if (!binding) { allBound = false; break; }
            }
            if (!allBound) continue;
            ExpressionPointer expectedOther =
                instantiateLemmaBinders(otherSide, bindings);
            if (!structurallyEqual(expectedOther, subRight)) continue;
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

    // Phase 3.0 hammer: a `?` placeholder asks the elaborator to fill
    // in a proof of the expected type. Current heuristics, tried in
    // order:
    //   1. Hypothesis match: scan local binders for one whose type is
    //      definitionally equal to the expected type; return that
    //      binder. Handles "I have a proof in scope; just use it".
    //   2. Reflexivity match: if the expected type is `Equality(A, x,
    //      x)` (the two endpoints are definitionally equal), return
    //      `reflexivity(x)`.
    // If neither succeeds we throw with a diagnostic listing the
    // expected type and the in-scope candidates.
    // Try the direct hammer strategies (hypothesis-match and
    // reflexivity-match) for the given goal. Returns the proof on
    // success (in closed local-binder form) or nullptr on failure.
    // Used both at the top level and recursively when trying
    // local-hypothesis application.
    ExpressionPointer tryDirectHammer(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer goalType) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalType, localBinders, localBinders.size());
        ExpressionPointer goalNormalised =
            weakHeadNormalForm(environment_, goalOpened);
        Context openedContext;
        for (size_t i = 0; i < localBinders.size(); ++i) {
            ExpressionPointer openedType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            openedContext.push_back({localBinders[i].name, openedType,
                                       FreeVariableOrigin::Internal});
        }
        // Hypothesis match.
        for (int i = static_cast<int>(localBinders.size()) - 1;
             i >= 0; --i) {
            ExpressionPointer candidateType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            if (isDefinitionallyEqual(environment_, openedContext,
                                        candidateType, goalNormalised)) {
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                return makeBoundVariable(deBruijnIndex);
            }
        }
        // Reflexivity match.
        ExpressionPointer cursor = goalNormalised;
        std::vector<ExpressionPointer> applicationArguments;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            applicationArguments.insert(
                applicationArguments.begin(),
                application->argument);
            cursor = application->function;
        }
        if (auto* constant = std::get_if<Constant>(&cursor->node)) {
            if (constant->name == "Equality"
                && applicationArguments.size() == 3) {
                if (isDefinitionallyEqual(
                        environment_, openedContext,
                        applicationArguments[1],
                        applicationArguments[2])) {
                    ExpressionPointer reflexivity = makeConstant(
                        "reflexivity", constant->universeArguments);
                    ExpressionPointer applied = makeApplication(
                        reflexivity, applicationArguments[0]);
                    applied = makeApplication(
                        applied, applicationArguments[1]);
                    return closeOverLocalBinders(
                        applied, localBinders, localBinders.size());
                }
            }
        }
        return nullptr;
    }

    // Try depth-1 application of an in-scope hypothesis. For each
    // local binder whose type is a non-dependent Pi chain ending in
    // (something definitionally equal to) the goal, recursively
    // hammer each domain with the direct strategies. If every arg is
    // fillable, return the application.
    //
    // "Non-dependent" means each Pi's codomain doesn't reference its
    // own binder. Dependent chains would need higher-order matching
    // to figure out what to fill the bound variable with — out of
    // scope for Phase 3.1.
    ExpressionPointer tryLocalHypothesisApplication(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer goalType) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalType, localBinders, localBinders.size());
        ExpressionPointer goalNormalised =
            weakHeadNormalForm(environment_, goalOpened);
        Context openedContext;
        for (size_t i = 0; i < localBinders.size(); ++i) {
            ExpressionPointer openedType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            openedContext.push_back({localBinders[i].name, openedType,
                                       FreeVariableOrigin::Internal});
        }
        for (int i = static_cast<int>(localBinders.size()) - 1;
             i >= 0; --i) {
            ExpressionPointer binderTypeOpened = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            std::vector<ExpressionPointer> openedDomains;
            ExpressionPointer cursor = weakHeadNormalForm(
                environment_, binderTypeOpened);
            bool nonDependent = true;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                if (referencesBoundBelowThreshold(pi->codomain, 1)) {
                    nonDependent = false;
                    break;
                }
                openedDomains.push_back(pi->domain);
                // Non-dependent: shift codomain down by 1 to drop the
                // unused binder, then continue walking.
                cursor = weakHeadNormalForm(
                    environment_, shift(pi->codomain, -1));
            }
            if (!nonDependent || openedDomains.empty()) continue;
            if (!isDefinitionallyEqual(environment_, openedContext,
                                         cursor, goalNormalised)) {
                continue;
            }
            // Recursively hammer each domain. Close back to local-
            // binder form first so `tryDirectHammer` sees the goal
            // shape it expects.
            std::vector<ExpressionPointer> arguments;
            bool allArgumentsFilled = true;
            for (const auto& openedDomain : openedDomains) {
                ExpressionPointer closedDomain = closeOverLocalBinders(
                    openedDomain, localBinders,
                    localBinders.size());
                ExpressionPointer argumentProof = tryDirectHammer(
                    localBinders, closedDomain);
                if (!argumentProof) {
                    allArgumentsFilled = false;
                    break;
                }
                arguments.push_back(std::move(argumentProof));
            }
            if (!allArgumentsFilled) continue;
            int deBruijnIndex =
                static_cast<int>(localBinders.size()) - 1 - i;
            ExpressionPointer applied = makeBoundVariable(deBruijnIndex);
            for (auto& argument : arguments) {
                applied = makeApplication(applied, std::move(argument));
            }
            return applied;
        }
        return nullptr;
    }

    // Try constructor-disjointness: if the goal is
    // `Not(Equality(I, C_i(...), C_j(...)))` for distinct constructors
    // C_i, C_j of the same inductive I, synthesize a discriminator
    // (I_recursor applied to a constant Proposition motive that
    // returns True for case i and False for everything else) and
    // build the proof via Equality_recursor. Currently restricted to
    // non-indexed inductives.
    ExpressionPointer tryConstructorDisjointness(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer goalType) {
        ExpressionPointer goalOpened = openOverLocalBinders(
            goalType, localBinders, localBinders.size());
        ExpressionPointer goalNormalised = weakHeadNormalForm(
            environment_, goalOpened);
        // `Not(X)` desugars to `X → False`, i.e. Pi with non-dependent
        // codomain False.
        auto* topPi = std::get_if<Pi>(&goalNormalised->node);
        if (!topPi) return nullptr;
        if (referencesBoundBelowThreshold(topPi->codomain, 1)) return nullptr;
        ExpressionPointer codomainNormalised = weakHeadNormalForm(
            environment_, topPi->codomain);
        auto* codomainConstant =
            std::get_if<Constant>(&codomainNormalised->node);
        if (!codomainConstant || codomainConstant->name != "False") {
            return nullptr;
        }
        // Domain must be Equality.{u}(I, lhs, rhs) applied to three args.
        ExpressionPointer domainNormalised = weakHeadNormalForm(
            environment_, topPi->domain);
        std::vector<ExpressionPointer> equalityArguments;
        ExpressionPointer cursor = domainNormalised;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            equalityArguments.insert(equalityArguments.begin(),
                                      application->argument);
            cursor = application->function;
        }
        auto* equalityConstant = std::get_if<Constant>(&cursor->node);
        if (!equalityConstant || equalityConstant->name != "Equality"
            || equalityArguments.size() != 3) {
            return nullptr;
        }
        ExpressionPointer inductiveTypeApplied = equalityArguments[0];
        ExpressionPointer leftHandSide  = equalityArguments[1];
        ExpressionPointer rightHandSide = equalityArguments[2];
        LevelPointer equalityUniverse =
            equalityConstant->universeArguments.empty()
                ? makeLevelConst(0)
                : equalityConstant->universeArguments[0];

        auto extractConstructorHead =
                [&](ExpressionPointer expression)
                    -> std::pair<const Constructor*, std::string> {
            ExpressionPointer e = weakHeadNormalForm(
                environment_, expression);
            while (auto* application =
                       std::get_if<Application>(&e->node)) {
                e = application->function;
            }
            auto* constant = std::get_if<Constant>(&e->node);
            if (!constant) return {nullptr, ""};
            const Declaration* declaration =
                environment_.lookup(constant->name);
            if (!declaration) return {nullptr, ""};
            auto* constructor =
                std::get_if<Constructor>(declaration);
            if (!constructor) return {nullptr, ""};
            return {constructor, constant->name};
        };
        auto leftHead  = extractConstructorHead(leftHandSide);
        auto rightHead = extractConstructorHead(rightHandSide);
        if (!leftHead.first || !rightHead.first) return nullptr;
        if (leftHead.first->inductiveName
            != rightHead.first->inductiveName) return nullptr;
        if (leftHead.first->constructorIndex
            == rightHead.first->constructorIndex) return nullptr;

        const std::string& inductiveName =
            leftHead.first->inductiveName;
        const Declaration* inductiveDeclaration =
            environment_.lookup(inductiveName);
        auto* inductive = inductiveDeclaration
            ? std::get_if<Inductive>(inductiveDeclaration) : nullptr;
        if (!inductive) return nullptr;
        std::string recursorName = inductiveName + "_recursor";
        const Declaration* recursorDeclaration =
            environment_.lookup(recursorName);
        auto* recursor = recursorDeclaration
            ? std::get_if<Recursor>(recursorDeclaration) : nullptr;
        if (!recursor) return nullptr;
        if (recursor->numIndices != 0) return nullptr;  // v1: non-indexed.

        // Extract the inductive's universe args + parameter values from
        // the applied form `I.{...}(p1, p2, ..., pN)` of the type.
        std::vector<ExpressionPointer> parameterValues;
        std::vector<LevelPointer> inductiveUniverseArguments;
        {
            ExpressionPointer e = weakHeadNormalForm(
                environment_, inductiveTypeApplied);
            std::vector<ExpressionPointer> appliedArgs;
            while (auto* application =
                       std::get_if<Application>(&e->node)) {
                appliedArgs.insert(appliedArgs.begin(),
                                    application->argument);
                e = application->function;
            }
            auto* inductiveConstant = std::get_if<Constant>(&e->node);
            if (!inductiveConstant
                || inductiveConstant->name != inductiveName) {
                return nullptr;
            }
            inductiveUniverseArguments =
                inductiveConstant->universeArguments;
            if (static_cast<int>(appliedArgs.size())
                != inductive->numParameters) {
                return nullptr;
            }
            parameterValues = std::move(appliedArgs);
        }

        // Required environment dependencies.
        if (!environment_.lookup("True")
            || !environment_.lookup("True.trivial")
            || !environment_.lookup("False")
            || !environment_.lookup("Equality_recursor")) {
            return nullptr;
        }

        // Build the constant motive: `function (_ : I_applied) => Proposition`.
        // The motive's domain is the fully-applied inductive type.
        ExpressionPointer constantMotive = makeLambda(
            "_discriminator_target", inductiveTypeApplied,
            makeProposition());

        // Build a case body for each constructor. The body is the
        // constant True (for the lhs's constructor index) or False
        // (for all others), wrapped in lambdas matching the recursor's
        // case signature: one lambda per constructor value-arg, plus an
        // extra lambda per recursive arg (immediately following it).
        // The recursive-arg lambdas have domain `Proposition` —
        // definitionally equal to `motive(arg)` for our constant motive,
        // which is what the recursor expects.
        std::vector<ExpressionPointer> caseLambdas;
        for (size_t constructorIndex = 0;
             constructorIndex < inductive->constructorNames.size();
             ++constructorIndex) {
            const std::string& constructorName =
                inductive->constructorNames[constructorIndex];
            const Declaration* constructorDeclaration =
                environment_.lookup(constructorName);
            auto* constructor = constructorDeclaration
                ? std::get_if<Constructor>(constructorDeclaration)
                : nullptr;
            if (!constructor) return nullptr;
            ExpressionPointer constructorCursor = constructor->type;
            for (const auto& parameterValue : parameterValues) {
                auto* parameterPi =
                    std::get_if<Pi>(&constructorCursor->node);
                if (!parameterPi) return nullptr;
                constructorCursor = substitute(parameterPi->codomain,
                                                0, parameterValue);
            }
            struct ValueArgument {
                std::string defaultName;
                ExpressionPointer type;
                bool isRecursive;
            };
            std::vector<ValueArgument> valueArguments;
            while (auto* valuePi =
                       std::get_if<Pi>(&constructorCursor->node)) {
                ValueArgument argument;
                argument.defaultName = valuePi->displayHint;
                argument.type = valuePi->domain;
                ExpressionPointer typeHead = valuePi->domain;
                while (auto* application =
                           std::get_if<Application>(&typeHead->node)) {
                    typeHead = application->function;
                }
                auto* typeHeadConstant =
                    std::get_if<Constant>(&typeHead->node);
                argument.isRecursive = typeHeadConstant
                    && typeHeadConstant->name == inductiveName;
                valueArguments.push_back(std::move(argument));
                constructorCursor = valuePi->codomain;
            }
            bool returnsTrue =
                static_cast<int>(constructorIndex)
                    == leftHead.first->constructorIndex;
            ExpressionPointer caseBody =
                makeConstant(returnsTrue ? "True" : "False");
            // Wrap in reverse order: innermost = caseBody, outermost
            // = the first value arg. Recursion lambdas sit immediately
            // INSIDE their corresponding constructor-arg lambda — i.e.
            // after the constructor arg in declaration order.
            for (int argumentIndex =
                     static_cast<int>(valueArguments.size()) - 1;
                 argumentIndex >= 0; --argumentIndex) {
                const ValueArgument& argument =
                    valueArguments[argumentIndex];
                if (argument.isRecursive) {
                    caseBody = makeLambda(
                        argument.defaultName.empty()
                            ? "_unused_recursion_argument"
                            : argument.defaultName
                                  + "_recursion_argument",
                        makeProposition(),
                        std::move(caseBody));
                }
                caseBody = makeLambda(
                    argument.defaultName.empty()
                        ? "_unused_value_argument"
                        : argument.defaultName,
                    argument.type,
                    std::move(caseBody));
            }
            caseLambdas.push_back(std::move(caseBody));
        }

        // Assemble the discriminator: I_recursor.{...inductiveUniArgs, 1}
        // applied to (parameterValues, constantMotive, caseLambdas...,
        // discriminatorTargetVar). The motive `λ _ : I. Proposition`
        // returns the Proposition universe — whose type is `Type 0`
        // (= Sort 1) — so the motive's universe level is 1.
        bool recursorHasMotiveLevel =
            recursor->universeParameters.size()
                > inductive->universeParameters.size();
        std::vector<LevelPointer> recursorUniverseArguments =
            inductiveUniverseArguments;
        if (recursorHasMotiveLevel) {
            recursorUniverseArguments.push_back(makeLevelConst(1));
        }
        ExpressionPointer discriminatorApplied = makeConstant(
            recursorName,
            std::move(recursorUniverseArguments));
        for (const auto& parameterValue : parameterValues) {
            discriminatorApplied = makeApplication(
                discriminatorApplied, parameterValue);
        }
        discriminatorApplied = makeApplication(
            discriminatorApplied, constantMotive);
        for (const auto& caseLambda : caseLambdas) {
            discriminatorApplied = makeApplication(
                discriminatorApplied, caseLambda);
        }
        // No index args (numIndices == 0). Apply the discriminator's
        // bound target var (de Bruijn 0 inside the outer Lambda).
        discriminatorApplied = makeApplication(
            discriminatorApplied, makeBoundVariable(0));
        // Wrap in a Lambda over the target.
        ExpressionPointer discriminator = makeLambda(
            "_discriminator_target", inductiveTypeApplied,
            std::move(discriminatorApplied));

        // Build the J/Equality_recursor motive:
        //   function (other : I) (_ : Equality(I, lhs, other)) =>
        //     discriminator(other)
        // The target Lambda sits at de Bruijn 1 (when we're in the
        // motive body); we shift discriminator down so the outer Lambda
        // it carries is unaffected (it has no free bound vars referring
        // to our local context since it's a closed kernel term).
        // Wait — discriminator may reference parameterValues which DO
        // come from the local context. Treat them carefully: the
        // discriminator was built with closed kernel expressions
        // (parameterValues are closed) so it's a closed term modulo
        // any free Bound vars referring to outer binders.
        //
        // The motive body `discriminator(other)` references `other`
        // (Bound 1 inside motive's nested-Lambda body). All other free
        // Bound refs in discriminator need to be SHIFTED by +2 (we're
        // adding two binders: `other` and the equality-proof).
        ExpressionPointer discriminatorShifted = shift(discriminator, 2);
        ExpressionPointer motiveBody = makeApplication(
            discriminatorShifted,
            makeBoundVariable(1));  // `other` arg of the motive
        // motive = λ (other : I). λ (_ : Equality(I, lhs, other)).
        //                discriminator(other)
        // Build the Equality-type expression for the inner Pi/Lambda
        // domain — Equality.{u}(I, lhs_shifted, Bound(0)).
        // Since we're at depth 1 (inside `other` Lambda), references to
        // lhs and inductiveTypeApplied (which come from the local
        // context) must be shifted by 1.
        ExpressionPointer equalityForMotive = makeConstant(
            "Equality", {equalityUniverse});
        equalityForMotive = makeApplication(
            equalityForMotive, shift(inductiveTypeApplied, 1));
        equalityForMotive = makeApplication(
            equalityForMotive, shift(leftHandSide, 1));
        equalityForMotive = makeApplication(
            equalityForMotive, makeBoundVariable(0));
        ExpressionPointer jMotive = makeLambda(
            "_equality_proof_for_motive", equalityForMotive, motiveBody);
        jMotive = makeLambda("_motive_other", inductiveTypeApplied,
                              std::move(jMotive));

        // Build the reflexivity case: True.trivial.
        ExpressionPointer reflexivityCase =
            makeConstant("True.trivial");

        // Assemble Equality_recursor.{0, equalityUniverse}(
        //   I, lhs, jMotive, True.trivial, rhs, equalityProofBound)
        // where equalityProofBound is the outer-most Lambda we wrap at
        // the end (the user's eq proof, Bound 0).
        ExpressionPointer recursorCall = makeConstant(
            "Equality_recursor",
            {makeLevelConst(0), equalityUniverse});
        recursorCall = makeApplication(
            recursorCall, shift(inductiveTypeApplied, 1));
        recursorCall = makeApplication(
            recursorCall, shift(leftHandSide, 1));
        recursorCall = makeApplication(
            recursorCall, shift(jMotive, 1));
        recursorCall = makeApplication(recursorCall, reflexivityCase);
        recursorCall = makeApplication(
            recursorCall, shift(rightHandSide, 1));
        recursorCall = makeApplication(recursorCall,
                                        makeBoundVariable(0));

        // Wrap in λ (equalityProof : Equality(I, lhs, rhs)). recursorCall.
        ExpressionPointer proofLambda = makeLambda(
            "_disjointness_equality", topPi->domain, recursorCall);
        // Close back over local binders so the caller's `expectedType`
        // (which is in closed form) matches.
        return closeOverLocalBinders(proofLambda, localBinders,
                                       localBinders.size());
    }

    // Try to discharge the current goal from a contradictory pair of
    // hypotheses in scope: H : P and H' : ¬P (= P → False). Build the
    // False proof H'(H) and lift to the goal via False.eliminate or
    // False.eliminate_proposition depending on the goal's universe.
    ExpressionPointer tryContradictionFromHypotheses(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer goalType) {
        if (!environment_.lookup("False")) return nullptr;
        Context openedContext;
        for (size_t i = 0; i < localBinders.size(); ++i) {
            ExpressionPointer openedType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            openedContext.push_back({localBinders[i].name, openedType,
                                       FreeVariableOrigin::Internal});
        }
        // Walk binders looking for one whose type is `P → False` for
        // some P. For each, scan for another binder whose type is
        // definitionally equal to P.
        for (int i = static_cast<int>(localBinders.size()) - 1;
             i >= 0; --i) {
            ExpressionPointer negationCandidate = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            ExpressionPointer normalised = weakHeadNormalForm(
                environment_, negationCandidate);
            auto* pi = std::get_if<Pi>(&normalised->node);
            if (!pi) continue;
            // Codomain must be False with no dependence on the bound
            // variable (Not(P) = P → False).
            if (referencesBoundBelowThreshold(pi->codomain, 1)) continue;
            ExpressionPointer codomainNormalised = weakHeadNormalForm(
                environment_, pi->codomain);
            auto* codomainConstant =
                std::get_if<Constant>(&codomainNormalised->node);
            if (!codomainConstant
                || codomainConstant->name != "False") continue;
            ExpressionPointer negatedProposition = pi->domain;
            for (int j = static_cast<int>(localBinders.size()) - 1;
                 j >= 0; --j) {
                if (j == i) continue;
                ExpressionPointer candidatePropositionType =
                    openOverLocalBinders(
                        localBinders[j].type, localBinders, j);
                if (!isDefinitionallyEqual(environment_, openedContext,
                                            candidatePropositionType,
                                            negatedProposition)) {
                    continue;
                }
                int negationDeBruijn =
                    static_cast<int>(localBinders.size()) - 1 - i;
                int propositionDeBruijn =
                    static_cast<int>(localBinders.size()) - 1 - j;
                ExpressionPointer falseProof = makeApplication(
                    makeBoundVariable(negationDeBruijn),
                    makeBoundVariable(propositionDeBruijn));
                // Lift False to the goal. Determine whether the goal
                // lives in Proposition (Sort 0) or Type u by inspecting
                // its inferred universe.
                LevelPointer goalUniverseLevel;
                bool goalIsProposition = false;
                try {
                    goalUniverseLevel = typeUniverseOf(
                        localBinders,
                        // Pass an "expression of type goalType" — we
                        // can't easily synthesise one; instead infer the
                        // universe of goalType directly.
                        goalType);
                    (void)goalUniverseLevel;
                } catch (...) {
                    // Fall back to eliminate_proposition on error.
                }
                {
                    // Inspect goal type's universe via a direct
                    // inferType on goalType. If it's Sort 0, we use
                    // eliminate_proposition; otherwise eliminate (Type).
                    ExpressionPointer goalTypeOpened =
                        openOverLocalBinders(goalType, localBinders,
                                              localBinders.size());
                    ExpressionPointer goalKind = weakHeadNormalForm(
                        environment_,
                        inferType(environment_, openedContext,
                                   goalTypeOpened));
                    auto* sort = std::get_if<Sort>(&goalKind->node);
                    if (sort) {
                        auto level = levelAsConstant(sort->level);
                        if (level && *level == 0) {
                            goalIsProposition = true;
                        }
                    }
                }
                const char* eliminator = goalIsProposition
                    ? "False.eliminate_proposition"
                    : "False.eliminate";
                if (!environment_.lookup(eliminator)) return nullptr;
                ExpressionPointer call = makeConstant(eliminator);
                call = makeApplication(std::move(call), goalType);
                call = makeApplication(std::move(call),
                                        std::move(falseProof));
                return call;
            }
        }
        return nullptr;
    }

    ExpressionPointer elaborateHammerPlaceholder(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        (void)column;
        Frame frame(*this,
            "hammer placeholder '?' at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "needs an expected type from context — '?' fills in a "
                "proof of the expected type, so the elaborator must "
                "know what that type is");
        }
        if (auto direct = tryDirectHammer(localBinders, expectedType)) {
            return direct;
        }
        if (auto applied =
                tryLocalHypothesisApplication(localBinders, expectedType)) {
            return applied;
        }
        if (auto disjoint =
                tryConstructorDisjointness(localBinders, expectedType)) {
            return disjoint;
        }
        if (auto contradiction =
                tryContradictionFromHypotheses(localBinders, expectedType)) {
            return contradiction;
        }
        std::string message =
            "could not find a proof of:\n      "
            + prettyPrintInLocalScope(expectedType, localBinders)
            + "\n  Tried: hypothesis-match, reflexivity-match, "
              "depth-1 hypothesis-application against "
            + std::to_string(localBinders.size())
            + " in-scope binders.";
        if (!localBinders.empty()) {
            message += "\n  Candidates in scope:";
            for (int i =
                     static_cast<int>(localBinders.size()) - 1;
                 i >= 0; --i) {
                message += "\n    ";
                message += localBinders[i].name;
                message += " : ";
                message += prettyPrintInLocalScope(
                    localBinders[i].type, localBinders, i);
            }
        }
        throwElaborate(message);
    }

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
        const std::vector<LocalBinder>& /*localBinders*/,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this, "ring at line " + std::to_string(line));
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
            throwElaborate(
                "`ring`: could not solve the goal with either `"
                + carrierName + ".multiply`-axioms or `"
                + carrierName + ".add`-axioms; v1 handles pure-product "
                "or pure-sum rearrangement only (no distributivity / "
                "mixed forms)");
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
            Context openedContext;
            for (size_t i = 0; i < localBinders.size(); ++i) {
                ExpressionPointer openedType = openOverLocalBinders(
                    localBinders[i].type, localBinders, i);
                openedContext.push_back({localBinders[i].name,
                                          openedType,
                                          FreeVariableOrigin::Internal});
            }
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

    // `cases scrutinee { | pattern => body | ... }`. Phase 1 covers
    // non-indexed inductives only. Re-uses the existing
    // `buildCaseLambda` helper by synthesizing a minimal pattern-match
    // declaration whose cases mirror the user's clauses.
    ExpressionPointer elaborateCasesExpression(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {

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
            Context openedContext;
            for (size_t i = 0; i < localBinders.size(); ++i) {
                ExpressionPointer openedType = openOverLocalBinders(
                    localBinders[i].type, localBinders, i);
                openedContext.push_back(
                    {localBinders[i].name, openedType,
                     FreeVariableOrigin::Internal});
            }
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
        std::vector<LocalBinder> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (const auto& name : lambda.binder.names) {
            ExpressionPointer domainHere =
                elaborateExpression(*lambda.binder.type, extended);
            domainsPerName.push_back(domainHere);
            extended.push_back({name, domainHere});
        }
        // If we have an expected Pi type, peel off as many Pi binders
        // as the lambda has names so we can pass the codomain down to
        // the body's elaboration. This lets constructor parameter
        // inference inside the body see the expected return type.
        ExpressionPointer expectedBody = nullptr;
        if (expectedType) {
            ExpressionPointer cursor =
                weakHeadNormalForm(environment_, expectedType);
            bool ok = true;
            for (size_t k = 0; k < lambda.binder.names.size(); ++k) {
                auto* pi = std::get_if<Pi>(&cursor->node);
                if (!pi) { ok = false; break; }
                cursor = pi->codomain;
            }
            if (ok) {
                expectedBody = cursor;
            }
        }
        ExpressionPointer body =
            elaborateExpression(*lambda.body, extended, expectedBody);
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
        ExpressionPointer leftKernel =
            elaborateExpression(leftSurface, localBinders);
        ExpressionPointer rightKernel =
            elaborateExpression(rightSurface, localBinders);
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
        auto* leftTypeConstantRaw =
            std::get_if<Constant>(&leftTypeRaw->node);
        std::string operandTypeName;
        if (leftTypeConstantRaw) {
            operandTypeName = leftTypeConstantRaw->name;
        } else {
            ExpressionPointer leftType =
                weakHeadNormalForm(environment_, leftTypeRaw);
            auto* leftTypeConstant =
                std::get_if<Constant>(&leftType->node);
            operandTypeName =
                leftTypeConstant ? leftTypeConstant->name : "<unknown>";
        }
        std::string targetFunction;
        // First consult the user-declared registry: any
        // `operator (sym) on (T1, T2) := F;` registration wins. This is
        // the extensible path — Rational, Real, Complex, polynomial
        // rings, etc. all hook in here.
        std::string rightTypeName;
        ExpressionPointer rightTypeRaw =
            inferTypeInLocalContext(localBinders, rightKernel);
        if (auto* rightTypeConstantRaw =
                std::get_if<Constant>(&rightTypeRaw->node)) {
            rightTypeName = rightTypeConstantRaw->name;
        } else {
            ExpressionPointer rightType =
                weakHeadNormalForm(environment_, rightTypeRaw);
            auto* rightTypeConstant =
                std::get_if<Constant>(&rightType->node);
            rightTypeName =
                rightTypeConstant ? rightTypeConstant->name : "<unknown>";
        }
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
        ExpressionPointer termTypeOpened = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, termKernel));
        ExpressionPointer termTypeClosed = closeOverLocalBinders(
            termTypeOpened, localBinders, localBinders.size());

        int occurrenceCount = 0;
        ExpressionPointer abstractedBody = abstractStructuralOccurrence(
            termTypeClosed, leftEndpoint,
            /*currentDepth=*/0, occurrenceCount);
        if (occurrenceCount == 0) {
            throwElaborate(
                "rewrite(eq, term): the equality's left endpoint "
                "does not appear (structurally) in term's type "
                "(`"
                + prettyPrintInLocalScope(termTypeOpened, localBinders)
                + "`); use explicit "
                "Equality.transport_proposition(...) if a "
                "non-structural rewrite is intended");
        }
        if (occurrenceCount > 1) {
            throwElaborate(
                "rewrite(eq, term): the equality's left endpoint "
                "appears "
                + std::to_string(occurrenceCount)
                + " times in term's type — use explicit "
                "Equality.transport_proposition(...) to "
                "disambiguate the position");
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
        std::vector<ExpressionPointer> argumentKernels;
        std::vector<std::string> argumentTypeNames;
        for (const auto& argumentSurface : argumentSurfaces) {
            ExpressionPointer argumentKernel =
                elaborateExpression(*argumentSurface, localBinders);
            argumentKernels.push_back(argumentKernel);
            ExpressionPointer argumentTypeRaw =
                inferTypeInLocalContext(localBinders, argumentKernel);
            std::string typeName = headConstantName(argumentTypeRaw);
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
            term = openBinder(term, localBinders[i - 1].name,
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
            term = closeBinder(term, localBinders[i].name,
                                FreeVariableOrigin::Internal);
        }
        return term;
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
        Context context;
        for (size_t i = 0; i < localBinders.size(); ++i) {
            ExpressionPointer openedType = openOverLocalBinders(
                localBinders[i].type, localBinders, i);
            context.push_back({localBinders[i].name, openedType,
                                FreeVariableOrigin::Internal});
        }
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
    std::vector<LevelPointer> inferUniverseArguments(
        const Declaration& declaration,
        const std::vector<ExpressionPointer>& valueArguments,
        const std::vector<LocalBinder>& localBinders) {

        const std::vector<std::string>& universeParameters =
            declarationUniverseParameters(declaration);
        if (universeParameters.empty()) return {};

        std::map<std::string, LevelPointer> assignment;
        ExpressionPointer cursor = declarationType(declaration);
        for (size_t i = 0;
             i < valueArguments.size() && cursor != nullptr; ++i) {
            cursor = weakHeadNormalForm(environment_, cursor);
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) break;
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
    std::string currentDeclarationName_;
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
    std::vector<std::string> contextFrames_;
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
                     std::vector<std::string>& importedModules) {
    Elaborator elaborator(environment, importedModules);
    elaborator.runModule(module);
}
