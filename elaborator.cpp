#include "elaborator.hpp"

#include "printer.hpp"

#include <iostream>
#include <set>
#include <string>
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

class Elaborator {
public:
    Elaborator(Environment& environment,
               std::vector<std::string>& importedModules)
        : environment_(environment),
          importedModules_(importedModules) {}

    void runModule(const SurfaceModule& module) {
        moduleName_ = module.moduleName;
        for (const auto& statement : module.statements) {
            elaborateTopStatement(statement);
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
        throw ElaborateError("unhandled top-level statement variant");
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
        // Axioms are accepted without proof — flag every one so that
        // verifying a file is never silent about its unproved assumptions.
        std::cerr << "warning: axiom '" << declaration.name
                  << "' admitted without proof\n";
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
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

    void elaborateDefinition(const SurfaceDefinitionDeclaration& declaration) {
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
            std::vector<SurfaceExpressionPointer> rewrittenArguments;
            for (const auto& argument : application->arguments) {
                rewrittenArguments.push_back(rewriteRecursiveCalls(
                    argument, thisDeclName, recursiveArgToHypothesis,
                    outerBinderCount));
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
                        &rewrittenArguments[outerBinderCount]->node);
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
                        std::vector<SurfaceExpressionPointer>
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

    ExpressionPointer elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType = nullptr) {

        if (auto* identifier =
                std::get_if<SurfaceIdentifier>(&expression.node)) {
            (void)expectedType;
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
            if (headIdentifier && headIdentifier->universeArgs.empty()) {
                const std::string& name = headIdentifier->qualifiedName;
                size_t argumentCount = application->arguments.size();
                if (name == "congruenceOf" && argumentCount == 2) {
                    return desugarCongruenceOf(
                        application->arguments[0],
                        application->arguments[1],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "reflexivity" && argumentCount == 1) {
                    return desugarReflexivity(
                        application->arguments[0],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "Equality.symmetry" && argumentCount == 1) {
                    return desugarEqualitySymmetry(
                        application->arguments[0],
                        localBinders,
                        expression.line, expression.column);
                }
                if (name == "Equality.transitivity"
                    && argumentCount == 2) {
                    return desugarEqualityTransitivity(
                        application->arguments[0],
                        application->arguments[1],
                        localBinders,
                        expression.line, expression.column);
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
                                    application->arguments,
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
                                        application->arguments,
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
                         application->arguments) {
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
            for (const auto& argument : application->arguments) {
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
            // type doesn't match the ascribed type but a canonical
            // embedding chain between them exists, compose the chain
            // and apply it. Currently a single hardcoded link —
            //     Natural → Integer  (via `Natural.to_integer`)
            // — which grows as Rational / Real / Complex land. The
            // lookup uses definitional equality, so type-level
            // aliases and δ-reducible definitions are matched
            // transparently.
            //
            // When no coercion fires, fall through to returning
            // `inner` directly; any type mismatch surfaces at the
            // eventual use site, exactly as it did before.
            if (environment_.lookup("Natural.to_integer") != nullptr) {
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
                    ExpressionPointer naturalType = makeConstant("Natural");
                    ExpressionPointer integerType = makeConstant("Integer");
                    if (isDefinitionallyEqual(environment_, coercionContext,
                                                innerTypeOpened, naturalType)
                        && isDefinitionallyEqual(environment_, coercionContext,
                                                   ascribedTypeOpened,
                                                   integerType)) {
                        return makeApplication(
                            makeConstant("Natural.to_integer"),
                            std::move(inner));
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
                ExpressionPointer rightKernel =
                    elaborateExpression(*binary->right, localBinders);
                ExpressionPointer leftTypeOpen =
                    inferTypeInLocalContext(localBinders, leftKernel);
                ExpressionPointer leftType = closeOverLocalBinders(
                    leftTypeOpen, localBinders, localBinders.size());
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
            ExpressionPointer stepProofKernel = elaborateExpression(
                *step.stepProof, localBinders, stepEqualityType);
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
        // For `<` we wrap the left operand in `successor`, since
        // `a < b` is defined as `LessOrEqual(successor(a), b)`.
        bool wrapLeftInSuccessor = false;
        if (operandTypeName == "Natural") {
            if (operatorSymbol == "+") targetFunction = "Natural.add";
            else if (operatorSymbol == "*") targetFunction = "Natural.multiply";
            else if (operatorSymbol == "≤") targetFunction = "LessOrEqual";
            else if (operatorSymbol == "<") {
                targetFunction = "LessOrEqual";
                wrapLeftInSuccessor = true;
            }
            else if (operatorSymbol == "∣") targetFunction = "Natural.divides";
        }
        else if (operandTypeName == "Integer") {
            if (operatorSymbol == "+") targetFunction = "Integer.add";
            else if (operatorSymbol == "*") targetFunction = "Integer.multiply";
            else if (operatorSymbol == "-") targetFunction = "Integer.subtract";
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
        int line, int column) {
        ExpressionPointer firstEqualityKernel =
            elaborateExpression(*firstEqualitySurface, localBinders);
        ExpressionPointer secondEqualityKernel =
            elaborateExpression(*secondEqualitySurface, localBinders);
        ExpressionPointer firstEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          firstEqualityKernel));
        ExpressionPointer secondEqualityType =
            weakHeadNormalForm(environment_,
                inferTypeInLocalContext(localBinders,
                                          secondEqualityKernel));
        EqualityComponents firstComponents = extractEqualityComponents(
            firstEqualityType,
            "Equality.transitivity (first argument)", line);
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
