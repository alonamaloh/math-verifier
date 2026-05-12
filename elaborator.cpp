#include "elaborator.hpp"

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
    // -------- top-level statements --------

    void elaborateTopStatement(const SurfaceTopStatement& statement) {
        if (auto* import = std::get_if<SurfaceImportDecl>(&statement)) {
            importedModules_.push_back(import->moduleName);
            return;
        }
        if (std::get_if<SurfaceUsingDecl>(&statement)) {
            // No-op for v0: notation resolution not implemented yet. Modules
            // must use explicit qualified function calls.
            return;
        }
        if (auto* inductive = std::get_if<SurfaceInductiveDecl>(&statement)) {
            elaborateInductive(*inductive);
            return;
        }
        if (auto* axiom = std::get_if<SurfaceAxiomDecl>(&statement)) {
            elaborateAxiom(*axiom);
            return;
        }
        if (auto* definition = std::get_if<SurfaceDefinitionDecl>(&statement)) {
            elaborateDefinition(*definition);
            return;
        }
        throw ElaborateError("unhandled top-level statement variant");
    }

    void elaborateAxiom(const SurfaceAxiomDecl& declaration) {
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();
        ExpressionPointer type =
            elaborateExpression(*declaration.type, {});
        addAxiom(environment_, declaration.name,
                 finalUniverseParameters(declaration.universeParameters),
                 std::move(type));
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

    void elaborateDefinition(const SurfaceDefinitionDecl& declaration) {
        if (!declaration.cases.empty()) {
            elaboratePatternMatchDefinition(declaration);
            return;
        }
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
        ExpressionPointer bodyExpression =
            elaborateExpression(*declaration.body, localBinders);

        // Build the full declared type and body by wrapping in reverse.
        ExpressionPointer fullType = returnType;
        ExpressionPointer fullBody = bodyExpression;
        for (auto iterator = argumentBinders.rbegin();
             iterator != argumentBinders.rend(); ++iterator) {
            fullType = makePi(iterator->first, iterator->second, fullType);
            fullBody = makeLambda(iterator->first, iterator->second,
                                   fullBody);
        }

        addDefinition(environment_, declaration.name,
                      finalUniverseParameters(declaration.universeParameters),
                      std::move(fullType), std::move(fullBody));
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
        const SurfaceDefinitionDecl& declaration) {

        if (!declaration.arguments.empty()) {
            throw ElaborateError(
                "pattern-match definition '" + declaration.name
                + "' must declare its arguments in the type signature, "
                "not as binders before the colon. (Support for outer "
                "binders is a future iteration.)");
        }

        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();

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

        // The first argument is the scrutinee. Its type is either a
        // bare identifier (no parameters) or an application of an
        // inductive identifier to parameter values (e.g.,
        // `Exists(Natural, P)`). Indices aren't supported by pattern
        // matching yet — see Equality / LessOrEqual, which still need
        // direct recursor calls.
        const SurfaceArgument& scrutineeArgument = functionArguments[0];
        std::string inductiveName;
        {
            SurfaceExpressionPointer head = scrutineeArgument.type;
            while (auto* application =
                       std::get_if<SurfaceApplication>(&head->node)) {
                head = application->function;
            }
            auto* identifier =
                std::get_if<SurfaceIdentifier>(&head->node);
            if (!identifier) {
                throw ElaborateError(
                    "pattern-match definition '" + declaration.name
                    + "': scrutinee type must be an inductive name "
                    "(optionally applied to parameter values)");
            }
            inductiveName = identifier->qualifiedName;
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

        // Elaborate the kernel types for each function argument, and
        // the kernel return type. We need these for both type signature
        // and motive construction.
        std::vector<LocalBinder> binderStack;
        std::vector<ExpressionPointer> argumentKernelTypes;
        for (const auto& argument : functionArguments) {
            ExpressionPointer argumentType =
                elaborateExpression(*argument.type, binderStack);
            argumentKernelTypes.push_back(argumentType);
            binderStack.push_back({argument.name, argumentType});
        }
        ExpressionPointer returnKernelType =
            elaborateExpression(*returnType, binderStack);

        // Analyse the elaborated scrutinee type to extract the
        // inductive's universe arguments and (for parameterised
        // inductives) the parameter values that the scrutinee is
        // applied to. The form is Application(Application(...
        // Constant("Inductive", {univ_args}), p1), p2) for an
        // inductive applied to two parameters.
        std::vector<LevelPointer> inductiveUniverseArguments;
        std::vector<ExpressionPointer> parameterValues;
        {
            ExpressionPointer cursor = weakHeadNormalForm(
                environment_, argumentKernelTypes[0]);
            while (auto* application =
                       std::get_if<Application>(&cursor->node)) {
                parameterValues.insert(parameterValues.begin(),
                                        application->argument);
                cursor = weakHeadNormalForm(
                    environment_, application->function);
            }
            auto* headConstant = std::get_if<Constant>(&cursor->node);
            if (!headConstant) {
                throw ElaborateError(
                    "internal: scrutinee type's head is not an inductive constant");
            }
            inductiveUniverseArguments = headConstant->universeArguments;
        }
        int numInductiveArgs =
            static_cast<int>(parameterValues.size());
        int numIndexArgs =
            numInductiveArgs - inductive->numParameters;
        if (numIndexArgs != 0) {
            throw ElaborateError(
                "pattern matching on indexed inductives is not yet "
                "supported (inductive '" + inductiveName
                + "' applied with " + std::to_string(numIndexArgs)
                + " index argument(s) — use a direct recursor call)");
        }

        // Build the full type as a Pi chain.
        ExpressionPointer fullType = returnKernelType;
        for (int i = static_cast<int>(functionArguments.size()) - 1;
             i >= 0; --i) {
            fullType = makePi(functionArguments[i].name,
                              argumentKernelTypes[i],
                              std::move(fullType));
        }

        // Build the motive in the kernel. The motive is a lambda over
        // the scrutinee, with body = Pi over the remaining arguments
        // ending
        // in the return type. The return type may reference any of the
        // function's arguments, so we elaborate it with the full binder
        // stack [scrutinee, otherArg1, ..., otherArgN] in scope and
        // then wrap with Pis for the non-scrutinee arguments.
        ExpressionPointer motive;
        {
            std::vector<LocalBinder> motiveStack;
            motiveStack.push_back({scrutineeArgument.name,
                                   argumentKernelTypes[0]});
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
            for (int i =
                     static_cast<int>(otherArgumentKernelTypes.size()) - 1;
                 i >= 0; --i) {
                motiveCodomain = makePi(functionArguments[i + 1].name,
                                         otherArgumentKernelTypes[i],
                                         std::move(motiveCodomain));
            }
            motive = makeLambda(scrutineeArgument.name,
                                argumentKernelTypes[0],
                                std::move(motiveCodomain));
        }

        // Determine the motive's universe level by asking the kernel for
        // its type (a Pi chain ending in a Sort).
        LevelPointer motiveLevel;
        {
            ExpressionPointer motiveType =
                inferType(environment_, {}, motive);
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

        // Collect surface types for buildCaseLambda to use when
        // elaborating non-scrutinee argument types per case.
        std::vector<FunctionArgumentPair> functionArgumentPairs;
        for (const auto& argument : functionArguments) {
            functionArgumentPairs.push_back({argument.name, argument.type});
        }
        // Build a case lambda for each constructor, in declared order.
        // For parameterised inductives, pass the parameter values so the
        // case lambda can strip the constructor's parameter Pis and
        // substitute the values into the remaining argument types.
        std::vector<ExpressionPointer> caseLambdas;
        for (const auto& constructorName : inductive->constructorNames) {
            caseLambdas.push_back(
                buildCaseLambda(declaration, constructorName,
                                inductiveName, motive,
                                functionArgumentPairs,
                                inductive->numParameters,
                                parameterValues));
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
        for (const auto& parameterValue : parameterValues) {
            applied = makeApplication(std::move(applied), parameterValue);
        }
        applied = makeApplication(std::move(applied), motive);
        for (auto& caseLambda : caseLambdas) {
            applied = makeApplication(std::move(applied),
                                       std::move(caseLambda));
        }
        // The scrutinee. The function's arguments are bound (from
        // innermost outermost) at depths n-1, n-2, ..., 0 inside the
        // body lambda. The scrutinee is the FIRST function argument,
        // so its de Bruijn index when we're inside ALL function
        // argument binders is (n - 1) — counting from innermost
        // outward.
        int argumentCount = static_cast<int>(functionArguments.size());
        applied = makeApplication(std::move(applied),
                                   makeBoundVariable(argumentCount - 1));
        // Then apply to all the other arguments (in declaration order,
        // from
        // the second onward). At the point we apply argument i, its de
        // Bruijn index inside the body lambda is (argumentCount - 1 - i).
        for (int i = 1; i < argumentCount; ++i) {
            applied = makeApplication(
                std::move(applied),
                makeBoundVariable(argumentCount - 1 - i));
        }

        // Wrap in lambdas over function arguments.
        ExpressionPointer fullBody = applied;
        for (int i = argumentCount - 1; i >= 0; --i) {
            fullBody = makeLambda(functionArguments[i].name,
                                   argumentKernelTypes[i],
                                   std::move(fullBody));
        }

        addDefinition(environment_, declaration.name,
                      finalUniverseParameters(declaration.universeParameters),
                      std::move(fullType), std::move(fullBody));

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
    ExpressionPointer buildCaseLambda(
        const SurfaceDefinitionDecl& declaration,
        const std::string& constructorName,
        const std::string& inductiveName,
        ExpressionPointer motive,
        const std::vector<FunctionArgumentPair>& functionArgumentTypes,
        int numParameters,
        const std::vector<ExpressionPointer>& parameterValues) {

        // Find the case in the declaration matching this constructor.
        const SurfacePatternCase* matchedCase = nullptr;
        for (const auto& caseDecl : declaration.cases) {
            const SurfacePattern& firstPattern = *caseDecl.patterns.front();
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
                matchedCase = &caseDecl;
                break;
            }
        }
        if (!matchedCase) {
            throw ElaborateError(
                "missing pattern case for constructor '" + constructorName
                + "' in definition '" + declaration.name + "'");
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
        {
            // Skip the constructor's parameter Pis (the first
            // numParameters of them); they're filled by the recursor
            // application and aren't bound by the case lambda.
            ExpressionPointer cursor = constructor->type;
            for (int i = 0; i < numParameters; ++i) {
                auto* pi = std::get_if<Pi>(&cursor->node);
                if (!pi) {
                    throw ElaborateError(
                        "internal: constructor '" + constructorName
                        + "' has fewer parameter Pis than expected");
                }
                cursor = pi->codomain;
            }
            // Substitute the parameter values into the remaining type,
            // innermost-bound (last) parameter first. After all
            // substitutions, the remaining Pis bind only non-parameter
            // arguments and reference the parameter values directly.
            for (auto iterator = parameterValues.rbegin();
                 iterator != parameterValues.rend(); ++iterator) {
                cursor = substitute(cursor, 0, *iterator);
            }
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                ConstructorArgument constructorArgument;
                constructorArgument.defaultName = pi->displayHint;
                constructorArgument.type = pi->domain;
                // Recursive argument: type's head (after peeling
                // Applications) is the inductive constant.
                ExpressionPointer typeHead = pi->domain;
                while (auto* application =
                           std::get_if<Application>(&typeHead->node)) {
                    typeHead = application->function;
                }
                auto* constant =
                    std::get_if<Constant>(&typeHead->node);
                constructorArgument.isRecursive =
                    constant && constant->name == inductiveName;
                constructorArguments.push_back(constructorArgument);
                cursor = pi->codomain;
            }
        }
        if (destructuredNames.size() != constructorArguments.size()) {
            throw ElaborateError(
                "pattern for '" + constructorName + "' binds "
                + std::to_string(destructuredNames.size())
                + " arguments but the constructor takes "
                + std::to_string(constructorArguments.size()));
        }

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
            lambdaBinders.push_back({destructuredName, constructorArgumentType});
            binderDepth++;
            if (constructorArgument.isRecursive) {
                // Recursive hypothesis: type = motive(<this destructured>).
                // Motive lives at the outer (empty) context, so we shift
                // by binderDepth to bring it under all current binders.
                ExpressionPointer shiftedMotive = shift(motive, binderDepth);
                ExpressionPointer recursionHypothesisType =
                    makeApplication(shiftedMotive,
                                    makeBoundVariable(0));
                // ^ Bound(0) is the most-recently-bound name, which is
                // the constructor argument we just added
                // (destructuredName).
                std::string hypothesisName =
                    "_inductionHypothesisFor_" + destructuredName;
                lambdaBinders.push_back({hypothesisName,
                                          recursionHypothesisType});
                recursiveArgToHypothesis[destructuredName] = hypothesisName;
                binderDepth++;
            }
        }

        // Add the function's other arguments (patterns[1..n-1]).
        for (size_t i = 1; i < matchedCase->patterns.size(); ++i) {
            const SurfacePattern& pattern = *matchedCase->patterns[i];
            auto* bareName = std::get_if<SurfacePatternBareName>(
                &pattern.node);
            if (!bareName) {
                throw ElaborateError(
                    "non-scrutinee pattern positions must be variable "
                    "patterns (e.g. 'm' or '_')");
            }
            // Look up the i-th function argument's surface type. We use
            // the pre-decomposed `functionArgumentTypes` list rather than
            // re-walking declaration.type, because surface Pi nodes may
            // bind multiple names per Pi (e.g. `(a b : Natural)`).
            if (i >= functionArgumentTypes.size()) {
                throw ElaborateError(
                    "pattern case for '" + constructorName + "' has too "
                    "many positions for the function signature");
            }
            SurfaceExpressionPointer surfaceArgType =
                functionArgumentTypes[i].surfaceType;
            // Elaborate this surface type in a binder stack reflecting
            // our current lambda binders.
            std::vector<LocalBinder> stack;
            for (const auto& binder : lambdaBinders) {
                stack.push_back({binder.name, binder.type});
            }
            ExpressionPointer argumentType =
                elaborateExpression(*surfaceArgType, stack);
            lambdaBinders.push_back({bareName->name, argumentType});
            binderDepth++;
        }

        // Translate the body: rewrite recursive calls.
        SurfaceExpressionPointer rewrittenBody = rewriteRecursiveCalls(
            matchedCase->body, declaration.name, recursiveArgToHypothesis);

        // Elaborate the body with all binders in scope.
        std::vector<LocalBinder> bodyStack;
        for (const auto& binder : lambdaBinders) {
            bodyStack.push_back({binder.name, binder.type});
        }
        ExpressionPointer bodyKernel =
            elaborateExpression(*rewrittenBody, bodyStack);

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
    // `thisDeclName(<destructuredName>, ...rest)` with `<recursionHypothesis>(...rest)`,
    // where the mapping `destructuredName → recursionHypothesis` is
    // determined by the case currently being translated. Non-recursive
    // calls (or recursive calls on something other than a destructured
    // variable) are left alone — the kernel will reject them as ill-
    // typed if structural recursion was actually required.
    SurfaceExpressionPointer rewriteRecursiveCalls(
        SurfaceExpressionPointer expression,
        const std::string& thisDeclName,
        const std::map<std::string, std::string>&
            recursiveArgToHypothesis) {

        const SurfaceExpression& node = *expression;
        if (auto* application =
                std::get_if<SurfaceApplication>(&node.node)) {
            // Recurse into function and arguments first.
            auto rewrittenFunction = rewriteRecursiveCalls(
                application->function, thisDeclName,
                recursiveArgToHypothesis);
            std::vector<SurfaceExpressionPointer> rewrittenArguments;
            for (const auto& argument : application->arguments) {
                rewrittenArguments.push_back(rewriteRecursiveCalls(
                    argument, thisDeclName, recursiveArgToHypothesis));
            }
            // Check if this is a recursive call we should rewrite.
            auto* functionIdentifier = std::get_if<SurfaceIdentifier>(
                &application->function->node);
            if (functionIdentifier
                && functionIdentifier->qualifiedName == thisDeclName
                && functionIdentifier->universeArgs.empty()
                && !rewrittenArguments.empty()) {
                auto* firstArgumentIdentifier =
                    std::get_if<SurfaceIdentifier>(
                        &rewrittenArguments[0]->node);
                if (firstArgumentIdentifier
                    && firstArgumentIdentifier->universeArgs.empty()) {
                    auto iterator = recursiveArgToHypothesis.find(
                        firstArgumentIdentifier->qualifiedName);
                    if (iterator != recursiveArgToHypothesis.end()) {
                        // Replace head with the recursion hypothesis,
                        // dropping the first argument (which the kernel
                        // handles implicitly via the recursor).
                        auto hypothesisIdentifier =
                            makeSurfaceIdentifier(iterator->second, {},
                                                   node.line, node.column);
                        std::vector<SurfaceExpressionPointer>
                            remainingArguments(
                                rewrittenArguments.begin() + 1,
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
                                        recursiveArgToHypothesis)},
                rewriteRecursiveCalls(piType->codomain, thisDeclName,
                                       recursiveArgToHypothesis),
                node.line, node.column);
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&node.node)) {
            return makeSurfaceLambda(
                {lambda->binder.names,
                 rewriteRecursiveCalls(lambda->binder.type, thisDeclName,
                                        recursiveArgToHypothesis)},
                rewriteRecursiveCalls(lambda->body, thisDeclName,
                                       recursiveArgToHypothesis),
                node.line, node.column);
        }
        if (auto* let = std::get_if<SurfaceLet>(&node.node)) {
            return makeSurfaceLet(
                let->name,
                rewriteRecursiveCalls(let->type, thisDeclName,
                                       recursiveArgToHypothesis),
                rewriteRecursiveCalls(let->value, thisDeclName,
                                       recursiveArgToHypothesis),
                rewriteRecursiveCalls(let->body, thisDeclName,
                                       recursiveArgToHypothesis),
                node.line, node.column);
        }
        if (auto* ascription = std::get_if<SurfaceAscription>(&node.node)) {
            return makeSurfaceAscription(
                rewriteRecursiveCalls(ascription->expression,
                                       thisDeclName,
                                       recursiveArgToHypothesis),
                rewriteRecursiveCalls(ascription->type, thisDeclName,
                                       recursiveArgToHypothesis),
                node.line, node.column);
        }
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&node.node)) {
            return makeSurfaceBinaryOperation(
                binary->opSymbol,
                rewriteRecursiveCalls(binary->left, thisDeclName,
                                       recursiveArgToHypothesis),
                rewriteRecursiveCalls(binary->right, thisDeclName,
                                       recursiveArgToHypothesis),
                node.line, node.column);
        }
        if (auto* unary = std::get_if<SurfaceUnaryOperation>(&node.node)) {
            return makeSurfaceUnaryOperation(
                unary->opSymbol,
                rewriteRecursiveCalls(unary->operand, thisDeclName,
                                       recursiveArgToHypothesis),
                node.line, node.column);
        }
        // Atomic forms (identifier, numeric literal, Type, Proposition) are
        // unchanged.
        return expression;
    }

    void elaborateInductive(const SurfaceInductiveDecl& declaration) {
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
        addInductive(environment_, declaration.name,
                     finalUniverseParameters(declaration.universeParameters),
                     fullKind, numParameters,
                     std::move(kernelConstructors));

        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

    // -------- expression elaboration --------

    ExpressionPointer elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<LocalBinder>& localBinders) {

        if (auto* identifier =
                std::get_if<SurfaceIdentifier>(&expression.node)) {
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
                // Stage 2 universe inference: if the head is a polymorphic
                // constant called without explicit `.{...}`, infer the
                // universe arguments by unifying the value arguments'
                // types against the declaration's parameter types.
                bool isCurrentDeclaration =
                    !currentDeclarationName_.empty()
                    && currentDeclarationName_ == name;
                const Declaration* environmentDeclaration =
                    environment_.lookup(name);
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
            for (const auto& argument : application->arguments) {
                ExpressionPointer argumentTerm =
                    elaborateExpression(*argument, localBinders);
                head = makeApplication(std::move(head),
                                        std::move(argumentTerm));
            }
            return head;
        }
        if (auto* piType = std::get_if<SurfacePiType>(&expression.node)) {
            return elaboratePiType(*piType, localBinders);
        }
        if (auto* lambda = std::get_if<SurfaceLambda>(&expression.node)) {
            return elaborateLambda(*lambda, localBinders);
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            ExpressionPointer letType =
                elaborateExpression(*let->type, localBinders);
            ExpressionPointer letValue =
                elaborateExpression(*let->value, localBinders);
            std::vector<LocalBinder> extended = localBinders;
            extended.push_back({let->name, letType});
            ExpressionPointer letBody =
                elaborateExpression(*let->body, extended);
            return makeLet(let->name, std::move(letType),
                           std::move(letValue), std::move(letBody));
        }
        if (auto* ascription =
                std::get_if<SurfaceAscription>(&expression.node)) {
            // For v0 the type ascription is informative only; we trust
            // the user and elaborate the inner expression. Type checking
            // happens when the kernel sees the term.
            return elaborateExpression(*ascription->expression,
                                        localBinders);
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
            return desugarArithmeticOperator(
                binary->opSymbol, *binary->left, *binary->right,
                localBinders, expression.line);
        }
        if (auto* unary =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            throw ElaborateError(
                "unary operator '" + unary->opSymbol + "' is not yet "
                "supported by the elaborator");
        }
        throw ElaborateError("unhandled surface expression variant");
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
        const std::vector<LocalBinder>& localBinders) {
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
        ExpressionPointer body =
            elaborateExpression(*lambda.body, extended);
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
        ExpressionPointer leftKernel =
            elaborateExpression(leftSurface, localBinders);
        ExpressionPointer rightKernel =
            elaborateExpression(rightSurface, localBinders);
        // Determine the operand type by inferring the type of the left
        // operand. We peel any FreeVars from opening because we only
        // need to peek at the head.
        ExpressionPointer leftType = weakHeadNormalForm(environment_,
            inferTypeInLocalContext(localBinders, leftKernel));
        auto* leftTypeConstant = std::get_if<Constant>(&leftType->node);
        std::string operandTypeName =
            leftTypeConstant ? leftTypeConstant->name : "<unknown>";
        std::string targetFunction;
        if (operandTypeName == "Natural") {
            if (operatorSymbol == "+") targetFunction = "Natural.add";
            else if (operatorSymbol == "*") targetFunction = "Natural.multiply";
        }
        if (targetFunction.empty()) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' is not supported for "
                "operand type '" + operandTypeName + "' (line "
                + std::to_string(line)
                + "); v1 supports + and * on Natural only");
        }
        if (environment_.lookup(targetFunction) == nullptr) {
            throw ElaborateError(
                "operator '" + operatorSymbol + "' resolves to '"
                + targetFunction + "' but that function is not in scope "
                "(line " + std::to_string(line) + ")");
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

        // The endpoints came out of the inferred type, which lives in
        // the opened form with FreeVariables for our local binders.
        // Close them back to BoundVariables so they make sense in the
        // calling context.
        ExpressionPointer closedLeftEndpoint = closeOverLocalBinders(
            leftEndpoint, localBinders, localBinders.size());
        ExpressionPointer closedRightEndpoint = closeOverLocalBinders(
            rightEndpoint, localBinders, localBinders.size());

        // Build Equality.congruence.{u, v}(A, B, f, x, y, proof).
        ExpressionPointer call = makeConstant(
            "Equality.congruence",
            {domainUniverseLevel, codomainUniverseLevel});
        call = makeApplication(std::move(call), std::move(domainType));
        call = makeApplication(std::move(call), std::move(codomainType));
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
