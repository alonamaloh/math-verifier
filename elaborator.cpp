#include "elaborator.hpp"

#include <iostream>
#include <set>
#include <string>
#include <utility>
#include <vector>

namespace {

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
        ExpressionPointer type =
            elaborateExpression(*declaration.type, {});
        addAxiom(environment_, declaration.name,
                 declaration.universeParameters,
                 std::move(type));
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
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

        // Surface form has explicit (a : T) binders before the colon, plus
        // a return type after, plus a body. To register with the kernel:
        //   declared type = (a1 : T1) → (a2 : T2) → ... → returnType
        //   body          = fun (a1 : T1) (a2 : T2) ... => bodyExpression
        // We thread a local-binder list as we elaborate the type and body
        // in parallel, then wrap both with the appropriate Pi / Lambda.
        std::vector<std::string> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            argumentBinders;
        for (const auto& binder : declaration.arguments) {
            ExpressionPointer argumentType =
                elaborateExpression(*binder.type, localBinders);
            for (const auto& name : binder.names) {
                argumentBinders.push_back({name, argumentType});
                localBinders.push_back(name);
                // Re-elaborate type if multiple names share one binder
                // — but we share the same kernel term across names; the
                // kernel handles de Bruijn lifting correctly only if we
                // re-elaborate in the extended context for each name.
                // We re-elaborate below if there's another name to bind.
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
                      declaration.universeParameters,
                      std::move(fullType), std::move(fullBody));
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
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
    //     (Pi-chain). No `(args)` allowed before the colon.
    //   - The first argument is the scrutinee. Its type must be a bare
    //     inductive identifier with zero parameters (Natural, Boolean,
    //     enum-like types).
    //   - Other positions in each pattern row must be bare variable
    //     patterns (or `_`).
    //   - Every constructor must have exactly one matching case.
    //   - Recursive calls in case bodies must use the destructured arg
    //     of the case as their first argument (structural recursion).

    void elaboratePatternMatchDefinition(
        const SurfaceDefinitionDecl& declaration) {

        if (!declaration.arguments.empty()) {
            throw ElaborateError(
                "pattern-match definition '" + declaration.name
                + "' must declare its arguments in the type signature, "
                "not as binders before the colon");
        }

        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;

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
                argument.name = "_arg" + std::to_string(syntheticIndex++);
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

        // The first argument is the scrutinee. Require its type to be a
        // bare identifier referencing an inductive.
        const SurfaceArgument& scrutineeArgument = functionArguments[0];
        auto* scrutineeTypeIdentifier =
            std::get_if<SurfaceIdentifier>(&scrutineeArgument.type->node);
        if (!scrutineeTypeIdentifier
            || !scrutineeTypeIdentifier->universeArgs.empty()) {
            throw ElaborateError(
                "pattern-match definition '" + declaration.name
                + "': first argument's type must be a bare inductive "
                "name with no parameters or universe arguments");
        }
        std::string inductiveName = scrutineeTypeIdentifier->qualifiedName;
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
        if (inductive->numParameters != 0) {
            throw ElaborateError(
                "pattern matching on parameterised inductives is not "
                "supported in v1 (inductive '" + inductiveName
                + "' has " + std::to_string(inductive->numParameters)
                + " parameters; use a direct recursor call instead)");
        }

        // Elaborate the kernel types for each function argument, and
        // the kernel return type. We need these for both type signature
        // and motive construction.
        std::vector<std::string> binderStack;
        std::vector<ExpressionPointer> argumentKernelTypes;
        for (const auto& argument : functionArguments) {
            argumentKernelTypes.push_back(
                elaborateExpression(*argument.type, binderStack));
            binderStack.push_back(argument.name);
        }
        ExpressionPointer returnKernelType =
            elaborateExpression(*returnType, binderStack);

        // Build the full type as a Pi chain.
        ExpressionPointer fullType = returnKernelType;
        for (int i = static_cast<int>(functionArguments.size()) - 1;
             i >= 0; --i) {
            fullType = makePi(functionArguments[i].name,
                              argumentKernelTypes[i],
                              std::move(fullType));
        }

        // Build the motive in the kernel. The motive is a lambda over
        // the scrutinee, with body = Pi over the remaining args ending
        // in the return type. The return type may reference any of the
        // function's arguments, so we elaborate it with the full binder
        // stack [scrutinee, otherArg1, ..., otherArgN] in scope and
        // then wrap with Pis for the non-scrutinee args.
        ExpressionPointer motive;
        {
            std::vector<std::string> motiveStack;
            motiveStack.push_back(scrutineeArgument.name);
            std::vector<ExpressionPointer> otherArgKernelTypes;
            for (size_t i = 1; i < functionArguments.size(); ++i) {
                otherArgKernelTypes.push_back(
                    elaborateExpression(*functionArguments[i].type,
                                         motiveStack));
                motiveStack.push_back(functionArguments[i].name);
            }
            ExpressionPointer motiveCodomain =
                elaborateExpression(*returnType, motiveStack);
            for (int i =
                     static_cast<int>(otherArgKernelTypes.size()) - 1;
                 i >= 0; --i) {
                motiveCodomain = makePi(functionArguments[i + 1].name,
                                         otherArgKernelTypes[i],
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
        std::vector<ExpressionPointer> caseLambdas;
        for (const auto& constructorName : inductive->constructorNames) {
            caseLambdas.push_back(
                buildCaseLambda(declaration, constructorName,
                                inductiveName, motive,
                                functionArgumentPairs));
        }

        // Build the recursor call.
        //   Inductive_recursor.{motiveLevel}(motive, case_1, ..., case_n,
        //                                      scrutinee)(otherArgs...)
        // The function's body is a lambda over all arguments wrapping
        // the recursor application.
        ExpressionPointer recursorReference =
            makeConstant(inductiveName + "_recursor",
                          {motiveLevel});
        ExpressionPointer applied = makeApplication(
            std::move(recursorReference), motive);
        for (auto& caseLambda : caseLambdas) {
            applied = makeApplication(std::move(applied),
                                       std::move(caseLambda));
        }
        // The scrutinee. The function's args are bound (from innermost
        // outermost) at depths n-1, n-2, ..., 0 inside the body lambda.
        // The scrutinee is the FIRST function arg, so its de Bruijn
        // index when we're inside ALL function arg binders is
        // (n - 1) — counting from innermost outward.
        int argumentCount = static_cast<int>(functionArguments.size());
        applied = makeApplication(std::move(applied),
                                   makeBoundVariable(argumentCount - 1));
        // Then apply to all the other args (in declaration order, from
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
                      declaration.universeParameters,
                      std::move(fullType), std::move(fullBody));

        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
    }

    struct FunctionArgumentPair {
        std::string name;
        SurfaceExpressionPointer surfaceType;
    };

    // Builds the kernel Lambda for one case of a pattern-match definition.
    ExpressionPointer buildCaseLambda(
        const SurfaceDefinitionDecl& declaration,
        const std::string& constructorName,
        const std::string& inductiveName,
        ExpressionPointer motive,
        const std::vector<FunctionArgumentPair>& functionArgumentTypes) {

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
        // Decompose constructor type into per-arg Pis. For a non-
        // parameterised inductive, the constructor's type is exactly
        // a Pi chain over its arguments ending in the inductive type.
        struct ConstructorArgument {
            std::string defaultName;
            ExpressionPointer type;
            bool isRecursive;
        };
        std::vector<ConstructorArgument> constructorArguments;
        {
            ExpressionPointer cursor = constructor->type;
            while (auto* pi = std::get_if<Pi>(&cursor->node)) {
                ConstructorArgument constructorArgument;
                constructorArgument.defaultName = pi->displayHint;
                constructorArgument.type = pi->domain;
                auto* constant = std::get_if<Constant>(&pi->domain->node);
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
        //   For each constructor arg i:
        //     - destructuredNames[i] : constructorArguments[i].type
        //     - if recursive, a hypothesis  "_rec_<name>"  of type motive(arg_i)
        //   Then the remaining function args (in order), using names
        //   from matchedCase->patterns[1..n-1] (must be bare-name patterns).
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
            // previously-bound constructor args. We must shift the type
            // by (binderDepth - i) to account for our current binder count
            // — i is the number of OTHER ctor args already in the lambda
            // binder list (each ctor arg adds 1, each rec hyp adds 1).
            // For a non-recursive ctor like zero, this loop runs zero
            // times. For successor, just one ctor arg (and its rec hyp).
            // Within one constructor, the kernel-emitted types reference
            // earlier ctor args via Bound(i - 1 - j). After shifting by
            // (binderDepth - i), the types match our actual lambda depth.
            ExpressionPointer ctorArgType =
                shift(constructorArgument.type, binderDepth - static_cast<int>(i));
            lambdaBinders.push_back({destructuredName, ctorArgType});
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
                // the constructor arg we just added (destructuredName).
                std::string hypothesisName = "_rec_" + destructuredName;
                lambdaBinders.push_back({hypothesisName,
                                          recursionHypothesisType});
                recursiveArgToHypothesis[destructuredName] = hypothesisName;
                binderDepth++;
            }
        }

        // Add the function's other args (patterns[1..n-1]).
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
            std::vector<std::string> stack;
            for (const auto& binder : lambdaBinders) stack.push_back(binder.name);
            ExpressionPointer argType =
                elaborateExpression(*surfaceArgType, stack);
            lambdaBinders.push_back({bareName->name, argType});
            binderDepth++;
        }

        // Translate the body: rewrite recursive calls.
        SurfaceExpressionPointer rewrittenBody = rewriteRecursiveCalls(
            matchedCase->body, declaration.name, recursiveArgToHypothesis);

        // Elaborate the body with all binders in scope.
        std::vector<std::string> bodyStack;
        for (const auto& binder : lambdaBinders) {
            bodyStack.push_back(binder.name);
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
        // Atomic forms (identifier, numeric literal, Type, Prop) are
        // unchanged.
        return expression;
    }

    void elaborateInductive(const SurfaceInductiveDecl& declaration) {
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;

        // Build the kind: parameter Pis wrapped around the surface kind.
        std::vector<std::string> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            parameterBinders;
        for (const auto& binder : declaration.parameters) {
            ExpressionPointer parameterType =
                elaborateExpression(*binder.type, localBinders);
            for (const auto& name : binder.names) {
                parameterBinders.push_back({name, parameterType});
                localBinders.push_back(name);
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
        // inductive being declared and the parameters. We elaborate in
        // the parameter-extended context, then wrap with parameter Pis.
        std::vector<ConstructorSpec> kernelConstructors;
        for (const auto& constructorSpec : declaration.constructors) {
            // Re-establish localBinders for parameters.
            std::vector<std::string> ctorLocalBinders;
            std::vector<std::pair<std::string, ExpressionPointer>>
                ctorParameterBinders;
            for (const auto& binder : declaration.parameters) {
                ExpressionPointer parameterType =
                    elaborateExpression(*binder.type, ctorLocalBinders);
                for (const auto& name : binder.names) {
                    ctorParameterBinders.push_back({name, parameterType});
                    ctorLocalBinders.push_back(name);
                    if (&name != &binder.names.back()) {
                        parameterType = elaborateExpression(
                            *binder.type, ctorLocalBinders);
                    }
                }
            }
            ExpressionPointer constructorBody =
                elaborateExpression(*constructorSpec.type, ctorLocalBinders);
            ExpressionPointer fullConstructorType = constructorBody;
            for (auto iterator = ctorParameterBinders.rbegin();
                 iterator != ctorParameterBinders.rend(); ++iterator) {
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
                     declaration.universeParameters,
                     fullKind, numParameters,
                     std::move(kernelConstructors));

        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
    }

    // -------- expression elaboration --------

    ExpressionPointer elaborateExpression(
        const SurfaceExpression& expression,
        const std::vector<std::string>& localBinders) {

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
            std::vector<std::string> extended = localBinders;
            extended.push_back(let->name);
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
        if (std::get_if<SurfaceProp>(&expression.node)) {
            return makeProp();
        }
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            throw ElaborateError(
                "operator '" + binary->opSymbol + "' is not yet supported "
                "by the elaborator; use the explicit function call form "
                "(e.g. Natural.add(a, b) instead of a + b)");
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
        const std::vector<std::string>& localBinders,
        int line, int column) {

        for (int i = static_cast<int>(localBinders.size()) - 1; i >= 0; --i) {
            if (localBinders[i] == identifier.qualifiedName) {
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
        const std::vector<std::string>& localBinders) {
        if (piType.binder.names.empty()) {
            // Anonymous: T → U.
            ExpressionPointer domain =
                elaborateExpression(*piType.binder.type, localBinders);
            std::vector<std::string> extended = localBinders;
            extended.push_back("_");
            ExpressionPointer codomain =
                elaborateExpression(*piType.codomain, extended);
            return makePi("_", std::move(domain), std::move(codomain));
        }
        // Multi-name binder: (x y z : T) → U becomes a chain of Pis.
        std::vector<std::string> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (const auto& name : piType.binder.names) {
            domainsPerName.push_back(
                elaborateExpression(*piType.binder.type, extended));
            extended.push_back(name);
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
        const std::vector<std::string>& localBinders) {
        if (lambda.binder.names.empty()) {
            throw ElaborateError("lambda binder must have at least one name");
        }
        std::vector<std::string> extended = localBinders;
        std::vector<ExpressionPointer> domainsPerName;
        for (const auto& name : lambda.binder.names) {
            domainsPerName.push_back(
                elaborateExpression(*lambda.binder.type, extended));
            extended.push_back(name);
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
                base = makeLevelSucc(std::move(base));
            }
            return base;
        }
        throw ElaborateError("unhandled level variant");
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

    Environment& environment_;
    std::vector<std::string>& importedModules_;
    std::string moduleName_;
    std::string currentDeclarationName_;
    // Ordered list of universe parameters of the current declaration —
    // ordered so we can auto-fill universe arguments at self-reference
    // sites (the user writes `Equality(A, x, x)` inside reflexivity's
    // constructor type; we elaborate it as `Equality.{u}(A, x, x)`).
    std::vector<std::string> currentUniverseParametersOrdered_;
    std::set<std::string> currentUniverseParameters_;
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
