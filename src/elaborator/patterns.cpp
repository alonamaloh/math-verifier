// Out-of-line Elaborator method definitions: pattern-matching definitions (case lambdas, recursive-call rewriting) + inductive types
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

namespace {

// The spelling of a constructor in ARM GOALS. The raw Natural
// constructors live in the `Natural.Raw` namespace, but consumers (and
// the whole lemma library) spell their transparent alias-typed wrappers
// `zero`/`successor` (PLAN_NATURAL_SEALING). Instantiating a case
// motive with the wrapper keeps arm goals structurally aligned with
// those spellings; the kernel accepts the recursor application either
// way because the wrapper δ-reduces to the constructor.
const std::string& publicConstructorSpelling(const std::string& name) {
    static const std::string zeroWrapper = "zero";
    static const std::string successorWrapper = "successor";
    if (name == "Natural.Raw.zero") return zeroWrapper;
    if (name == "Natural.Raw.successor") return successorWrapper;
    return name;
}

// The same public preference for a destructured BINDER's type: a
// constructor argument declared at the raw type binds at the public
// alias (defeq through the transparent alias), so every carrier-keyed
// reader downstream — operator dispatch, calc relation registries,
// certificate tiers — sees `Natural`, exactly as consumers spell it.
ExpressionPointer publicTypeSpelling(ExpressionPointer type) {
    if (auto* constant = std::get_if<Constant>(&type->node)) {
        if (constant->name == "Natural.Raw"
            && constant->universeArguments.empty()) {
            return makeConstant("Natural");
        }
    }
    return type;
}

} // namespace

std::optional<Elaborator::BoundaryRecursion>
Elaborator::resolveBoundaryRecursion(
        const ExpressionPointer& scrutineeType) const {
        auto* aliasConstant = std::get_if<Constant>(&scrutineeType->node);
        if (!aliasConstant || !aliasConstant->universeArguments.empty()) {
            return std::nullopt;
        }
        const Declaration* aliasLookup =
            environment_.lookup(aliasConstant->name);
        if (!aliasLookup) return std::nullopt;
        auto* aliasDefinition = std::get_if<Definition>(aliasLookup);
        if (!aliasDefinition
            || !aliasDefinition->universeParameters.empty()) {
            return std::nullopt;
        }
        std::string combinatorName = aliasConstant->name + ".recursion";
        const Declaration* combinatorLookup =
            environment_.lookup(combinatorName);
        if (!combinatorLookup
            || !std::get_if<Definition>(combinatorLookup)) {
            return std::nullopt;
        }
        auto* bodyConstant =
            std::get_if<Constant>(&aliasDefinition->body->node);
        if (!bodyConstant) return std::nullopt;
        const Declaration* inductiveLookup =
            environment_.lookup(bodyConstant->name);
        if (!inductiveLookup) return std::nullopt;
        auto* inductive = std::get_if<Inductive>(inductiveLookup);
        if (!inductive || inductive->numParameters != 0
            || !std::get_if<Sort>(&inductive->kind->node)) {
            return std::nullopt;
        }
        BoundaryRecursion result;
        result.combinatorName = std::move(combinatorName);
        result.inductiveName = bodyConstant->name;
        result.aliasName = aliasConstant->name;
        std::string propositionCombinatorName =
            aliasConstant->name + ".induction_on_successor";
        const Declaration* propositionLookup =
            environment_.lookup(propositionCombinatorName);
        if (propositionLookup
            && std::get_if<Definition>(propositionLookup)) {
            result.propositionCombinatorName =
                std::move(propositionCombinatorName);
        }
        result.aliasIsOpaque =
            aliasDefinition->opacity == Opacity::Opaque;
        return result;
    }

LevelPointer Elaborator::boundaryRecursionUniverse(
        const LevelPointer& motiveLevel) {
        if (auto* constant = std::get_if<LevelConst>(&motiveLevel->node)) {
            if (constant->value >= 1) {
                return makeLevelConst(constant->value - 1);
            }
            return nullptr;
        }
        if (auto* successor =
                std::get_if<LevelSuccessor>(&motiveLevel->node)) {
            return successor->base;
        }
        return nullptr;
    }

void Elaborator::elaboratePatternMatchDefinition(
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
        // Boundary route (PLAN_NATURAL_SEALING Stage 4): a scrutinee
        // spelled at a sealed-inductive alias with a `.recursion`
        // combinator in scope compiles onto the combinator, never the
        // raw recursor. Resolved on the SYNTACTIC head so the routing
        // is identical whether the alias is still transparent or
        // already sealed.
        std::optional<BoundaryRecursion> boundaryRecursion =
            resolveBoundaryRecursion(argumentKernelTypes[0]);
        if (boundaryRecursion) {
            inductiveName = boundaryRecursion->inductiveName;
        } else {
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
        // Arm goals and destructured binders keep the scrutinee's own
        // spelling: public wrappers for an alias-spelled scrutinee, raw
        // constructors for a raw-floor definition over the inductive
        // itself.
        bool spellPublicly =
            headConstantName(argumentKernelTypes[0]) != inductiveName;
        for (const auto& constructorName : inductive->constructorNames) {
            caseLambdas.push_back(
                buildCaseLambda(declaration, constructorName,
                                inductiveName,
                                inductiveUniverseArguments, motive,
                                parameterValues,
                                outerBinderStack,
                                /*injectedInductionHypothesisName=*/"",
                                spellPublicly));
        }

        // Build the eliminator call — the boundary combinator when the
        // scrutinee is spelled at a sealed-inductive alias (its motive
        // lives at `Type(u)`, so u = motiveLevel - 1), the raw recursor
        // otherwise. The recursor's universe arguments are the
        // inductive's universe arguments preceded (for large-eliminating
        // recursors) by the motive's universe level. For restricted-
        // elimination recursors (Proposition inductives that aren't
        // singletons), the motive is forced to Proposition and the
        // recursor takes no extra universe argument.
        ExpressionPointer recursorReference;
        if (boundaryRecursion) {
            LevelPointer combinatorUniverse =
                boundaryRecursionUniverse(motiveLevel);
            auto* motiveLevelConstant =
                std::get_if<LevelConst>(&motiveLevel->node);
            bool motiveIsProposition =
                motiveLevelConstant && motiveLevelConstant->value == 0;
            if (combinatorUniverse) {
                recursorReference = makeConstant(
                    boundaryRecursion->combinatorName,
                    {std::move(combinatorUniverse)});
            } else if (motiveIsProposition
                       && !boundaryRecursion->propositionCombinatorName
                               .empty()) {
                // A Proposition-valued match rides the Prop-level twin
                // (`induction_on_successor`), whose argument layout
                // matches the recursor's exactly.
                recursorReference = makeConstant(
                    boundaryRecursion->propositionCombinatorName);
            } else if (boundaryRecursion->aliasIsOpaque) {
                throw ElaborateError(
                    "pattern-match definition '" + declaration.name
                    + "': the scrutinee type '"
                    + boundaryRecursion->aliasName
                    + "' is sealed and the result does not land in a "
                    "Type universe the boundary combinator '"
                    + boundaryRecursion->combinatorName
                    + "' can produce (a Proposition-valued match cannot "
                    "ride it) — restate the definition as a theorem by "
                    "induction, or move it to the raw floor (`unfold "
                    + boundaryRecursion->aliasName + " in …`)");
            }
            // A Proposition-level motive over a still-transparent alias
            // falls through to the raw recursor below.
        }
        if (!recursorReference) {
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
            // The motive level leads the recursor's universe arguments
            // (Lean's convention, mirrored by addInductive).
            std::vector<LevelPointer> recursorUniverseArguments;
            if (recursorHasMotiveLevel) {
                recursorUniverseArguments.push_back(motiveLevel);
            }
            recursorUniverseArguments.insert(
                recursorUniverseArguments.end(),
                inductiveUniverseArguments.begin(),
                inductiveUniverseArguments.end());
            recursorReference =
                makeConstant(std::move(recursorName),
                              std::move(recursorUniverseArguments));
        }
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

ExpressionPointer Elaborator::buildCaseLambda(
        const SurfaceDefinitionDeclaration& declaration,
        const std::string& constructorName,
        const std::string& inductiveName,
        const std::vector<LevelPointer>& inductiveUniverseArguments,
        ExpressionPointer motive,
        const std::vector<ExpressionPointer>& parameterValues,
        const std::vector<LocalBinder>& outerBinderStack,
        const std::string& injectedInductionHypothesisName,
        bool spellPublicly) {

        Frame frame(*this,
            "case for '" + constructorName + "' of '"
            + inductiveName + "'");

        // Find the case in the declaration matching this constructor.
        // A pattern label matches on the constructor's full name or on
        // its last component (`| successor(k)` matches the qualified
        // constructor `Natural.Raw.successor` — patterns keep the
        // historical bare spelling while the constructor lives in the
        // raw namespace, PLAN_NATURAL_SEALING).
        const std::string constructorLastComponent =
            constructorName.substr(constructorName.rfind('.') + 1);
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
            if (seenName == constructorName
                || seenName == constructorLastComponent) {
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
                        "nested patterns are not supported");
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
        // Instantiate the constructor type at THIS scrutinee's universe
        // arguments before reading off its argument types. Only the
        // parameter VALUES are substituted below (via β on the parameter
        // Pis); the universe PARAMETERS must be substituted here, or a
        // field type that mentions the inductive keeps the raw universe
        // parameter (`Accessible.{u}` instead of `Accessible.{0}`). A direct
        // recursive field's binder incidentally reconciles that against the
        // recursor's minor premise, but a HIGHER-ORDER field's occurrence is
        // buried under its own Pi telescope and stays `.{u}`, so the
        // assembled recursor fails to typecheck. No-op for a non-polymorphic
        // inductive (empty parameter list).
        ExpressionPointer constructorType = constructor->type;
        if (!constructor->universeParameters.empty()
            && constructor->universeParameters.size()
                   == inductiveUniverseArguments.size()) {
            constructorType = substituteUniverseLevels(
                constructor->type, constructor->universeParameters,
                inductiveUniverseArguments);
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
            ExpressionPointer originalCursor = constructorType;
            for (size_t p = 0; p < parameterValues.size(); ++p) {
                auto* pi =
                    std::get_if<Pi>(&originalCursor->node);
                if (!pi) break;
                originalCursor = pi->codomain;
            }
            while (auto* pi =
                       std::get_if<Pi>(&originalCursor->node)) {
                // Peel any leading Pi telescope: a HIGHER-ORDER recursive
                // field (Accessible's `below`) sits under binders (strictly
                // positive, so those domains don't mention the inductive)
                // before the recursive occurrence. A direct recursive field
                // has an empty telescope. Then peel the base's application
                // chain to reach its head.
                ExpressionPointer typeHead = pi->domain;
                while (auto* telescopePi =
                           std::get_if<Pi>(&typeHead->node)) {
                    typeHead = telescopePi->codomain;
                }
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
            ExpressionPointer cursor = constructorType;
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
        // `by induction … with IH` makes the parser append the IH name to
        // every case pattern. A non-recursive constructor has no IH slot to
        // absorb it, so that trailing name is spurious — drop it. (A
        // recursive constructor keeps it; it names that case's hypothesis.)
        if (!injectedInductionHypothesisName.empty()
            && recursiveCount == 0
            && destructuredNames.size() == constructorArguments.size() + 1
            && destructuredNames.back() == injectedInductionHypothesisName) {
            destructuredNames.pop_back();
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

        // The case lambda's binders, in the recursor's minor-premise
        // order (Lean's layout, mirrored by the kernel's buildCaseType):
        //   - all constructor value arguments first,
        //     destructuredNames[i] : constructorArguments[i].type;
        //   - then one induction hypothesis per recursive argument, in
        //     argument order, "_inductionHypothesisFor_<name>" of type
        //     motive(<indices>, argument_i);
        //   Then the remaining function arguments (in order), using
        //   names from matchedCase->patterns[1..n-1] (must be
        //   bare-name patterns).
        std::vector<LocalBinder> lambdaBinders;
        std::map<std::string, std::string> recursiveArgToHypothesis;
        // Position of each destructured constructor argument inside
        // lambdaBinders (with the value arguments bound contiguously
        // these are 0,1,2,…; kept as a list for the consumers below).
        std::vector<size_t> destructuredArgumentPositions;
        for (size_t i = 0; i < constructorArguments.size(); ++i) {
            // Within one constructor, the kernel-emitted types reference
            // earlier constructor arguments via Bound(i - 1 - j); the
            // value arguments are bound contiguously, so the lambda
            // depth already matches — no shift.
            destructuredArgumentPositions.push_back(lambdaBinders.size());
            // Beta-reduce the argument type, mirroring the motive and
            // recursion-hypothesis treatments below: destructuring an
            // existential whose predicate was INSTANTIATED from a
            // definition (`choose … from sumNonneg(ε, εPositive)` where
            // the source's type unfolds to `∃ N. … f(m) …` with f a
            // lambda) leaves `(λ …)(…)` redexes inside the hypothesis
            // binder's type, and the arm body's structural matchers
            // (order steps, premise instantiation) match on the binder
            // type as written. Beta only — no δ, so declared aliases
            // survive.
            ExpressionPointer valueArgumentType = spellPublicly
                ? publicTypeSpelling(constructorArguments[i].type)
                : constructorArguments[i].type;
            lambdaBinders.push_back(
                {destructuredNames[i],
                 deepBetaReduce(valueArgumentType)});
        }
        for (size_t i = 0; i < constructorArguments.size(); ++i) {
            const auto& constructorArgument = constructorArguments[i];
            if (!constructorArgument.isRecursive) continue;
            const std::string& destructuredName = destructuredNames[i];
            // Recursive hypothesis: type = motive(<indices>,
            // <the destructured argument>). For non-indexed inductives
            // the index list is empty and the motive takes a single
            // argument (the scrutinee). For indexed ones (e.g.
            // LessOrEqual.step's recursive proof argument has type
            // LessOrEqual(smaller, larger)), we must extract those
            // indices from the value-arg's type and feed them to
            // the motive in order.
            int binderDepth = static_cast<int>(lambdaBinders.size());
            // View the field type from the current binder depth (it was
            // written at depth i).
            ExpressionPointer fieldType = shift(
                constructorArgument.type,
                binderDepth - static_cast<int>(i));
            // Peel the field's leading Pi telescope — empty for a direct
            // recursive arg, `(y : A) → r(y, x) →` for a higher-order one
            // (Accessible's `below`). Each domain is captured in its own
            // deepening scope, matching the kernel's buildCaseType.
            std::vector<ExpressionPointer> telescopeDomains;
            ExpressionPointer recursiveBase = fieldType;
            while (auto* telescopePi =
                       std::get_if<Pi>(&recursiveBase->node)) {
                telescopeDomains.push_back(telescopePi->domain);
                recursiveBase = telescopePi->codomain;
            }
            int telescopeSize = static_cast<int>(telescopeDomains.size());
            // `recursiveBase` is `Inductive params indices` in scope
            // (binderDepth + telescopeSize); read off its indices.
            std::vector<ExpressionPointer> recursiveTypeArguments;
            {
                ExpressionPointer typeCursor = recursiveBase;
                while (auto* application =
                           std::get_if<Application>(&typeCursor->node)) {
                    recursiveTypeArguments.insert(
                        recursiveTypeArguments.begin(),
                        application->argument);
                    typeCursor = application->function;
                }
            }
            // IH codomain, in scope (binderDepth + telescopeSize):
            //   motive(indices…) (field applied to the telescope binders).
            ExpressionPointer recursionHypothesisType =
                shift(motive, binderDepth + telescopeSize);
            for (size_t k = parameterValues.size();
                 k < recursiveTypeArguments.size(); ++k) {
                recursionHypothesisType = makeApplication(
                    recursionHypothesisType,
                    recursiveTypeArguments[k]);
            }
            ExpressionPointer fieldApplied = makeBoundVariable(
                binderDepth + telescopeSize - 1 - static_cast<int>(i));
            for (int t = 0; t < telescopeSize; ++t) {
                fieldApplied = makeApplication(
                    fieldApplied,
                    makeBoundVariable(telescopeSize - 1 - t));
            }
            recursionHypothesisType = makeApplication(
                recursionHypothesisType, fieldApplied);
            // Beta-reduce the motive application so the hypothesis
            // binder carries the DECLARED result type (e.g. the
            // alias `ComplexNumber`), not a stuck
            // `(λ …)(…)` redex — operator dispatch and implicit
            // inference in the arm body match on the binder type
            // as written. Beta only: a weak-head normalisation
            // would also δ-unfold the alias to its underlying
            // quotient and lose the dispatch.
            recursionHypothesisType =
                deepBetaReduce(recursionHypothesisType);
            // Re-abstract the telescope: `Π telescope. motive indices
            // (field telescope)`. Innermost domain wraps first.
            for (int t = telescopeSize - 1; t >= 0; --t) {
                recursionHypothesisType = makePi(
                    "recursivePredecessor", telescopeDomains[t],
                    recursionHypothesisType);
            }
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
            // them to body coordinates — the value args sit
            // contiguously at the bottom of lambdaBinders (the
            // induction hypotheses all come after them), so this
            // shift is exact.
            for (const auto& indexValue : constructorIndexValuesRaw) {
                motiveAtCase = makeApplication(
                    motiveAtCase,
                    shift(indexValue,
                           totalBinderDepth
                           - constructorValueArgCount));
            }
            // Apply to the constructor application of (params,
            // destructured-values) — spelled publicly (see
            // publicConstructorSpelling) so arm goals match the
            // library's spellings; raw-floor splits over the raw
            // inductive itself keep the constructor spelling.
            ExpressionPointer constructorApplication =
                makeConstant(spellPublicly
                                 ? publicConstructorSpelling(constructorName)
                                 : constructorName,
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
            // Beta-reduce the motive application WITHOUT delta-unfolding
            // the result head: a declared return type like `ComplexNumber`
            // must survive as the alias (operator dispatch and implicit
            // inference in the arm body match on it), not as the
            // underlying `Quotient(…)` a weak-head normalisation would
            // expose.
            motiveAtCase = deepBetaReduce(motiveAtCase);
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
                // Footgun guard: a bare name in a non-scrutinee pattern
                // slot binds a NEW variable — it does NOT match a
                // constructor. When that name IS a constructor of the
                // slot's type (`| successor(i), zero => …` with `zero`
                // shadowing Natural.zero), every downstream failure is
                // baffling ("expected X / got X" with byte-identical
                // printouts, the binder vs the constructor). Reject it
                // by name here.
                if (!positionName.empty() && positionName[0] != '_') {
                    std::string slotHead = headConstantName(pi->domain);
                    const Declaration* slotDeclaration = slotHead.empty()
                        ? nullptr : environment_.lookup(slotHead);
                    const Inductive* slotInductive = slotDeclaration
                        ? std::get_if<Inductive>(slotDeclaration)
                        : nullptr;
                    // The slot type may be spelled at an alias over the
                    // inductive (`Natural` over `Natural.Raw`) — resolve
                    // through it so the guard still sees the
                    // constructors. WHNF handles a transparent alias;
                    // the body-peek loop handles a sealed (opaque) one,
                    // where the footgun is just as baffling.
                    if (!slotInductive && slotDeclaration
                        && std::get_if<Definition>(slotDeclaration)) {
                        std::string reducedHead = headConstantName(
                            weakHeadNormalForm(environment_, pi->domain));
                        const Declaration* reducedDeclaration =
                            reducedHead.empty()
                                ? nullptr
                                : environment_.lookup(reducedHead);
                        slotInductive = reducedDeclaration
                            ? std::get_if<Inductive>(reducedDeclaration)
                            : nullptr;
                        if (slotInductive) slotHead = reducedHead;
                    }
                    if (!slotInductive && slotDeclaration
                        && std::get_if<Definition>(slotDeclaration)) {
                        std::string aliasCursor = slotHead;
                        for (int guard = 0; guard < 8; ++guard) {
                            const Declaration* cursorLookup =
                                environment_.lookup(aliasCursor);
                            auto* cursorDefinition = cursorLookup
                                ? std::get_if<Definition>(cursorLookup)
                                : nullptr;
                            if (!cursorDefinition) break;
                            std::string bodyHead = headConstantName(
                                cursorDefinition->body);
                            if (bodyHead.empty()
                                || bodyHead == aliasCursor) {
                                break;
                            }
                            aliasCursor = bodyHead;
                        }
                        const Declaration* peekedDeclaration =
                            environment_.lookup(aliasCursor);
                        slotInductive = peekedDeclaration
                            ? std::get_if<Inductive>(peekedDeclaration)
                            : nullptr;
                        if (slotInductive) slotHead = aliasCursor;
                    }
                    if (slotInductive) {
                        for (const std::string& ctor :
                             slotInductive->constructorNames) {
                            std::string lastComponent =
                                ctor.substr(ctor.rfind('.') + 1);
                            if (positionName == ctor
                                || positionName == lastComponent) {
                                throw ElaborateError(
                                    "pattern variable `" + positionName
                                    + "` at position "
                                    + std::to_string(i + 1)
                                    + " shadows constructor `" + ctor
                                    + "` of `" + slotHead
                                    + "` — a bare name in a non-first "
                                      "pattern slot binds a NEW variable, "
                                      "it does not match the constructor. "
                                      "Rename the binder, or move the "
                                      "constructor pattern to the first "
                                      "(scrutinee) position (e.g. via a "
                                      "helper that recurses on this "
                                      "argument).");
                            }
                        }
                    }
                }
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
                // The elaborator just found this mismatch itself, so it
                // owns the message — report it as mathematics rather than
                // laundering it through rethrowKernelError's "kernel: "
                // path (WS1). The OPENED types render with named
                // FreeVariables, not `<bound N>` indices.
                throwElaborate(
                    "this case's result has the wrong type for the "
                    "function's declared return type\n"
                    "    expected:            "
                    + prettyPrintForDisplay(expectedOpened) + "\n"
                    "    but this case gives: "
                    + prettyPrintForDisplay(bodyTypeOpened));
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

ExpressionPointer Elaborator::buildBodyForCase(
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

        // Resolve the inner inductive and verify the supported-shape
        // restrictions.
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
            // extras would be index values; indexed inner inductives
            // are not supported.
            throw ElaborateError(
                "inner constructor pattern at position "
                + std::to_string(nextCtorPos) + ": inductive '"
                + innerInductiveName
                + "' is indexed; inner constructor patterns support "
                "only non-indexed inductives");
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
                + " constructors; inner constructor patterns are "
                "supported only on single-constructor inductives");
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
                                + "' is recursive; inner constructor "
                                "patterns are supported only on "
                                "non-recursive constructors");
                        }
                    }
                    originalCursor = originalPi->codomain;
                }
                ctorArgTypes.push_back(publicTypeSpelling(pi->domain));
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
        // The motive level leads the recursor's universe arguments
        // (Lean's convention, mirrored by addInductive).
        std::vector<LevelPointer> recursorUniverseArguments;
        if (recursorHasMotiveLevel) {
            recursorUniverseArguments.push_back(motiveLevel);
        }
        recursorUniverseArguments.insert(
            recursorUniverseArguments.end(),
            indConstant->universeArguments.begin(),
            indConstant->universeArguments.end());

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
            publicConstructorSpelling(expectedCtorName),
            indConstant->universeArguments);
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

SurfaceExpressionPointer Elaborator::rewriteRecursiveCalls(
        SurfaceExpressionPointer expression,
        const std::string& thisDeclName,
        const std::map<std::string, std::string>&
            recursiveArgToHypothesis,
        int outerBinderCount) {

        // Optional sub-expressions reach this pass as a null pointer — a
        // by-less calc step's `stepProof`, an omitted `let`/lambda/Pi/
        // ascription type annotation, and so on. There is nothing to rewrite,
        // so hand the null straight back. Without this guard the `*expression`
        // below binds a reference to a null pointer (and then reads `node.node`
        // off a near-null address) — undefined behavior that different
        // toolchains compile into different results.
        if (!expression) return expression;
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
        if (auto* ellipsis = std::get_if<SurfaceEllipsisFold>(&node.node)) {
            std::vector<SurfaceExpressionPointer> newPrefix;
            for (const auto& term : ellipsis->prefixTerms) {
                newPrefix.push_back(
                    rewriteRecursiveCalls(term, thisDeclName,
                                           recursiveArgToHypothesis,
                                           outerBinderCount));
            }
            return makeSurfaceEllipsisFold(
                ellipsis->operatorSymbol, std::move(newPrefix),
                rewriteRecursiveCalls(ellipsis->generalTerm, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* foldBinder = std::get_if<SurfaceFoldBinder>(&node.node)) {
            return makeSurfaceFoldBinder(
                foldBinder->operatorSymbol, foldBinder->binderName,
                rewriteRecursiveCalls(foldBinder->lowerBound, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(foldBinder->upperBound, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(foldBinder->body, thisDeclName,
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
                                         node.line, node.column,
                                         cases->inductionHypothesisName,
                                         cases->isInductionBlock,
                                         cases->userWritten);
            }
            return makeSurfaceCasesWithRefining(
                std::move(rewrittenScrutinee),
                std::move(rewrittenClauses),
                cases->equalityHypothesisName,
                cases->refiningNames,
                node.line, node.column,
                cases->inductionHypothesisName,
                cases->isInductionBlock,
                cases->userWritten);
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
                // Full copy first: structural flags (`isOtherwise`,
                // witness binders) must survive the rewrite — see the
                // matching clone in substituteSurfaceName.
                SurfaceStructuredClaimArm rewrittenArm = arm;
                rewrittenArm.disjunctType = arm.disjunctType
                    ? rewriteRecursiveCalls(arm.disjunctType,
                                             thisDeclName,
                                             recursiveArgToHypothesis,
                                             outerBinderCount)
                    : nullptr;
                rewrittenArm.body = arm.body
                    ? rewriteRecursiveCalls(arm.body, thisDeclName,
                                             recursiveArgToHypothesis,
                                             outerBinderCount)
                    : nullptr;
                rewrittenArm.witnessBinders.clear();
                for (const auto& binder : arm.witnessBinders) {
                    SurfaceWitnessBinder rewrittenBinder = binder;
                    rewrittenBinder.type = binder.type
                        ? rewriteRecursiveCalls(binder.type, thisDeclName,
                                                 recursiveArgToHypothesis,
                                                 outerBinderCount)
                        : nullptr;
                    rewrittenArm.witnessBinders.push_back(
                        std::move(rewrittenBinder));
                }
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
                // Copy the whole step (relation, relationOperator, line,
                // column) and overwrite only the rewritten sub-expressions,
                // so a new SurfaceCalcStep field can't be silently dropped
                // by this pass.
                SurfaceCalcStep rewrittenStep = step;
                rewrittenStep.nextExpression = rewriteRecursiveCalls(
                    step.nextExpression, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount);
                rewrittenStep.stepProof = rewriteRecursiveCalls(
                    step.stepProof, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount);
                rewrittenSteps.push_back(std::move(rewrittenStep));
            }
            return makeSurfaceCalc(std::move(rewrittenInitial),
                                    std::move(rewrittenSteps),
                                    node.line, node.column);
        }
        if (auto* decide = std::get_if<SurfaceDecide>(&node.node)) {
            // A self-call inside a decision arm is the natural way to
            // write a classically-filtered recursion (e.g. List.filter
            // keeping `head` when `P(head)` holds) — without this case
            // it survives unrewritten and trips the kernel's
            // "undefined constant: <thisDeclName>".
            return makeSurfaceDecide(
                rewriteRecursiveCalls(decide->proposition, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                decide->yesBinderName,
                rewriteRecursiveCalls(decide->yesBody, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                decide->noBinderName,
                rewriteRecursiveCalls(decide->noBody, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* tuple = std::get_if<SurfaceAnonymousTuple>(&node.node)) {
            std::vector<SurfaceExpressionPointer> rewrittenComponents;
            for (const auto& component : tuple->components) {
                rewrittenComponents.push_back(rewriteRecursiveCalls(
                    component, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount));
            }
            return makeSurfaceAnonymousTuple(
                std::move(rewrittenComponents), node.line, node.column,
                tuple->userWritten);
        }
        if (auto* note = std::get_if<SurfaceNote>(&node.node)) {
            auto rewriteOrNull = [&](const SurfaceExpressionPointer& sub) {
                return sub ? rewriteRecursiveCalls(
                                 sub, thisDeclName,
                                 recursiveArgToHypothesis, outerBinderCount)
                           : nullptr;
            };
            return makeSurfaceNote(
                rewriteOrNull(note->goalType),
                rewriteOrNull(note->proposition),
                rewriteOrNull(note->body),
                node.line, node.column,
                note->changesGoal,
                rewriteOrNull(note->proof));
        }
        if (auto* choose = std::get_if<SurfaceChoose>(&node.node)) {
            return makeSurfaceChoose(
                choose->name,
                rewriteRecursiveCalls(choose->predicate, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(choose->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column,
                choose->conditionName,
                rewriteRecursiveCalls(choose->source, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                choose->additionalNames);
        }
        if (auto* strongInduction =
                std::get_if<SurfaceByStrongInduction>(&node.node)) {
            return makeSurfaceByStrongInduction(
                rewriteRecursiveCalls(strongInduction->scrutinee,
                                       thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                strongInduction->subjectName,
                strongInduction->ihName,
                rewriteRecursiveCalls(strongInduction->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* eventuallyScope =
                std::get_if<SurfaceEventuallyScope>(&node.node)) {
            return makeSurfaceEventuallyScope(
                eventuallyScope->binderName,
                rewriteRecursiveCalls(eventuallyScope->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* inductionUsing =
                std::get_if<SurfaceByInductionUsing>(&node.node)) {
            return makeSurfaceByInductionUsing(
                rewriteRecursiveCalls(inductionUsing->scrutinee,
                                       thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                rewriteRecursiveCalls(inductionUsing->inductionLemma,
                                       thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                inductionUsing->subjectName,
                inductionUsing->ihName,
                rewriteRecursiveCalls(inductionUsing->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* unfold = std::get_if<SurfaceUnfold>(&node.node)) {
            return makeSurfaceUnfold(
                unfold->names,
                rewriteRecursiveCalls(unfold->body, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* given = std::get_if<SurfaceGiven>(&node.node)) {
            return makeSurfaceGiven(
                rewriteRecursiveCalls(given->proposition, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* field = std::get_if<SurfaceField>(&node.node)) {
            std::vector<SurfaceExpressionPointer> rewrittenHypotheses;
            for (const auto& hypothesis : field->nonzeroHypotheses) {
                rewrittenHypotheses.push_back(rewriteRecursiveCalls(
                    hypothesis, thisDeclName,
                    recursiveArgToHypothesis, outerBinderCount));
            }
            return makeSurfaceField(
                std::move(rewrittenHypotheses), node.line, node.column);
        }
        if (auto* linearCombination =
                std::get_if<SurfaceLinearCombination>(&node.node)) {
            return makeSurfaceLinearCombination(
                rewriteRecursiveCalls(linearCombination->combination,
                                       thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        if (auto* blockTail = std::get_if<SurfaceBlockTail>(&node.node)) {
            // A recursive self-call sitting in the block's final
            // expression must be rewritten too, or it survives to the
            // kernel as "undefined constant: <thisDeclName>".
            return makeSurfaceBlockTail(
                rewriteRecursiveCalls(blockTail->expression, thisDeclName,
                                       recursiveArgToHypothesis,
                                       outerBinderCount),
                node.line, node.column);
        }
        // Atomic forms (identifier, numeric literal, Type, Proposition,
        // sorry, ring, goal, hole, cite-inferred) carry no rewritable
        // sub-expressions and are unchanged. NOTE if you add a surface
        // node with sub-expressions, it needs a case above — a silent
        // fall-through here leaves self-calls unrewritten and they die
        // at the kernel as "undefined constant: <the definition's name>".
        return expression;
    }

void Elaborator::elaborateInductive(const SurfaceInductiveDeclaration& declaration) {
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

        synthesizeCoverageLemma(declaration);
    }

void Elaborator::synthesizeCoverageLemma(
        const SurfaceInductiveDeclaration& declaration) {
        // Type-valued, non-indexed inductives with at least one
        // constructor only. (An indexed inductive's surface kind is a
        // Pi; Prop-valued ones don't get equation-shaped case splits.)
        if (!std::get_if<SurfaceType>(&declaration.kind->node)) return;
        if (declaration.constructors.empty()) return;
        // The logic vocabulary must be in scope at the declaration site
        // (the foundational files declare their inductives before Or /
        // Exists / Equality exist — those keep hand-written lemmas).
        for (const char* needed :
             {"Or", "Or.introduceLeft", "Or.introduceRight", "Exists",
              "Exists.introduce", "Equality", "reflexivity"}) {
            if (environment_.declarations.find(needed)
                    == environment_.declarations.end()) {
                return;
            }
        }

        int line = declaration.kind->line;
        int column = declaration.kind->column;
        auto identifier = [&](const std::string& name) {
            return makeSurfaceIdentifier(name, {}, line, column);
        };

        std::vector<std::string> parameterNames;
        for (const auto& binder : declaration.parameters) {
            if (binder.isImplicit) return;
            for (const auto& name : binder.names) {
                parameterNames.push_back(name);
            }
        }
        auto isTaken = [&](const std::string& name) {
            return std::find(parameterNames.begin(), parameterNames.end(),
                             name) != parameterNames.end();
        };
        std::string subjectName = "subject";
        while (isTaken(subjectName)) subjectName += "_";

        auto applyToParameters = [&](const std::string& head)
                -> SurfaceExpressionPointer {
            if (parameterNames.empty()) return identifier(head);
            std::vector<SurfaceExpressionPointer> arguments;
            for (const auto& name : parameterNames) {
                arguments.push_back(identifier(name));
            }
            return makeSurfaceApplication(identifier(head),
                                          std::move(arguments),
                                          line, column);
        };

        // Per constructor: the argument telescope (from the SURFACE
        // constructor type — value args only; parameter Pis are added
        // at elaboration), the ∃-wrapped equation disjunct, and the
        // cases-arm proof.
        struct ConstructorArgument {
            std::string name;
            SurfaceExpressionPointer type;
        };
        std::vector<SurfaceExpressionPointer> disjuncts;
        std::vector<SurfaceCasesClause> clauses;
        std::vector<SurfaceExpressionPointer> armProofs;
        for (const auto& constructorSpec : declaration.constructors) {
            std::vector<ConstructorArgument> constructorArguments;
            const SurfaceExpression* cursor = constructorSpec.type.get();
            int freshCounter = 0;
            while (auto* pi = std::get_if<SurfacePiType>(&cursor->node)) {
                if (pi->binder.isImplicit) return;
                if (!pi->binder.type) return;
                size_t nameCount = pi->binder.names.empty()
                    ? 1 : pi->binder.names.size();
                for (size_t i = 0; i < nameCount; ++i) {
                    std::string name = pi->binder.names.empty()
                        ? std::string() : pi->binder.names[i];
                    if (name.empty() || name == "_") {
                        name = "value" + std::to_string(++freshCounter);
                    }
                    while (isTaken(name) || name == subjectName) {
                        name += "_";
                    }
                    bool duplicate = false;
                    for (const auto& earlier : constructorArguments) {
                        if (earlier.name == name) { duplicate = true; break; }
                    }
                    if (duplicate) {
                        name += std::to_string(++freshCounter);
                    }
                    constructorArguments.push_back({name, pi->binder.type});
                }
                cursor = pi->codomain.get();
            }

            // subject = C(params…, args…), ∃-wrapped over the args.
            SurfaceExpressionPointer constructorApplication;
            {
                std::vector<SurfaceExpressionPointer> arguments;
                for (const auto& name : parameterNames) {
                    arguments.push_back(identifier(name));
                }
                for (const auto& argument : constructorArguments) {
                    arguments.push_back(identifier(argument.name));
                }
                constructorApplication = arguments.empty()
                    ? identifier(constructorSpec.name)
                    : makeSurfaceApplication(identifier(constructorSpec.name),
                                             std::move(arguments),
                                             line, column);
            }
            SurfaceExpressionPointer disjunct = makeSurfaceBinaryOperation(
                "=", identifier(subjectName), constructorApplication,
                line, column);
            for (auto it = constructorArguments.rbegin();
                 it != constructorArguments.rend(); ++it) {
                SurfaceBinder existsBinder{{it->name}, it->type};
                disjunct = makeSurfaceApplication(
                    identifier("Exists"),
                    std::vector<SurfaceExpressionPointer>{
                        it->type,
                        makeSurfaceLambda(std::move(existsBinder), disjunct,
                                          line, column)},
                    line, column);
            }
            disjuncts.push_back(std::move(disjunct));

            // Arm: | C(args…) => witness-chain(reflexivity(C(params…, args…)))
            SurfaceExpressionPointer proof = makeSurfaceApplication(
                identifier("reflexivity"),
                std::vector<SurfaceExpressionPointer>{constructorApplication},
                line, column);
            for (auto it = constructorArguments.rbegin();
                 it != constructorArguments.rend(); ++it) {
                proof = makeSurfaceAnonymousTuple(
                    std::vector<SurfaceExpressionPointer>{
                        identifier(it->name), std::move(proof)},
                    line, column, /*userWritten=*/false);
            }
            armProofs.push_back(std::move(proof));

            std::vector<SurfacePatternPointer> patternArguments;
            for (const auto& argument : constructorArguments) {
                patternArguments.push_back(makeSurfacePatternBareName(
                    argument.name, line, column));
            }
            SurfaceCasesClause clause;
            clause.pattern = makeSurfacePatternConstructor(
                constructorSpec.name, std::move(patternArguments),
                line, column);
            clause.line = line;
            clause.column = column;
            clauses.push_back(std::move(clause));
        }

        // Right-associated disjunction, with each arm's proof wrapped in
        // the matching Or-injection chain (constructor i of n: i Rights
        // then a Left, the last constructor all Rights).
        size_t constructorCount = disjuncts.size();
        SurfaceExpressionPointer statement = disjuncts.back();
        for (size_t i = constructorCount - 1; i-- > 0;) {
            statement = makeSurfaceBinaryOperation(
                "∨", disjuncts[i], std::move(statement), line, column);
        }
        for (size_t i = 0; i < constructorCount; ++i) {
            SurfaceExpressionPointer wrapped = std::move(armProofs[i]);
            if (i + 1 < constructorCount) {
                wrapped = makeSurfaceApplication(
                    identifier("Or.introduceLeft"),
                    std::vector<SurfaceExpressionPointer>{std::move(wrapped)},
                    line, column);
            }
            for (size_t j = 0; j < i; ++j) {
                wrapped = makeSurfaceApplication(
                    identifier("Or.introduceRight"),
                    std::vector<SurfaceExpressionPointer>{std::move(wrapped)},
                    line, column);
            }
            clauses[i].body = std::move(wrapped);
        }

        SurfaceDefinitionDeclaration lemma;
        lemma.name = declaration.name + ".cases_covered";
        lemma.universeParameters = declaration.universeParameters;
        lemma.arguments = declaration.parameters;
        SurfaceBinder subjectBinder{{subjectName},
                                    applyToParameters(declaration.name)};
        lemma.arguments.push_back(std::move(subjectBinder));
        lemma.type = std::move(statement);
        lemma.body = makeSurfaceCases(identifier(subjectName),
                                      std::move(clauses), line, column);
        lemma.isTheorem = true;
        lemma.automatic = true;
        try {
            elaborateDefinition(lemma);
        } catch (const ElaborateError&) {
            // The vocabulary was present but the lemma didn't elaborate
            // (dependent corner, exotic constructor shape, name clash) —
            // the inductive itself is unaffected; hand-written coverage
            // lemmas remain the fallback.
        } catch (const TypeError&) {
        }
    }

