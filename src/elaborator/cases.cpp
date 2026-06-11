// Out-of-line Elaborator method definitions: less-common surface expression forms: sorry, anonymous tuple, cases-on-expression family (incl. quotient/refining/equality-hypothesis), note, decide
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateSorry(
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

ExpressionPointer Elaborator::elaborateAnonymousTuple(
        const SurfaceAnonymousTuple& tuple,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {

        if (!expectedType) {
            throw ElaborateError(
                "anonymous tuple '⟨...⟩' needs an expected type from "
                "context (line " + std::to_string(line) + ")");
        }
        // Force opaque heads transparent so an `IsNonneg(x)`-typed expected
        // type exposes its underlying `Exists` inductive — the construct-site
        // counterpart of the kernel's opacity-tolerant retries (replaces the
        // old `unfold IsNonneg in ⟨…⟩` wrap).
        ExpressionPointer head =
            weakHeadNormalFormForcingOpaqueHead(expectedType);
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
        // Pass the inductive-headed `head` (opaque wrappers forced off) as the
        // expected type, NOT the original opaque `expectedType` — the
        // constructor-parameter inference needs to read the inductive's
        // arguments (e.g. `Exists`'s predicate) from it. The kernel's defeq
        // bridge re-checks the built term against the opaque expected type.
        return elaborateExpression(*surfaceCall, localBinders, head);
    }

ExpressionPointer Elaborator::elaborateQuotientCases(
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
                "(`<rep> => …` or `Quotient.mk(<rep>) => …`), got "
                + std::to_string(cases.clauses.size()));
        }
        const SurfaceCasesClause& clause = cases.clauses[0];

        // Accepted pattern shapes (where <pat_inner> is itself a bare
        // name or a constructor pattern over the carrier type):
        //   - <bare_name>                      — bind rep, no destructure
        //   - Quotient.mk(<pat_inner>)         — explicit wrap (also accepted)
        //   - <Constructor.…>(args)            — destructure rep directly
        //
        // For the non-bare-name inner patterns, we synthesise a fresh
        // representative binder name and wrap the user's body in
        // `cases <fresh> { | <pat_inner> => <body> }` so the underlying
        // structural-recursor elaboration handles the destructure.
        std::string representativeName;
        SurfacePatternPointer innerDestructurePattern;  // non-null iff
                                                         // we need to
                                                         // wrap the body
        {
            auto* bareName = std::get_if<SurfacePatternBareName>(
                &clause.pattern->node);
            auto* constructorPattern =
                std::get_if<SurfacePatternConstructor>(&clause.pattern->node);
            if (bareName) {
                // `cases x { | rep_x => body }`: no destructure.
                representativeName = bareName->name;
            } else if (constructorPattern
                && constructorPattern->constructorName == "Quotient.mk") {
                if (constructorPattern->arguments.size() != 1) {
                    throwElaborate(
                        "quotient-cases: `Quotient.mk` pattern takes "
                        "one argument (the representative), got "
                        + std::to_string(
                            constructorPattern->arguments.size()));
                }
                auto* innerBareName = std::get_if<SurfacePatternBareName>(
                    &constructorPattern->arguments[0]->node);
                if (innerBareName) {
                    representativeName = innerBareName->name;
                } else {
                    representativeName = "_quotientRep_"
                        + std::to_string(clause.line) + "_"
                        + std::to_string(clause.column);
                    innerDestructurePattern =
                        constructorPattern->arguments[0];
                }
            } else if (constructorPattern) {
                // `cases x { | <Constructor>(args) => body }` —
                // destructure directly. Synthesise the rep binder.
                representativeName = "_quotientRep_"
                    + std::to_string(clause.line) + "_"
                    + std::to_string(clause.column);
                innerDestructurePattern = clause.pattern;
            } else if (std::get_if<SurfacePatternTuple>(
                           &clause.pattern->node)) {
                // `cases x { | ⟨a, b⟩ => body }` — destructure the
                // representative via the carrier's sole constructor
                // (resolved by the inner cases from the carrier type, so
                // the constructor name need not be written). This is the
                // form `by_representatives x as ⟨a, b⟩` desugars to.
                representativeName = "_quotientRep_"
                    + std::to_string(clause.line) + "_"
                    + std::to_string(clause.column);
                innerDestructurePattern = clause.pattern;
            } else {
                throwElaborate(
                    "quotient-cases pattern must be a bare name "
                    "(binding the representative), a constructor "
                    "pattern or tuple `⟨…⟩` over the carrier type "
                    "(destructures the representative), or "
                    "`Quotient.mk(<inner>)`");
            }
        }

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

        // If the user supplied a destructure pattern on the rep,
        // synthesize a `cases <fresh_rep> { | <inner_pattern> => <body> }`
        // wrap before elaborating; otherwise elaborate the body directly.
        SurfaceExpressionPointer bodySurface = clause.body;
        if (innerDestructurePattern) {
            SurfaceExpressionPointer scrutineeIdentifier =
                makeSurfaceIdentifier(representativeName, {},
                                       clause.line, clause.column);
            SurfaceCasesClause innerClause;
            innerClause.pattern = innerDestructurePattern;
            innerClause.body = bodySurface;
            innerClause.line = clause.line;
            innerClause.column = clause.column;
            std::vector<SurfaceCasesClause> innerClauses;
            innerClauses.push_back(std::move(innerClause));
            bodySurface = makeSurfaceCases(
                std::move(scrutineeIdentifier),
                std::move(innerClauses),
                clause.line, clause.column);
        }

        // Elaborate the body in the extended local context.
        ExpressionPointer bodyKernel =
            elaborateExpression(*bodySurface, innerBinders,
                                 bodyExpectedType);
        // Run the diff/class-equality coercions on the body, exactly as the
        // structural-`cases` and lambda-body paths do. Without this a
        // quotient-`cases` arm whose body proves the bare equivalence
        // `R(g x, g y)` could not close a `motive(mk rep)` goal that
        // reduces to `mk(g x) = mk(g y)` (e.g. the outer respect of a
        // binary define-by-representatives, whose goal is a literal
        // `Quotient.lift(…, mk rep)` equality).
        // WHNF the expected type first: it is the motive *applied* to
        // `mk(rep)` (an unreduced redex), and coerceToExpectedTypeViaDiff's
        // cheap prefilter checks for an `Equality` head without reducing —
        // so the beta-redex would hide the goal and the coercion would bail.
        bodyKernel = coerceToExpectedTypeViaDiff(
            innerBinders, bodyKernel,
            weakHeadNormalForm(environment_, bodyExpectedType));

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

SurfaceExpressionPointer Elaborator::patternToSurfaceExpression(
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

ExpressionPointer Elaborator::elaborateCasesWithEqualityHypothesis(
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

ExpressionPointer Elaborator::elaborateCasesWithRefining(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        if (!expectedType) {
            throwElaborate(
                "cases ... refining ... { ... } needs an expected "
                "type from context");
        }
        // Bound re-entrancy: an infinite refining recursion would overflow the
        // stack and crash the process. Genuine nesting is shallow.
        if (casesRefiningDepth_ >= kCasesRefiningDepthCap) {
            throwElaborate(
                "cases ... refining ... nested too deeply (possible "
                "non-terminating refinement) at line " + std::to_string(line));
        }
        struct RefiningDepthGuard {
            int& depth;
            RefiningDepthGuard(int& d) : depth(d) { ++depth; }
            ~RefiningDepthGuard() { --depth; }
        } refiningDepthGuard(casesRefiningDepth_);
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
            // T_i is the type of h_i and belongs in the scope at the
            // position where Pi(h_i_new, T_i, ...) is being inserted.
            // The chain places h_1 outermost, h_2 inside it, ..., h_N
            // innermost — so each subsequent outer-abstract (in future
            // iterations) will descend through this Pi's domain at
            // currentDepth=0 and lift its outer BVs by 1, naturally
            // shifting T_i by the number of refining Pis above it.
            // No extra lifting is needed here.
            ExpressionPointer domain = refiningTypesAtOuterDepth[i];
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
            cases.scrutinee, std::move(wrappedClauses), line, column,
            cases.inductionHypothesisName);

        // (4) Elaborate the synthetic cases against the wrapped Pi
        // chain. Call the INNER elaborator directly rather than going through
        // elaborateExpression → elaborateCasesExpression: the dependent
        // hypotheses have already been generalised into `wrappedExpectedType`,
        // so the auto-refine in elaborateCasesExpression must NOT fire again —
        // it would still see those hypotheses in scope and recurse into
        // refining forever (stack overflow).
        const SurfaceCases& syntheticCasesNode =
            std::get<SurfaceCases>(syntheticCases->node);
        ExpressionPointer innerCasesKernel = elaborateCasesExpressionInner(
            syntheticCasesNode, localBinders, wrappedExpectedType,
            line, column);

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

ExpressionPointer Elaborator::elaborateNoteExpression(
        const SurfaceNote& note,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int /*column*/) {
        Frame frame(*this,
            "note at line " + std::to_string(line),
            localBinders, expectedType, line, /*column=*/0);
        // `change T;` replaces the goal by `T` for the body (after the
        // defeq check below); `note goal : T;` leaves it unchanged. This
        // holds the replacement goal in the `change` case.
        ExpressionPointer changedGoal;
        if (note.goalType) {
            if (!expectedType) {
                throwElaborate(
                    (note.changesGoal
                         ? "`change T` needs an expected type from "
                           "context (none available at line "
                         : "`note goal : T` needs an expected type from "
                           "context (none available at line ")
                    + std::to_string(line) + ")");
            }
            ExpressionPointer declaredKernel = elaborateExpression(
                *note.goalType, localBinders);
            if (note.changesGoal) changedGoal = declaredKernel;
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
                    std::string(note.changesGoal
                        ? "`change` mismatch at line "
                        : "`note goal :` mismatch at line ")
                    + std::to_string(line)
                    + " (the given type is not definitionally equal to "
                      "the goal):\n"
                    + (note.changesGoal ? "  change to:     "
                                        : "  noted form:    ")
                    + prettyPrintInLocalScope(declaredKernel, localBinders)
                    + "\n  actual goal:   "
                    + prettyPrintInLocalScope(expectedType, localBinders));
            }
        } else if (note.proposition) {
            ExpressionPointer propKernel = elaborateExpression(
                *note.proposition, localBinders,
                makeSort(makeLevelConst(0)));
            if (note.proof) {
                // `note P by V;` — check the supplied reason V proves P.
                // Like every `note`, it's non-binding (the term is
                // discarded) and never flagged unused/redundant; the `by V`
                // just lets the reason be shown to the reader (and lets the
                // note hold when the auto-prover can't close P on its own).
                ExpressionPointer proofKernel = elaborateExpression(
                    *note.proof, localBinders, propKernel);
                ExpressionPointer proofType = inferTypeInLocalContext(
                    localBinders, proofKernel);
                ExpressionPointer propOpened = openOverLocalBinders(
                    propKernel, localBinders, localBinders.size());
                Context context =
                    buildContextFromLocalBinders(localBinders);
                if (!isDefinitionallyEqual(environment_, context,
                                            proofType, propOpened)) {
                    throwElaborate(
                        std::string("`note P by V` at line ")
                        + std::to_string(line)
                        + ": the proof does not have the noted type `"
                        + prettyPrintInLocalScope(propKernel, localBinders)
                        + "`");
                }
            } else {
                try {
                    (void)autoProveClaim(propKernel, localBinders, line);
                } catch (const ElaborateError&) {
                    throwElaborate(
                        std::string("`note <proposition>` at line ")
                        + std::to_string(line)
                        + ": the auto-prover could not close the noted "
                        "proposition: "
                        + prettyPrintInLocalScope(propKernel, localBinders)
                        + " (supply the reason with `note P by <proof>`)");
                } catch (const TypeError&) {
                    throwElaborate(
                        std::string("`note <proposition>` at line ")
                        + std::to_string(line)
                        + ": the auto-prover raised a type error on the "
                        "noted proposition: "
                        + prettyPrintInLocalScope(propKernel, localBinders));
                }
            }
        } else {
            throwElaborate(
                "internal: SurfaceNote with neither goalType nor "
                "proposition set");
        }
        return elaborateExpression(
            *note.body, localBinders,
            note.changesGoal ? changedGoal : expectedType);
    }

ExpressionPointer Elaborator::elaborateDecideExpression(
        const SurfaceDecide& decide,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "decide expression at line " + std::to_string(line));
        TimedScope _scope(*this, "elaborateDecide");
        if (!expectedType) {
            throwElaborate(
                "decide P { … } needs an expected type from context");
        }
        // `decide P { yes m => Y | no n => N }` IS constructor `cases` on
        // `Logic.classical_decidable(P) : Logic.Decidable(P)` — a Type(0)
        // inductive with `yes : P → _` and `no : Not(P) → _`. Desugar to
        // that surface `cases` and reuse the ordinary cases elaboration:
        // the expression-scrutinee path builds the dependent motive (so an
        // arm's expected type ι-reduces with the constructor substituted —
        // e.g. `decide_pick(P, yes(_))` reduces), and each arm body gets the
        // standard coerceToExpectedTypeViaDiff treatment. So a `decide` arm
        // closes exactly what a `cases` arm closes. (This replaced a bespoke
        // ~270-line recursor/motive build that hand-rolled the motive
        // abstraction AND skipped arm coercion — the capability-matrix gap.)
        SurfaceExpressionPointer scrutinee = makeSurfaceApplication(
            makeSurfaceIdentifier("Logic.classical_decidable", {}, line, column),
            std::vector<SurfaceExpressionPointer>{decide.proposition},
            line, column);
        auto armClause = [&](const std::string& constructorName,
                             const std::string& binderName,
                             const SurfaceExpressionPointer& body) {
            std::vector<SurfacePatternPointer> arguments;
            arguments.push_back(makeSurfacePatternBareName(
                binderName.empty() ? std::string("_") : binderName,
                line, column));
            SurfaceCasesClause clause;
            clause.pattern = makeSurfacePatternConstructor(
                constructorName, std::move(arguments), line, column);
            clause.body = body;
            clause.line = line;
            clause.column = column;
            return clause;
        };
        std::vector<SurfaceCasesClause> clauses;
        clauses.push_back(armClause("Logic.Decidable.yes",
            decide.yesBinderName, decide.yesBody));
        clauses.push_back(armClause("Logic.Decidable.no",
            decide.noBinderName, decide.noBody));
        SurfaceExpressionPointer syntheticCases = makeSurfaceCases(
            std::move(scrutinee), std::move(clauses), line, column);
        return elaborateExpression(
            *syntheticCases, localBinders, expectedType);
    }

std::vector<std::string> Elaborator::scrutineeDependentBinders(
        const SurfaceExpressionPointer& scrutinee,
        const std::vector<LocalBinder>& localBinders) {
        ExpressionPointer scrutineeKernel;
        try {
            scrutineeKernel =
                elaborateExpression(*scrutinee, localBinders);
        } catch (const ElaborateError&) {
            return {};
        } catch (const TypeError&) {
            return {};
        }
        auto* boundVariable =
            std::get_if<BoundVariable>(&scrutineeKernel->node);
        if (!boundVariable) return {};
        int total = static_cast<int>(localBinders.size());
        int scrutineePosition = total - 1 - boundVariable->deBruijnIndex;
        if (scrutineePosition < 0 || scrutineePosition >= total) return {};
        std::vector<std::string> names;
        for (int i = scrutineePosition + 1; i < total; ++i) {
            // The scrutinee's de Bruijn index within binder i's type
            // scope (binders 0..i-1 are in scope there).
            int scrutineeIndexInTypeScope = (i - 1) - scrutineePosition;
            if (referencesBoundVariable(
                    localBinders[i].type, scrutineeIndexInTypeScope)) {
                names.push_back(localBinders[i].name);
            }
        }
        return names;
    }

ExpressionPointer Elaborator::elaborateCasesExpression(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        bool plain = cases.refiningNames.empty()
            && cases.equalityHypothesisName.empty();
        if (plain && expectedType) {
            std::vector<std::string> autoRefine =
                scrutineeDependentBinders(cases.scrutinee, localBinders);
            if (!autoRefine.empty()) {
                // A hypothesis depends on the scrutinee, so it must be
                // generalised (reverted) before the case-split. Go straight to
                // the refining path: trying the plain path first can LOOP on
                // such a hypothesis (the motive/typecheck never terminates)
                // rather than failing fast, so we must not attempt it here.
                SurfaceCases reverted = cases;
                reverted.refiningNames = std::move(autoRefine);
                return elaborateCasesExpressionInner(
                    reverted, localBinders, expectedType, line, column);
            }
        }
        return elaborateCasesExpressionInner(
            cases, localBinders, expectedType, line, column);
    }

ExpressionPointer Elaborator::elaborateCasesExpressionInner(
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
        } else if (scrutineeLocalIndex < 0 && indexLocalIndices.empty()) {
            // Expression scrutinee (not a local variable) of a non-indexed
            // inductive: build a DEPENDENT motive by abstracting the
            // scrutinee's structural occurrences in the goal, so each arm's
            // expected type ι-reduces with the constructor substituted for
            // the scrutinee (e.g. `decide` on `Logic.classical_decidable(P)`
            // — the yes arm sees `f(yes(_))` reduced). WHNF-aware so a
            // scrutinee buried behind a δ/ζ-reducible wrapper still matches.
            // When the goal does NOT mention the scrutinee, abstraction
            // finds 0 occurrences and this equals the old constant motive
            // `shift(expectedType, 1)` — so this is purely additive (it only
            // enables the dependent case, which a constant motive rejects).
            ExpressionPointer scrutineeReduced = zetaUnfoldLetBinders(
                scrutinee, localBinders, /*currentDepth=*/0);
            std::string scrutineeHeadName =
                applicationHeadConstantName(scrutineeReduced);
            int occurrences = 0;
            int whnfFuel = 2048;
            motiveWalkerCache_.clear();
            motiveBody = abstractStructuralOccurrenceWithWHNF(
                expectedType, scrutineeReduced, scrutineeHeadName,
                /*currentDepth=*/0, occurrences, whnfFuel);
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
                localBinders, cases.inductionHypothesisName));
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

