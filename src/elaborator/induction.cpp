// Out-of-line Elaborator method definitions: by-induction / strong-induction / choose / structured-claim / given
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateByStrongInduction(
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

ExpressionPointer Elaborator::elaborateChoose(
        const SurfaceChoose& choose,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "choose " + choose.name + " at line "
            + std::to_string(line));
        int N = static_cast<int>(localBinders.size());

        // Decide the existential's SOURCE — what the cases below
        // destructures. Three forms:
        //   (a) `from <hypothesis>` — destructure that hypothesis directly
        //       (names WHICH one, when several existentials are in scope);
        //   (b) `from <lemma>` — cite the lemma argument-free, shaped by
        //       `such that <prop>` into `∃ (name : _). prop`, and
        //       destructure the result;
        //   (c) no `from` — scan scope for the most-recent Exists (the
        //       original behaviour).
        SurfaceExpressionPointer scrutinee;
        if (choose.source) {
            // Does the source ALREADY have an existential type — a
            // hypothesis (`aDividesB`), or any applied term (`gSurjective(z)`,
            // `List.Permutation.extract(…)`)? Then destructure it directly.
            // Only a still-unapplied lemma (a Pi type) needs citing. Decide
            // by elaborating the source and inspecting its type, so applied
            // terms aren't mistaken for lemmas.
            bool sourceIsExistential = false;
            try {
                ExpressionPointer sourceTerm = elaborateExpression(
                    *choose.source, localBinders);
                ExpressionPointer sourceType = weakHeadNormalForm(
                    environment_, openOverLocalBinders(
                        inferTypeInLocalContext(localBinders, sourceTerm),
                        localBinders, N));
                ExpressionPointer head = sourceType;
                while (auto* app = std::get_if<Application>(&head->node)) {
                    head = app->function;
                }
                if (auto* headConstant =
                        std::get_if<Constant>(&head->node)) {
                    sourceIsExistential = headConstant->name == "Exists";
                }
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            }
            if (sourceIsExistential) {
                scrutinee = choose.source;
            } else if (!choose.predicate) {
                // Lemma source, no `such that`: cite the lemma argument-free
                // and destructure its existential — its premises discharge
                // from context, exactly like `obtain ⟨…⟩ by <lemma>`. No body
                // restatement needed. (Add `such that` only to DISAMBIGUATE
                // when several in-scope facts could discharge the premise.)
                scrutinee = makeSurfaceCiteInferred(
                    choose.source, line, column);
            } else {
                // Lemma source WITH `such that`: cite it against the explicit
                // `∃ (name : T). prop`, so the body disambiguates which
                // hypothesis the lemma's premise discharges against; the
                // witness type T is read off the lemma's own conclusion.
                ExpressionPointer lemmaTerm = elaborateExpression(
                    *choose.source, localBinders);
                ExpressionPointer lemmaType = inferTypeInLocalContext(
                    localBinders, lemmaTerm);
                ExpressionPointer conclusion = openOverLocalBinders(
                    lemmaType, localBinders, N);
                while (auto* pi = std::get_if<Pi>(&conclusion->node)) {
                    conclusion = pi->codomain;
                }
                conclusion = weakHeadNormalForm(environment_, conclusion);
                // Exists(T, motive) = App(App(Const "Exists"), T, motive).
                ExpressionPointer witnessType;
                if (auto* outer =
                        std::get_if<Application>(&conclusion->node)) {
                    if (auto* inner = std::get_if<Application>(
                            &outer->function->node)) {
                        if (auto* head = std::get_if<Constant>(
                                &inner->function->node)) {
                            if (head->name == "Exists") {
                                witnessType = inner->argument;
                            }
                        }
                    }
                }
                auto* witnessConstant = witnessType
                    ? std::get_if<Constant>(&witnessType->node) : nullptr;
                if (!witnessConstant) {
                    throwElaborate(
                        "choose " + choose.name + " from <lemma>: could not "
                        "read a simple (closed) witness type from the "
                        "lemma's existential conclusion. Use the explicit "
                        "form `claim ∃ (" + choose.name + " : <T>). <prop> "
                        "by <lemma>; choose " + choose.name + " …` instead.");
                }
                SurfaceExpressionPointer witnessTypeSurface =
                    makeSurfaceIdentifier(witnessConstant->name, {},
                        line, column);
                SurfaceBinder witnessBinder;
                witnessBinder.names = {choose.name};
                witnessBinder.type = witnessTypeSurface;
                SurfaceExpressionPointer motive = makeSurfaceLambda(
                    witnessBinder, choose.predicate, line, column);
                SurfaceExpressionPointer existential =
                    makeSurfaceApplication(
                        makeSurfaceIdentifier("Exists", {}, line, column),
                        std::vector<SurfaceExpressionPointer>{
                            witnessTypeSurface, motive},
                        line, column);
                scrutinee = makeSurfaceAscription(
                    makeSurfaceCiteInferred(choose.source, line, column),
                    existential, line, column);
            }
        } else {
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
                    "Name the source with `from <hypothesis-or-lemma>`, or "
                    "prepend `claim ∃ …;` (optionally `by <lemma>`) to bring "
                    "the existential into scope first.");
            }
            scrutinee = makeSurfaceIdentifier(
                localBinders[matchedIndex].name, {}, line, column);
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
                "`choose ...`");
        }
        // Build a SurfaceCases destructuring the chosen existential. The
        // condition hypothesis takes the user's `as <name>` when given, else
        // an internal name (the auto-prover finds it by type-match anyway).
        std::string predHypName = choose.conditionName.empty()
            ? ("_choice_pred_" + std::to_string(line) + "_"
               + std::to_string(column))
            : choose.conditionName;
        std::vector<SurfacePatternPointer> patternComponents;
        patternComponents.push_back(
            makeSurfacePatternBareName(
                choose.name, line, column));
        patternComponents.push_back(
            makeSurfacePatternBareName(
                std::move(predHypName), line, column));
        SurfacePatternPointer tuplePattern = makeSurfacePatternTuple(
            std::move(patternComponents), line, column,
            /*userWritten=*/false);
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

ExpressionPointer Elaborator::elaborateByInductionUsing(
        const SurfaceByInductionUsing& form,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        if (expectedType) {
            std::vector<std::string> deps =
                scrutineeDependentBinders(form.scrutinee, localBinders);
            if (!deps.empty()) {
                // Try the plain induction. Unlike the `cases` path, the
                // lemma path builds the final application without
                // typechecking it, so a stale-hypothesis mismatch only
                // surfaces at the kernel boundary (a TypeError) — we must
                // validate the result here to know whether to fall back.
                try {
                    ExpressionPointer plain =
                        elaborateByInductionUsingInner(
                            form, localBinders, expectedType, line, column);
                    inferTypeInLocalContext(localBinders, plain);
                    return plain;
                } catch (const ElaborateError&) {
                } catch (const TypeError&) {
                }
                return elaborateByInductionUsingReverted(
                    form, deps, localBinders, expectedType, line, column);
            }
        }
        return elaborateByInductionUsingInner(
            form, localBinders, expectedType, line, column);
    }

ExpressionPointer Elaborator::elaborateByInductionUsingReverted(
        const SurfaceByInductionUsing& form,
        const std::vector<std::string>& deps,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        int total = static_cast<int>(localBinders.size());
        int depCount = static_cast<int>(deps.size());
        // Resolve each dep to its outer BoundVariable index and its type
        // lifted to the outer (depth = total) scope.
        std::vector<int> depBoundVariableIndices;
        std::vector<ExpressionPointer> depTypesAtOuterDepth;
        for (const auto& name : deps) {
            int positionInArray = -1;
            for (int i = total - 1; i >= 0; --i) {
                if (localBinders[i].name == name) { positionInArray = i; break; }
            }
            if (positionInArray < 0) {
                throwElaborate("by_induction auto-generalize: no binder '"
                    + name + "' in scope");
            }
            depBoundVariableIndices.push_back(total - 1 - positionInArray);
            depTypesAtOuterDepth.push_back(liftBoundVariables(
                localBinders[positionInArray].type,
                total - positionInArray, 0));
        }
        // Build the reverted goal: Π(d_1)…Π(d_k). Goal, abstracting each
        // dep (innermost-first) so earlier deps' references resolve to
        // the new Π binders.
        ExpressionPointer revertedGoal = expectedType;
        for (int i = depCount - 1; i >= 0; --i) {
            revertedGoal = abstractOverBoundVariable(
                revertedGoal, depBoundVariableIndices[i]);
            revertedGoal = makePi(deps[i],
                depTypesAtOuterDepth[i], std::move(revertedGoal));
        }
        // Wrap the body in `function (d_1) … (d_k) => body`.
        SurfaceExpressionPointer wrappedBody = form.body;
        for (int i = depCount - 1; i >= 0; --i) {
            SurfaceBinder binder;
            binder.names = {deps[i]};
            binder.type = nullptr;
            binder.isImplicit = false;
            wrappedBody = makeSurfaceLambda(
                std::move(binder), wrappedBody, line, column);
        }
        SurfaceByInductionUsing wrappedForm{
            form.scrutinee, form.inductionLemma,
            form.subjectName, form.ihName, wrappedBody};
        ExpressionPointer result = elaborateByInductionUsingInner(
            wrappedForm, localBinders, revertedGoal, line, column);
        // Apply the actual hypotheses to unwind the Π chain back to Goal.
        for (int i = 0; i < depCount; ++i) {
            result = makeApplication(std::move(result),
                makeBoundVariable(depBoundVariableIndices[i]));
        }
        return result;
    }

ExpressionPointer Elaborator::elaborateByInductionUsingInner(
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
        // inferTypeInLocalContext returns the type in OPENED form (outer
        // binders are Internal FreeVariables). Close it back over
        // localBinders before extracting sub-terms: those sub-terms
        // (`ihTypeAfterSubject`) get embedded as lambda domains in the
        // returned closed-form term, so a free `r` left over from the
        // opened motive would dangle as "unbound internal variable r".
        // (Only bites when the motive references an outer binder — hence
        // the existing motive-free tests never exercised this path.)
        ExpressionPointer remainingType = closeOverLocalBinders(
            inferTypeInLocalContext(localBinders, lemmaAppliedToMotive),
            localBinders, localBinders.size());
        remainingType = weakHeadNormalForm(environment_, remainingType);
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

ExpressionPointer Elaborator::elaborateByInductionOnePlusReverted(
        const SurfaceCases& cases,
        const std::vector<std::string>& refiningNames,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "by_induction (1+n) refining at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "by_induction needs an expected type from context");
        }
        int total = static_cast<int>(localBinders.size());
        int count = static_cast<int>(refiningNames.size());
        // Resolve each refining name to its outer BoundVariable index and its
        // type lifted to the outer (depth = total) scope — exactly as the
        // legacy `elaborateByInductionUsingReverted` does for the recursor.
        std::vector<int> boundVariableIndices;
        std::vector<ExpressionPointer> typesAtOuterDepth;
        for (const auto& name : refiningNames) {
            int positionInArray = -1;
            for (int i = total - 1; i >= 0; --i) {
                if (localBinders[i].name == name) {
                    positionInArray = i;
                    break;
                }
            }
            if (positionInArray < 0) {
                throwElaborate(
                    "by_induction ... refining " + name
                    + ": no binder named '" + name + "' in scope");
            }
            boundVariableIndices.push_back(total - 1 - positionInArray);
            typesAtOuterDepth.push_back(liftBoundVariables(
                localBinders[positionInArray].type,
                total - positionInArray, 0));
        }
        // Reverted goal: Π(h_1)…Π(h_k). Goal, abstracting each hypothesis
        // (innermost-first) so earlier ones resolve to the new Π binders.
        ExpressionPointer revertedGoal = expectedType;
        for (int i = count - 1; i >= 0; --i) {
            revertedGoal = abstractOverBoundVariable(
                revertedGoal, boundVariableIndices[i]);
            revertedGoal = makePi(refiningNames[i],
                typesAtOuterDepth[i], std::move(revertedGoal));
        }
        // Wrap each `case base:` / `case step(k):` body in
        // `function (h_1) … (h_k) => body`, and clear refiningNames so the
        // inner one-plus elaboration sees a plain induction at the reverted
        // goal. The motive becomes `λn. Π h(n). goal(n)`, so the step's
        // `IH : motive(k)` is a function expecting the refined hypothesis —
        // matching how such proofs apply it (`IH(prefixBounded)`).
        SurfaceCases reverted = cases;
        reverted.refiningNames.clear();
        for (auto& clause : reverted.clauses) {
            SurfaceExpressionPointer wrappedBody = clause.body;
            for (int i = count - 1; i >= 0; --i) {
                SurfaceBinder binder;
                binder.names = {refiningNames[i]};
                binder.type = nullptr;
                binder.isImplicit = false;
                wrappedBody = makeSurfaceLambda(
                    std::move(binder), std::move(wrappedBody), line, column);
            }
            clause.body = std::move(wrappedBody);
        }
        ExpressionPointer result = elaborateByInductionOnePlus(
            reverted, localBinders, revertedGoal, line, column);
        // Apply the actual hypotheses to unwind the Π chain back to Goal.
        for (int i = 0; i < count; ++i) {
            result = makeApplication(std::move(result),
                makeBoundVariable(boundVariableIndices[i]));
        }
        (void)column;
        return result;
    }

ExpressionPointer Elaborator::elaborateByInductionOnePlus(
        const SurfaceCases& cases,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "by_induction (1+n) at line " + std::to_string(line));
        if (!expectedType) {
            throwElaborate(
                "by_induction needs an expected type from context");
        }

        // --- Extract the `case base:` and `case step(k):` clause bodies.
        // The parser appended the IH name to the `step` constructor pattern,
        // so its arguments are [predecessor, IH].
        const SurfaceExpression* baseBody = nullptr;
        const SurfaceExpression* stepBody = nullptr;
        std::string stepSubjectName;
        std::string ihName = cases.inductionHypothesisName;
        for (const auto& clause : cases.clauses) {
            if (auto* bareName = std::get_if<SurfacePatternBareName>(
                    &clause.pattern->node)) {
                if (bareName->name == "base") {
                    baseBody = clause.body.get();
                    continue;
                }
            }
            if (auto* constructorPattern =
                    std::get_if<SurfacePatternConstructor>(
                        &clause.pattern->node)) {
                if (constructorPattern->constructorName == "step") {
                    if (constructorPattern->arguments.empty()) {
                        throwElaborate(
                            "by_induction: `case step` must bind the "
                            "predecessor, as `case step(k):`");
                    }
                    auto* predecessorName =
                        std::get_if<SurfacePatternBareName>(
                            &constructorPattern->arguments[0]->node);
                    if (!predecessorName) {
                        throwElaborate(
                            "by_induction: `case step`'s first binder "
                            "must be a plain name (the predecessor `k`)");
                    }
                    stepSubjectName = predecessorName->name;
                    stepBody = clause.body.get();
                    continue;
                }
            }
            // Reached only for a clause that is neither `base` nor `step` —
            // most often a not-yet-converted `case zero:` / `case
            // successor(k):` left from the legacy recursor vocabulary, which a
            // sibling `base`/`step` clause already routed us onto the 1+n path.
            std::string offending;
            if (auto* bareName = std::get_if<SurfacePatternBareName>(
                    &clause.pattern->node)) {
                offending = bareName->name;
            } else if (auto* constructorPattern =
                    std::get_if<SurfacePatternConstructor>(
                        &clause.pattern->node)) {
                offending = constructorPattern->constructorName;
            }
            if (offending == "zero" || offending == "successor") {
                throwElaborate(
                    "by_induction: a `case " + offending + "` clause is mixed "
                    "with `case base`/`case step` — these are different "
                    "induction vocabularies. The `1 + n` form uses `case base:` "
                    "and `case step(k):`; rename `zero`→`base` and "
                    "`successor(k)`→`step(k)`. (To keep the raw-recursor form "
                    "instead, use `case zero`/`case successor` for every clause.)");
            }
            throwElaborate(
                "by_induction (1+n form) expects exactly `case base:` and "
                "`case step(k):` clauses (got a `" + offending + "` clause)");
        }
        if (!baseBody || !stepBody) {
            throwElaborate(
                "by_induction (1+n form) needs both a `case base:` and a "
                "`case step(k):` clause");
        }

        // --- Scrutinee must be a local-binder variable (so we can abstract
        // it from the goal to form the motive).
        ExpressionPointer scrutineeKernel = elaborateExpression(
            *cases.scrutinee, localBinders);
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
            static_cast<int>(localBinders.size()) - 1 - scrutineeDeBruijn;
        ExpressionPointer scrutineeType =
            localBinders[scrutineeArrayIndex].type;

        // --- Resolve `<Carrier>.induction_on_one_plus` from the scrutinee's
        // carrier head.
        ExpressionPointer scrutineeTypeWhnf = weakHeadNormalForm(
            environment_,
            inferTypeInLocalContext(localBinders, scrutineeKernel));
        ExpressionPointer spineHead = scrutineeTypeWhnf;
        while (auto* app = std::get_if<Application>(&spineHead->node)) {
            spineHead = app->function;
        }
        auto* headConstant = std::get_if<Constant>(&spineHead->node);
        if (!headConstant) {
            throwElaborate(
                "by_induction: scrutinee's type has no named carrier "
                "(head must be a constant like `Natural`)");
        }
        std::string lemmaName =
            headConstant->name + ".induction_on_one_plus";
        if (!environment_.lookup(lemmaName)) {
            throwElaborate(
                "by_induction: no `" + lemmaName + "` in scope (the "
                "`1 + n` induction principle for carrier `"
                + headConstant->name + "`); import the module that "
                "provides it, or use `case zero` / `case successor` for "
                "the raw-recursor form");
        }
        SurfaceExpressionPointer lemmaSurface = makeSurfaceIdentifier(
            lemmaName, {}, line, column);
        ExpressionPointer lemmaKernel = elaborateExpression(
            *lemmaSurface, localBinders);

        // --- Motive: λ(subject : T). expectedType[scrutinee := Bound 0].
        ExpressionPointer motiveBody =
            abstractOverBoundVariables(expectedType, {scrutineeDeBruijn});
        ExpressionPointer motive = makeLambda(
            stepSubjectName, scrutineeType, motiveBody);

        // Apply the motive; read the remaining argument types off the
        // lemma's own type (kernel-computed, with the motive substituted).
        // Close back over localBinders before extracting sub-terms (the
        // opened-vs-closed discipline of elaborateByInductionUsingInner).
        ExpressionPointer lemmaAppliedToMotive =
            makeApplication(lemmaKernel, motive);
        ExpressionPointer remainingType = weakHeadNormalForm(
            environment_,
            closeOverLocalBinders(
                inferTypeInLocalContext(localBinders, lemmaAppliedToMotive),
                localBinders, localBinders.size()));
        // remainingType = (base : P 0)
        //               → (step : (k : T) → P(k) → P(1 + k))
        //               → (target : T) → P(target)
        auto* basePi = std::get_if<Pi>(&remainingType->node);
        if (!basePi) {
            throwElaborate(
                "induction_on_one_plus has no base argument after the "
                "motive");
        }
        // Beta-reduce the motive applications (`motive 0`, `motive k`,
        // `motive (1+k)`) into clean goal shapes. Leaving them as redexes
        // makes the downstream cases/claim motive machinery in a complex
        // step body build a malformed term — the recursor path never hits
        // this because ι-reduction already delivers a reduced case goal.
        ExpressionPointer baseType = weakHeadNormalForm(
            environment_, basePi->domain);  // P(0), our context
        // basePi->codomain lives UNDER the `base` binder (base : P(0)), so its
        // localBinder references sit one deeper than our actual step context
        // (stepBinders has [subject, ih], not base). The step/target types
        // never use the base proof, so strengthen that binder out — lower
        // every bound variable above index 0 by one. (Single-step induction
        // à la strong_induction has no base binder, hence no such fixup.)
        ExpressionPointer afterBase = weakHeadNormalForm(
            environment_,
            liftBoundVariables(basePi->codomain, -1, 1));
        auto* stepPi = std::get_if<Pi>(&afterBase->node);
        if (!stepPi) {
            throwElaborate(
                "induction_on_one_plus has no step argument after the "
                "base");
        }
        ExpressionPointer stepType = weakHeadNormalForm(
            environment_, stepPi->domain);
        auto* stepSubjectPi = std::get_if<Pi>(&stepType->node);
        if (!stepSubjectPi) {
            throwElaborate(
                "induction_on_one_plus's step must begin with a "
                "predecessor argument (Pi)");
        }
        ExpressionPointer afterSubject = weakHeadNormalForm(
            environment_, stepSubjectPi->codomain);
        auto* stepIhPi = std::get_if<Pi>(&afterSubject->node);
        if (!stepIhPi) {
            throwElaborate(
                "induction_on_one_plus's step must have an IH argument "
                "after the predecessor");
        }
        ExpressionPointer ihType = weakHeadNormalForm(
            environment_, stepIhPi->domain);        // P(k), ctx [k]
        ExpressionPointer stepBodyType = weakHeadNormalForm(
            environment_, stepIhPi->codomain);      // P(1+k), ctx [k, ih]

        // --- Base body: prove P(0).
        ExpressionPointer baseKernel = elaborateExpression(
            *baseBody, localBinders, baseType);

        // --- Step body: prove P(1 + k) given k and IH : P(k). The step
        // body's context is localBinders ++ [(k, T), (IH, P(k))], with k at
        // Bound(1) and IH at Bound(0); ihType / stepBodyType already live in
        // that context (extracted from the closed lemma type).
        std::vector<LocalBinder> stepBinders = localBinders;
        stepBinders.push_back({stepSubjectName, scrutineeType});
        stepBinders.push_back({ihName, ihType});
        ExpressionPointer stepBodyKernel = elaborateExpression(
            *stepBody, stepBinders, stepBodyType);
        ExpressionPointer ihLambda = makeLambda(
            ihName, ihType, stepBodyKernel);
        ExpressionPointer stepLambda = makeLambda(
            stepSubjectName, scrutineeType, ihLambda);

        // --- Assemble: lemma(motive)(base)(step)(scrutinee).
        ExpressionPointer application =
            makeApplication(lemmaAppliedToMotive, std::move(baseKernel));
        application = makeApplication(
            std::move(application), std::move(stepLambda));
        application = makeApplication(
            std::move(application), std::move(scrutineeKernel));
        (void)column;
        return application;
    }

ExpressionPointer Elaborator::elaborateStructuredClaim(
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

        // Resolve the goal proposition. A `goal` proposition (the form
        // `claim goal …`, and `done`/`okay` which desugar to it) is the
        // expected type itself — use it directly rather than elaborating
        // the `goal` reference.
        ExpressionPointer goalClosed;
        bool propositionIsGoal = claim.proposition
            && std::holds_alternative<SurfaceGoal>(claim.proposition->node);
        if (claim.proposition && !propositionIsGoal) {
            goalClosed = elaborateExpression(
                *claim.proposition, localBinders);
        } else if (expectedType) {
            goalClosed = expectedType;
        } else {
            throwElaborate(
                "bare `claim` / `done` needs an expected type from context "
                "(none available — wrap it in `(claim : T)` "
                "or provide a proposition: `claim P [by Hint]`)");
        }

        if (!claim.byHint && !claim.bySubstitution) {
            // `claim <proofTerm>` — the argument elaborated to a PROOF, not
            // the proposition to prove, so claim its TYPE with the argument
            // as the proof. This is the mirror of the proposition-as-proof
            // coercion (a proof position may take a proposition, auto-proved);
            // here a proposition position takes a proof, and we read off its
            // type. Detected by: the argument is not itself a proposition, but
            // its type is. Lets `claim Rational.is_commutative_ring;` bring the
            // named fact into context without restating its (long) type.
            if (claim.proposition && !propositionIsGoal) {
                try {
                    Context openedContext =
                        buildContextFromLocalBinders(localBinders);
                    ExpressionPointer goalOpened = openOverLocalBinders(
                        goalClosed, localBinders, localBinders.size());
                    if (!typeIsProposition(openedContext, goalOpened)) {
                        ExpressionPointer goalType = inferType(
                            environment_, openedContext, goalOpened);
                        if (typeIsProposition(openedContext, goalType)) {
                            return goalClosed;
                        }
                    }
                } catch (...) {
                    // fall through to the ordinary auto-prove path
                }
            }
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
        // Also propagate for `ring` / `field` — both tactics reject
        // outright when called without an expected type, so the
        // anonymous-claim form `claim T by ring;` / `claim T by
        // field(…);` requires it.
        //
        // Other byHint shapes (applications, identifiers, etc.) keep
        // the no-expected-type path so `autoFillHintForClaim` can
        // peel a partial-application byHint's Pi chain and fill
        // missing args. Forcing expected type on a partial app would
        // make the kernel reject the Pi-typed result mid-elaboration,
        // before autoFillHintForClaim gets to bridge the gap.
        bool propagateExpectedTypeToHint =
            hintShapeIsProofTerm(*claim.byHint);
        const char* claimSizeFlag = std::getenv("MATH_CLAIM_SIZES");
        bool dumpClaimSize = claimSizeFlag && claimSizeFlag[0] != '\0'
            && claimSizeFlag[0] != '0';
        long long t0 = monotonicNanos();
        ExpressionPointer result;
        ExpressionPointer hintType;
        ExpressionPointer hintTerm;
        // Allow a bare universe-polymorphic citation (no `.{...}`) for the
        // span of this hint's elaboration AND its match against the goal:
        // placeholder levels are introduced during elaboration and resolved
        // inside the matcher (Gap 1). Restored on scope exit so the
        // placeholder set never leaks into unrelated elaboration.
        bool savedAllowCiteLevels = allowImplicitCitationLevels_;
        std::set<std::string> savedCitePlaceholders = citationLevelPlaceholders_;
        allowImplicitCitationLevels_ = true;
        struct CiteLevelsGuard {
            bool& flag; bool savedFlag;
            std::set<std::string>& placeholders;
            std::set<std::string> savedPlaceholders;
            ~CiteLevelsGuard() {
                flag = savedFlag;
                placeholders = std::move(savedPlaceholders);
            }
        } citeLevelsGuard{allowImplicitCitationLevels_, savedAllowCiteLevels,
                          citationLevelPlaceholders_,
                          std::move(savedCitePlaceholders)};
        try {
            hintTerm = elaborateExpression(
                *claim.byHint, localBinders,
                propagateExpectedTypeToHint ? goalClosed : nullptr);
            // `inferTypeInLocalContext` returns an OPENED type;
            // `autoFillHintForClaim` expects closed form throughout
            // (matchAgainstPattern / instantiateLemmaBinders are
            // closed-form helpers).
            ExpressionPointer hintTypeOpened =
                inferTypeInLocalContext(localBinders, hintTerm);
            hintType = closeOverLocalBinders(
                hintTypeOpened, localBinders, localBinders.size());
            result = autoFillHintForClaim(
                hintTerm, hintType, goalClosed, localBinders, line);
        } catch (const ElaborateError&) {
            // A proof-TERM hint (a lambda or a block, or ring/field) whose
            // own elaboration failed has no recovery: recoverClaimHint
            // would just re-elaborate the identical term and fail again,
            // masking the genuinely informative inner error (the failing
            // claim inside the body) behind the generic citation message.
            // Re-throw the inner error instead — it is the real one.
            if (!hintTerm && hintShapeIsProofTerm(*claim.byHint)) {
                throw;
            }
            // Otherwise: the hint didn't fill against the goal directly.
            // Either it is a cited fact `by (P)` (a Proposition — prove it,
            // then bridge its proof to the goal), or an ordinary hint that
            // needs the diff-congruence path on a goal-typed re-elaboration —
            // the behaviour the named (`let`-style) claim path always
            // provided. Having both strategies here is what makes
            // `claim NAME : T by …` and `claim T by …` elaborate identically
            // (the name only adds a binding); e.g. `claim f(a) = f(b) by eq`
            // with `eq : a = b`.
            result = recoverClaimHint(
                hintTerm, *claim.byHint, goalClosed, localBinders, line);
        } catch (const TypeError&) {
            if (!hintTerm && hintShapeIsProofTerm(*claim.byHint)) {
                throw;
            }
            result = recoverClaimHint(
                hintTerm, *claim.byHint, goalClosed, localBinders, line);
        }
        long long tFill = monotonicNanos();
        if (dumpClaimSize && hintType) {
            size_t goalSize = countExpressionNodes(goalClosed);
            size_t hintSize = countExpressionNodes(hintType);
            long long totalMs = (tFill - t0) / 1000000;
            if (totalMs >= 50 || goalSize >= 100) {
                std::cerr << "[claim-size] " << moduleName_
                          << ":" << line
                          << " goal=" << goalSize
                          << " hint=" << hintSize
                          << " total=" << totalMs << " ms\n";
            }
        }

        // `--check-redundant-by`: speculatively run the bare-`claim`
        // auto-prover on the same goal. If it would also discharge
        // the goal, warn that the hint is redundant. A `since` hint is an
        // intentional explanation — exempt it from the check.
        //
        // Also exempt a `by unfolding <X>` hint: it flips `<X>`'s opacity for
        // the proof, and the speculative re-proof runs while that transparency
        // is still in scope — so it would spuriously "succeed" (the hint looks
        // redundant) even though removing it leaves `<X>` opaque and the bare
        // claim fails. An unfolding hint is load-bearing by construction, so
        // the check can't faithfully test its removal.
        bool byInvolvesUnfolding = claim.byHint
            && std::get_if<SurfaceUnfold>(&claim.byHint->node) != nullptr;
        if (reportRedundantBy_ && !claim.byIsExplanation
            && !byInvolvesUnfolding) {
            // Cap the budget so each re-proof bails early; exceeding it
            // (the hint is load-bearing for speed) yields no proof. The guard
            // also bounds the bare-citation re-elaboration below (its backward
            // chaining respects autoProveBudgetLimit_).
            uint64_t stepsBefore = kernelStepsSoFar();
            RedundancyBudgetGuard budgetGuard(*this);
            ExpressionPointer autoAttempt;
            try {
                autoAttempt = autoProveClaim(
                    goalClosed, localBinders, line);
            } catch (const ElaborateError&) {
                autoAttempt = nullptr;
            } catch (const TypeError&) {
                autoAttempt = nullptr;
            } catch (const AutoProverBudgetError&) {
                autoAttempt = nullptr;
            }
            // A single deep conversion can close the bare claim while
            // overshooting the low budget without tripping it (sampled only at
            // candidate boundaries); an expensive by-less re-proof means the
            // hint earns its keep on speed, so don't call it redundant.
            if (autoAttempt
                && redundancyReproofWasExpensive(stepsBefore)) {
                autoAttempt = nullptr;
            }
            if (autoAttempt) {
                // Name the claim when it has a label: several multi-line
                // claims in a row put many `claim …`/`by …` lines near the
                // reported one, and an unnamed warning is easy to pin on
                // the wrong claim.
                std::cerr << "warning: " << moduleName_
                    << ":" << line
                    << ": redundant `by` on `claim"
                    << (claim.label.empty() ? "" : " " + claim.label)
                    << "` — auto-prover closes the goal without help\n";
                const char* debugRedundant =
                    std::getenv("MATH_DEBUG_REDUNDANT");
                if (debugRedundant && debugRedundant[0] != '\0'
                    && debugRedundant[0] != '0') {
                    std::cerr << "[debug-redundant] " << moduleName_ << ":"
                        << line << " re-proof term: "
                        << prettyPrint(autoAttempt) << "\n";
                    for (size_t bi = 0; bi < localBinders.size(); ++bi) {
                        std::cerr << "[debug-redundant]   binder " << bi
                            << " (bound "
                            << (localBinders.size() - 1 - bi) << "): "
                            << localBinders[bi].name << " : "
                            << prettyPrint(localBinders[bi].type) << "\n";
                    }
                }
            } else if (claim.byHint) {
                // The whole `by` isn't removable, but maybe its ARGUMENTS are:
                // `claim T by Lemma(args)` where `by Lemma` alone (args
                // inferred from the goal, premises discharged from context or
                // backward-chained) would also close it. Mirrors the calc-step
                // args check in calc.cpp. Only a real theorem cited with
                // explicit args; congruenceOf has its own dedicated check.
                auto* surfApp = std::get_if<SurfaceApplication>(
                    &claim.byHint->node);
                auto* head = surfApp
                    ? std::get_if<SurfaceIdentifier>(
                          &surfApp->function->node)
                    : nullptr;
                const Declaration* citedDeclaration =
                    head ? environment_.lookup(head->qualifiedName) : nullptr;
                // Skip universe-POLYMORPHIC lemmas. The speculative re-elaborate
                // below cites the lemma BARE (`makeSurfaceIdentifier(name, {})`,
                // no universe args), which forces the implicit-citation-level
                // placeholder path (`_cite_u_N` wildcards resolved post-match).
                // When that match FAILS — which it does precisely when the
                // stripped value arguments were what pinned the universe levels
                // — it leaves elaborator state subtly corrupted, breaking a
                // later citation in the same file (e.g. a `since fraction_equal`
                // whose premise discharge then fails). For a monomorphic lemma
                // the bare citation needs no levels, so the path is never taken.
                // The check is a marginal "you can drop the args" hint; declining
                // it for universe-poly lemmas costs almost nothing.
                if (surfApp && !surfApp->arguments.empty()
                    && head && head->universeArgs.empty()
                    && head->qualifiedName != "congruenceOf"
                    && citedDeclaration
                    && universeParameterCount(*citedDeclaration) == 0) {
                    ExpressionPointer bareAttempt = nullptr;
                    try {
                        SurfaceExpressionPointer bare =
                            makeSurfaceIdentifier(
                                head->qualifiedName, {}, line, 0);
                        bareAttempt = elaborateExpression(
                            *bare, localBinders, goalClosed);
                    } catch (const ElaborateError&) {
                        bareAttempt = nullptr;
                    } catch (const TypeError&) {
                        bareAttempt = nullptr;
                    } catch (const AutoProverBudgetError&) {
                        bareAttempt = nullptr;
                    }
                    bool valid = false;
                    if (bareAttempt && !containsFreeVariable(bareAttempt)) {
                        try {
                            ExpressionPointer t = inferTypeInLocalContext(
                                localBinders, bareAttempt);
                            ExpressionPointer g = openOverLocalBinders(
                                goalClosed, localBinders, localBinders.size());
                            Context c = buildContextFromLocalBinders(
                                localBinders);
                            valid = isDefinitionallyEqual(
                                environment_, c, t, g);
                        } catch (...) { valid = false; }
                    }
                    if (valid) {
                        std::cerr << "warning: " << moduleName_
                            << ":" << line
                            << ": arguments to `" << head->qualifiedName
                            << "` are inferable from the goal — `by "
                            << head->qualifiedName << "` alone suffices\n";
                    }
                }
            }
        }
        return result;
    }

bool Elaborator::hintShapeIsProofTerm(const SurfaceExpression& byHint) {
        return std::holds_alternative<SurfaceLambda>(byHint.node)
            || std::holds_alternative<SurfaceLet>(byHint.node)
            || std::holds_alternative<SurfaceRing>(byHint.node)
            || std::holds_alternative<SurfaceField>(byHint.node);
    }

ExpressionPointer Elaborator::autoFillHintForClaim(
        ExpressionPointer hintTerm,
        ExpressionPointer hintType,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
        // First try the citation on the forms as written. On failure,
        // retry with let-bound names ζ-unfolded in both the goal and the
        // hint's type: a `let m := successor(n);` abbreviation is an
        // opaque FreeVariable to the structural matchers, and a lemma
        // conclusion that needs `m` and `successor(n)` to be the same
        // term can only unify on the unfolded forms (the long-standing
        // "let-opacity in citation matching" gap). Fallback-only so
        // citations that match the FOLDED spelling — e.g. against
        // context facts stated in terms of the let name — keep working
        // exactly as before.
        std::exception_ptr firstError;
        try {
            ExpressionPointer direct = autoFillHintForClaimCore(
                hintTerm, hintType, goalClosed, localBinders, line);
            if (direct) return direct;
        } catch (const ElaborateError&) {
            firstError = std::current_exception();
        } catch (const TypeError&) {
            firstError = std::current_exception();
        }
        ExpressionPointer goalUnfolded =
            zetaUnfoldLetBinders(goalClosed, localBinders);
        ExpressionPointer hintTypeUnfolded =
            zetaUnfoldLetBinders(hintType, localBinders);
        if (structurallyEqual(goalUnfolded, goalClosed)
            && structurallyEqual(hintTypeUnfolded, hintType)) {
            // No lets to see through: the ζ-unfolded retry would re-run the
            // identical match and fail identically. Re-raise the original
            // error rather than recomputing it (the recompute is the single
            // costliest redundancy in the context-fact scan's failing path).
            if (firstError) std::rethrow_exception(firstError);
            return autoFillHintForClaimCore(
                hintTerm, hintType, goalClosed, localBinders, line);
        }
        return autoFillHintForClaimCore(
            hintTerm, hintTypeUnfolded, goalUnfolded, localBinders, line);
    }

ExpressionPointer Elaborator::autoFillHintForClaimCore(
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
        if (isDefinitionallyEqual(environment_, openedContext,
                      hintTypeOpened, goalOpened)) {
            return hintTerm;
        }

        // Peel Pi chain, collecting domains outermost-first and the
        // cursor at each peel depth. When the cursor is not syntactically
        // a Pi, try a single WHNF step to expose a HIDDEN one: a
        // conclusion headed by a definition that unfolds to a function —
        // most importantly `¬P` (`Not(P)` = `P → False`) — so that e.g.
        // `claim False by no_member_in_empty` (whose conclusion is
        // `¬member(n, empty)`) peels the `member` premise and reaches the
        // `False` the goal wants. If WHNF makes no progress, or doesn't
        // produce a Pi, stop — leaving the un-unfolded conclusion as the
        // last cursor (so a `definition`-headed conclusion like
        // `Natural.divides …` is preserved for the folded-match attempts,
        // not eagerly expanded to its `Exists` body here).
        std::vector<ExpressionPointer> domainsOutermostFirst;
        std::vector<ExpressionPointer> cursorsAtDepth;
        cursorsAtDepth.push_back(hintTypeReduced);
        ExpressionPointer cursor = hintTypeReduced;
        while (true) {
            auto* pi = std::get_if<Pi>(&cursor->node);
            if (!pi) {
                ExpressionPointer unfolded =
                    weakHeadNormalForm(environment_, cursor);
                if (unfolded.get() == cursor.get()) break;
                pi = std::get_if<Pi>(&unfolded->node);
                if (!pi) break;
                cursor = unfolded;
            }
            domainsOutermostFirst.push_back(pi->domain);
            cursor = pi->codomain;
            cursorsAtDepth.push_back(cursor);
        }
        int totalBinders =
            static_cast<int>(domainsOutermostFirst.size());
        if (totalBinders == 0) {
            // No Pi's and not defeq: nothing more to try. Under the
            // speculative scan the message is discarded, so skip the
            // (pretty-printing) string build entirely.
            if (inSpeculativeContextScan_) throwElaborate("hint type mismatch");
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
            if (matchAgainstPatternWithDeferredProjections(
                    cursorsAtDepth[trialDepth], goalReduced,
                    trialDepth, trialReduced)) {
                matchedDepth = trialDepth;
                bindings = std::move(trialReduced);
                break;
            }
            // Skip the un-reduced attempt when the goal needed no WHNF: it
            // would re-run the identical match against the same pointer.
            if (goalClosed.get() != goalReduced.get()) {
                std::vector<ExpressionPointer> trialUnreduced(trialDepth);
                if (matchAgainstPatternWithDeferredProjections(
                        cursorsAtDepth[trialDepth], goalClosed,
                        trialDepth, trialUnreduced)) {
                    matchedDepth = trialDepth;
                    bindings = std::move(trialUnreduced);
                    break;
                }
            }
            // Third attempt: reduce the conclusion cursor too. The lemma's
            // conclusion may be headed by a `definition` (e.g.
            // `Natural.divides …`) while the goal arrives unfolded (e.g.
            // `Exists …` — as a propositionless `done`/`goal`/`okay` sees it
            // when the goal flowed through an eliminator motive that WHNF'd
            // it). WHNF-ing the cursor folds the two onto a common head so
            // the data binders still pin. The cursor is open (its trialDepth
            // peeled binders act as pattern metavariables); WHNF only does
            // δ/β, leaving those bound variables intact.
            ExpressionPointer cursorReduced = weakHeadNormalForm(
                environment_, cursorsAtDepth[trialDepth]);
            // Skip when WHNF was a no-op: the cursor is unchanged, so this
            // would re-run the first attempt verbatim.
            if (cursorReduced.get() != cursorsAtDepth[trialDepth].get()) {
                std::vector<ExpressionPointer> trialCursorReduced(trialDepth);
                if (matchAgainstPatternWithDeferredProjections(
                        cursorReduced, goalReduced,
                        trialDepth, trialCursorReduced)) {
                    matchedDepth = trialDepth;
                    bindings = std::move(trialCursorReduced);
                    break;
                }
            }
        }
        // The conclusion may be an APPLICATION OF A PEELED BINDER —
        // `P(x)` for a lemma quantified over the predicate P. First-order
        // matching can then "succeed" with the wrong split (binding P to
        // a partial application of the goal's head), or fail outright —
        // either way the premises are the authority: they mention P and x
        // under rigid heads (`filter(P, list)`), so a premise-driven
        // recovery with nothing pre-pinned is the fallback strategy.
        bool conclusionHeadIsFlexible = false;
        {
            ExpressionPointer head = cursorsAtDepth[totalBinders];
            while (auto* app = std::get_if<Application>(&head->node)) {
                head = app->function;
            }
            if (auto* headBinder = std::get_if<BoundVariable>(&head->node)) {
                conclusionHeadIsFlexible =
                    headBinder->deBruijnIndex < totalBinders;
            }
        }
        if (matchedDepth >= 0) {
            try {
                return completeCitationFromBindings(
                    hintTerm, goalClosed, goalOpened, openedContext,
                    localBinders, domainsOutermostFirst, cursorsAtDepth,
                    totalBinders, matchedDepth, bindings,
                    /*conclusionWasFlexApplication=*/false);
            } catch (const ElaborateError&) {
                if (!conclusionHeadIsFlexible) throw;
                // fall through to the premise-driven strategy
            }
        }
        if (conclusionHeadIsFlexible) {
            std::vector<ExpressionPointer> deferred(totalBinders);
            return completeCitationFromBindings(
                hintTerm, goalClosed, goalOpened, openedContext,
                localBinders, domainsOutermostFirst, cursorsAtDepth,
                totalBinders, totalBinders, std::move(deferred),
                /*conclusionWasFlexApplication=*/true);
        }
        if (inSpeculativeContextScan_) throwElaborate("hint conclusion mismatch");
        throwElaborate(
            "the `by` hint's conclusion (`"
            + prettyPrintInLocalScope(
                  cursorsAtDepth[totalBinders], localBinders)
            + "`) does not unify with the goal (`"
            + prettyPrintInLocalScope(goalClosed, localBinders)
            + "`)");
    }

ExpressionPointer Elaborator::completeCitationFromBindings(
        ExpressionPointer hintTerm,
        const ExpressionPointer& goalClosed,
        const ExpressionPointer& goalOpened,
        const Context& openedContext,
        const std::vector<LocalBinder>& localBinders,
        const std::vector<ExpressionPointer>& domainsOutermostFirst,
        const std::vector<ExpressionPointer>& cursorsAtDepth,
        int totalBinders,
        int matchedDepth,
        std::vector<ExpressionPointer> bindings,
        bool conclusionWasFlexApplication) {
        // Back-inference pass. The conclusion match above pins only the
        // binders that appear in the conclusion; many lemmas keep their key
        // arguments in their HYPOTHESES (e.g. all_prime_under_prepend_equality
        // mentions head/tail/list only in `member(c, list)` and
        // `list = prepend(head, tail)`). Recover them by unifying each unfilled
        // binder's domain against the context:
        //   (a) a hypothesis premise unifies against an in-scope hypothesis,
        //       selecting it AND back-filling the data binders it mentions
        //       (matching `member(c, list)` to `member(c, prepend(h,t))` pins
        //       `list`); and
        //   (b) an equality premise whose two sides are now determined and
        //       definitionally equal is discharged by `reflexivity`.
        // Iterated to a fixpoint since one discharge can unblock the next.
        // Additive: when the conclusion already pins everything, the loop is a
        // no-op, so existing `by <lemma>` sites are unaffected.
        {
            int N = static_cast<int>(localBinders.size());
            auto domainInPatternScope = [&](int innerIndex) {
                int pos = matchedDepth - 1 - innerIndex;
                return liftBoundVariables(
                    domainsOutermostFirst[pos], matchedDepth - pos, 0);
            };
            std::function<bool(const ExpressionPointer&, int)> referencesUnfilled =
                [&](const ExpressionPointer& e, int depth) -> bool {
                    if (auto* bv = std::get_if<BoundVariable>(&e->node)) {
                        int rel = bv->deBruijnIndex - depth;
                        return rel >= 0 && rel < matchedDepth && !bindings[rel];
                    }
                    if (auto* app = std::get_if<Application>(&e->node))
                        return referencesUnfilled(app->function, depth)
                            || referencesUnfilled(app->argument, depth);
                    if (auto* pi = std::get_if<Pi>(&e->node))
                        return referencesUnfilled(pi->domain, depth)
                            || referencesUnfilled(pi->codomain, depth + 1);
                    if (auto* lam = std::get_if<Lambda>(&e->node))
                        return referencesUnfilled(lam->domain, depth)
                            || referencesUnfilled(lam->body, depth + 1);
                    return false;
                };
            bool progress = true;
            while (progress) {
                progress = false;
                for (int innerIndex = 0; innerIndex < matchedDepth;
                     ++innerIndex) {
                    if (bindings[innerIndex]) continue;
                    ExpressionPointer domain = domainInPatternScope(innerIndex);
                    // (a) discharge against an in-scope hypothesis, back-
                    // filling any data binders the premise mentions.
                    for (int b = N - 1; b >= 0; --b) {
                        ExpressionPointer hypType = liftBoundVariables(
                            localBinders[b].type, N - b, 0);
                        std::vector<ExpressionPointer> trial = bindings;
                        bool matched = matchAgainstPattern(
                            domain, hypType, matchedDepth, trial);
                        if (!matched) {
                            // The hypothesis may be stated through a
                            // definition that folds the premise's rigid
                            // head (`coprime_residues(n)` for
                            // `filter(P, list)`). Unfold the head one
                            // step at a time — full WHNF would reduce
                            // PAST the head the pattern wants.
                            ExpressionPointer unfolded = hypType;
                            for (int step = 0; step < 4 && !matched;
                                 ++step) {
                                ExpressionPointer next =
                                    unfoldHeadConstantOneStep(unfolded);
                                if (!next || next.get() == unfolded.get()) {
                                    break;
                                }
                                unfolded = next;
                                trial = bindings;
                                matched = matchAgainstPattern(
                                    domain, unfolded, matchedDepth, trial);
                            }
                        }
                        if (matched) {
                            bindings = std::move(trial);
                            bindings[innerIndex] = makeBoundVariable(N - 1 - b);
                            progress = true;
                            break;
                        }
                    }
                    if (bindings[innerIndex]) continue;
                    // (a') local defeq search once the premise is fully
                    // determined. The syntactic matcher in (a) lines a
                    // hypothesis up by first-order structure; it misses when
                    // the matching hypothesis's type mentions `choose`-bound
                    // (Exists-eliminator) witnesses, whose de Bruijn indexing
                    // the matcher can't reconcile even though the types are
                    // definitionally equal — OR when a `let`-bound alias makes
                    // the premise read over `s` and the hypothesis over the
                    // unfolded value (or vice versa). Compare the now-concrete
                    // premise against each in-scope hypothesis by
                    // `isDefinitionallyEqual` instead — bounded (one defeq per
                    // binder, no library scan or recursive proving). Additive:
                    // it runs only after (a) already failed, and selects a
                    // hypothesis whose type IS the premise, so it cannot change
                    // a citation that already resolves. Kept ON even in the
                    // speculative context-fact scan: a context ∀-fact (e.g. a
                    // decomposed conjunction leg) whose premise needs ζ to meet
                    // a hypothesis only applies through this path, and the
                    // search is cheap enough to afford per candidate.
                    if (!referencesUnfilled(domain, 0)) {
                        ExpressionPointer concretePremise =
                            instantiateLemmaBinders(domain, bindings);
                        ExpressionPointer concreteOpened = openOverLocalBinders(
                            concretePremise, localBinders, N);
                        for (int b = N - 1; b >= 0; --b) {
                            ExpressionPointer hypTypeOpened = openOverLocalBinders(
                                liftBoundVariables(
                                    localBinders[b].type, N - b, 0),
                                localBinders, N);
                            if (isDefinitionallyEqual(environment_, openedContext,
                                                      concreteOpened,
                                                      hypTypeOpened)) {
                                bindings[innerIndex] =
                                    makeBoundVariable(N - 1 - b);
                                progress = true;
                                break;
                            }
                        }
                        if (bindings[innerIndex]) continue;
                    }
                    // (b) reflexivity for a now-determined equality premise.
                    if (referencesUnfilled(domain, 0)) continue;
                    ExpressionPointer concrete =
                        instantiateLemmaBinders(domain, bindings);
                    ExpressionPointer head = concrete;
                    std::vector<ExpressionPointer> spineArgs;
                    while (auto* app = std::get_if<Application>(&head->node)) {
                        spineArgs.push_back(app->argument);
                        head = app->function;
                    }
                    std::reverse(spineArgs.begin(), spineArgs.end());
                    auto* headConstant = std::get_if<Constant>(&head->node);
                    if (!headConstant || headConstant->name != "Equality"
                        || spineArgs.size() != 3) {
                        continue;
                    }
                    ExpressionPointer leftOpened = openOverLocalBinders(
                        spineArgs[1], localBinders, N);
                    ExpressionPointer rightOpened = openOverLocalBinders(
                        spineArgs[2], localBinders, N);
                    if (!isDefinitionallyEqual(environment_, openedContext,
                                               leftOpened, rightOpened)) {
                        continue;
                    }
                    ExpressionPointer refl = makeConstant(
                        "reflexivity", headConstant->universeArguments);
                    refl = makeApplication(refl, spineArgs[0]);
                    refl = makeApplication(refl, spineArgs[1]);
                    bindings[innerIndex] = refl;
                    progress = true;
                }
            }
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

        // Resolve citation universe placeholders (Gap 1). The lemma was
        // cited bare, so `elaborateIdentifier` filled its universe arguments
        // with placeholder parameters and the matcher above treated them as
        // wildcards. Now that every argument binding is known, read off the
        // concrete levels by unifying each peeled binder's expected type
        // against the inferred type of its recovered binding — the same
        // type-driven level inference `inferUniverseArguments` does for an
        // ordinary call's value arguments — and substitute them in.
        if (!citationLevelPlaceholders_.empty()) {
            std::map<std::string, LevelPointer> levelAssignment;
            for (int innerIndex = 0; innerIndex < matchedDepth; ++innerIndex) {
                if (!bindings[innerIndex]) continue;
                int outermostPosition = matchedDepth - 1 - innerIndex;
                int outerSlotCount = outermostPosition;
                std::vector<ExpressionPointer> domainBindings(outerSlotCount);
                bool allOuterBound = true;
                for (int j = 0; j < outerSlotCount; ++j) {
                    domainBindings[j] = bindings[innerIndex + 1 + j];
                    if (!domainBindings[j]) { allOuterBound = false; break; }
                }
                if (!allOuterBound) continue;
                ExpressionPointer expectedSlotType = instantiateLemmaBinders(
                    domainsOutermostFirst[outermostPosition], domainBindings);
                ExpressionPointer actualType;
                try {
                    actualType = inferTypeInLocalContext(
                        localBinders, bindings[innerIndex]);
                } catch (const ElaborateError&) {
                    continue;
                } catch (const TypeError&) {
                    continue;
                }
                unifyTypes(
                    weakHeadNormalForm(environment_, expectedSlotType),
                    weakHeadNormalForm(environment_, actualType),
                    levelAssignment);
            }
            std::vector<std::string> placeholderNames;
            std::vector<LevelPointer> placeholderLevels;
            for (const auto& entry : levelAssignment) {
                if (citationLevelPlaceholders_.count(entry.first)) {
                    placeholderNames.push_back(entry.first);
                    placeholderLevels.push_back(entry.second);
                }
            }
            if (!placeholderNames.empty()) {
                hintTerm = substituteUniverseLevels(
                    hintTerm, placeholderNames, placeholderLevels);
                for (auto& binding : bindings) {
                    if (binding) {
                        binding = substituteUniverseLevels(
                            binding, placeholderNames, placeholderLevels);
                    }
                }
            }
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
        if (conclusionWasFlexApplication) {
            // Nothing was pinned from the goal, so nothing yet checks
            // that the recovered P and x actually instantiate the
            // conclusion to the claim. β-reduce `P(x)` and compare.
            ExpressionPointer callType = openOverLocalBinders(
                inferTypeInLocalContext(localBinders, call),
                localBinders, localBinders.size());
            if (!isDefinitionallyEqual(environment_, openedContext,
                                       callType, goalOpened)) {
                throwElaborate(
                    "the `by` hint's conclusion (`"
                    + prettyPrintInLocalScope(
                          cursorsAtDepth[totalBinders], localBinders)
                    + "`), instantiated from the premises, does not "
                    "give the goal (`"
                    + prettyPrintInLocalScope(goalClosed, localBinders)
                    + "`)");
            }
        }
        return call;
    }

ExpressionPointer Elaborator::elaborateGiven(
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

