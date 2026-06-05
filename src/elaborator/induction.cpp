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
            std::holds_alternative<SurfaceLambda>(claim.byHint->node)
            || std::holds_alternative<SurfaceLet>(claim.byHint->node)
            || std::holds_alternative<SurfaceRing>(claim.byHint->node)
            || std::holds_alternative<SurfaceField>(claim.byHint->node);
        const char* claimSizeFlag = std::getenv("MATH_CLAIM_SIZES");
        bool dumpClaimSize = claimSizeFlag && claimSizeFlag[0] != '\0'
            && claimSizeFlag[0] != '0';
        auto t0 = std::chrono::steady_clock::now();
        ExpressionPointer result;
        ExpressionPointer hintType;
        ExpressionPointer hintTerm;
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
            // The hint didn't fill against the goal directly. Either it is a
            // cited fact `by (P)` (a Proposition — prove it, then bridge its
            // proof to the goal), or an ordinary hint that needs the diff-
            // congruence path on a goal-typed re-elaboration — the behaviour
            // the named (`let`-style) claim path always provided. Having both
            // strategies here is what makes `claim NAME : T by …` and
            // `claim T by …` elaborate identically (the name only adds a
            // binding); e.g. `claim f(a) = f(b) by eq` with `eq : a = b`.
            result = recoverClaimHint(
                hintTerm, *claim.byHint, goalClosed, localBinders, line);
        } catch (const TypeError&) {
            result = recoverClaimHint(
                hintTerm, *claim.byHint, goalClosed, localBinders, line);
        }
        auto tFill = std::chrono::steady_clock::now();
        if (dumpClaimSize && hintType) {
            size_t goalSize = countExpressionNodes(goalClosed);
            size_t hintSize = countExpressionNodes(hintType);
            long long totalMs =
                std::chrono::duration_cast<std::chrono::milliseconds>(
                    tFill - t0).count();
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
        if (reportRedundantBy_ && !claim.byIsExplanation) {
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

ExpressionPointer Elaborator::autoFillHintForClaim(
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
                        if (matchAgainstPattern(
                                domain, hypType, matchedDepth, trial)) {
                            bindings = std::move(trial);
                            bindings[innerIndex] = makeBoundVariable(N - 1 - b);
                            progress = true;
                            break;
                        }
                    }
                    if (bindings[innerIndex]) continue;
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

