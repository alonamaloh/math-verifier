// Out-of-line Elaborator method definitions: claim-by-substitution and claim-by-cases
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::elaborateClaimBySubstitution(
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
            // `by substituting (<equation>)`: the equation may be cited as a
            // bare proposition (e.g. `by substituting (a = b)`); auto-prove it
            // so the substitution runs against a proof of the equation.
            if (termIsProposition(localBinders, eqProof)) {
                eqProof = proveCitedFact(eqProof, localBinders, line);
            }
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
            bool directEquality = true;
            try {
                components = extractEqualityComponents(
                    eqProofTypeOpened,
                    "by substituting argument", line);
            } catch (const ElaborateError&) {
                directEquality = false;
            }
            if (directEquality) {
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
                // A quantified equation (e.g. `by substituting
                // Natural.add_zero` with `add_zero : (a) → a + 0 = a`):
                // infer the arguments from the goal, mirroring what
                // `by <lemma>` and the unnamed `by substitution`
                // already do. Throws a tailored error when it can't.
                collectQuantifiedSubstitutionCandidates(
                    eqProof, eqProofTypeOpened, goalClosed,
                    localBinders, line, candidates);
            }
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
        // Third form: when the goal is headed by an opaque definition, the
        // substitution target may live inside its body. Force-unfold opaque
        // heads (search-only) so e.g. `divide_step(succ f, p, n) = …` exposes
        // its `cases monus(p, n) {…}` and the `monus(p, n)` endpoint becomes
        // reachable — replacing the old `unfold X in claim by substituting …`
        // wrap. Gated on an opaque head so ordinary goals skip the extra work;
        // the kernel's defeq bridge re-checks the rewritten goal.
        if (mentionsOpaqueDefinition(goalClosed)) {
            // Protect the substitution endpoints' own heads from being
            // force-unfolded — they are the targets we need to keep visible
            // (e.g. unfold `divide_step` to expose its `cases monus(p, n)`,
            // but keep `monus(p, n)` itself intact to match the `monus(p, n) =
            // 0` endpoint).
            std::set<std::string> protectedDefinitions;
            for (const ContextEquality& eq : candidates) {
                std::string l = headConstantName(eq.lhs);
                std::string r = headConstantName(eq.rhs);
                if (!l.empty()) protectedDefinitions.insert(l);
                if (!r.empty()) protectedDefinitions.insert(r);
            }
            ExpressionPointer goalForced =
                deepWhnfForcingOpaque(goalClosed, protectedDefinitions);
            if (goalForced.get() != goalClosed.get()
                && goalForced.get() != goalDeepWhnf.get()) {
                goalForms.push_back(goalForced);
            }
        }
        // Last-resort form: head-only WHNF unfolds a predicate head
        // (`MeansInequalityAt(1)`, `Qpred(1)`) to expose its body WITHOUT
        // δ-reducing the coercion towers inside it — so an endpoint numeral
        // like `(1 : Rational)` (⤳ the opaque `Rational.one`) can still be
        // matched, via the numeral bridge, against the body's
        // `Natural.to_rational(1)`. Deep WHNF above dissolves both into raw
        // quotient representatives, losing the recognisable literal on the
        // goal side. Tried LAST so proofs that already match in the surface
        // or deep form keep their existing (cheaper) motive shape.
        ExpressionPointer goalHeadWhnf =
            weakHeadNormalForm(environment_, goalClosed);
        bool headWhnfIsNovel = goalHeadWhnf.get() != goalClosed.get();
        for (const ExpressionPointer& existing : goalForms) {
            if (goalHeadWhnf.get() == existing.get()) headWhnfIsNovel = false;
        }
        if (headWhnfIsNovel) {
            goalForms.push_back(goalHeadWhnf);
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
        // Two passes over (candidate × direction). PASS 0 ("fast only") tries
        // every rewrite but closes ONLY via the reflexivity/defeq fast path —
        // no prover call — so a goal that becomes reflexive after the right
        // rewrite is settled cheaply, in WHICHEVER direction achieves it,
        // before any direction's backward rewrite can grow the goal and burn
        // the full prover search closing it. PASS 1 is the original behaviour
        // (prover allowed), with the original direction order preserved, so
        // proofs that legitimately need the search are unaffected.
        for (int pass = 0; pass < 2; ++pass) {
          bool fastPathOnly = (pass == 0);
          for (const ContextEquality& eq : candidates) {
            for (int direction = 0; direction < 2; ++direction) {
                ExpressionPointer fromSide =
                    (direction == 0) ? eq.rhs : eq.lhs;
                ExpressionPointer toSide =
                    (direction == 0) ? eq.lhs : eq.rhs;
                // When the endpoint contains a numeral literal, bridge it to
                // any definitionally-equal numeral form in the goal — e.g. an
                // endpoint `f((1 : Rational))` (where `(1 : Rational)` ⤳ the
                // opaque `Rational.one`) against a goal `f(Natural.to_rational(1))`,
                // which an opaque Rational cannot WHNF-reduce to `Rational.one`.
                // Mirrors the citation matcher's `asNumeralLiteral`
                // canonicalisation. Gated on the endpoint actually carrying a
                // numeral, so non-numeral rewrites pay nothing.
                StructuralNodeMatcher numeralBridge =
                    [this](const ExpressionPointer& candidate,
                           const ExpressionPointer& shiftedTarget) -> bool {
                        return numeralAwareStructurallyEqual(
                            candidate, shiftedTarget);
                    };
                // Engage the bridge only when the endpoint CONTAINS a numeral
                // but is not ITSELF a bare numeral literal. Bridging a bare
                // endpoint (`Rational.one`, `(2 : Rational)`) would let it
                // match — and catastrophically rewrite — every same-valued
                // numeral hiding elsewhere in the goal (e.g. the `1` inside
                // `reciprocal_function((successor 0) : Rational)`). An endpoint
                // that merely carries a numeral inside a larger structure
                // (`f((1 : Rational))`) is safe: the whole structure must match.
                const StructuralNodeMatcher* numeralBridgePtr =
                    (containsNumeralLiteral(fromSide)
                     && !asNumeralLiteral(fromSide))
                        ? &numeralBridge : nullptr;
                // Find the goal form (surface, else deep-WHNF) in which
                // the endpoint occurs, and how many times.
                ExpressionPointer chosenForm;
                int occurrences = 0;
                int surfaceCount = 0;
                int deepCount = 0;
                // The numeral bridge is a LAST-RESORT widening: pass 0 searches
                // structurally only, pass 1 retries with the bridge. A proof
                // that already matches the endpoint structurally never sees the
                // bridge, so its occurrence set (and motive shape) is unchanged
                // — the widening only rescues endpoints that match NOWHERE
                // structurally (a numeral hidden behind an opaque coercion).
                const StructuralNodeMatcher* activeBridge = nullptr;
                for (int bridgePass = 0; bridgePass < 2; ++bridgePass) {
                    const StructuralNodeMatcher* bridge =
                        (bridgePass == 0) ? nullptr : numeralBridgePtr;
                    if (bridgePass == 1 && !numeralBridgePtr) break;
                    for (size_t formIdx = 0;
                         formIdx < goalForms.size(); ++formIdx) {
                        int formOccurrences = 0;
                        abstractStructuralOccurrence(
                            goalForms[formIdx], fromSide,
                            /*currentDepth=*/0, formOccurrences, bridge);
                        if (bridgePass == 0 && formIdx == 0) {
                            surfaceCount = formOccurrences;
                        } else if (bridgePass == 0) {
                            deepCount = formOccurrences;
                        }
                        if (formOccurrences > 0) {
                            chosenForm = goalForms[formIdx];
                            occurrences = formOccurrences;
                            activeBridge = bridge;
                            break;
                        }
                    }
                    if (occurrences > 0) break;
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
                // Build the transport term from an abstracted motive body
                // (which occurrences are abstracted is the caller's choice)
                // and a proof of the rewritten goal. The motive shape is
                // the only thing that varies between a full and a masked
                // (single-occurrence) rewrite — the transport plumbing is
                // identical.
                auto buildTransport =
                    [&](ExpressionPointer abstractedBody,
                        ExpressionPointer proofRewritten) -> ExpressionPointer {
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
                };
                auto tryCloseAndBuild =
                    [&](ExpressionPointer abstractedBody,
                        int budget) -> ExpressionPointer {
                    ExpressionPointer rewrittenGoal = substitute(
                        abstractedBody, 0, toSide);
                    // A rewrite is valid only if it yields a WELL-TYPED goal.
                    // The deep-WHNF / opaque-forcing goal forms above δ-reduce
                    // a transparent `construction` (e.g. `Integer.from_difference`)
                    // past an opaque boundary, leaving a raw `Quotient.class_of`
                    // where the surrounding consumer expects the opaque type
                    // (`Integer`). Such a form is well-typed under opacity-IGNORING
                    // defeq but ILL-TYPED under the normal inferType — and the
                    // wrong rewrite direction (rewriting a stray numeral inside
                    // that expansion) lands there. Type-check the result so the
                    // bad (form, direction) is skipped cleanly instead of handed
                    // to the prover, which would build a proof term that only the
                    // FINAL kernel check rejects (an opaque-boundary leak).
                    try {
                        inferTypeInLocalContext(localBinders, rewrittenGoal);
                    } catch (const ElaborateError&) {
                        return nullptr;
                    } catch (const TypeError&) {
                        return nullptr;
                    }
                    // Fast path: the rewrite alone settled the goal. A
                    // directly-supplied equality usually rewrites one side
                    // of an `a = b` step onto the other, leaving `a = a` —
                    // close that with reflexivity, no prover call. (The
                    // prover route costs tens of thousands of kernel steps
                    // per DIRECTION on real files; this path is what makes
                    // `by substituting <eq>` as cheap as `by <eq>`.)
                    {
                        bool plainEquality = true;
                        EqualityComponents components;
                        try {
                            components = extractEqualityComponents(
                                rewrittenGoal,
                                "`by substituting` fast path", line);
                        } catch (const ElaborateError&) {
                            plainEquality = false;
                        } catch (const TypeError&) {
                            plainEquality = false;
                        }
                        bool sidesEqual = plainEquality
                            && structurallyEqual(components.leftEndpoint,
                                                 components.rightEndpoint);
                        if (plainEquality && !sidesEqual) {
                            // The rewrite frequently yields endpoints that are
                            // definitionally — but not *syntactically* — equal
                            // (the substituted term reaches the kernel via a
                            // slightly different elaboration than the matching
                            // term on the other side). A bounded defeq probe
                            // catches those, so the reflexive close still fires
                            // instead of falling through to the full prover
                            // search — which, on a goal carrying a recursive
                            // term like `power(_, m)`, scans hundreds of
                            // candidate lemmas at ~170k kernel-steps. The
                            // reflexivity proof we build is still checked at
                            // full fuel by the kernel, so a bounded false
                            // positive can't slip through — at worst the probe
                            // is wasted and we take the slow path anyway.
                            int N = static_cast<int>(localBinders.size());
                            try {
                                sidesEqual = isDefinitionallyEqual(
                                    environment_,
                                    buildContextFromLocalBinders(localBinders),
                                    openOverLocalBinders(
                                        components.leftEndpoint, localBinders, N),
                                    openOverLocalBinders(
                                        components.rightEndpoint, localBinders, N),
                                    kDefeqProbeFuel);
                            } catch (...) { sidesEqual = false; }
                        }
                        if (sidesEqual) {
                            ExpressionPointer reflexive = makeConstant(
                                "reflexivity",
                                {components.carrierUniverseLevel});
                            reflexive = makeApplication(
                                reflexive, components.carrierType);
                            reflexive = makeApplication(
                                reflexive, components.leftEndpoint);
                            return buildTransport(abstractedBody, reflexive);
                        }
                    }
                    // Fast-path-only pass: the rewrite didn't make the goal
                    // reflexive, so do NOT pay the prover here — let a different
                    // rewrite/direction (or the later prover pass) handle it.
                    if (fastPathOnly) return nullptr;
                    try {
                        AutoProveCallerLabelGuard callerLabel(
                            *this, "`by substituting` re-proof");
                        ExpressionPointer proofRewritten = autoProveClaim(
                            rewrittenGoal, localBinders, line, budget);
                        return buildTransport(abstractedBody, proofRewritten);
                    } catch (const ElaborateError&) {
                        return nullptr;
                    } catch (const TypeError&) {
                        return nullptr;
                    }
                };
                // Phase 1: try rewriting each SUBSET of the occurrences and
                // closing CHEAPLY (transportBudget 0 — a hypothesis/fact
                // match, no further equality-bridge search). This finds the
                // intended rewrite when the endpoint occurs several times —
                // e.g. only the standalone `0` in `successor(0) ≤ 0`, which
                // lands on a hypothesis — and returns fast, instead of
                // rewriting ALL occurrences into an unprovable goal and then
                // burning the full search on it. Bounded to a small
                // occurrence count so the 2^n subset sweep stays cheap.
                constexpr int maxOccurrencesForSubsetSearch = 6;
                if (occurrences <= maxOccurrencesForSubsetSearch) {
                    for (uint32_t mask = 1;
                         mask < (1u << occurrences); ++mask) {
                        int counter = 0;
                        ExpressionPointer maskedBody =
                            abstractStructuralOccurrenceMasked(
                                chosenForm, fromSide, /*currentDepth=*/0,
                                counter, mask, activeBridge);
                        ExpressionPointer result =
                            tryCloseAndBuild(maskedBody, /*budget=*/0);
                        if (result) return result;
                    }
                }
                // Phase 2: rewrite ALL occurrences and close with the full
                // auto-prover (default budget — may recurse through one
                // equality bridge, which some goals legitimately need).
                {
                    int counter = 0;
                    ExpressionPointer allBody = abstractStructuralOccurrence(
                        chosenForm, fromSide, /*currentDepth=*/0, counter,
                        activeBridge);
                    ExpressionPointer result =
                        tryCloseAndBuild(allBody, /*budget=*/1);
                    if (result) return result;
                }
                attempt.rewrittenProveFailed = true;
                if (!fastPathOnly) attemptLog.push_back(attempt);
                continue;
            }
          }
        }
        // Hypothesis-rewriting fallback (narrowed `by substituting <eq>`
        // only). Goal-rewriting can't reach an endpoint hidden behind a
        // FOLDED definition — e.g. Real `x ≤ y` := `IsNonneg(y - x)`, so
        // the goal `x+z ≤ y+z` never shows `(y+z)-(x+z)` without unfolding.
        // The dual of the explicit `rewrite(eq, hyp)` works: rewrite an
        // in-scope HYPOTHESIS by the equation and keep it if the result is
        // def-equal to the goal (def-eq unfolds the definition). Bounded to
        // the one supplied equality × 2 directions × in-scope proofs; only
        // runs once goal-rewriting has already failed.
        if (claim.byHint && !candidates.empty()) {
            int N = static_cast<int>(localBinders.size());
            Context context = buildContextFromLocalBinders(localBinders);
            ExpressionPointer goalOpened = openOverLocalBinders(
                goalClosed, localBinders, N);
            const ContextEquality& eq = candidates.front();
            for (int dir = 0; dir < 2; ++dir) {
                ExpressionPointer fromSide = (dir == 0) ? eq.lhs : eq.rhs;
                ExpressionPointer toSide = (dir == 0) ? eq.rhs : eq.lhs;
                // eqForTransport : fromSide = toSide.
                ExpressionPointer eqForTransport;
                if (dir == 0) {
                    eqForTransport = eq.proofExpr;
                } else {
                    eqForTransport = makeConstant(
                        "Equality.symmetry", {eq.carrierLevel});
                    for (ExpressionPointer a :
                         {eq.carrierType, eq.lhs, eq.rhs, eq.proofExpr}) {
                        eqForTransport = makeApplication(eqForTransport, a);
                    }
                }
                for (int b = N - 1; b >= 0; --b) {
                    ExpressionPointer hyp = makeBoundVariable(N - 1 - b);
                    ExpressionPointer hypTypeOpened;
                    try {
                        hypTypeOpened = inferTypeInLocalContext(
                            localBinders, hyp);
                    } catch (...) { continue; }
                    bool isProp = false;
                    try {
                        isProp = typeIsProposition(context,
                            weakHeadNormalForm(environment_, hypTypeOpened));
                    } catch (...) { isProp = false; }
                    if (!isProp) continue;
                    ExpressionPointer hypType = closeOverLocalBinders(
                        hypTypeOpened, localBinders, N);
                    // Abstract `fromSide` in the hypothesis type — the
                    // unreduced form first (preserves the user-visible
                    // shape), then WHNF (peels a folded def like
                    // `LessOrEqual` to expose `y - x`). Mirrors the
                    // explicit `rewrite(eq, term)` search.
                    ExpressionPointer chosen;
                    int counter = 0;
                    abstractStructuralOccurrence(hypType, fromSide, 0,
                                                  counter);
                    if (counter > 0) {
                        chosen = hypType;
                    } else {
                        ExpressionPointer whnf = closeOverLocalBinders(
                            weakHeadNormalForm(environment_, hypTypeOpened),
                            localBinders, N);
                        int whnfCount = 0;
                        abstractStructuralOccurrence(whnf, fromSide, 0,
                                                      whnfCount);
                        if (whnfCount == 0) continue;
                        chosen = whnf;
                    }
                    int abstractionCounter = 0;
                    ExpressionPointer body = abstractStructuralOccurrence(
                        chosen, fromSide, 0, abstractionCounter);
                    ExpressionPointer motive = makeLambda(
                        "_rewriteHole", eq.carrierType, body);
                    ExpressionPointer transport = makeConstant(
                        "Equality.transport_proposition", {eq.carrierLevel});
                    for (ExpressionPointer a : {eq.carrierType, motive,
                             fromSide, toSide, eqForTransport, hyp}) {
                        transport = makeApplication(transport, a);
                    }
                    ExpressionPointer transportTypeOpened;
                    try {
                        transportTypeOpened = inferTypeInLocalContext(
                            localBinders, transport);
                    } catch (...) { continue; }
                    bool matchesGoal = false;
                    try {
                        matchesGoal = isDefinitionallyEqual(environment_,
                            context, transportTypeOpened, goalOpened);
                    } catch (...) { matchesGoal = false; }
                    if (matchesGoal) return transport;
                }
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

void Elaborator::collectQuantifiedSubstitutionCandidates(
        ExpressionPointer citedProof,
        ExpressionPointer citedTypeOpened,
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line,
        std::vector<ContextEquality>& out) {
        int N = static_cast<int>(localBinders.size());
        std::string citedPrinted = prettyPrintInLocalScope(
            citedProof, localBinders);
        // Peel the Pi chain off the citation's type (closed over the
        // local binders, so the chain's own BoundVariables are the only
        // ones below `binderCount` — the metavariable slots
        // matchAgainstPattern expects).
        ExpressionPointer citedTypeClosed = closeOverLocalBinders(
            citedTypeOpened, localBinders, N);
        ExpressionPointer conclusion = citedTypeClosed;
        int binderCount = 0;
        while (auto* pi = std::get_if<Pi>(&conclusion->node)) {
            conclusion = pi->codomain;
            ++binderCount;
        }
        // The conclusion must be `Equality(carrier, lhs, rhs)`.
        auto* eqApp3 = std::get_if<Application>(&conclusion->node);
        auto* eqApp2 = eqApp3
            ? std::get_if<Application>(&eqApp3->function->node) : nullptr;
        auto* eqApp1 = eqApp2
            ? std::get_if<Application>(&eqApp2->function->node) : nullptr;
        auto* eqHead = eqApp1
            ? std::get_if<Constant>(&eqApp1->function->node) : nullptr;
        if (binderCount == 0 || !eqHead || eqHead->name != "Equality") {
            throwElaborate(
                "`by substituting`: the supplied expression's "
                "type is not an equality `a = b`"
                + std::string(binderCount > 0
                    ? " — '" + citedPrinted + "' is a function whose "
                      "conclusion is not an equality"
                    : ""));
        }
        ExpressionPointer lhsPattern = eqApp2->argument;
        ExpressionPointer rhsPattern = eqApp3->argument;
        // Scan the goal's Application subterms (surface form first,
        // then the deep-WHNF fallback the bridge itself uses) for an
        // instance of either endpoint pattern; each complete match
        // instantiates the citation into a concrete equality candidate.
        // Bare-BoundVariable patterns are skipped — they match every
        // subterm and carry no inference signal.
        std::vector<ContextEquality> inferred;
        std::function<void(ExpressionPointer)> scan =
            [&](ExpressionPointer subexpr) {
            auto* app = std::get_if<Application>(&subexpr->node);
            if (!app) return;
            for (const ExpressionPointer& pattern :
                     {lhsPattern, rhsPattern}) {
                if (std::holds_alternative<BoundVariable>(pattern->node)) {
                    continue;
                }
                std::vector<ExpressionPointer> bindings(binderCount);
                if (!matchAgainstPattern(pattern, subexpr,
                                           binderCount, bindings)) {
                    continue;
                }
                bool allBound = true;
                for (const auto& binding : bindings) {
                    if (!binding) { allBound = false; break; }
                }
                if (!allBound) continue;
                // Assemble `cited(binding_for_BV(n-1), …, BV(0))` —
                // outermost binder first, matching the Pi chain.
                ExpressionPointer instance = citedProof;
                for (int i = binderCount - 1; i >= 0; --i) {
                    instance = makeApplication(instance, bindings[i]);
                }
                ExpressionPointer instanceTypeOpened;
                try {
                    instanceTypeOpened = inferTypeInLocalContext(
                        localBinders, instance);
                } catch (const TypeError&) { continue; }
                  catch (const ElaborateError&) { continue; }
                EqualityComponents components;
                try {
                    components = extractEqualityComponents(
                        instanceTypeOpened,
                        "by substituting argument", line);
                } catch (const ElaborateError&) { continue; }
                ContextEquality eq;
                eq.cost = 1;
                eq.source = "supplied via `by substituting` ("
                    + citedPrinted + ", arguments inferred)";
                eq.carrierType = closeOverLocalBinders(
                    components.carrierType, localBinders, N);
                eq.lhs = closeOverLocalBinders(
                    components.leftEndpoint, localBinders, N);
                eq.rhs = closeOverLocalBinders(
                    components.rightEndpoint, localBinders, N);
                eq.carrierLevel = components.carrierUniverseLevel;
                eq.proofExpr = std::move(instance);
                bool duplicate = false;
                for (const ContextEquality& seen : inferred) {
                    if (structurallyEqual(seen.lhs, eq.lhs)
                        && structurallyEqual(seen.rhs, eq.rhs)) {
                        duplicate = true;
                        break;
                    }
                }
                if (!duplicate) inferred.push_back(std::move(eq));
            }
            scan(app->function);
            scan(app->argument);
        };
        scan(goalClosed);
        ExpressionPointer goalDeepWhnf =
            deepWhnfThroughApplications(goalClosed);
        if (goalDeepWhnf.get() != goalClosed.get()) {
            scan(goalDeepWhnf);
        }
        if (inferred.empty()) {
            throwElaborate(
                "`by substituting`: '" + citedPrinted
                + "' is a quantified equation — it still expects "
                + std::to_string(binderCount)
                + " argument(s), and no instance of its left- or "
                  "right-hand side occurs in the goal, so they could "
                  "not be inferred. Apply it explicitly (`by "
                  "substituting " + citedPrinted + "(…)`), or use the "
                  "unnamed `by substitution` to search every equality "
                  "in scope.");
        }
        for (ContextEquality& eq : inferred) {
            out.push_back(std::move(eq));
        }
    }

ExpressionPointer Elaborator::elaborateClaimByCases(
        const SurfaceStructuredClaim& claim,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line) {
        Frame frame(*this,
            "claim by cases at line " + std::to_string(line));

        if (claim.arms.size() < 2) {
            throwElaborate(
                "`by cases` needs at least 2 arms; got "
                + std::to_string(claim.arms.size()));
        }
        const size_t armCount = claim.arms.size();

        // The goal each arm must prove. A `goal` proposition (`claim goal
        // by cases …`, and the `done`/`okay` desugaring) is the expected
        // type itself.
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
                "`claim by cases` / `done by cases` needs either a "
                "proposition or an expected type from context");
        }

        // Elaborate each arm's disjunct proposition. An `otherwise:` arm
        // (always last; the parser enforces it) has no stated proposition:
        // its hypothesis is the complement ¬(P₀ ∨ … ∨ Pₖ₋₁) of the stated
        // cases, built below.
        bool hasOtherwise = claim.arms.back().isOtherwise;
        size_t statedCount = hasOtherwise ? armCount - 1 : armCount;
        std::vector<ExpressionPointer> disjuncts;
        // Witness arms (`case P for some k:`): the disjunct is ∃ k. P.
        // The witness type is the annotation when given, else inferred
        // as the type of the equation's left endpoint.
        std::vector<ExpressionPointer> witnessTypes(armCount);
        std::vector<ExpressionPointer> witnessEquations(armCount);
        std::vector<LevelPointer> witnessLevels(armCount);
        for (size_t i = 0; i < statedCount; ++i) {
            const SurfaceStructuredClaimArm& arm = claim.arms[i];
            if (arm.witnessName.empty()) {
                disjuncts.push_back(elaborateExpression(
                    *arm.disjunctType, localBinders));
                continue;
            }
            ExpressionPointer witnessT;
            if (arm.witnessType) {
                witnessT = elaborateExpression(
                    *arm.witnessType, localBinders);
            } else {
                auto* binary = std::get_if<SurfaceBinaryOperation>(
                    &arm.disjunctType->node);
                if (!binary || binary->opSymbol != "=") {
                    throwElaborate(
                        "`for some " + arm.witnessName + "` without a "
                        "type annotation needs the case proposition to "
                        "be an equation `lhs = rhs` (the witness type "
                        "is inferred from the left side) — annotate "
                        "it: `for some (" + arm.witnessName + " : T)`");
                }
                ExpressionPointer lhsKernel = elaborateExpression(
                    *binary->left, localBinders);
                ExpressionPointer lhsTypeOpened =
                    inferTypeInLocalContext(localBinders, lhsKernel);
                witnessT = closeOverLocalBinders(
                    lhsTypeOpened, localBinders, localBinders.size());
            }
            LevelPointer witnessLevel;
            {
                ExpressionPointer tSort = weakHeadNormalForm(
                    environment_,
                    inferTypeInLocalContext(localBinders, witnessT));
                auto* sort = std::get_if<Sort>(&tSort->node);
                if (!sort) {
                    throwElaborate(
                        "`for some " + arm.witnessName + "`: cannot "
                        "determine the witness type's universe");
                }
                witnessLevel = predecessorOfSortLevel(sort->level);
            }
            std::vector<LocalBinder> withWitness = localBinders;
            withWitness.push_back({arm.witnessName, witnessT});
            ExpressionPointer equationClosed = elaborateExpression(
                *arm.disjunctType, withWitness);
            ExpressionPointer predicate = makeLambda(
                arm.witnessName, witnessT, equationClosed);
            ExpressionPointer existsDisjunct = makeApplication(
                makeApplication(
                    makeConstant("Exists", {witnessLevel}), witnessT),
                predicate);
            disjuncts.push_back(std::move(existsDisjunct));
            witnessTypes[i] = std::move(witnessT);
            witnessEquations[i] = std::move(equationClosed);
            witnessLevels[i] = std::move(witnessLevel);
        }
        auto makeOr = [&](ExpressionPointer a, ExpressionPointer b) {
            return makeApplication(
                makeApplication(makeConstant("Or", {}), a), b);
        };
        // statedDisjunction[i] = Pᵢ ∨ … ∨ Pₖ₋₁ over the STATED cases only —
        // the proposition whose excluded middle covers an `otherwise`.
        std::vector<ExpressionPointer> statedDisjunction(statedCount);
        statedDisjunction[statedCount - 1] = disjuncts[statedCount - 1];
        for (int i = static_cast<int>(statedCount) - 2; i >= 0; --i) {
            statedDisjunction[i] =
                makeOr(disjuncts[i], statedDisjunction[i + 1]);
        }
        ExpressionPointer complement;
        if (hasOtherwise) {
            complement = makeApplication(
                makeConstant("Not", {}), statedDisjunction[0]);
            disjuncts.push_back(complement);
        }
        // Right-nested disjunction `Or` (a non-polymorphic Proposition):
        // restDisjunction[i] = Pᵢ ∨ Pᵢ₊₁ ∨ … ∨ Pₙ₋₁, so restDisjunction[0]
        // is the whole `P₀ ∨ … ∨ Pₙ₋₁` the cases must cover.
        std::vector<ExpressionPointer> restDisjunction(armCount);
        restDisjunction[armCount - 1] = disjuncts[armCount - 1];
        for (int i = static_cast<int>(armCount) - 2; i >= 0; --i) {
            restDisjunction[i] = makeOr(disjuncts[i], restDisjunction[i + 1]);
        }
        ExpressionPointer expectedDisjunction = restDisjunction[0];

        ExpressionPointer disjProof;
        if (hasOtherwise) {
            // Exhaustiveness by construction: excluded middle on the
            // stated disjunction Q gives Q ∨ ¬Q; map the left leg into
            // the (right-nested) target by injecting each stated case at
            // its position, and the ¬Q leg to the final `otherwise` slot.
            // No prover involvement, so `otherwise` never fails to cover.
            if (!environment_.lookup("Logic.excluded_middle")) {
                throwElaborate(
                    "`otherwise:` needs `Logic.excluded_middle` in scope "
                    "(import axioms) to split on the stated cases");
            }
            const size_t k = statedCount;
            ExpressionPointer statedQ = statedDisjunction[0];
            auto inject = [&](const char* constructor,
                              ExpressionPointer left,
                              ExpressionPointer right,
                              ExpressionPointer value) {
                return makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant(constructor, {}), std::move(left)),
                        std::move(right)),
                    std::move(value));
            };
            // mapStated(i, lift): (Pᵢ ∨ … ∨ Pₖ₋₁) → (Pᵢ ∨ … ∨ Pₖ₋₁ ∨ ¬Q),
            // built `lift` binders deep inside the surrounding term.
            std::function<ExpressionPointer(size_t, int)> mapStated =
                [&](size_t i, int lift) -> ExpressionPointer {
                    ExpressionPointer domain =
                        liftBoundVariables(statedDisjunction[i], lift, 0);
                    int inner = lift + 1;
                    ExpressionPointer body;
                    if (i + 1 == k) {
                        // The last stated case: Pₖ₋₁ ↦ Pₖ₋₁ ∨ ¬Q, left leg.
                        body = inject(
                            "Or.introduceLeft",
                            liftBoundVariables(disjuncts[i], inner, 0),
                            liftBoundVariables(complement, inner, 0),
                            makeBoundVariable(0));
                    } else {
                        ExpressionPointer handleLeft = makeLambda(
                            "_stated_case",
                            liftBoundVariables(disjuncts[i], inner, 0),
                            inject(
                                "Or.introduceLeft",
                                liftBoundVariables(disjuncts[i], inner + 1, 0),
                                liftBoundVariables(
                                    restDisjunction[i + 1], inner + 1, 0),
                                makeBoundVariable(0)));
                        ExpressionPointer handleRight = makeLambda(
                            "_stated_rest",
                            liftBoundVariables(
                                statedDisjunction[i + 1], inner, 0),
                            inject(
                                "Or.introduceRight",
                                liftBoundVariables(disjuncts[i], inner + 1, 0),
                                liftBoundVariables(
                                    restDisjunction[i + 1], inner + 1, 0),
                                makeApplication(
                                    mapStated(i + 1, inner + 1),
                                    makeBoundVariable(0))));
                        ExpressionPointer call =
                            makeConstant("Or.eliminate", {});
                        call = makeApplication(call,
                            liftBoundVariables(disjuncts[i], inner, 0));
                        call = makeApplication(call,
                            liftBoundVariables(
                                statedDisjunction[i + 1], inner, 0));
                        call = makeApplication(call,
                            liftBoundVariables(restDisjunction[i], inner, 0));
                        call = makeApplication(call, std::move(handleLeft));
                        call = makeApplication(call, std::move(handleRight));
                        call = makeApplication(call, makeBoundVariable(0));
                        body = std::move(call);
                    }
                    return makeLambda("_stated", domain, body);
                };
            // ¬Q ↦ the last slot of the target disjunction.
            ExpressionPointer complementBody = makeBoundVariable(0);
            for (int i = static_cast<int>(k) - 1; i >= 0; --i) {
                complementBody = inject(
                    "Or.introduceRight",
                    liftBoundVariables(disjuncts[i], 1, 0),
                    liftBoundVariables(restDisjunction[i + 1], 1, 0),
                    std::move(complementBody));
            }
            ExpressionPointer mapComplement = makeLambda(
                "_complement", complement, std::move(complementBody));
            ExpressionPointer excludedMiddle = makeApplication(
                makeConstant("Logic.excluded_middle", {}), statedQ);
            ExpressionPointer split = makeConstant("Or.eliminate", {});
            split = makeApplication(split, statedQ);
            split = makeApplication(split, complement);
            split = makeApplication(split, expectedDisjunction);
            split = makeApplication(split, mapStated(0, 0));
            split = makeApplication(split, std::move(mapComplement));
            split = makeApplication(split, std::move(excludedMiddle));
            disjProof = std::move(split);
        } else {
            // Find OR synthesize the disjunction via the unified hammer
            // dispatch. This is the same "find or synthesize" function
            // bare `claim P;` uses — local hypothesis match, library
            // scan, transitivity, the lot. If nothing in scope proves
            // the disjunction, the dispatch error message (wrapped by
            // the Frame above) tells the user exactly what failed.
            try {
                disjProof = autoProveClaim(
                    expectedDisjunction, localBinders, line);
            } catch (const ElaborateError&) {
                throwElaborate(
                    "couldn't automatically prove `"
                    + prettyPrintInLocalScope(
                          expectedDisjunction, localBinders)
                    + "` to finish off `by cases` — either bring that "
                    "disjunction into scope explicitly (`claim <P₀> ∨ … ∨ "
                    "<Pₙ₋₁> by …;`), or check that the cases really do "
                    "cover the goal");
            }
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
            if (!arm.witnessName.empty()) {
                // `case P for some k:` — the hypothesis is ∃ k. P; open
                // it so the body sees BOTH the witness `k` and the
                // equation. Body elaborates under localBinders + [k]
                // + [equation]; the assembled arm is
                //   λ (h : ∃ k. P).
                //     Exists.eliminate(T, λk. P, Goal, λ k eq. body, h).
                // `as h` names the EQUATION hypothesis (the witness has
                // its own name; the ∃ itself is consumed on the spot).
                ExpressionPointer witnessT = witnessTypes[index];
                ExpressionPointer equation = witnessEquations[index];
                std::string equationName = arm.binderName.empty()
                    ? "_case_equation" : arm.binderName;
                std::vector<LocalBinder> innerBinders = localBinders;
                innerBinders.push_back({arm.witnessName, witnessT});
                innerBinders.push_back({equationName, equation});
                ExpressionPointer goalLiftedTwo =
                    liftBoundVariables(goalClosed, 2, 0);
                Frame armFrame(*this,
                    "`by cases` arm at line " + std::to_string(arm.line),
                    innerBinders, goalLiftedTwo, arm.line, arm.column);
                ExpressionPointer body = elaborateExpression(
                    *arm.body, innerBinders, goalLiftedTwo);
                body = coerceToExpectedTypeViaDiff(
                    innerBinders, body, goalLiftedTwo);
                // Reposition under the ∃-hypothesis binder `h`, which
                // sits between the locals and (k, equation): the locals'
                // indices shift by one, k and the equation keep theirs.
                ExpressionPointer bodyShifted =
                    liftBoundVariables(body, 1, 2);
                ExpressionPointer equationShifted =
                    liftBoundVariables(equation, 1, 1);
                ExpressionPointer typeShifted =
                    liftBoundVariables(witnessT, 1, 0);
                ExpressionPointer handler = makeLambda(
                    arm.witnessName, typeShifted,
                    makeLambda(equationName, equationShifted,
                               std::move(bodyShifted)));
                ExpressionPointer predicateShifted = makeLambda(
                    arm.witnessName, typeShifted, equationShifted);
                ExpressionPointer call = makeConstant(
                    "Exists.eliminate", {witnessLevels[index]});
                call = makeApplication(call, typeShifted);
                call = makeApplication(call, predicateShifted);
                call = makeApplication(call, goalLifted);
                call = makeApplication(call, std::move(handler));
                call = makeApplication(call, makeBoundVariable(0));
                return makeLambda(
                    "_disjunct_hypothesis", domain, std::move(call));
            }
            std::string binderName = arm.binderName.empty()
                ? "_disjunct_hypothesis" : arm.binderName;
            std::vector<LocalBinder> extendedBinders = localBinders;
            extendedBinders.push_back({binderName, domain});
            // Frame anchors any error in this arm at the arm's own position,
            // not at the enclosing eliminator (the misleading "case for
            // 'Exists.introduce'" / wrong-line report otherwise).
            Frame armFrame(*this,
                "`by cases` arm at line " + std::to_string(arm.line),
                extendedBinders, goalLifted, arm.line, arm.column);
            ExpressionPointer body = elaborateExpression(
                *arm.body, extendedBinders, goalLifted);
            // Coerce the arm body to the goal, exactly as a lambda body or a
            // `cases` arm is coerced. This lets an arm state a proof of one
            // DISJUNCT (`calc n = … = 0`) and have the disjunction-injection
            // coercion wrap the matching `Or.introduce*` — consistent with
            // `cases` arms, instead of demanding an explicit `Or.introduceLeft`.
            body = coerceToExpectedTypeViaDiff(
                extendedBinders, body, goalLifted);
            // If the (coerced) body still doesn't prove the goal, report it
            // here, at the arm, with a math-shaped message — rather than
            // letting the mismatch surface later as a kernel Pi-domain error
            // pinned to the surrounding `obtain`/eliminator.
            try {
                ExpressionPointer bodyTypeOpened =
                    inferTypeInLocalContext(extendedBinders, body);
                ExpressionPointer goalOpened = openOverLocalBinders(
                    goalLifted, extendedBinders, extendedBinders.size());
                if (!isDefinitionallyEqual(
                        environment_,
                        buildContextFromLocalBinders(extendedBinders),
                        bodyTypeOpened, goalOpened)) {
                    ExpressionPointer bodyTypeClosed = closeOverLocalBinders(
                        bodyTypeOpened, extendedBinders, extendedBinders.size());
                    throwElaborate(
                        "this `by cases` arm must prove the goal\n      "
                        + prettyPrintInLocalScope(goalLifted, extendedBinders)
                        + "\n  but its body proves\n      "
                        + prettyPrintInLocalScope(bodyTypeClosed, extendedBinders)
                        + "\n  — if that is meant to be one side of the "
                        "disjunction, make sure it matches a disjunct exactly "
                        "(it is then wrapped automatically); otherwise this "
                        "case does not close the goal");
                }
            } catch (const TypeError&) {
                // Body isn't well-typed on its own — let the normal flow
                // surface that error.
            }
            warnIfBinderUnused(
                arm.binderName, body, arm.line, arm.column,
                "`case ... as`");
            return makeLambda(binderName, domain, body);
        };
        // Fold the arms into nested `Or.eliminate` calls. Define
        //   eliminator(i) : (Pᵢ ∨ … ∨ Pₙ₋₁) → Goal
        //     eliminator(n-1) = armLambda(n-1)
        //     eliminator(i)   = λ (tail : Pᵢ ∨ rest).
        //                         Or.eliminate(Pᵢ, rest, Goal,
        //                                      armLambda(i), eliminator(i+1),
        //                                      tail)
        // The top-level call feeds the proved disjunction directly. For two
        // arms this is exactly `Or.eliminate(P₀, P₁, Goal, arm₀, arm₁, proof)`.
        std::function<ExpressionPointer(size_t)> eliminator =
            [&](size_t i) -> ExpressionPointer {
                if (i + 1 == armCount) {
                    return buildArmLambda(i, disjuncts[i]);
                }
                ExpressionPointer armLambda = buildArmLambda(i, disjuncts[i]);
                ExpressionPointer restEliminator = eliminator(i + 1);
                // Inside the new `tail` binder (de Bruijn 0), the closed
                // sub-terms shift up by one.
                auto lift = [](const ExpressionPointer& e) {
                    return liftBoundVariables(e, 1, 0);
                };
                ExpressionPointer body = makeConstant("Or.eliminate", {});
                body = makeApplication(body, lift(disjuncts[i]));
                body = makeApplication(body, lift(restDisjunction[i + 1]));
                body = makeApplication(body, lift(goalClosed));
                body = makeApplication(body, lift(armLambda));
                body = makeApplication(body, lift(restEliminator));
                body = makeApplication(body, makeBoundVariable(0));
                return makeLambda(
                    "_disjunction_tail", restDisjunction[i], body);
            };
        ExpressionPointer call = makeConstant("Or.eliminate", {});
        call = makeApplication(call, disjuncts[0]);
        call = makeApplication(call, restDisjunction[1]);
        call = makeApplication(call, goalClosed);
        call = makeApplication(call, buildArmLambda(0, disjuncts[0]));
        call = makeApplication(call, eliminator(1));
        call = makeApplication(call, disjProof);
        return call;
    }

