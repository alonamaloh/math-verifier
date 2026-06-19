// src/elaborator/group.cpp
//
// The `group` / `monoid` decision tactic. Closes an `=` goal over an
// abstract group or monoid by normalising both sides to a canonical word
// (a flattened non-commutative product — the same canonical form a
// non-commutative ring monomial uses) and, for groups, cancelling adjacent
// inverses and dropping identity. If both sides reduce to the same word the
// goal holds, and we emit the chain `L = canon = R` built from the
// structure's associativity / identity / inverse axioms (so the kernel
// rechecks an explicit proof — the trusted base stays the kernel).
//
// The structure (operation / identity / inverse / axiom proof) is found from
// an in-scope `IsGroup` / `IsMonoid` hypothesis; the axioms are cited through
// the `IsGroup.*` / `IsMonoid.*` accessor lemmas.

#include "elaborator/internal.hpp"

namespace {

// A signed generator in a group word: `term` is the underlying atom, and
// `inverted` flags `atom⁻¹`. Two atoms cancel when they share a term and
// differ in sign.
struct GroupAtom {
    ExpressionPointer term;
    bool inverted;
};

// A normalisation result: the reduced word, its canonical term
// (= wordToTerm(word)), and a proof `original = term`.
struct GroupNorm {
    std::vector<GroupAtom> word;
    ExpressionPointer term;
    ExpressionPointer proof;
};

// The detected algebraic structure plus how to cite its axioms.
struct GroupScheme {
    ExpressionPointer operation;   // the binary op expression
    ExpressionPointer identity;    // the identity element
    ExpressionPointer inverse;     // inverse op, or null (monoid / no cancel)
    ExpressionPointer carrierType; // opened carrier type
    LevelPointer carrierLevel;
    std::vector<ExpressionPointer> bundlePrefix;  // args before x,y,z
    std::string associativityName;
    std::string identityLeftName;
    std::string identityRightName;
    std::string inverseLeftName;   // only meaningful when inverse != null
    std::string inverseRightName;
};

}  // namespace

ExpressionPointer Elaborator::proveGroupEquality(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        bool allowInverses, int line) {
    if (!expectedType) return nullptr;
    expectedType = zetaUnfoldLetBinders(expectedType, localBinders);

    // The goal must be an equality.
    {
        ExpressionPointer goalWhnf =
            weakHeadNormalForm(environment_, expectedType);
        ExpressionPointer head = goalWhnf;
        int depth = 0;
        while (auto* app = std::get_if<Application>(&head->node)) {
            head = app->function;
            ++depth;
        }
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant || constant->name != "Equality" || depth < 3) {
            return nullptr;
        }
    }
    EqualityComponents goal =
        extractEqualityComponents(expectedType, "group", line);

    size_t binderCount = localBinders.size();
    ExpressionPointer carrierOpened =
        openOverLocalBinders(goal.carrierType, localBinders, binderCount);
    ExpressionPointer leftOpened =
        openOverLocalBinders(goal.leftEndpoint, localBinders, binderCount);
    ExpressionPointer rightOpened =
        openOverLocalBinders(goal.rightEndpoint, localBinders, binderCount);
    LevelPointer level = goal.carrierUniverseLevel;
    Context context = buildContextFromLocalBinders(localBinders);

    // ---- Structure detection: find an in-scope IsGroup / IsMonoid proof
    // whose carrier matches the goal's. Prefer IsGroup (carries inverses).
    GroupScheme scheme;
    bool found = false;
    bool foundIsGroup = false;
    for (size_t i = 0; i < binderCount; ++i) {
        // Peel the binder's STATED type without normalising: `IsGroup` /
        // `IsMonoid` are transparent definitions, so a whnf would unfold the
        // head to its conjunction body and hide the structure name.
        ExpressionPointer btype =
            openOverLocalBinders(localBinders[i].type, localBinders, i);
        ExpressionPointer head;
        std::vector<ExpressionPointer> args;
        peelSpine(btype, head, args);
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant) continue;
        const bool isGroupHyp =
            constant->name == "IsGroup" && args.size() == 4;
        const bool isMonoidHyp =
            constant->name == "IsMonoid" && args.size() == 3;
        if (!isGroupHyp && !isMonoidHyp) continue;
        // Carrier must match the goal's.
        if (!isDefinitionallyEqual(
                environment_, context, args[0], carrierOpened)) {
            continue;
        }
        // Already have an IsGroup proof and this is only a monoid: keep the
        // stronger one.
        if (found && foundIsGroup && !isGroupHyp) continue;
        ExpressionPointer proofTerm =
            openedLocalBinderReference(localBinders, i);
        scheme.carrierType = carrierOpened;
        scheme.carrierLevel = level;
        scheme.operation = args[1];
        scheme.identity = args[2];
        if (isGroupHyp) {
            scheme.inverse = args[3];
            scheme.bundlePrefix = {args[0], args[1], args[2], args[3],
                                   proofTerm};
            scheme.associativityName = "IsGroup.associativity";
            scheme.identityLeftName = "IsGroup.identity_left";
            scheme.identityRightName = "IsGroup.identity_right";
            scheme.inverseLeftName = "IsGroup.inverse_left";
            scheme.inverseRightName = "IsGroup.inverse_right";
            foundIsGroup = true;
        } else {
            scheme.inverse = nullptr;
            scheme.bundlePrefix = {args[0], args[1], args[2], proofTerm};
            scheme.associativityName = "IsMonoid.associativity";
            scheme.identityLeftName = "IsMonoid.identity_left";
            scheme.identityRightName = "IsMonoid.identity_right";
        }
        found = true;
        if (isGroupHyp) break;  // can't do better
    }
    if (!found) return nullptr;
    // `group` (cancellation) needs an inverse, i.e. an IsGroup proof.
    const bool cancelInverses = allowInverses && scheme.inverse != nullptr;
    if (allowInverses && !cancelInverses) return nullptr;
    // The accessor lemmas must be in scope.
    for (const std::string& name :
            {scheme.associativityName, scheme.identityLeftName,
             scheme.identityRightName}) {
        if (environment_.lookup(name) == nullptr) return nullptr;
    }
    if (cancelInverses
        && (environment_.lookup(scheme.inverseLeftName) == nullptr
            || environment_.lookup(scheme.inverseRightName) == nullptr)) {
        return nullptr;
    }
    // For a monoid (no cancellation) inverses are opaque atoms.
    ExpressionPointer effectiveInverse =
        cancelInverses ? scheme.inverse : nullptr;

    ExpressionPointer carrier = scheme.carrierType;

    // ---- term builders -------------------------------------------------
    auto buildOp = [&](ExpressionPointer A,
                       ExpressionPointer B) -> ExpressionPointer {
        return makeApplication(makeApplication(scheme.operation, A), B);
    };
    auto atomTerm = [&](const GroupAtom& a) -> ExpressionPointer {
        if (a.inverted) return makeApplication(scheme.inverse, a.term);
        return a.term;
    };
    std::function<ExpressionPointer(const std::vector<GroupAtom>&, size_t)>
        wordToTermFrom =
            [&](const std::vector<GroupAtom>& w, size_t i) -> ExpressionPointer {
        if (i >= w.size()) return scheme.identity;
        if (i + 1 == w.size()) return atomTerm(w[i]);
        return buildOp(atomTerm(w[i]), wordToTermFrom(w, i + 1));
    };
    auto wordToTerm = [&](const std::vector<GroupAtom>& w) -> ExpressionPointer {
        return wordToTermFrom(w, 0);
    };
    auto applyAccessor = [&](const std::string& name,
                             const std::vector<ExpressionPointer>& extra)
        -> ExpressionPointer {
        ExpressionPointer e = makeConstant(name);
        for (const auto& a : scheme.bundlePrefix) e = makeApplication(e, a);
        for (const auto& a : extra) e = makeApplication(e, a);
        return e;
    };
    auto refl = [&](ExpressionPointer e) -> ExpressionPointer {
        return buildReflexivity(level, carrier, e);
    };

    // op(A,B) = op(A',B') from proofA : A=A', proofB : B=B' (abstract op).
    auto opCongruence = [&](ExpressionPointer A, ExpressionPointer Ap,
                            ExpressionPointer pA, ExpressionPointer B,
                            ExpressionPointer Bp, ExpressionPointer pB)
        -> ExpressionPointer {
        ExpressionPointer opLift = liftBoundVariables(scheme.operation, 1, 0);
        ExpressionPointer Blift = liftBoundVariables(B, 1, 0);
        ExpressionPointer body1 = makeApplication(
            makeApplication(opLift, makeBoundVariable(0)), Blift);
        ExpressionPointer lambda1 = makeLambda("_g", carrier, body1);
        ExpressionPointer step1 = buildEqualityCongruenceSameCarrier(
            level, carrier, lambda1, A, Ap, pA);
        ExpressionPointer Aplift = liftBoundVariables(Ap, 1, 0);
        ExpressionPointer body2 = makeApplication(
            makeApplication(opLift, Aplift), makeBoundVariable(0));
        ExpressionPointer lambda2 = makeLambda("_g", carrier, body2);
        ExpressionPointer step2 = buildEqualityCongruenceSameCarrier(
            level, carrier, lambda2, B, Bp, pB);
        return buildEqualityTransitivity(
            level, carrier, buildOp(A, B), buildOp(Ap, B), buildOp(Ap, Bp),
            step1, step2);
    };
    auto trans = [&](ExpressionPointer A, ExpressionPointer B,
                     ExpressionPointer C, ExpressionPointer p1,
                     ExpressionPointer p2) -> ExpressionPointer {
        return buildEqualityTransitivity(level, carrier, A, B, C, p1, p2);
    };

    // ---- matchers ------------------------------------------------------
    auto sameTerm = [&](ExpressionPointer a, ExpressionPointer b) -> bool {
        return structurallyEqual(a, b);
    };
    auto matchOp = [&](ExpressionPointer e, ExpressionPointer& a,
                       ExpressionPointer& b) -> bool {
        auto* outer = std::get_if<Application>(&e->node);
        if (!outer) return false;
        auto* inner = std::get_if<Application>(&outer->function->node);
        if (!inner) return false;
        if (!sameTerm(inner->function, scheme.operation)) return false;
        a = inner->argument;
        b = outer->argument;
        return true;
    };
    auto matchInverse = [&](ExpressionPointer e,
                            ExpressionPointer& x) -> bool {
        if (!effectiveInverse) return false;
        auto* app = std::get_if<Application>(&e->node);
        if (!app) return false;
        if (!sameTerm(app->function, effectiveInverse)) return false;
        x = app->argument;
        return true;
    };
    auto isIdentity = [&](ExpressionPointer e) -> bool {
        return sameTerm(e, scheme.identity);
    };
    auto cancels = [&](const GroupAtom& s, const GroupAtom& h) -> bool {
        return sameTerm(s.term, h.term) && s.inverted != h.inverted;
    };

    // ---- concat: op(termA, termB) = canonical(reduce(wordA ++ wordB)) ---
    // Returns the combined reduced word, its term, and the proof of the
    // above equality. Cancellation happens at the junction (and cascades
    // via the recursion).
    std::function<GroupNorm(const std::vector<GroupAtom>&, ExpressionPointer,
                            const std::vector<GroupAtom>&, ExpressionPointer)>
        concat = [&](const std::vector<GroupAtom>& wordA, ExpressionPointer termA,
                     const std::vector<GroupAtom>& wordB,
                     ExpressionPointer termB) -> GroupNorm {
        if (wordA.empty()) {
            // op(identity, termB) = termB
            return {wordB, termB,
                    applyAccessor(scheme.identityLeftName, {termB})};
        }
        if (wordB.empty()) {
            // op(termA, identity) = termA
            return {wordA, termA,
                    applyAccessor(scheme.identityRightName, {termA})};
        }
        if (wordA.size() == 1) {
            const GroupAtom& s = wordA[0];
            ExpressionPointer sTerm = termA;  // = atomTerm(s)
            const GroupAtom& h = wordB[0];
            if (cancelInverses && cancels(s, h)) {
                // op(s,h) = identity by inverse_{right if s positive}.
                ExpressionPointer cancelProof = s.inverted
                    ? applyAccessor(scheme.inverseLeftName, {s.term})
                    : applyAccessor(scheme.inverseRightName, {s.term});
                std::vector<GroupAtom> restB(wordB.begin() + 1, wordB.end());
                ExpressionPointer hTerm = atomTerm(h);
                if (restB.empty()) {
                    // op(sTerm, hTerm) = identity
                    return {{}, scheme.identity, cancelProof};
                }
                ExpressionPointer restBTerm = wordToTerm(restB);
                // op(sTerm, op(hTerm, restBTerm))
                //   = op(op(sTerm,hTerm), restBTerm)   [reversed assoc]
                ExpressionPointer assocFwd = applyAccessor(
                    scheme.associativityName, {sTerm, hTerm, restBTerm});
                ExpressionPointer revAssoc = buildEqualitySymmetry(
                    level, carrier,
                    buildOp(buildOp(sTerm, hTerm), restBTerm),
                    buildOp(sTerm, buildOp(hTerm, restBTerm)), assocFwd);
                //   = op(identity, restBTerm)   [cong: op(sTerm,hTerm)=identity]
                ExpressionPointer cong = opCongruence(
                    buildOp(sTerm, hTerm), scheme.identity, cancelProof,
                    restBTerm, restBTerm, refl(restBTerm));
                //   = restBTerm   [identity_left]
                ExpressionPointer idl =
                    applyAccessor(scheme.identityLeftName, {restBTerm});
                ExpressionPointer p1 = trans(
                    buildOp(sTerm, termB),
                    buildOp(buildOp(sTerm, hTerm), restBTerm),
                    buildOp(scheme.identity, restBTerm), revAssoc, cong);
                ExpressionPointer proof = trans(
                    buildOp(sTerm, termB),
                    buildOp(scheme.identity, restBTerm), restBTerm, p1, idl);
                return {restB, restBTerm, proof};
            }
            // No cancellation: op(sTerm, termB) is already canonical.
            std::vector<GroupAtom> w;
            w.push_back(s);
            w.insert(w.end(), wordB.begin(), wordB.end());
            ExpressionPointer t = buildOp(sTerm, termB);
            return {w, t, refl(t)};
        }
        // wordA.size() >= 2: peel the head, reassociate, recurse.
        GroupAtom s1 = wordA[0];
        ExpressionPointer s1Term = atomTerm(s1);
        std::vector<GroupAtom> restA(wordA.begin() + 1, wordA.end());
        ExpressionPointer restATerm = wordToTerm(restA);
        // op(op(s1,restA), termB) = op(s1, op(restA, termB))   [assoc]
        ExpressionPointer assocP = applyAccessor(
            scheme.associativityName, {s1Term, restATerm, termB});
        GroupNorm inner = concat(restA, restATerm, wordB, termB);
        // op(s1, op(restA,termB)) = op(s1, inner.term)   [cong right]
        ExpressionPointer congR = opCongruence(
            s1Term, s1Term, refl(s1Term),
            buildOp(restATerm, termB), inner.term, inner.proof);
        // prepend s1 to inner.word (may cancel with its head)
        std::vector<GroupAtom> single{s1};
        GroupNorm prep = concat(single, s1Term, inner.word, inner.term);
        ExpressionPointer p1 = trans(
            buildOp(termA, termB), buildOp(s1Term, buildOp(restATerm, termB)),
            buildOp(s1Term, inner.term), assocP, congR);
        ExpressionPointer proof = trans(
            buildOp(termA, termB), buildOp(s1Term, inner.term), prep.term,
            p1, prep.proof);
        return {prep.word, prep.term, proof};
    };

    // inverse(A) = inverse(A') from proofA : A = A'.
    auto inverseCongruence = [&](ExpressionPointer A, ExpressionPointer Ap,
                                 ExpressionPointer pA) -> ExpressionPointer {
        ExpressionPointer invLift = liftBoundVariables(scheme.inverse, 1, 0);
        ExpressionPointer body =
            makeApplication(invLift, makeBoundVariable(0));
        ExpressionPointer lambda = makeLambda("_g", carrier, body);
        return buildEqualityCongruenceSameCarrier(
            level, carrier, lambda, A, Ap, pA);
    };

    // Push an inverse inward (de Morgan for groups): given P = wordToTerm(W)
    // with W reduced, produce the reduced inverse word (reverse + flip
    // signs), its term Q, and a proof `inverse(P) = Q` built from the group
    // axioms only. Proof = the right-inverse-uniqueness template
    //   Q = id·Q = (P⁻¹·P)·Q = P⁻¹·(P·Q) = P⁻¹·id = P⁻¹
    // where `P·Q = id` is exactly what `concat(W, invertedW)` proves.
    auto pushInverse = [&](const std::vector<GroupAtom>& W,
                           ExpressionPointer P) -> GroupNorm {
        std::vector<GroupAtom> inv;
        for (auto it = W.rbegin(); it != W.rend(); ++it) {
            inv.push_back(GroupAtom{it->term, !it->inverted});
        }
        ExpressionPointer Q = wordToTerm(inv);
        ExpressionPointer Pinv = makeApplication(scheme.inverse, P);
        GroupNorm hc = concat(W, P, inv, Q);  // hc.proof : op(P,Q) = identity
        ExpressionPointer H = hc.proof;
        ExpressionPointer idQ =
            applyAccessor(scheme.identityLeftName, {Q});       // id·Q = Q
        ExpressionPointer sa = buildEqualitySymmetry(
            level, carrier, buildOp(scheme.identity, Q), Q, idQ);  // Q = id·Q
        ExpressionPointer invLeftP =
            applyAccessor(scheme.inverseLeftName, {P});        // P⁻¹·P = id
        ExpressionPointer idEq = buildEqualitySymmetry(
            level, carrier, buildOp(Pinv, P), scheme.identity, invLeftP);
        ExpressionPointer sb = opCongruence(
            scheme.identity, buildOp(Pinv, P), idEq, Q, Q, refl(Q));
        ExpressionPointer sc =
            applyAccessor(scheme.associativityName, {Pinv, P, Q});
        ExpressionPointer sd = opCongruence(
            Pinv, Pinv, refl(Pinv), buildOp(P, Q), scheme.identity, H);
        ExpressionPointer se =
            applyAccessor(scheme.identityRightName, {Pinv});
        ExpressionPointer t1 = trans(
            Q, buildOp(scheme.identity, Q), buildOp(buildOp(Pinv, P), Q),
            sa, sb);
        ExpressionPointer t2 = trans(
            Q, buildOp(buildOp(Pinv, P), Q), buildOp(Pinv, buildOp(P, Q)),
            t1, sc);
        ExpressionPointer t3 = trans(
            Q, buildOp(Pinv, buildOp(P, Q)), buildOp(Pinv, scheme.identity),
            t2, sd);
        ExpressionPointer QeqPinv = trans(
            Q, buildOp(Pinv, scheme.identity), Pinv, t3, se);  // Q = P⁻¹
        ExpressionPointer proof = buildEqualitySymmetry(
            level, carrier, Q, Pinv, QeqPinv);                 // P⁻¹ = Q
        return {inv, Q, proof};
    };

    // ---- normalize: e = canonical reduced word, with proof -------------
    std::function<GroupNorm(ExpressionPointer)> normalize =
        [&](ExpressionPointer e) -> GroupNorm {
        if (isIdentity(e)) {
            return {{}, e, refl(e)};
        }
        ExpressionPointer invArg;
        if (matchInverse(e, invArg)) {
            ExpressionPointer a2, b2, innerInv;
            if (matchOp(invArg, a2, b2) || matchInverse(invArg, innerInv)
                || isIdentity(invArg)) {
                // inverse of a compound: normalise the body, then push the
                // inverse inward — `(x·y)⁻¹ = y⁻¹·x⁻¹`, `(x⁻¹)⁻¹ = x`,
                // `identity⁻¹ = identity` — from the axioms alone.
                GroupNorm ne = normalize(invArg);
                ExpressionPointer congInv =
                    inverseCongruence(invArg, ne.term, ne.proof);
                GroupNorm pushed = pushInverse(ne.word, ne.term);
                ExpressionPointer proof = trans(
                    e, makeApplication(scheme.inverse, ne.term), pushed.term,
                    congInv, pushed.proof);
                return {pushed.word, pushed.term, proof};
            }
            return {{GroupAtom{invArg, true}}, e, refl(e)};
        }
        ExpressionPointer a, b;
        if (matchOp(e, a, b)) {
            GroupNorm na = normalize(a);
            GroupNorm nb = normalize(b);
            ExpressionPointer cong = opCongruence(
                a, na.term, na.proof, b, nb.term, nb.proof);
            GroupNorm cc = concat(na.word, na.term, nb.word, nb.term);
            ExpressionPointer proof = trans(
                e, buildOp(na.term, nb.term), cc.term, cong, cc.proof);
            return {cc.word, cc.term, proof};
        }
        // opaque atom
        return {{GroupAtom{e, false}}, e, refl(e)};
    };

    GroupNorm nL = normalize(leftOpened);
    GroupNorm nR = normalize(rightOpened);

    // Words must match (⇒ canonical terms are structurally identical).
    if (nL.word.size() != nR.word.size()) return nullptr;
    for (size_t i = 0; i < nL.word.size(); ++i) {
        if (nL.word[i].inverted != nR.word[i].inverted
            || !structurallyEqual(nL.word[i].term, nR.word[i].term)) {
            return nullptr;
        }
    }

    // L = nL.term = nR.term = R
    ExpressionPointer symR = buildEqualitySymmetry(
        level, carrier, rightOpened, nR.term, nR.proof);
    ExpressionPointer result = trans(
        leftOpened, nL.term, rightOpened, nL.proof, symR);
    (void)foundIsGroup;
    return closeOverLocalBinders(result, localBinders, binderCount);
}

ExpressionPointer Elaborator::elaborateGroup(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column, bool allowInverses) {
    Frame frame(*this,
                std::string(allowInverses ? "group" : "monoid")
                    + " at line " + std::to_string(line),
                localBinders, expectedType, line, column);
    if (!expectedType) {
        throwElaborate(
            std::string("`") + (allowInverses ? "group" : "monoid")
            + "` needs an expected type from context — use it in a calc "
              "step or as the body of a theorem with a declared equality "
              "conclusion");
    }
    ExpressionPointer proof =
        proveGroupEquality(localBinders, expectedType, allowInverses, line);
    if (proof) return proof;
    throwElaborate(
        std::string("`") + (allowInverses ? "group" : "monoid")
        + "` could not close this goal. It proves `=` goals over an abstract "
          + (allowInverses ? "group" : "monoid")
          + " (found from an in-scope `"
          + (allowInverses ? "IsGroup" : "IsMonoid/IsGroup")
          + "` hypothesis) by flattening associativity"
          + (allowInverses ? ", cancelling adjacent inverses," : "")
          + " and dropping identity — check the goal is such a rearrangement "
            "and the structure proof is in scope.");
}
