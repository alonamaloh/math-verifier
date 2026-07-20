// src/elaborator/module_normalise.cpp
//
// The `module` decision tactic: the free-module / vector-space normaliser.
// Closes an `=` goal over a `VectorSpace.carrier(V)` by normalising both sides
// to a canonical linear combination `Σ cᵢ • vᵢ` — each distinct vector is an
// opaque atom, `•` is distributed over `+`/`−` and pushed through nested
// scales, like vectors are collected by ADDING their field coefficients (the
// coefficient equalities discharged by the `ring` prover), and the canonical
// forms are compared atom-by-atom. If they agree the goal holds, and we emit an
// explicit chain `L = canon = R` built from the vector-space scale/group axioms
// (the kernel rechecks it — the trusted base stays the kernel).
//
// This is strictly stronger than the abelian `group` mode over the same
// carrier, which treats `a • v` as an opaque atom and so cannot collect
// `a • v + b • v` or distribute `a • (u + v)`.

#include "elaborator/internal.hpp"

namespace {

// One term of a linear combination: `coefficient • atom`, where `atom` is an
// opaque vector expression and `coefficient` is a field expression.
struct ModuleTerm {
    ExpressionPointer coefficient;
    ExpressionPointer atom;
};

// A normalisation result: the reduced word (a list of `cᵢ • atomᵢ` terms), its
// canonical term (= wordToTerm(word)), and a proof `original = term`.
struct ModuleNorm {
    std::vector<ModuleTerm> word;
    ExpressionPointer term;
    ExpressionPointer proof;
};

}  // namespace

// The non-throwing core, shared with the calc-step auto-prover. Returns null
// when the tactic does not apply (carrier isn't a vector space, laws absent) or
// the two canonical forms disagree.
ExpressionPointer Elaborator::proveModuleEquality(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType, int line) {
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
        extractEqualityComponents(expectedType, "module", line);

    size_t binderCount = localBinders.size();
    ExpressionPointer carrierOpened =
        openOverLocalBinders(goal.carrierType, localBinders, binderCount);
    ExpressionPointer leftOpened =
        openOverLocalBinders(goal.leftEndpoint, localBinders, binderCount);
    ExpressionPointer rightOpened =
        openOverLocalBinders(goal.rightEndpoint, localBinders, binderCount);
    LevelPointer level = goal.carrierUniverseLevel;

    // Carrier must be `VectorSpace.carrier(f, V)`.
    ExpressionPointer carrierHead;
    std::vector<ExpressionPointer> carrierArgs;
    peelSpine(carrierOpened, carrierHead, carrierArgs);
    auto* carrierConstant = std::get_if<Constant>(&carrierHead->node);
    if (!carrierConstant || carrierConstant->name != "VectorSpace.carrier"
        || carrierArgs.size() != 2) {
        return nullptr;
    }
    // The scale/group laws the certificate cites must be in scope.
    for (const char* name :
            {"VectorSpace.scale_vector_add", "VectorSpace.scale_scalar_add",
             "VectorSpace.scale_scalar_multiply", "VectorSpace.one_scale",
             "VectorSpace.zero_scale", "VectorSpace.scale_zero",
             "VectorSpace.add_associative", "VectorSpace.add_commutative",
             "VectorSpace.zero_add", "VectorSpace.add_zero"}) {
        if (environment_.lookup(name) == nullptr) return nullptr;
    }

    ExpressionPointer f = carrierArgs[0];
    ExpressionPointer Vexp = carrierArgs[1];
    ExpressionPointer carrier = carrierOpened;
    ExpressionPointer fieldCarrier =
        makeApplication(makeConstant("Field.carrier"), f);

    // ---- term builders -------------------------------------------------
    auto vsOp = [&](const char* name) -> ExpressionPointer {
        return makeApplication(makeApplication(makeConstant(name), f), Vexp);
    };
    ExpressionPointer addOp = vsOp("VectorSpace.add");
    ExpressionPointer scaleOp = vsOp("VectorSpace.scale");
    ExpressionPointer negateOp = vsOp("VectorSpace.negate");
    ExpressionPointer vZero = vsOp("VectorSpace.zero");
    auto buildAdd = [&](ExpressionPointer A, ExpressionPointer B) {
        return makeApplication(makeApplication(addOp, A), B);
    };
    auto buildScale = [&](ExpressionPointer c, ExpressionPointer x) {
        return makeApplication(makeApplication(scaleOp, c), x);
    };
    // Field coefficient builders.
    ExpressionPointer fOne = makeApplication(makeConstant("Field.one"), f);
    ExpressionPointer fZero = makeApplication(makeConstant("Field.zero"), f);
    auto fAdd = [&](ExpressionPointer a, ExpressionPointer b) {
        return makeApplication(
            makeApplication(makeApplication(makeConstant("Field.add"), f), a), b);
    };
    auto fMul = [&](ExpressionPointer a, ExpressionPointer b) {
        return makeApplication(
            makeApplication(makeApplication(makeConstant("Field.multiply"), f), a),
            b);
    };
    // A vector-space scale/group law `Name(f, V, extra...)`.
    auto applyLaw = [&](const char* name,
                        const std::vector<ExpressionPointer>& extra)
        -> ExpressionPointer {
        ExpressionPointer e = makeApplication(
            makeApplication(makeConstant(name), f), Vexp);
        for (const auto& a : extra) e = makeApplication(e, a);
        return e;
    };
    auto refl = [&](ExpressionPointer e) {
        return buildReflexivity(level, carrier, e);
    };
    auto trans = [&](ExpressionPointer A, ExpressionPointer B, ExpressionPointer C,
                     ExpressionPointer p1, ExpressionPointer p2) {
        return buildEqualityTransitivity(level, carrier, A, B, C, p1, p2);
    };
    auto atomTerm = [&](const ModuleTerm& t) {
        return buildScale(t.coefficient, t.atom);
    };
    std::function<ExpressionPointer(const std::vector<ModuleTerm>&, size_t)>
        wordToTermFrom =
            [&](const std::vector<ModuleTerm>& w, size_t i) -> ExpressionPointer {
        if (i >= w.size()) return vZero;
        if (i + 1 == w.size()) return atomTerm(w[i]);
        return buildAdd(atomTerm(w[i]), wordToTermFrom(w, i + 1));
    };
    auto wordToTerm = [&](const std::vector<ModuleTerm>& w) {
        return wordToTermFrom(w, 0);
    };

    // ---- congruences ---------------------------------------------------
    // add(A,B) = add(A',B') from pA : A=A', pB : B=B'.
    auto addCongruence = [&](ExpressionPointer A, ExpressionPointer Ap,
                             ExpressionPointer pA, ExpressionPointer B,
                             ExpressionPointer Bp, ExpressionPointer pB)
        -> ExpressionPointer {
        ExpressionPointer addLift = liftBoundVariables(addOp, 1, 0);
        ExpressionPointer Blift = liftBoundVariables(B, 1, 0);
        ExpressionPointer body1 = makeApplication(
            makeApplication(addLift, makeBoundVariable(0)), Blift);
        ExpressionPointer lambda1 = makeLambda("_m", carrier, body1);
        ExpressionPointer step1 = buildEqualityCongruenceSameCarrier(
            level, carrier, lambda1, A, Ap, pA);
        ExpressionPointer Aplift = liftBoundVariables(Ap, 1, 0);
        ExpressionPointer body2 = makeApplication(
            makeApplication(addLift, Aplift), makeBoundVariable(0));
        ExpressionPointer lambda2 = makeLambda("_m", carrier, body2);
        ExpressionPointer step2 = buildEqualityCongruenceSameCarrier(
            level, carrier, lambda2, B, Bp, pB);
        return trans(buildAdd(A, B), buildAdd(Ap, B), buildAdd(Ap, Bp),
                     step1, step2);
    };
    // scale(c, X) = scale(c, X') from pX : X = X'.
    auto scaleVecCongruence = [&](ExpressionPointer c, ExpressionPointer X,
                                  ExpressionPointer Xp, ExpressionPointer pX)
        -> ExpressionPointer {
        ExpressionPointer scaleLift = liftBoundVariables(scaleOp, 1, 0);
        ExpressionPointer cLift = liftBoundVariables(c, 1, 0);
        ExpressionPointer body = makeApplication(
            makeApplication(scaleLift, cLift), makeBoundVariable(0));
        ExpressionPointer lambda = makeLambda("_m", carrier, body);
        return buildEqualityCongruenceSameCarrier(
            level, carrier, lambda, X, Xp, pX);
    };
    // scale(cL, a) = scale(cR, a) from pc : cL = cR (coefficient position, so
    // the source carrier is the field, the target the vector space).
    auto scaleCoeffCongruence = [&](ExpressionPointer cL, ExpressionPointer cR,
                                    ExpressionPointer a, ExpressionPointer pc)
        -> ExpressionPointer {
        ExpressionPointer scaleLift = liftBoundVariables(scaleOp, 1, 0);
        ExpressionPointer aLift = liftBoundVariables(a, 1, 0);
        ExpressionPointer body = makeApplication(
            makeApplication(scaleLift, makeBoundVariable(0)), aLift);
        ExpressionPointer lambda = makeLambda("_c", fieldCarrier, body);
        return buildEqualityCongruence(
            level, fieldCarrier, level, carrier, lambda, cL, cR, pc);
    };

    // ---- matchers ------------------------------------------------------
    auto matchBinary = [&](ExpressionPointer e, ExpressionPointer op,
                           ExpressionPointer& a, ExpressionPointer& b) -> bool {
        auto* outer = std::get_if<Application>(&e->node);
        if (!outer) return false;
        auto* inner = std::get_if<Application>(&outer->function->node);
        if (!inner) return false;
        if (!structurallyEqual(inner->function, op)) return false;
        a = inner->argument;
        b = outer->argument;
        return true;
    };
    auto matchUnary = [&](ExpressionPointer e, ExpressionPointer op,
                          ExpressionPointer& x) -> bool {
        auto* app = std::get_if<Application>(&e->node);
        if (!app) return false;
        if (!structurallyEqual(app->function, op)) return false;
        x = app->argument;
        return true;
    };
    auto matchSubtract = [&](ExpressionPointer e, ExpressionPointer& x,
                             ExpressionPointer& y) -> bool {
        ExpressionPointer head;
        std::vector<ExpressionPointer> args;
        peelSpine(e, head, args);
        auto* constant = std::get_if<Constant>(&head->node);
        if (!constant || constant->name != "VectorSpace.subtract") return false;
        if (args.size() != 4) return false;  // f, V, x, y
        x = args[2];
        y = args[3];
        return true;
    };

    // ---- normalise: e = wordToTerm(word), with proof -------------------
    // scale(c, wordToTerm(w)) = wordToTerm(scale-c word). Threads the
    // distribution `c•(u+v)=c•u+c•v` and collapse `c•(d•v)=(c*d)•v`.
    std::function<ExpressionPointer(ExpressionPointer,
                                    const std::vector<ModuleTerm>&,
                                    const std::vector<ModuleTerm>&)>
        scaleDistribute = [&](ExpressionPointer c,
                              const std::vector<ModuleTerm>& w,
                              const std::vector<ModuleTerm>& scaled)
        -> ExpressionPointer {
        if (w.empty()) {
            // scale(c, zero) = zero
            return applyLaw("VectorSpace.scale_zero", {c});
        }
        // First term: scale(c, scale(d0, a0)) = scale(c*d0, a0)  [rev scalarMul]
        ExpressionPointer d0 = w[0].coefficient;
        ExpressionPointer a0 = w[0].atom;
        ExpressionPointer scalarMul = applyLaw(
            "VectorSpace.scale_scalar_multiply", {c, d0, a0});
        ExpressionPointer firstProof = buildEqualitySymmetry(
            level, carrier, buildScale(fMul(c, d0), a0),
            buildScale(c, buildScale(d0, a0)),
            scalarMul);  // scale(c, scale(d0,a0)) = scale(c*d0, a0)
        if (w.size() == 1) {
            return firstProof;
        }
        std::vector<ModuleTerm> rest(w.begin() + 1, w.end());
        std::vector<ModuleTerm> scaledRest(scaled.begin() + 1, scaled.end());
        ExpressionPointer restTerm = wordToTerm(rest);
        ExpressionPointer scaledRestTerm = wordToTerm(scaledRest);
        // scale(c, add(scale(d0,a0), restTerm))
        //   = add(scale(c, scale(d0,a0)), scale(c, restTerm))   [distribute]
        ExpressionPointer distribute = applyLaw(
            "VectorSpace.scale_vector_add",
            {c, buildScale(d0, a0), restTerm});
        //   = add(scale(c*d0, a0), scaledRestTerm)   [cong both]
        ExpressionPointer restProof = scaleDistribute(c, rest, scaledRest);
        ExpressionPointer congBoth = addCongruence(
            buildScale(c, buildScale(d0, a0)), buildScale(fMul(c, d0), a0),
            firstProof, buildScale(c, restTerm), scaledRestTerm, restProof);
        return trans(
            buildScale(c, buildAdd(buildScale(d0, a0), restTerm)),
            buildAdd(buildScale(c, buildScale(d0, a0)), buildScale(c, restTerm)),
            buildAdd(buildScale(fMul(c, d0), a0), scaledRestTerm),
            distribute, congBoth);
    };
    // add(termA, termB) = wordToTerm(wA ++ wB), pure re-association.
    std::function<ExpressionPointer(const std::vector<ModuleTerm>&,
                                    const std::vector<ModuleTerm>&)>
        concatProof = [&](const std::vector<ModuleTerm>& wA,
                          const std::vector<ModuleTerm>& wB)
        -> ExpressionPointer {
        ExpressionPointer termB = wordToTerm(wB);
        if (wA.empty()) {
            return applyLaw("VectorSpace.zero_add", {termB});  // add(0,B)=B
        }
        if (wA.size() == 1) {
            ExpressionPointer a0 = atomTerm(wA[0]);
            if (wB.empty()) {
                return applyLaw("VectorSpace.add_zero", {a0});  // add(a0,0)=a0
            }
            return refl(buildAdd(a0, termB));  // already right-nested
        }
        ExpressionPointer a0 = atomTerm(wA[0]);
        std::vector<ModuleTerm> restA(wA.begin() + 1, wA.end());
        ExpressionPointer restATerm = wordToTerm(restA);
        // add(add(a0, restATerm), termB) = add(a0, add(restATerm, termB)) [assoc]
        ExpressionPointer assoc = applyLaw(
            "VectorSpace.add_associative", {a0, restATerm, termB});
        // = add(a0, wordToTerm(restA ++ wB))   [cong-right concatProof]
        ExpressionPointer inner = concatProof(restA, wB);
        std::vector<ModuleTerm> restAB = restA;
        restAB.insert(restAB.end(), wB.begin(), wB.end());
        ExpressionPointer congRight = addCongruence(
            a0, a0, refl(a0), buildAdd(restATerm, termB), wordToTerm(restAB),
            inner);
        return trans(
            buildAdd(buildAdd(a0, restATerm), termB),
            buildAdd(a0, buildAdd(restATerm, termB)),
            buildAdd(a0, wordToTerm(restAB)), assoc, congRight);
    };

    std::function<ModuleNorm(ExpressionPointer)> normalize =
        [&](ExpressionPointer e) -> ModuleNorm {
        if (structurallyEqual(e, vZero)) {
            return {{}, vZero, refl(vZero)};
        }
        ExpressionPointer subX, subY;
        if (matchSubtract(e, subX, subY)) {
            ExpressionPointer addForm =
                buildAdd(subX, makeApplication(negateOp, subY));
            ModuleNorm normed = normalize(addForm);
            // e ≡ addForm definitionally, so reflexivity bridges.
            ExpressionPointer proof =
                trans(e, addForm, normed.term, refl(e), normed.proof);
            return {normed.word, normed.term, proof};
        }
        ExpressionPointer negX;
        if (matchUnary(e, negateOp, negX)) {
            // negate(x) = scale(-1, x)   [rev negate_one_scale]
            ExpressionPointer negOne =
                makeApplication(makeConstant("Field.negate"), f);
            negOne = makeApplication(negOne, fOne);
            ExpressionPointer bridge = buildEqualitySymmetry(
                level, carrier, buildScale(negOne, negX), e,
                applyLaw("VectorSpace.negate_one_scale", {negX}));
            ExpressionPointer scaleForm = buildScale(negOne, negX);
            ModuleNorm normed = normalize(scaleForm);
            ExpressionPointer proof =
                trans(e, scaleForm, normed.term, bridge, normed.proof);
            return {normed.word, normed.term, proof};
        }
        ExpressionPointer c, sx;
        if (matchBinary(e, scaleOp, c, sx)) {
            ModuleNorm nx = normalize(sx);
            std::vector<ModuleTerm> scaled;
            for (const auto& t : nx.word) {
                scaled.push_back({fMul(c, t.coefficient), t.atom});
            }
            // e = scale(c, nx.term)   [cong] = wordToTerm(scaled)   [distribute]
            ExpressionPointer cong =
                scaleVecCongruence(c, sx, nx.term, nx.proof);
            ExpressionPointer dist = scaleDistribute(c, nx.word, scaled);
            ExpressionPointer term = wordToTerm(scaled);
            ExpressionPointer proof =
                trans(e, buildScale(c, nx.term), term, cong, dist);
            return {scaled, term, proof};
        }
        ExpressionPointer la, lb;
        if (matchBinary(e, addOp, la, lb)) {
            ModuleNorm na = normalize(la);
            ModuleNorm nb = normalize(lb);
            std::vector<ModuleTerm> combined = na.word;
            combined.insert(combined.end(), nb.word.begin(), nb.word.end());
            ExpressionPointer cong = addCongruence(
                la, na.term, na.proof, lb, nb.term, nb.proof);
            ExpressionPointer concat = concatProof(na.word, nb.word);
            ExpressionPointer term = wordToTerm(combined);
            ExpressionPointer proof =
                trans(e, buildAdd(na.term, nb.term), term, cong, concat);
            return {combined, term, proof};
        }
        // Opaque atom: e = 1 • e  [rev one_scale].
        ExpressionPointer atomProof = buildEqualitySymmetry(
            level, carrier, buildScale(fOne, e), e,
            applyLaw("VectorSpace.one_scale", {e}));
        return {{ModuleTerm{fOne, e}}, buildScale(fOne, e), atomProof};
    };

    // ---- coefficient sub-goals, discharged by the ring prover ----------
    auto proveCoeffEqual = [&](ExpressionPointer cL, ExpressionPointer cR)
        -> ExpressionPointer {
        ExpressionPointer openedGoal = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {level}), fieldCarrier),
                cL),
            cR);
        ExpressionPointer closedGoal =
            closeOverLocalBinders(openedGoal, localBinders, binderCount);
        try {
            ExpressionPointer p =
                elaborateRing(
                    localBinders, closedGoal, line, 0,
                    RingInvocation::InternalProofSearch);
            if (!p) return nullptr;
            return openOverLocalBinders(p, localBinders, binderCount);
        } catch (const ElaborateError&) {
            return nullptr;
        } catch (const TypeError&) {
            return nullptr;
        }
    };
    auto coeffIsZero = [&](ExpressionPointer c) -> ExpressionPointer {
        return proveCoeffEqual(c, fZero);
    };

    // ---- canonicalisation: sort by atom, merge like atoms, drop zeros --
    auto atomLess = [&](const ModuleTerm& x, const ModuleTerm& y) -> bool {
        return compareExpressionStructure(x.atom, y.atom) < 0;
    };
    // Proof that swapping adjacent terms (i, i+1) preserves the word's term.
    std::function<ExpressionPointer(const std::vector<ModuleTerm>&, size_t)>
        swapAdjacentProof =
            [&](const std::vector<ModuleTerm>& w, size_t i) -> ExpressionPointer {
        if (i > 0) {
            ExpressionPointer headTerm = atomTerm(w[0]);
            std::vector<ModuleTerm> tail(w.begin() + 1, w.end());
            ExpressionPointer tailTerm = wordToTerm(tail);
            std::vector<ModuleTerm> tailSwapped = tail;
            std::swap(tailSwapped[i - 1], tailSwapped[i]);
            ExpressionPointer inner = swapAdjacentProof(tail, i - 1);
            return addCongruence(headTerm, headTerm, refl(headTerm), tailTerm,
                                 wordToTerm(tailSwapped), inner);
        }
        ExpressionPointer a0 = atomTerm(w[0]);
        ExpressionPointer a1 = atomTerm(w[1]);
        ExpressionPointer commProof =
            applyLaw("VectorSpace.add_commutative", {a0, a1});
        if (w.size() == 2) return commProof;
        std::vector<ModuleTerm> rest(w.begin() + 2, w.end());
        ExpressionPointer restTerm = wordToTerm(rest);
        ExpressionPointer assoc1 =
            applyLaw("VectorSpace.add_associative", {a0, a1, restTerm});
        ExpressionPointer step1 = buildEqualitySymmetry(
            level, carrier, buildAdd(buildAdd(a0, a1), restTerm),
            buildAdd(a0, buildAdd(a1, restTerm)), assoc1);
        ExpressionPointer step2 = addCongruence(
            buildAdd(a0, a1), buildAdd(a1, a0), commProof, restTerm, restTerm,
            refl(restTerm));
        ExpressionPointer assoc2 =
            applyLaw("VectorSpace.add_associative", {a1, a0, restTerm});
        ExpressionPointer t1 = trans(
            buildAdd(a0, buildAdd(a1, restTerm)),
            buildAdd(buildAdd(a0, a1), restTerm),
            buildAdd(buildAdd(a1, a0), restTerm), step1, step2);
        return trans(
            buildAdd(a0, buildAdd(a1, restTerm)),
            buildAdd(buildAdd(a1, a0), restTerm),
            buildAdd(a1, buildAdd(a0, restTerm)), t1, assoc2);
    };
    // Proof that merging the like-atom pair (i, i+1) into one term with summed
    // coefficient preserves the word's term.
    std::function<ExpressionPointer(const std::vector<ModuleTerm>&, size_t)>
        mergePairProof =
            [&](const std::vector<ModuleTerm>& w, size_t i) -> ExpressionPointer {
        if (i > 0) {
            ExpressionPointer headTerm = atomTerm(w[0]);
            std::vector<ModuleTerm> tail(w.begin() + 1, w.end());
            ExpressionPointer tailTerm = wordToTerm(tail);
            std::vector<ModuleTerm> tailMerged = tail;
            tailMerged[i - 1] = {fAdd(tail[i - 1].coefficient,
                                      tail[i].coefficient),
                                 tail[i - 1].atom};
            tailMerged.erase(tailMerged.begin() + i);
            ExpressionPointer inner = mergePairProof(tail, i - 1);
            return addCongruence(headTerm, headTerm, refl(headTerm), tailTerm,
                                 wordToTerm(tailMerged), inner);
        }
        ExpressionPointer a = w[0].coefficient;
        ExpressionPointer b = w[1].coefficient;
        ExpressionPointer v = w[0].atom;
        // add(scale(a,v), scale(b,v)) = scale(a+b, v)   [rev scale_scalar_add]
        ExpressionPointer mergeProof = buildEqualitySymmetry(
            level, carrier, buildScale(fAdd(a, b), v),
            buildAdd(buildScale(a, v), buildScale(b, v)),
            applyLaw("VectorSpace.scale_scalar_add", {a, b, v}));
        if (w.size() == 2) return mergeProof;
        std::vector<ModuleTerm> rest(w.begin() + 2, w.end());
        ExpressionPointer restTerm = wordToTerm(rest);
        ExpressionPointer assocFwd = applyLaw(
            "VectorSpace.add_associative",
            {buildScale(a, v), buildScale(b, v), restTerm});
        ExpressionPointer revAssoc = buildEqualitySymmetry(
            level, carrier,
            buildAdd(buildAdd(buildScale(a, v), buildScale(b, v)), restTerm),
            buildAdd(buildScale(a, v), buildAdd(buildScale(b, v), restTerm)),
            assocFwd);
        ExpressionPointer cong = addCongruence(
            buildAdd(buildScale(a, v), buildScale(b, v)), buildScale(fAdd(a, b), v),
            mergeProof, restTerm, restTerm, refl(restTerm));
        return trans(
            buildAdd(buildScale(a, v), buildAdd(buildScale(b, v), restTerm)),
            buildAdd(buildAdd(buildScale(a, v), buildScale(b, v)), restTerm),
            buildAdd(buildScale(fAdd(a, b), v), restTerm), revAssoc, cong);
    };
    // Proof that dropping term i (whose coefficient is proved zero) preserves
    // the word's term. `zeroProof : coefficient(i) = 0`.
    std::function<ExpressionPointer(const std::vector<ModuleTerm>&, size_t,
                                    ExpressionPointer)>
        dropTermProof = [&](const std::vector<ModuleTerm>& w, size_t i,
                            ExpressionPointer zeroProof) -> ExpressionPointer {
        if (i > 0) {
            ExpressionPointer headTerm = atomTerm(w[0]);
            std::vector<ModuleTerm> tail(w.begin() + 1, w.end());
            ExpressionPointer tailTerm = wordToTerm(tail);
            std::vector<ModuleTerm> tailDropped = tail;
            tailDropped.erase(tailDropped.begin() + (i - 1));
            ExpressionPointer inner = dropTermProof(tail, i - 1, zeroProof);
            return addCongruence(headTerm, headTerm, refl(headTerm), tailTerm,
                                 wordToTerm(tailDropped), inner);
        }
        ExpressionPointer cc = w[0].coefficient;
        ExpressionPointer v = w[0].atom;
        // scale(cc, v) = scale(0, v)  [coeff cong] = 0  [zero_scale]
        ExpressionPointer toZeroCoeff =
            scaleCoeffCongruence(cc, fZero, v, zeroProof);
        ExpressionPointer zeroScale = applyLaw("VectorSpace.zero_scale", {v});
        ExpressionPointer termToZero = trans(
            buildScale(cc, v), buildScale(fZero, v), vZero, toZeroCoeff,
            zeroScale);
        if (w.size() == 1) return termToZero;  // [scale(cc,v)] = [] i.e. = 0
        std::vector<ModuleTerm> rest(w.begin() + 1, w.end());
        ExpressionPointer restTerm = wordToTerm(rest);
        // add(scale(cc,v), restTerm) = add(0, restTerm) [cong] = restTerm [zero_add]
        ExpressionPointer cong = addCongruence(
            buildScale(cc, v), vZero, termToZero, restTerm, restTerm,
            refl(restTerm));
        ExpressionPointer zeroAdd = applyLaw("VectorSpace.zero_add", {restTerm});
        return trans(buildAdd(buildScale(cc, v), restTerm),
                     buildAdd(vZero, restTerm), restTerm, cong, zeroAdd);
    };

    // Sort + merge + drop, threading the proof from `origExpr`.
    auto canonicalize = [&](ExpressionPointer origExpr,
                            ModuleNorm nrm) -> ModuleNorm {
        std::vector<ModuleTerm> w = nrm.word;
        ExpressionPointer currentTerm = nrm.term;
        ExpressionPointer proof = nrm.proof;
        // Insertion of swaps until sorted.
        bool changed = true;
        while (changed) {
            changed = false;
            for (size_t i = 0; i + 1 < w.size(); ++i) {
                if (atomLess(w[i + 1], w[i])) {
                    ExpressionPointer swp = swapAdjacentProof(w, i);
                    std::swap(w[i], w[i + 1]);
                    ExpressionPointer newTerm = wordToTerm(w);
                    proof = trans(origExpr, currentTerm, newTerm, proof, swp);
                    currentTerm = newTerm;
                    changed = true;
                }
            }
        }
        // Merge adjacent like atoms.
        bool merged = true;
        while (merged) {
            merged = false;
            for (size_t i = 0; i + 1 < w.size(); ++i) {
                if (structurallyEqual(w[i].atom, w[i + 1].atom)) {
                    ExpressionPointer mp = mergePairProof(w, i);
                    w[i] = {fAdd(w[i].coefficient, w[i + 1].coefficient),
                            w[i].atom};
                    w.erase(w.begin() + i + 1);
                    ExpressionPointer newTerm = wordToTerm(w);
                    proof = trans(origExpr, currentTerm, newTerm, proof, mp);
                    currentTerm = newTerm;
                    merged = true;
                    break;
                }
            }
        }
        // Drop terms whose coefficient is provably zero.
        bool dropped = true;
        while (dropped) {
            dropped = false;
            for (size_t i = 0; i < w.size(); ++i) {
                ExpressionPointer zeroProof = coeffIsZero(w[i].coefficient);
                if (zeroProof) {
                    ExpressionPointer dp = dropTermProof(w, i, zeroProof);
                    w.erase(w.begin() + i);
                    ExpressionPointer newTerm = wordToTerm(w);
                    proof = trans(origExpr, currentTerm, newTerm, proof, dp);
                    currentTerm = newTerm;
                    dropped = true;
                    break;
                }
            }
        }
        return {w, currentTerm, proof};
    };

    ModuleNorm nL = canonicalize(leftOpened, normalize(leftOpened));
    ModuleNorm nR = canonicalize(rightOpened, normalize(rightOpened));

    // The canonical forms must have the same atoms in the same order.
    if (nL.word.size() != nR.word.size()) return nullptr;
    std::vector<ExpressionPointer> coeffProofs;
    for (size_t i = 0; i < nL.word.size(); ++i) {
        if (!structurallyEqual(nL.word[i].atom, nR.word[i].atom)) return nullptr;
        if (structurallyEqual(nL.word[i].coefficient, nR.word[i].coefficient)) {
            coeffProofs.push_back(nullptr);  // identical → reflexivity later
            continue;
        }
        ExpressionPointer pc = proveCoeffEqual(nL.word[i].coefficient,
                                               nR.word[i].coefficient);
        if (!pc) return nullptr;
        coeffProofs.push_back(pc);
    }

    // Build wordToTerm(nL.word) = wordToTerm(nR.word) by adjusting each
    // coefficient, folded through the right-nested sum.
    std::function<ExpressionPointer(size_t)> coeffAdjustFrom =
        [&](size_t i) -> ExpressionPointer {
        // Proof: wordToTermFrom(nL.word, i) = wordToTermFrom(nR.word, i).
        ExpressionPointer aL = atomTerm(nL.word[i]);
        ExpressionPointer aR = atomTerm(nR.word[i]);
        ExpressionPointer headEq;
        if (!coeffProofs[i]) {
            headEq = refl(aL);
        } else {
            headEq = scaleCoeffCongruence(
                nL.word[i].coefficient, nR.word[i].coefficient,
                nL.word[i].atom, coeffProofs[i]);
        }
        if (i + 1 == nL.word.size()) {
            return headEq;
        }
        ExpressionPointer tailL = wordToTermFrom(nL.word, i + 1);
        ExpressionPointer tailR = wordToTermFrom(nR.word, i + 1);
        ExpressionPointer tailEq = coeffAdjustFrom(i + 1);
        return addCongruence(aL, aR, headEq, tailL, tailR, tailEq);
    };

    ExpressionPointer result;
    if (nL.word.empty()) {
        // Both reduce to the zero vector.
        result = trans(leftOpened, nL.term, rightOpened, nL.proof,
                       buildEqualitySymmetry(level, carrier, rightOpened,
                                             nR.term, nR.proof));
    } else {
        ExpressionPointer coeffAdjust = coeffAdjustFrom(0);
        ExpressionPointer lToR = trans(leftOpened, nL.term, nR.term, nL.proof,
                                       coeffAdjust);
        result = trans(leftOpened, nR.term, rightOpened, lToR,
                       buildEqualitySymmetry(level, carrier, rightOpened,
                                             nR.term, nR.proof));
    }
    return closeOverLocalBinders(result, localBinders, binderCount);
}

ExpressionPointer Elaborator::elaborateModuleNormalise(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType, int line, int column) {
    Frame frame(*this, "module at line " + std::to_string(line),
                localBinders, expectedType, line, column);
    if (!expectedType) {
        throwElaborate(
            "`module` needs an expected type from context — use it in a calc "
            "step or as the body of a theorem with a declared equality "
            "conclusion");
    }
    ExpressionPointer proof = proveModuleEquality(localBinders, expectedType, line);
    if (proof) return proof;
    throwElaborate(
        "`module` could not close this goal. It proves `=` goals over a "
        "`VectorSpace.carrier(V)` by normalising both sides to a canonical "
        "`Σ cᵢ • vᵢ` (distributing `•`, collecting like vectors by adding "
        "coefficients) — check the goal is such a rearrangement and the "
        "vector-space laws are in scope.");
}
