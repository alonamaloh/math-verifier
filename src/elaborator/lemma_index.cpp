// Out-of-line Elaborator method definitions: lemma-index lookup + diff classification used by the auto-prover
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

ExpressionPointer Elaborator::instantiateLemmaBinders(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth) {
        int N = static_cast<int>(bindings.size());
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            if (bv->deBruijnIndex < nestedBinderDepth) {
                return expression;
            }
            int relative = bv->deBruijnIndex - nestedBinderDepth;
            if (relative < N) {
                return liftBoundVariables(bindings[relative],
                                            nestedBinderDepth, 0);
            }
            // A reference past the lemma's own binders. Library
            // rewrite lemmas shouldn't produce one, but if they do,
            // close the gap left by the eliminated lemma binders.
            return makeBoundVariable(
                bv->deBruijnIndex - N);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return makeApplication(
                instantiateLemmaBinders(application->function,
                                          bindings, nestedBinderDepth),
                instantiateLemmaBinders(application->argument,
                                          bindings, nestedBinderDepth));
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                instantiateLemmaBinders(pi->domain, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(pi->codomain, bindings,
                                          nestedBinderDepth + 1));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                instantiateLemmaBinders(lambda->domain, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(lambda->body, bindings,
                                          nestedBinderDepth + 1));
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return makeLet(let->displayHint,
                instantiateLemmaBinders(let->type, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(let->value, bindings,
                                          nestedBinderDepth),
                instantiateLemmaBinders(let->body, bindings,
                                          nestedBinderDepth + 1));
        }
        return expression;
    }

ExpressionPointer Elaborator::tryLemmaIndexLookup(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
        // We look up two buckets: the subLeft-keyed bucket, and the
        // wildcard bucket. The wildcard bucket holds reverse-direction
        // entries for lemmas whose RHS is a bare metavariable (e.g.
        // the identity `(x : T) → op(x, unit) = x`, which we want to
        // fire when subLeft is `x` and subRight is `op(x, unit)`). The
        // forward-direction entry of those lemmas, indexed under their
        // op-headed LHS, lands in the regular bucket as usual.
        std::vector<uint64_t> keys;
        keys.push_back(spineHash(subLeft));
        ExpressionPointer wildcardProbe = makeBoundVariable(0);
        uint64_t wildcardKey = spineHash(wildcardProbe);
        if (wildcardKey != keys[0]) {
            keys.push_back(wildcardKey);
        }
        for (uint64_t key : keys) {
        auto range = lemmaIndex_.equal_range(key);
        for (auto iterator = range.first;
             iterator != range.second; ++iterator) {
            const RewriteLemma& lemma = iterator->second;
            std::vector<ExpressionPointer> bindings(lemma.binderCount);
            ExpressionPointer patternFor = lemma.reverseDirection
                ? lemma.rhs : lemma.lhs;
            ExpressionPointer otherSide = lemma.reverseDirection
                ? lemma.lhs : lemma.rhs;
            if (!matchAgainstPattern(patternFor, subLeft,
                                       lemma.binderCount, bindings)) {
                continue;
            }
            // Symmetric pass: also match `otherSide` against
            // `subRight` so the lemma's binders get filled from
            // WHICHEVER side carries them. Without this, a lemma
            // stated `-x + x = 0` would fire on `-1 + 1 = 0` (the
            // matched LHS binds x) but NOT on `0 = -1 + 1` (the
            // matched RHS is bare, leaving x unbound). matchAgainst-
            // Pattern's set-or-check logic also doubles as the
            // consistency check that used to live in the
            // `structurallyEqual(expectedOther, subRight)` line
            // below — when bindings overlap between the two sides,
            // re-binding the same slot to the same subterm succeeds,
            // and a conflict between the two sides correctly rejects
            // the lemma.
            if (!matchAgainstPattern(otherSide, subRight,
                                       lemma.binderCount, bindings)) {
                continue;
            }
            // Discharge unbound preconditions outer-to-inner: a binder
            // type at conclusion-frame index i may reference outer
            // binders (index > i), so we need those filled first.
            // Pattern matching populates LHS/RHS slots; this pass
            // populates propositional preconditions by searching local
            // hypotheses for proofs of the instantiated type. Lemmas
            // like `padic_valuation_multiplicative(prime, a, b)
            // (primality)(aPos)(bPos)` have primality/aPos/bPos in
            // scope via the user's `claim`s — the discharge finds them
            // and the lemma fires without an explicit `by`.
            bool dischargedAll = true;
            if (static_cast<int>(lemma.binderTypes.size())
                == lemma.binderCount) {
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                for (int i = lemma.binderCount - 1; i >= 0; --i) {
                    if (bindings[i]) continue;
                    if (!binderReferencesAllBound(
                            lemma.binderTypes[i], bindings)) {
                        dischargedAll = false;
                        break;
                    }
                    ExpressionPointer slotType = instantiateLemmaBinders(
                        lemma.binderTypes[i], bindings);
                    ExpressionPointer slotTypeOpened =
                        openOverLocalBinders(slotType, localBinders,
                                              localBinders.size());
                    ExpressionPointer slotTypeNormalised;
                    try {
                        slotTypeNormalised = weakHeadNormalForm(
                            environment_, slotTypeOpened);
                    } catch (const TypeError&) {
                        dischargedAll = false;
                        break;
                    }
                    bool found = false;
                    for (int j =
                             static_cast<int>(localBinders.size()) - 1;
                         j >= 0; --j) {
                        ExpressionPointer candidateType =
                            openOverLocalBinders(
                                localBinders[j].type, localBinders, j);
                        bool eq;
                        try {
                            eq = isDefinitionallyEqual(environment_,
                                openedContext, candidateType,
                                slotTypeNormalised);
                        } catch (const TypeError&) {
                            eq = false;
                        }
                        if (eq) {
                            int deBruijnIndex =
                                static_cast<int>(localBinders.size())
                                - 1 - j;
                            bindings[i] =
                                makeBoundVariable(deBruijnIndex);
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        dischargedAll = false;
                        break;
                    }
                }
            } else {
                // Older registration without binderTypes; fall back to
                // the original all-or-nothing check.
                dischargedAll = false;
                for (const auto& binding : bindings) {
                    if (!binding) { dischargedAll = false; break; }
                    dischargedAll = true;
                }
            }
            if (!dischargedAll) continue;
            bool allBound = true;
            for (const auto& binding : bindings) {
                if (!binding) { allBound = false; break; }
            }
            if (!allBound) continue;
            // The two `matchAgainstPattern` calls above already
            // enforced `otherSide[bindings] = subRight` structurally,
            // so the redundant re-check that used to live here is
            // gone. (Propositional preconditions filled by the
            // discharge pass don't appear in `otherSide` — they're
            // referenced from binder types, not from the conclusion's
            // LHS/RHS — so they don't change the check's outcome.)
            // Assemble the lemma application: `lemmaName(binding_for_BV(n-1),
            // …, binding_for_BV(0))` — outer binder first since that's
            // the order of the Π chain.
            ExpressionPointer call =
                makeConstant(lemma.lemmaName, {});
            for (int i = lemma.binderCount - 1; i >= 0; --i) {
                call = makeApplication(std::move(call), bindings[i]);
            }
            if (!lemma.reverseDirection) {
                return call;
            }
            // Reverse direction: lemma proves `RHS = LHS` but the diff
            // wants `subLeft = subRight` where subLeft matches the
            // lemma's RHS. So the lemma instance proves
            // `subRight = subLeft`, which we wrap with
            // `Equality.symmetry` to get the desired direction.
            ExpressionPointer carrierClosed;
            LevelPointer carrierLevelAtThisLevel;
            try {
                // inferTypeInLocalContext returns the type in OPENED form
                // (Internal free variables for the local binders). The
                // symmetry term we splice it into is in CLOSED (de Bruijn)
                // form, so the carrier MUST be closed too — otherwise an
                // abstract carrier like `Group.carrier(H)` leaks an
                // unbound internal `H` that the kernel later rejects.
                carrierClosed = closeOverLocalBinders(
                    inferTypeInLocalContext(localBinders, subLeft),
                    localBinders, localBinders.size());
                carrierLevelAtThisLevel = typeUniverseOf(
                    localBinders, subLeft);
            } catch (const TypeError&) {
                continue;
            } catch (const ElaborateError&) {
                continue;
            }
            ExpressionPointer symmetryCall = makeConstant(
                "Equality.symmetry", {carrierLevelAtThisLevel});
            symmetryCall = makeApplication(
                std::move(symmetryCall), carrierClosed);
            symmetryCall = makeApplication(
                std::move(symmetryCall), subRight);
            symmetryCall = makeApplication(
                std::move(symmetryCall), subLeft);
            symmetryCall = makeApplication(
                std::move(symmetryCall), std::move(call));
            return symmetryCall;
        }
        }
        return nullptr;
    }

ExpressionPointer Elaborator::tryClassifyDiff(
        const std::vector<LocalBinder>& localBinders,
        const Context& openedContext,
        ExpressionPointer subLeft,
        ExpressionPointer subRight) {
        if (ExpressionPointer proof = tryLemmaIndexLookup(
                localBinders, subLeft, subRight)) {
            return proof;
        }
        // Local hypothesis match (forward and symmetric). Scan
        // local binders for one whose type is
        // Equality(_, subLeft, subRight) or
        // Equality(_, subRight, subLeft).
        {
            ExpressionPointer subLeftOpened = openOverLocalBinders(
                subLeft, localBinders, localBinders.size());
            ExpressionPointer subRightOpened = openOverLocalBinders(
                subRight, localBinders, localBinders.size());
            for (int i =
                     static_cast<int>(localBinders.size()) - 1;
                 i >= 0; --i) {
                ExpressionPointer binderTypeOpened = openOverLocalBinders(
                    localBinders[i].type, localBinders, i);
                ExpressionPointer normalized = weakHeadNormalForm(
                    environment_, binderTypeOpened);
                // Expect App(App(App(Equality, carrier), x), y).
                auto* app3 =
                    std::get_if<Application>(&normalized->node);
                if (!app3) continue;
                auto* app2 =
                    std::get_if<Application>(&app3->function->node);
                if (!app2) continue;
                auto* app1 =
                    std::get_if<Application>(&app2->function->node);
                if (!app1) continue;
                auto* head =
                    std::get_if<Constant>(&app1->function->node);
                if (!head || head->name != "Equality") continue;
                ExpressionPointer eqLeft = app2->argument;
                ExpressionPointer eqRight = app3->argument;
                int deBruijnIndex =
                    static_cast<int>(localBinders.size()) - 1 - i;
                if (isDefinitionallyEqual(environment_,
                        openedContext, eqLeft, subLeftOpened)
                    && isDefinitionallyEqual(environment_,
                        openedContext, eqRight, subRightOpened)) {
                    return makeBoundVariable(deBruijnIndex);
                }
                if (isDefinitionallyEqual(environment_,
                        openedContext, eqLeft, subRightOpened)
                    && isDefinitionallyEqual(environment_,
                        openedContext, eqRight, subLeftOpened)) {
                    // Wrap with Equality.symmetry.
                    auto* carrierConst =
                        std::get_if<Constant>(&app1->argument->node);
                    (void)carrierConst;
                    ExpressionPointer carrierAtThisLevel =
                        app1->argument;
                    LevelPointer carrierLevelAtThisLevel;
                    if (!head->universeArguments.empty()) {
                        carrierLevelAtThisLevel =
                            head->universeArguments[0];
                    } else {
                        // Should not happen: Equality is universe-
                        // polymorphic and always has a level arg.
                        return nullptr;
                    }
                    ExpressionPointer carrierClosed =
                        closeOverLocalBinders(
                            carrierAtThisLevel, localBinders,
                            localBinders.size());
                    ExpressionPointer hypBoundVar =
                        makeBoundVariable(deBruijnIndex);
                    ExpressionPointer symmetryCall = makeConstant(
                        "Equality.symmetry",
                        {carrierLevelAtThisLevel});
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), carrierClosed);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), subRight);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall), subLeft);
                    symmetryCall = makeApplication(
                        std::move(symmetryCall),
                        std::move(hypBoundVar));
                    return symmetryCall;
                }
            }
        }
        return nullptr;
    }

// ---- B2 sign-judgment rule index (tier 4) -------------------------------
// See the SignRule declaration comment in internal.hpp. Registration
// mirrors registerGenericRewriteLemma's binder handling; discharge
// mirrors tryLemmaIndexLookup's precondition pass, except that a
// premise which is ITSELF a sign judgment recurses into the index —
// that recursion is what turns per-composite sign breadcrumbs
// (`0 < ε/2 · roof` etc.) into a single silent procedure.

namespace {

// Application-spine head constant name + spine arguments (outermost
// last). Local copy — the equivalent helper in warnings.cpp is
// file-static by design (each elaborator slice stays self-contained).
std::string signSpineHead(ExpressionPointer term,
                          std::vector<ExpressionPointer>& arguments) {
    arguments.clear();
    ExpressionPointer cursor = term;
    while (auto* application = std::get_if<Application>(&cursor->node)) {
        arguments.push_back(application->argument);
        cursor = application->function;
    }
    std::reverse(arguments.begin(), arguments.end());
    if (auto* constant = std::get_if<Constant>(&cursor->node)) {
        return constant->name;
    }
    return std::string();
}

bool endsWith(const std::string& text, const std::string& suffix) {
    return text.size() >= suffix.size()
        && text.compare(text.size() - suffix.size(),
                        suffix.size(), suffix) == 0;
}

// Rebuild `term` with the subtree that IS `target` (pointer identity)
// replaced. `replacement(depth)` supplies the substitute for the binder
// depth at which the target was found — used both to splice in a
// same-frame term (lifted under any crossed binders) and to abstract a
// hole (BV at the crossing depth).
template <typename Replacement>
ExpressionPointer rebuildAtPointer(const ExpressionPointer& term,
                                   const ExpressionPointer& target,
                                   const Replacement& replacement,
                                   int depth) {
    if (term.get() == target.get()) return replacement(depth);
    if (auto* application = std::get_if<Application>(&term->node)) {
        return makeApplication(
            rebuildAtPointer(application->function, target,
                             replacement, depth),
            rebuildAtPointer(application->argument, target,
                             replacement, depth));
    }
    if (auto* pi = std::get_if<Pi>(&term->node)) {
        return makePi(pi->displayHint,
            rebuildAtPointer(pi->domain, target, replacement, depth),
            rebuildAtPointer(pi->codomain, target, replacement,
                             depth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&term->node)) {
        return makeLambda(lambda->displayHint,
            rebuildAtPointer(lambda->domain, target, replacement, depth),
            rebuildAtPointer(lambda->body, target, replacement,
                             depth + 1));
    }
    if (auto* let = std::get_if<Let>(&term->node)) {
        return makeLet(let->displayHint,
            rebuildAtPointer(let->type, target, replacement, depth),
            rebuildAtPointer(let->value, target, replacement, depth),
            rebuildAtPointer(let->body, target, replacement, depth + 1));
    }
    return term;
}

// Abstract the subtree that IS `target` (pointer identity) out of
// `term`, producing the body of a one-binder motive lambda: the target
// becomes the motive's variable (BV(depth) under `depth` crossed
// binders), and every OTHER BoundVariable free at the current depth —
// a reference into the enclosing local frame — shifts up by one to
// make room for the motive binder. Internal bound references are
// untouched.
ExpressionPointer abstractAtPointer(const ExpressionPointer& term,
                                    const ExpressionPointer& target,
                                    int depth) {
    if (term.get() == target.get()) return makeBoundVariable(depth);
    if (auto* bv = std::get_if<BoundVariable>(&term->node)) {
        if (bv->deBruijnIndex >= depth) {
            return makeBoundVariable(bv->deBruijnIndex + 1);
        }
        return term;
    }
    if (auto* application = std::get_if<Application>(&term->node)) {
        return makeApplication(
            abstractAtPointer(application->function, target, depth),
            abstractAtPointer(application->argument, target, depth));
    }
    if (auto* pi = std::get_if<Pi>(&term->node)) {
        return makePi(pi->displayHint,
            abstractAtPointer(pi->domain, target, depth),
            abstractAtPointer(pi->codomain, target, depth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&term->node)) {
        return makeLambda(lambda->displayHint,
            abstractAtPointer(lambda->domain, target, depth),
            abstractAtPointer(lambda->body, target, depth + 1));
    }
    if (auto* let = std::get_if<Let>(&term->node)) {
        return makeLet(let->displayHint,
            abstractAtPointer(let->type, target, depth),
            abstractAtPointer(let->value, target, depth),
            abstractAtPointer(let->body, target, depth + 1));
    }
    return term;
}

// Does any Constant in `term` satisfy the predicate?
template <typename NamePredicate>
bool containsConstantWhere(const ExpressionPointer& term,
                           const NamePredicate& predicate) {
    if (!term) return false;
    if (auto* constant = std::get_if<Constant>(&term->node)) {
        return predicate(constant->name);
    }
    if (auto* application = std::get_if<Application>(&term->node)) {
        return containsConstantWhere(application->function, predicate)
            || containsConstantWhere(application->argument, predicate);
    }
    if (auto* pi = std::get_if<Pi>(&term->node)) {
        return containsConstantWhere(pi->domain, predicate)
            || containsConstantWhere(pi->codomain, predicate);
    }
    if (auto* lambda = std::get_if<Lambda>(&term->node)) {
        return containsConstantWhere(lambda->domain, predicate)
            || containsConstantWhere(lambda->body, predicate);
    }
    if (auto* let = std::get_if<Let>(&term->node)) {
        return containsConstantWhere(let->type, predicate)
            || containsConstantWhere(let->value, predicate)
            || containsConstantWhere(let->body, predicate);
    }
    return false;
}

} // namespace

bool Elaborator::parseSignJudgment(ExpressionPointer proposition,
                                   SignJudgment& out) const {
    if (!proposition) return false;
    std::vector<ExpressionPointer> arguments;
    std::string head = signSpineHead(proposition, arguments);
    if (head == "Not" && arguments.size() == 1) {
        std::vector<ExpressionPointer> equalityArguments;
        std::string equalityHead =
            signSpineHead(arguments[0], equalityArguments);
        if (equalityHead != "Equality" || equalityArguments.size() != 3) {
            return false;
        }
        auto leftNumeral = asNumeralLiteral(equalityArguments[1]);
        auto rightNumeral = asNumeralLiteral(equalityArguments[2]);
        if (rightNumeral && rightNumeral->second == 0
            && !(leftNumeral && leftNumeral->second == 0)) {
            out = {"neq0", "Equality", equalityArguments[1]};
            return true;
        }
        if (leftNumeral && leftNumeral->second == 0
            && !(rightNumeral && rightNumeral->second == 0)) {
            out = {"neq0", "Equality", equalityArguments[2]};
            return true;
        }
        return false;
    }
    if (arguments.size() == 2) {
        bool weak = endsWith(head, ".LessOrEqual");
        bool strict = endsWith(head, ".LessThan");
        if (!weak && !strict) return false;
        auto leftNumeral = asNumeralLiteral(arguments[0]);
        if (leftNumeral && leftNumeral->second == 0) {
            out = {weak ? "zle" : "zlt", head, arguments[1]};
            return true;
        }
        return false;
    }
    // Unary nonnegativity predicates (`Real.IsNonneg(x)`).
    if (arguments.size() == 1 && endsWith(head, ".IsNonneg")) {
        out = {"nonneg", head, arguments[0]};
        return true;
    }
    return false;
}

std::string Elaborator::signRuleKey(const SignJudgment& judgment) const {
    // Numeral subjects key by canonical (carrier, value) so ground base
    // facts (`0 < 1`, `0 < 2`) register and match across spellings.
    std::string subjectTag;
    if (auto numeral = asNumeralLiteral(judgment.subject)) {
        subjectTag = "num:" + numeral->first + ":"
            + std::to_string(numeral->second);
    } else {
        std::vector<ExpressionPointer> arguments;
        std::string head = signSpineHead(judgment.subject, arguments);
        if (head.empty()) return std::string();
        subjectTag = head;
    }
    return judgment.kindTag + "\x1f" + judgment.relationName + "\x1f"
        + subjectTag;
}

void Elaborator::registerSignJudgmentRule(const std::string& theoremName,
                                          ExpressionPointer typeExpr) {
    const Declaration* declaration = environment_.lookup(theoremName);
    if (!declaration) return;
    auto* asDefinition = std::get_if<Definition>(declaration);
    if (!asDefinition) return;
    if (!asDefinition->universeParameters.empty()) return;
    std::vector<ExpressionPointer> rawDomains;
    ExpressionPointer cursor = typeExpr;
    while (auto* pi = std::get_if<Pi>(&cursor->node)) {
        rawDomains.push_back(pi->domain);
        cursor = pi->codomain;
    }
    SignJudgment conclusion;
    if (!parseSignJudgment(cursor, conclusion)) return;
    // Admission criterion: a premise that is itself a sign judgment
    // must have a bare lemma-binder as its subject — the conclusion
    // match then binds it to a proper subterm of the goal's subject,
    // so discharge is guaranteed structural descent.
    bool hasJudgmentPremise = false;
    std::string premiseKindTag;
    for (const auto& domain : rawDomains) {
        SignJudgment premise;
        if (parseSignJudgment(domain, premise)) {
            if (!std::holds_alternative<BoundVariable>(
                    premise.subject->node)) {
                return;
            }
            hasJudgmentPremise = true;
            premiseKindTag = premise.kindTag + "\x1f"
                + premise.relationName;
        }
    }
    std::string key;
    if (std::holds_alternative<BoundVariable>(conclusion.subject->node)) {
        // Conclusion on a bare binder: a FORM BRIDGE (e.g.
        // `IsNonneg(x) → 0 ≤ x`) — same subject, different judgment
        // form. Registered under the wildcard subject tag; consulted
        // only when no subject-headed rule fires, and never twice in a
        // row (see trySignJudgmentRecursion). A same-form "bridge"
        // (`0 ≤ x → 0 ≤ x` shapes) is useless and would only burn
        // depth — skip it.
        if (!hasJudgmentPremise) return;
        if (premiseKindTag == conclusion.kindTag + "\x1f"
                + conclusion.relationName) {
            return;
        }
        key = conclusion.kindTag + "\x1f" + conclusion.relationName
            + "\x1f*";
    } else {
        key = signRuleKey(conclusion);
    }
    if (key.empty()) return;
    // Multiple rules per key are legitimate ordered alternatives
    // (`IsNonneg.multiply` needs both factors nonneg; `square_IsNonneg`
    // closes `x·x` unconditionally — same (judgment, head) key): the
    // lookup tries them in registration order, first full discharge
    // wins. Track the multiplicity for the eventual audit.
    if (!signRuleIndex_[key].empty()) {
        ++signRuleConflicts_;
    }
    int binderCount = static_cast<int>(rawDomains.size());
    std::vector<ExpressionPointer> binderTypes(binderCount);
    for (int peelIdx = 0; peelIdx < binderCount; ++peelIdx) {
        int conclusionIdx = binderCount - 1 - peelIdx;
        binderTypes[conclusionIdx] = liftBoundVariables(
            rawDomains[peelIdx], binderCount - peelIdx, 0);
    }
    SignRule rule;
    rule.lemmaName = theoremName;
    rule.binderCount = binderCount;
    rule.conclusion = cursor;
    rule.binderTypes = std::move(binderTypes);
    signRuleIndex_[key].push_back(std::move(rule));
}

ExpressionPointer Elaborator::trySignJudgmentRecursion(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int depth,
        bool allowFormBridge) {
    if (depth <= 0) return nullptr;
    SignJudgment judgment;
    if (!parseSignJudgment(goalClosed, judgment)) return nullptr;
    // Subject-headed rules first; if none fires and we didn't just
    // arrive via a bridge, try the form bridges into this judgment
    // (same subject, other form — e.g. `0 ≤ x·y` via `IsNonneg(x·y)`).
    // A bridge's own judgment premise recurses with bridges disallowed,
    // so two bridges can never chain — no form ping-pong.
    std::vector<std::pair<std::string, bool>> probes;
    std::string directKey = signRuleKey(judgment);
    if (!directKey.empty()) probes.emplace_back(directKey, false);
    if (allowFormBridge) {
        probes.emplace_back(
            judgment.kindTag + "\x1f" + judgment.relationName + "\x1f*",
            true);
    }
    for (const auto& [key, bridgeHop] : probes) {
    auto bucket = signRuleIndex_.find(key);
    if (bucket == signRuleIndex_.end()) continue;
    for (const SignRule& rule : bucket->second) {
        std::vector<ExpressionPointer> bindings(rule.binderCount);
        if (!matchAgainstPattern(rule.conclusion, goalClosed,
                                 rule.binderCount, bindings)) {
            continue;
        }
        // Fill the binders the conclusion match left open,
        // outer-to-inner (a binder type may reference outer binders):
        // sign-judgment premises recurse into the index; anything else
        // discharges from a local hypothesis, exactly like
        // tryLemmaIndexLookup's precondition pass.
        Context openedContext =
            buildContextFromLocalBinders(localBinders);
        bool dischargedAll = true;
        for (int i = rule.binderCount - 1; i >= 0; --i) {
            if (bindings[i]) continue;
            if (!binderReferencesAllBound(rule.binderTypes[i],
                                          bindings)) {
                dischargedAll = false;
                break;
            }
            ExpressionPointer slotType = instantiateLemmaBinders(
                rule.binderTypes[i], bindings);
            ExpressionPointer proof;
            SignJudgment premise;
            if (parseSignJudgment(slotType, premise)) {
                proof = trySignJudgmentRecursion(
                    slotType, localBinders, depth - 1,
                    /*allowFormBridge=*/!bridgeHop);
            }
            if (!proof) {
                ExpressionPointer slotTypeOpened = openOverLocalBinders(
                    slotType, localBinders, localBinders.size());
                ExpressionPointer slotTypeNormalised;
                try {
                    slotTypeNormalised = weakHeadNormalForm(
                        environment_, slotTypeOpened);
                } catch (const TypeError&) {
                    dischargedAll = false;
                    break;
                }
                for (int j =
                         static_cast<int>(localBinders.size()) - 1;
                     j >= 0; --j) {
                    ExpressionPointer candidateType =
                        openOverLocalBinders(
                            localBinders[j].type, localBinders, j);
                    bool equal;
                    try {
                        equal = isDefinitionallyEqual(environment_,
                            openedContext, candidateType,
                            slotTypeNormalised);
                    } catch (const TypeError&) {
                        equal = false;
                    }
                    if (equal) {
                        proof = makeBoundVariable(
                            static_cast<int>(localBinders.size())
                            - 1 - j);
                        break;
                    }
                }
            }
            if (!proof) {
                dischargedAll = false;
                break;
            }
            bindings[i] = std::move(proof);
        }
        if (!dischargedAll) continue;
        bool allBound = true;
        for (const auto& binding : bindings) {
            if (!binding) { allBound = false; break; }
        }
        if (!allBound) continue;
        ExpressionPointer call = makeConstant(rule.lemmaName, {});
        for (int i = rule.binderCount - 1; i >= 0; --i) {
            call = makeApplication(std::move(call), bindings[i]);
        }
        static const bool debugEnabled = [] {
            const char* flag = std::getenv("MATH_SIGN_INDEX_DEBUG");
            return flag && flag[0] != '\0' && flag[0] != '0';
        }();
        if (debugEnabled) {
            std::cerr << "[sign-index] " << moduleName_
                << ": rule " << rule.lemmaName
                << (bridgeHop ? " (form bridge)" : "")
                << " closes " << prettyPrint(goalClosed) << "\n";
        }
        return call;
    }
    }

    // ---- B3 cast retry ---------------------------------------------
    // No rule fired and the subject carries casts: push them to the
    // leaves (lemma-mediated, proof-carrying), retry — first a direct
    // defeq scan of the local hypotheses at the normalized form, then
    // the index — and transport the result back along the
    // normalization equality. The normalized subject is cast-normal,
    // so a nested retry is a no-op and the recursion terminates.
    if (containsConstantWhere(judgment.subject,
            [&](const std::string& name) {
                return isCoercionFunctionName(name);
            })) {
        CastNormalForm normalized{};
        try {
            normalized = castPushToLeaves(judgment.subject, localBinders);
        } catch (const ElaborateError&) {
            normalized.proof = nullptr;
        } catch (const TypeError&) {
            normalized.proof = nullptr;
        }
        if (normalized.proof) {
            ExpressionPointer normalizedGoal = rebuildAtPointer(
                goalClosed, judgment.subject,
                [&](int holeDepth) {
                    return liftBoundVariables(
                        normalized.term, holeDepth, 0);
                }, 0);
            // Direct hypothesis at the normalized spelling first (the
            // structural pre-tactic scan saw only the ORIGINAL form).
            ExpressionPointer proofAtNormalized;
            {
                Context openedContext =
                    buildContextFromLocalBinders(localBinders);
                ExpressionPointer normalizedOpened = openOverLocalBinders(
                    normalizedGoal, localBinders, localBinders.size());
                for (int j = static_cast<int>(localBinders.size()) - 1;
                     j >= 0; --j) {
                    ExpressionPointer candidateType = openOverLocalBinders(
                        localBinders[j].type, localBinders, j);
                    bool equal;
                    try {
                        equal = isDefinitionallyEqual(environment_,
                            openedContext, candidateType,
                            normalizedOpened);
                    } catch (const TypeError&) {
                        equal = false;
                    }
                    if (equal) {
                        proofAtNormalized = makeBoundVariable(
                            static_cast<int>(localBinders.size())
                            - 1 - j);
                        break;
                    }
                }
            }
            if (!proofAtNormalized) {
                proofAtNormalized = trySignJudgmentRecursion(
                    normalizedGoal, localBinders, depth - 1,
                    allowFormBridge);
            }
            if (proofAtNormalized) {
                try {
                    ExpressionPointer carrier = closeOverLocalBinders(
                        inferTypeInLocalContext(localBinders,
                                                judgment.subject),
                        localBinders, localBinders.size());
                    LevelPointer level = typeUniverseOf(
                        localBinders, judgment.subject);
                    ExpressionPointer motive = makeLambda(
                        "_sign_z", carrier,
                        abstractAtPointer(goalClosed, judgment.subject,
                                          0));
                    // normalized.proof : subject = normalized.term;
                    // flip it, then transport P(normalized) to
                    // P(subject) — which β-reduces to the goal.
                    ExpressionPointer flipped = makeConstant(
                        "Equality.symmetry", {level});
                    flipped = makeApplication(flipped, carrier);
                    flipped = makeApplication(flipped, judgment.subject);
                    flipped = makeApplication(flipped, normalized.term);
                    flipped = makeApplication(flipped, normalized.proof);
                    ExpressionPointer transported = makeConstant(
                        "Equality.transport_proposition", {level});
                    transported = makeApplication(transported, carrier);
                    transported = makeApplication(transported, motive);
                    transported = makeApplication(transported,
                                                  normalized.term);
                    transported = makeApplication(transported,
                                                  judgment.subject);
                    transported = makeApplication(transported, flipped);
                    transported = makeApplication(transported,
                                                  proofAtNormalized);
                    static const bool debugRetry = [] {
                        const char* flag =
                            std::getenv("MATH_SIGN_INDEX_DEBUG");
                        return flag && flag[0] != '\0'
                            && flag[0] != '0';
                    }();
                    if (debugRetry) {
                        std::cerr << "[sign-index] " << moduleName_
                            << ": cast retry closes "
                            << prettyPrint(goalClosed) << "\n";
                    }
                    return transported;
                } catch (const TypeError&) {
                } catch (const ElaborateError&) {
                }
            }
        }
    }
    return nullptr;
}

