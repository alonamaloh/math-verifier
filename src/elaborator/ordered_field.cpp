// `ordered_field` — linear arithmetic over an ordered field.
// PLAN_ORDERED_FIELD_TACTIC.md; specification is FRICTION_PLANE_LAYER0.md's
// entry I4.
//
// A goal that follows from the ordered-field axioms alone should close the
// way a commutative-ring identity closes with `ring`. Given the in-scope
// hypotheses and the goal, this finds a NONNEGATIVE RATIONAL COMBINATION
// of the hypotheses that yields the goal — Farkas' lemma says one exists
// exactly when the goal is a linear consequence — and emits it as a kernel
// term.
//
// The search is never trusted. Whatever multipliers come out, the emitted
// proof is a fold of real hypothesis proofs over the carrier's
// nonnegativity lemmas plus a bridge equation checked by the ring
// normaliser, so a wrong coefficient vector fails to typecheck rather than
// producing a bad proof. That property is the reason the tactic is
// allowed to contain a search at all — preserve it under any later
// optimisation.
//
// The linear model reuses the ring normaliser wholesale: goal and
// hypotheses become RingPolynomials over ONE shared normalisation context,
// and the linear-model variables are the polynomial's MONOMIAL
// SIGNATURES. So `x · y`, `abs(a − b)` and `innerProduct(u, v)²` are
// ordinary variables and "linear in the atoms" is not a separate check —
// it is what the representation already is.

#include "internal.hpp"

#include <algorithm>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <vector>

namespace {

// The monomial signature, spelled locally: `Elaborator`'s alias is
// private, and this file's helpers live outside the class.
using MonomialSignature = std::vector<uint64_t>;

// One row of the Fourier–Motzkin system: `Σ coefficients[v]·v + constant`
// is `≥ 0`, or `> 0` when `strict`. `multipliers` records the nonnegative
// combination of ORIGINAL rows this row is — the Farkas certificate under
// construction.
struct EliminationRow {
    std::map<MonomialSignature, mpq_class> coefficients;
    mpq_class constant;
    bool strict = false;
    std::vector<mpq_class> multipliers;
};

void dropZeroCoefficients(EliminationRow& row) {
    for (auto iterator = row.coefficients.begin();
         iterator != row.coefficients.end();) {
        if (iterator->second == 0) iterator = row.coefficients.erase(iterator);
        else ++iterator;
    }
}

// `scaleLeft · left + scaleRight · right`, both scales positive.
EliminationRow combineRows(const EliminationRow& left,
                           const mpq_class& scaleLeft,
                           const EliminationRow& right,
                           const mpq_class& scaleRight) {
    EliminationRow result;
    result.constant = scaleLeft * left.constant + scaleRight * right.constant;
    result.strict = left.strict || right.strict;
    result.coefficients = left.coefficients;
    for (auto& entry : result.coefficients) entry.second *= scaleLeft;
    for (const auto& entry : right.coefficients) {
        result.coefficients[entry.first] += scaleRight * entry.second;
    }
    dropZeroCoefficients(result);
    result.multipliers.resize(
        std::max(left.multipliers.size(), right.multipliers.size()), 0);
    for (size_t index = 0; index < left.multipliers.size(); ++index) {
        result.multipliers[index] += scaleLeft * left.multipliers[index];
    }
    for (size_t index = 0; index < right.multipliers.size(); ++index) {
        result.multipliers[index] += scaleRight * right.multipliers[index];
    }
    return result;
}

// A variable-free row is a contradiction when it asserts `k ≥ 0` for a
// negative `k`, or `k > 0` for `k = 0`.
bool rowIsContradictory(const EliminationRow& row) {
    if (!row.coefficients.empty()) return false;
    if (row.constant < 0) return true;
    return row.strict && row.constant == 0;
}

}  // namespace

// ---------------------------------------------------------------------
// The search: Fourier–Motzkin elimination with multiplier tracking.
// ---------------------------------------------------------------------

std::optional<Elaborator::OrderedFieldCertificate>
Elaborator::searchOrderedFieldCertificate(
        const std::vector<OrderedFieldRow>& rows,
        std::string& capReasonOut) {
    capReasonOut.clear();
    // Row and elimination caps. These bound a procedure that is doubly
    // exponential in the worst case; when one trips the caller must say so
    // rather than reporting "no certificate exists" — a bounded search that
    // reads as a completed one is a lie.
    const size_t maximumRows = 512;
    const size_t maximumEliminations = 32;

    std::vector<EliminationRow> system;
    system.reserve(rows.size());
    for (size_t index = 0; index < rows.size(); ++index) {
        EliminationRow row;
        row.strict = rows[index].strict;
        row.multipliers.assign(rows.size(), 0);
        row.multipliers[index] = 1;
        for (const auto& entry : rows[index].polynomial) {
            if (entry.first.empty()) row.constant += mpq_class(entry.second);
            else row.coefficients[entry.first] = mpq_class(entry.second);
        }
        dropZeroCoefficients(row);
        system.push_back(std::move(row));
    }

    auto findRefutation = [&]() -> std::optional<OrderedFieldCertificate> {
        for (const auto& row : system) {
            if (rowIsContradictory(row)) {
                return OrderedFieldCertificate{row.multipliers, row.constant};
            }
        }
        return std::nullopt;
    };
    if (auto immediate = findRefutation()) return immediate;

    std::set<RingMonomialSignature> remaining;
    for (const auto& row : system) {
        for (const auto& entry : row.coefficients) remaining.insert(entry.first);
    }

    size_t eliminations = 0;
    while (!remaining.empty()) {
        if (++eliminations > maximumEliminations) {
            capReasonOut = "the system needed more than "
                + std::to_string(maximumEliminations)
                + " variable eliminations";
            return std::nullopt;
        }
        // Eliminate the variable with the smallest positive×negative
        // product — the standard heuristic for keeping the row count down.
        const RingMonomialSignature* chosen = nullptr;
        size_t bestCost = 0;
        for (const auto& variable : remaining) {
            size_t positives = 0, negatives = 0;
            for (const auto& row : system) {
                auto found = row.coefficients.find(variable);
                if (found == row.coefficients.end()) continue;
                if (found->second > 0) ++positives; else ++negatives;
            }
            size_t cost = positives * negatives;
            if (!chosen || cost < bestCost) { chosen = &variable; bestCost = cost; }
        }
        RingMonomialSignature variable = *chosen;
        remaining.erase(variable);

        std::vector<EliminationRow> next;
        std::vector<const EliminationRow*> positiveRows, negativeRows;
        for (const auto& row : system) {
            auto found = row.coefficients.find(variable);
            if (found == row.coefficients.end()) { next.push_back(row); continue; }
            if (found->second > 0) positiveRows.push_back(&row);
            else negativeRows.push_back(&row);
        }
        for (const auto* positive : positiveRows) {
            for (const auto* negative : negativeRows) {
                const mpq_class& positiveCoefficient =
                    positive->coefficients.at(variable);
                const mpq_class& negativeCoefficient =
                    negative->coefficients.at(variable);
                EliminationRow combined = combineRows(
                    *positive, -negativeCoefficient,
                    *negative, positiveCoefficient);
                combined.coefficients.erase(variable);
                next.push_back(std::move(combined));
                if (next.size() > maximumRows) {
                    capReasonOut = "the elimination produced more than "
                        + std::to_string(maximumRows) + " rows";
                    return std::nullopt;
                }
            }
        }
        system = std::move(next);
        if (auto refutation = findRefutation()) return refutation;
    }
    return std::nullopt;
}

// ---------------------------------------------------------------------
// The failure witness: when the system is satisfiable, values at which
// every hypothesis holds and the goal fails. This is what makes the
// message say WHY rather than only what was tried.
// ---------------------------------------------------------------------

std::map<Elaborator::RingMonomialSignature, mpq_class>
Elaborator::findOrderedFieldWitnessValuation(
        const std::vector<OrderedFieldRow>& rows) {
    std::map<RingMonomialSignature, mpq_class> valuation;
    std::vector<EliminationRow> system;
    for (const auto& source : rows) {
        EliminationRow row;
        row.strict = source.strict;
        for (const auto& entry : source.polynomial) {
            if (entry.first.empty()) row.constant += mpq_class(entry.second);
            else row.coefficients[entry.first] = mpq_class(entry.second);
        }
        dropZeroCoefficients(row);
        system.push_back(std::move(row));
    }
    // Eliminate in a fixed order, remembering each step's pre-elimination
    // rows; then assign in REVERSE, so every other variable in a row
    // already has a value by the time we need it.
    std::vector<std::pair<RingMonomialSignature, std::vector<EliminationRow>>>
        history;
    std::set<RingMonomialSignature> remaining;
    for (const auto& row : system) {
        for (const auto& entry : row.coefficients) remaining.insert(entry.first);
    }
    size_t guard = 0;
    while (!remaining.empty() && ++guard <= 32) {
        RingMonomialSignature variable = *remaining.begin();
        remaining.erase(remaining.begin());
        history.emplace_back(variable, system);
        std::vector<EliminationRow> next;
        std::vector<const EliminationRow*> positiveRows, negativeRows;
        for (const auto& row : system) {
            auto found = row.coefficients.find(variable);
            if (found == row.coefficients.end()) { next.push_back(row); continue; }
            if (found->second > 0) positiveRows.push_back(&row);
            else negativeRows.push_back(&row);
        }
        for (const auto* positive : positiveRows) {
            for (const auto* negative : negativeRows) {
                EliminationRow combined = combineRows(
                    *positive, -negative->coefficients.at(variable),
                    *negative, positive->coefficients.at(variable));
                combined.coefficients.erase(variable);
                next.push_back(std::move(combined));
                if (next.size() > 512) return {};
            }
        }
        system = std::move(next);
    }
    for (auto step = history.rbegin(); step != history.rend(); ++step) {
        const RingMonomialSignature& variable = step->first;
        bool hasLower = false, hasUpper = false;
        bool lowerStrict = false, upperStrict = false;
        mpq_class lower = 0, upper = 0;
        for (const auto& row : step->second) {
            auto found = row.coefficients.find(variable);
            if (found == row.coefficients.end()) continue;
            // rest = constant + Σ (other coefficients · their values)
            mpq_class rest = row.constant;
            bool resolvable = true;
            for (const auto& entry : row.coefficients) {
                if (entry.first == variable) continue;
                auto value = valuation.find(entry.first);
                if (value == valuation.end()) { resolvable = false; break; }
                rest += entry.second * value->second;
            }
            if (!resolvable) continue;
            mpq_class bound = -rest / found->second;
            if (found->second > 0) {
                if (!hasLower || bound > lower) {
                    lower = bound; hasLower = true; lowerStrict = row.strict;
                } else if (bound == lower && row.strict) lowerStrict = true;
            } else {
                if (!hasUpper || bound < upper) {
                    upper = bound; hasUpper = true; upperStrict = row.strict;
                } else if (bound == upper && row.strict) upperStrict = true;
            }
        }
        mpq_class value = 0;
        if (hasLower && hasUpper) value = (lower + upper) / 2;
        else if (hasLower) value = lowerStrict ? lower + 1 : lower;
        else if (hasUpper) value = upperStrict ? upper - 1 : upper;
        value.canonicalize();
        valuation[variable] = value;
    }
    return valuation;
}

// ---------------------------------------------------------------------
// The tactic.
// ---------------------------------------------------------------------

namespace {

// A goal or hypothesis read as an order relation at a concrete carrier.
struct OrderProposition {
    std::string carrierName;   // "Real"
    ExpressionPointer left;
    ExpressionPointer right;
    bool strict = false;       // `<` rather than `≤`
};

// Read `C.LessOrEqual(a, b)` / `C.LessThan(a, b)` off the FOLDED form.
// Weak-head-normalising first would be exactly wrong: `Real.LessOrEqual`
// is a `definition`, so WHNF unfolds the head we are trying to read and
// the relation disappears into its representative-level body.
std::optional<OrderProposition> parseFoldedOrderProposition(
        ExpressionPointer proposition) {
    auto* outer = std::get_if<Application>(&proposition->node);
    if (!outer) return std::nullopt;
    auto* inner = std::get_if<Application>(&outer->function->node);
    if (!inner) return std::nullopt;
    auto* head = std::get_if<Constant>(&inner->function->node);
    if (!head) return std::nullopt;
    const std::string weakSuffix = ".LessOrEqual";
    const std::string strictSuffix = ".LessThan";
    OrderProposition parsed;
    if (head->name.size() > weakSuffix.size()
        && head->name.compare(head->name.size() - weakSuffix.size(),
                              weakSuffix.size(), weakSuffix) == 0) {
        parsed.carrierName =
            head->name.substr(0, head->name.size() - weakSuffix.size());
        parsed.strict = false;
    } else if (head->name.size() > strictSuffix.size()
        && head->name.compare(head->name.size() - strictSuffix.size(),
                              strictSuffix.size(), strictSuffix) == 0) {
        parsed.carrierName =
            head->name.substr(0, head->name.size() - strictSuffix.size());
        parsed.strict = true;
    } else {
        return std::nullopt;
    }
    // A dotted remainder means the head is something like
    // `Real.LessOrEqual.negate`, not the relation itself.
    if (parsed.carrierName.find('.') != std::string::npos) return std::nullopt;
    parsed.left = inner->argument;
    parsed.right = outer->argument;
    return parsed;
}

// The folded form is the normal case. A β-redex — a binder whose type
// arrived as `(λ p. …)(x)`, the way an `Exists` destructuring leaves it —
// needs one WHNF step to expose the application spine, so retry there;
// but only when the folded read failed, never before it.
std::optional<OrderProposition> parseOrderProposition(
        const Environment& environment, ExpressionPointer proposition) {
    if (auto folded = parseFoldedOrderProposition(proposition)) return folded;
    return parseFoldedOrderProposition(
        weakHeadNormalForm(environment, proposition));
}

}  // namespace

ExpressionPointer Elaborator::elaborateOrderedField(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
    Frame frame(*this, "ordered_field at line " + std::to_string(line),
                localBinders, expectedType, line, column);
    if (!expectedType) {
        throwElaborate("`ordered_field` needs an order goal from context");
    }
    size_t binderCount = localBinders.size();
    ExpressionPointer goalOpened =
        openOverLocalBinders(expectedType, localBinders, binderCount);
    std::optional<OrderProposition> goal =
        parseOrderProposition(environment_, goalOpened);
    // A `False` goal is the reductio idiom (`suppose … for contradiction
    // { …; done }`): there is nothing to negate, the hypotheses must be
    // inconsistent on their own. The carrier then has to come from them,
    // so read it off the first order hypothesis in scope.
    bool provingFalse = false;
    if (!goal && headConstantName(goalOpened) == "False") {
        for (const ContextFact& fact : collectLocalBinderFacts(localBinders)) {
            goal = parseOrderProposition(
                environment_,
                openOverLocalBinders(fact.type, localBinders, binderCount));
            if (goal) break;
        }
        if (!goal) {
            throwElaborate(
                "`ordered_field`: the goal is `False`, but no in-scope "
                "hypothesis is an order relation at a concrete carrier, so "
                "there is nothing to derive a contradiction from and no "
                "carrier to work over.");
        }
        provingFalse = true;
    }
    if (!goal) {
        throwElaborate(
            "`ordered_field`: the goal `"
            + prettyPrintInLocalScope(expectedType, localBinders)
            + "` is not an order relation at a concrete carrier. The tactic "
              "proves `≤` and `<` goals, and `False` from contradictory "
              "order hypotheses; for an equality use `ring` or "
              "`linear_combination`, and for a bundled-carrier order there "
              "is no ordered-field structure in the library to read the "
              "operations from.");
    }
    const std::string& carrierName = goal->carrierName;
    ExpressionPointer carrierType = makeConstant(carrierName);
    if (!environment_.lookup(carrierName)) {
        throwElaborate("`ordered_field`: carrier `" + carrierName
                       + "` is not in scope");
    }
    // `typeUniverseOf` opens its argument itself, so it wants the CLOSED
    // spelling — passing the already-opened endpoint happens to work
    // (opening is idempotent on FreeVariables) but violates the contract.
    LevelPointer carrierUniverseLevel = typeUniverseOf(
        localBinders,
        closeOverLocalBinders(goal->left, localBinders, binderCount));

    // The carrier's name table. `ordered_field` names a THEORY; the
    // implementation is this table until the library grows an ordered-field
    // bundle to read the operations from. A carrier missing an entry gets
    // told which one, rather than a generic decline.
    struct LemmaNames {
        std::string nonnegOfWeak, positiveOfStrict, nonnegOfEqual;
        std::string addNonneg, addPositiveNonneg, addNonnegPositive,
                    addPositivePositive, nonnegOfPositive;
        std::string weakCombination, strictCombination, irreflexive;
    } names;
    names.nonnegOfWeak = carrierName + ".nonneg_subtract_of_LessOrEqual";
    names.positiveOfStrict = carrierName + ".subtract_positive_of_LessThan";
    names.nonnegOfEqual = carrierName + ".nonneg_subtract_of_equal";
    names.addNonneg = carrierName + ".add_nonneg";
    names.addPositiveNonneg = carrierName + ".add_positive_nonneg";
    names.addNonnegPositive = carrierName + ".add_nonneg_positive";
    names.addPositivePositive = carrierName + ".add_positive_positive";
    names.nonnegOfPositive = carrierName + ".nonneg_of_positive";
    names.weakCombination =
        carrierName + ".LessOrEqual_of_scaled_nonneg_combination";
    names.strictCombination =
        carrierName + ".LessThan_of_scaled_positive_combination";
    names.irreflexive = carrierName + ".LessThan.irreflexive";
    for (const std::string* required : {
            &names.nonnegOfWeak, &names.positiveOfStrict,
            &names.nonnegOfEqual, &names.addNonneg,
            &names.addPositiveNonneg, &names.addNonnegPositive,
            &names.addPositivePositive, &names.nonnegOfPositive,
            &names.weakCombination, &names.strictCombination,
            &names.irreflexive}) {
        if (!environment_.lookup(*required)) {
            throwElaborate(
                "`ordered_field`: carrier `" + carrierName
                + "` is missing `" + *required
                + "`, which the certificate is assembled from. Either import "
                  "the module that defines it, or the carrier does not yet "
                  "carry the ordered-field lemma table (only carriers with "
                  "the full table are supported).");
        }
    }

    // ONE normalisation context for the goal and every hypothesis: the
    // atom hashes have to agree across rows or the linear model is
    // nonsense.
    RingScheme scheme = computeRingScheme(carrierType);
    RingStructurePrefixGuard prefixGuard(*this, scheme.structurePrefix);
    RingNormalisationContext context;
    context.carrierName = carrierName;
    context.carrierType = carrierType;
    context.carrierUniverseLevel = carrierUniverseLevel;
    context.opNamespace = scheme.opNamespace;
    context.isRingName = scheme.opNamespace + ".is_ring";
    context.addName = scheme.opNamespace + ".add";
    context.multiplyName = scheme.opNamespace + ".multiply";
    context.negateName = scheme.opNamespace + ".negate";
    context.subtractName = scheme.opNamespace + ".subtract";
    context.zeroName = scheme.opNamespace + ".zero";
    context.oneName = scheme.opNamespace + ".one";
    populateRingEmbeddingChain(context);
    // Coefficients and the denominator-clearing scale are emitted as
    // carrier numerals, which needs the embedding-chain literal story.
    if (!ringContextUsesLiteralCoefficients(context)) {
        throwElaborate(
            "`ordered_field`: carrier `" + carrierName
            + "` has no numeral story (its embedding chain from Natural is "
              "incomplete in this file), so a certificate's coefficients "
              "cannot be spelled. Import the carrier's embedding modules.");
    }

    // A `False` goal is proved by deriving `0 < 0` and hitting it with
    // irreflexivity, so retarget it at the carrier's zero. Everything
    // downstream — certificate, bridge, concluding lemma — is unchanged.
    if (provingFalse) {
        goal->left = buildRingZeroKernel(context);
        goal->right = goal->left;
        goal->strict = true;
    }

    auto subtractTerm = [&](ExpressionPointer larger,
                            ExpressionPointer smaller) {
        return makeApplication(
            makeApplication(makeConstant(context.subtractName), larger),
            smaller);
    };
    auto polynomialOfDifference = [&](ExpressionPointer larger,
                                      ExpressionPointer smaller) {
        RingPolynomial difference = normaliseToRingPolynomial(
            unfoldFieldDivides(larger, carrierName), context);
        RingPolynomial subtrahend = normaliseToRingPolynomial(
            unfoldFieldDivides(smaller, carrierName), context);
        ringPolynomialSubtract(difference, subtrahend);
        ringPolynomialCompact(difference);
        return difference;
    };

    // Rows from the context. A hypothesis `a ≤ b` becomes `b − a ≥ 0`,
    // proved by the carrier's subtraction bridge applied to it; an
    // equation `a = b` becomes BOTH `b − a ≥ 0` and `a − b ≥ 0`, so a
    // proof that mixes equations with inequalities does not have to
    // convert them by hand first.
    std::vector<OrderedFieldRow> rows;
    std::vector<std::string> skippedFacts;
    auto addRow = [&](const std::string& label, ExpressionPointer smaller,
                      ExpressionPointer larger, bool strict,
                      ExpressionPointer bridgeName, ExpressionPointer proof) {
        OrderedFieldRow row;
        row.strict = strict;
        row.label = label;
        row.expression = subtractTerm(larger, smaller);
        row.polynomial = polynomialOfDifference(larger, smaller);
        ExpressionPointer bridge = makeApplication(bridgeName, smaller);
        bridge = makeApplication(bridge, larger);
        row.proof = makeApplication(bridge, proof);
        rows.push_back(std::move(row));
    };
    for (const ContextFact& fact : collectLocalBinderFacts(localBinders)) {
        ExpressionPointer factType =
            openOverLocalBinders(fact.type, localBinders, binderCount);
        ExpressionPointer factProof =
            openOverLocalBinders(fact.proofTerm, localBinders, binderCount);
        if (std::optional<OrderProposition> relation =
                parseOrderProposition(environment_, factType)) {
            if (relation->carrierName != carrierName) {
                skippedFacts.push_back(
                    fact.source + " (at `" + relation->carrierName
                    + "`, not `" + carrierName + "`)");
                continue;
            }
            addRow(fact.source, relation->left, relation->right,
                   relation->strict,
                   makeConstant(relation->strict ? names.positiveOfStrict
                                                 : names.nonnegOfWeak),
                   factProof);
            continue;
        }
        // An equation at the carrier: two weak rows, the second built on
        // the symmetric proof so one bridge lemma serves both.
        EqualityComponents equation;
        try {
            equation = extractEqualityComponents(
                weakHeadNormalForm(environment_, factType),
                "ordered_field hypothesis", line);
        } catch (const ElaborateError&) {
            continue;
        }
        if (headConstantName(equation.carrierType) != carrierName) continue;
        ExpressionPointer equalityBridge = makeConstant(names.nonnegOfEqual);
        addRow(fact.source, equation.leftEndpoint, equation.rightEndpoint,
               false, equalityBridge, factProof);
        addRow(fact.source, equation.rightEndpoint, equation.leftEndpoint,
               false, equalityBridge,
               buildEqualitySymmetry(
                   equation.carrierUniverseLevel, equation.carrierType,
                   equation.leftEndpoint, equation.rightEndpoint, factProof));
    }
    size_t hypothesisCount = rows.size();

    // The negated goal. `L ≤ R` is refuted by `L − R > 0`; `L < R` by
    // `L − R ≥ 0`. It carries no proof — it is discharged by the
    // contradiction, never used as a term.
    size_t goalRowIndex = 0;
    if (!provingFalse) {
        OrderedFieldRow goalRow;
        goalRow.strict = !goal->strict;
        goalRow.label = "the negated goal";
        goalRow.polynomial = polynomialOfDifference(goal->left, goal->right);
        rows.push_back(goalRow);
        goalRowIndex = rows.size() - 1;
    }

    std::string capReason;
    std::optional<OrderedFieldCertificate> certificate =
        searchOrderedFieldCertificate(rows, capReason);

    // Everything user-facing prints the CLOSED term: an opened one shows
    // the elaborator's `@`-prefixed FreeVariables, which are not the
    // author's spelling of anything.
    auto describeClosed = [&](ExpressionPointer opened) {
        return prettyPrintInLocalScope(
            closeOverLocalBinders(opened, localBinders, binderCount),
            localBinders);
    };
    auto describeMonomial = [&](const RingMonomialSignature& signature) {
        return describeClosed(
            buildCanonicalMonomial(signature, RingCoefficient(1), context));
    };
    auto countedHypotheses = [&]() {
        return std::to_string(hypothesisCount)
             + (hypothesisCount == 1 ? " in-scope order hypothesis"
                                     : " in-scope order hypotheses");
    };
    // Monomials of degree ≥ 2 are independent variables of the linear
    // model. When the goal turns on one, saying so is the difference
    // between "your goal is false" and "this fragment cannot see it".
    auto describeNonlinearity = [&]() {
        std::set<std::string> compound;
        for (const auto& row : rows) {
            for (const auto& entry : row.polynomial) {
                if (entry.first.size() >= 2) {
                    compound.insert(describeMonomial(entry.first));
                }
            }
        }
        if (compound.empty()) return std::string();
        std::string text =
            " Note that the goal is not linear: ";
        bool first = true;
        for (const auto& name : compound) {
            if (!first) text += ", ";
            text += "`" + name + "`";
            first = false;
        }
        return text
             + (compound.size() == 1
                    ? " is an independent variable of the linear model, and "
                      "nothing relates it to its factors."
                    : " are independent variables of the linear model, and "
                      "nothing relates them to their factors.")
             + " That is a limit of the ordered-field fragment, not a false "
               "goal.";
    };
    auto describeSkipped = [&]() {
        if (skippedFacts.empty()) return std::string();
        std::string text = " Not read as rows: ";
        for (size_t index = 0; index < skippedFacts.size(); ++index) {
            if (index) text += ", ";
            text += "`" + skippedFacts[index] + "`";
        }
        return text + ".";
    };

    if (!capReason.empty()) {
        throwElaborate(
            "`ordered_field`: the search for a nonnegative combination "
            "proving `" + describeClosed(goalOpened)
            + "` hit a cap — " + capReason + " (from " + countedHypotheses()
            + "). No conclusion was reached: the goal may still be a linear "
              "consequence." + describeSkipped());
    }
    if (!certificate) {
        std::map<RingMonomialSignature, mpq_class> valuation =
            findOrderedFieldWitnessValuation(rows);
        std::string witness;
        for (const auto& entry : valuation) {
            if (!witness.empty()) witness += ", ";
            witness += describeMonomial(entry.first) + " = "
                     + entry.second.get_str();
        }
        if (provingFalse) {
            throwElaborate(
                "`ordered_field`: the " + countedHypotheses()
                + (hypothesisCount == 1 ? " is" : " are")
                + " consistent, so no nonnegative combination of them "
                  "reaches a contradiction"
                + (witness.empty()
                       ? std::string(".")
                       : (" — they all hold at " + witness + "."))
                + describeSkipped());
        }
        throwElaborate(
            "`ordered_field`: no nonnegative combination of the "
            + countedHypotheses() + " yields `" + describeClosed(goalOpened)
            + "`"
            + (witness.empty()
                   ? std::string(" — it is not a linear consequence of them.")
                   : (" — they all hold at " + witness
                      + " while the goal fails there, so it is not a linear "
                        "consequence of them."))
            + describeNonlinearity() + describeSkipped());
    }
    if (!provingFalse && certificate->rowMultipliers[goalRowIndex] == 0) {
        throwElaborate(
            "`ordered_field`: the in-scope hypotheses are already "
            "contradictory, so the goal follows vacuously rather than by a "
            "nonnegative combination. `ordered_field` builds a direct proof "
            "and cannot express that; close the goal by contradiction "
            "instead.");
    }

    // Direct form: divide the refutation through by the negated goal's
    // multiplier. `R − L = Σ cᵢ·Qᵢ + slack`, all cᵢ and slack ≥ 0.
    mpq_class goalMultiplier =
        provingFalse ? mpq_class(1) : certificate->rowMultipliers[goalRowIndex];
    std::vector<mpq_class> coefficients(hypothesisCount);
    for (size_t index = 0; index < hypothesisCount; ++index) {
        coefficients[index] = certificate->rowMultipliers[index] / goalMultiplier;
        coefficients[index].canonicalize();
    }
    mpq_class slack = -certificate->constant / goalMultiplier;
    slack.canonicalize();

    // Clear denominators so the emitter only ever handles integers:
    // `scale · (R − L) = Σ nᵢ·Qᵢ + integerSlack`.
    mpz_class scale = 1;
    auto absorbDenominator = [&](const mpq_class& value) {
        mpz_class denominator = value.get_den();
        mpz_class divisor;
        mpz_gcd(divisor.get_mpz_t(), scale.get_mpz_t(),
                denominator.get_mpz_t());
        scale = scale / divisor * denominator;
    };
    for (const auto& coefficient : coefficients) absorbDenominator(coefficient);
    absorbDenominator(slack);

    std::vector<mpz_class> repeats(hypothesisCount);
    mpz_class totalCopies = 0;
    for (size_t index = 0; index < hypothesisCount; ++index) {
        mpq_class scaled = coefficients[index] * scale;
        repeats[index] = scaled.get_num() / scaled.get_den();
        totalCopies += repeats[index];
    }
    mpq_class scaledSlack = slack * scale;
    mpz_class integerSlack = scaledSlack.get_num() / scaledSlack.get_den();
    // The certificate is emitted as repeated ADDITION rather than
    // multiplication, which keeps the nonnegativity fold to the four
    // `add_*` lemmas and needs no `0 ≤ c` proof for a coefficient. The
    // price is a term linear in the coefficient size, so it is capped.
    const long maximumCopies = 64;
    if (totalCopies > maximumCopies) {
        throwElaborate(
            "`ordered_field`: the certificate exists but its coefficients "
            "sum to " + totalCopies.get_str() + ", over the emitter's cap of "
            + std::to_string(maximumCopies)
            + " — it is emitted as repeated addition, so a large coefficient "
              "means a large proof term. The goal IS a linear consequence; "
              "this is an emitter limit, not a mathematical one.");
    }

    // Build the certificate expression and its nonnegativity proof
    // together, folding left: `Q + Q + … + slack`.
    ExpressionPointer certificateExpression = nullptr;
    ExpressionPointer certificateProof = nullptr;
    bool certificateStrict = false;
    auto addTerm = [&](ExpressionPointer term, ExpressionPointer proof,
                       bool strict) {
        if (!certificateExpression) {
            certificateExpression = term;
            certificateProof = proof;
            certificateStrict = strict;
            return;
        }
        std::string lemma =
            certificateStrict
                ? (strict ? names.addPositivePositive : names.addPositiveNonneg)
                : (strict ? names.addNonnegPositive : names.addNonneg);
        ExpressionPointer call = makeConstant(lemma);
        call = makeApplication(call, certificateExpression);
        call = makeApplication(call, term);
        call = makeApplication(call, certificateProof);
        call = makeApplication(call, proof);
        certificateExpression = makeApplication(
            makeApplication(makeConstant(context.addName),
                            certificateExpression),
            term);
        certificateProof = call;
        certificateStrict = certificateStrict || strict;
    };
    for (size_t index = 0; index < hypothesisCount; ++index) {
        for (mpz_class copy = 0; copy < repeats[index]; ++copy) {
            addTerm(rows[index].expression, rows[index].proof,
                    rows[index].strict);
        }
    }
    if (integerSlack != 0 || !certificateExpression) {
        ExpressionPointer slackTerm =
            integerSlack == 0
                ? buildRingZeroKernel(context)
                : buildEmbeddedCoefficientKernel(integerSlack, context);
        ExpressionPointer slackGoal = makeApplication(
            makeApplication(
                makeConstant(carrierName + (integerSlack > 0
                                                ? ".LessThan"
                                                : ".LessOrEqual")),
                buildRingZeroKernel(context)),
            slackTerm);
        ExpressionPointer slackProof = autoProveClaim(
            closeOverLocalBinders(slackGoal, localBinders, binderCount),
            localBinders, line);
        addTerm(slackTerm,
                openOverLocalBinders(slackProof, localBinders, binderCount),
                integerSlack > 0);
    }

    // A `≤` goal accepts a strictly positive certificate; weaken it.
    if (!goal->strict && certificateStrict) {
        ExpressionPointer weaken = makeConstant(names.nonnegOfPositive);
        weaken = makeApplication(weaken, certificateExpression);
        certificateProof = makeApplication(weaken, certificateProof);
        certificateStrict = false;
    }
    // Invariant: a strict goal's negated row is WEAK, so a refutation can
    // only come from a strict row or a negative constant — either way the
    // certificate is strict by the time we get here.
    if (goal->strict && !certificateStrict) {
        throwElaborate(
            "`ordered_field`: internal invariant — a refutation of the "
            "negated strict goal `" + describeClosed(goal->left) + " < "
            + describeClosed(goal->right)
            + "` produced a certificate with no strictness. Please report "
              "this with the proof that triggered it.");
    }

    // The bridge, checked by `ring`: this is what makes the search safe to
    // be a heuristic.
    ExpressionPointer scaleTerm =
        scale == 1 ? buildRingOneKernel(context)
                   : buildEmbeddedCoefficientKernel(scale, context);
    ExpressionPointer bridgeLeft = makeApplication(
        makeApplication(makeConstant(context.multiplyName), scaleTerm),
        subtractTerm(goal->right, goal->left));
    ExpressionPointer bridgeProof = elaborateRingByNormalisation(
        localBinders, bridgeLeft, certificateExpression,
        carrierType, carrierUniverseLevel, carrierName, line);

    ExpressionPointer scalePositiveGoal = makeApplication(
        makeApplication(makeConstant(carrierName + ".LessThan"),
                        buildRingZeroKernel(context)),
        scaleTerm);
    ExpressionPointer scalePositiveProof = openOverLocalBinders(
        autoProveClaim(
            closeOverLocalBinders(scalePositiveGoal, localBinders, binderCount),
            localBinders, line),
        localBinders, binderCount);

    ExpressionPointer conclusion = makeConstant(
        goal->strict ? names.strictCombination : names.weakCombination);
    for (ExpressionPointer argument : {
            goal->left, goal->right, certificateExpression, scaleTerm,
            scalePositiveProof, certificateProof, bridgeProof}) {
        conclusion = makeApplication(conclusion, argument);
    }
    if (provingFalse) {
        conclusion = makeApplication(
            makeApplication(makeConstant(names.irreflexive), goal->left),
            conclusion);
    }
    (void)column;
    return closeOverLocalBinders(conclusion, localBinders, binderCount);
}

// ---------------------------------------------------------------------------
// `ordered_field` as an auto-prover tier.
//
// The tactic above throws a helpful message when it cannot apply, which is
// right for `by ordered_field` — the author asked for it by name. As a tier
// the same failure has to be a quiet decline, so the battery can move on.
//
// Cost: the caller places this LAST, after every other tier has missed, so
// in a library that verifies it runs on nothing. What it changes is the
// error path — a linear consequence of the hypotheses now closes instead of
// being reported, which is the whole point: a step a mathematician would not
// have annotated no longer has to be.
ExpressionPointer Elaborator::tryOrderedFieldTier(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        int line) {
    if (inOrderedFieldTier_) return nullptr;

    size_t binderCount = localBinders.size();
    ExpressionPointer goalOpened;
    try {
        goalOpened =
            openOverLocalBinders(goalClosed, localBinders, binderCount);
    } catch (const ElaborateError&) {
        return nullptr;
    } catch (const TypeError&) {
        return nullptr;
    }
    if (!goalOpened) return nullptr;
    // The gate. `False` is admitted because it is the reductio idiom
    // (`suppose … for contradiction`), where the contradiction is among the
    // hypotheses; the tactic itself checks that some hypothesis is an order
    // relation and declines otherwise.
    if (!parseOrderProposition(environment_, goalOpened)
        && headConstantName(goalOpened) != "False") {
        return nullptr;
    }

    // RAII so the flag is cleared even when AutoProverBudgetError unwinds
    // through — that one must NOT be swallowed, or the budget stops binding.
    struct Guard {
        bool& flag;
        explicit Guard(bool& f) : flag(f) { flag = true; }
        ~Guard() { flag = false; }
    } guard(inOrderedFieldTier_);

    try {
        return elaborateOrderedField(
            localBinders, goalClosed, line, /*column=*/0);
    } catch (const ElaborateError&) {
        return nullptr;
    } catch (const TypeError&) {
        return nullptr;
    }
}
