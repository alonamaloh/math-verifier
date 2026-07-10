// Ground-relation decision tier (PLAN_FAST_NUMERALS §D).
//
// Decides ground `=` / `≠` / `≤` / `<` at ℕ/ℤ/ℚ (plus `Integer.IsNonneg`)
// by computing the answer with GMP and emitting a fixed spine of
// `ground_arithmetic` library lemmas. The kernel then checks the leaf
// premises by literal computation (the Stage-1 accelerated-op table), so
// no search happens: the tier either recognizes a ground goal and proves
// it in O(term size) lemma applications, or declines with nullptr.
//
// Shape of the certificates:
//   ℕ  — a term WHNFs to a NaturalLiteral (`zero` / successor chains
//        included); relations become `lt_intro` / `LessThan.weaken` /
//        `not_equal_of_less_than` witnesses over literals.
//   ℤ  — an operation tree over ground leaves normalizes to a canonical
//        `from_difference(litP, litN)` via the `*_evaluates` lemmas;
//        relations discharge through `Integer.ground_*`, whose premises
//        are ground-ℕ facts.
//   ℚ  — likewise to `fraction(n, d, _)` with ground-ℤ components via
//        `Rational.*_evaluates` / `Rational.ground_*`, one certificate
//        layer down.
//
// Every emitted lemma is looked up by name first; when one is not in
// scope (the file doesn't import the ground_arithmetic modules) the tier
// declines silently and the ordinary tactics proceed.

#include "elaborator/internal.hpp"

namespace {

struct SpineView {
    std::string headName;               // empty when the head is not a Constant
    std::vector<ExpressionPointer> args;  // in application order
};

SpineView decomposeSpine(ExpressionPointer term) {
    SpineView view;
    ExpressionPointer cursor = term;
    while (auto* application = std::get_if<Application>(&cursor->node)) {
        view.args.push_back(application->argument);
        cursor = application->function;
    }
    std::reverse(view.args.begin(), view.args.end());
    if (auto* constant = std::get_if<Constant>(&cursor->node)) {
        view.headName = constant->name;
    }
    return view;
}

ExpressionPointer applyAll(ExpressionPointer head,
                           std::initializer_list<ExpressionPointer> args) {
    ExpressionPointer result = std::move(head);
    for (const ExpressionPointer& argument : args) {
        result = makeApplication(std::move(result), argument);
    }
    return result;
}

// A term can only be ground if its VALUE positions mention no hypothesis
// (FreeVariable) and no bound variable — the proof slot of a partial
// operator (`fraction` / `…divide`'s nonzero witness) may legitimately be
// a hypothesis and is never read numerically, so it is skipped. Cheap
// structural pre-check with a node budget so a huge non-ground term never
// pays a WHNF here; DAG sharing can make the walk revisit nodes, which
// the budget also bounds.
bool quickGroundScan(const ExpressionPointer& term, int& budget) {
    if (--budget < 0) return false;
    if (std::holds_alternative<FreeVariable>(term->node)
        || std::holds_alternative<BoundVariable>(term->node)) {
        return false;
    }
    if (std::holds_alternative<Application>(term->node)) {
        SpineView view = decomposeSpine(term);
        bool proofCarrying =
            view.args.size() == 3
            && (view.headName == "Rational.fraction"
                || view.headName == "Rational.divide"
                || view.headName == "Integer.divide"
                || view.headName == "Natural.divide");
        size_t scanUpTo = proofCarrying ? 2 : view.args.size();
        if (view.headName.empty()) {
            // The head is not a constant (a λ-redex or a variable head) —
            // scan everything; the variable case fails in the recursion.
            auto* application = std::get_if<Application>(&term->node);
            return quickGroundScan(application->function, budget)
                && quickGroundScan(application->argument, budget);
        }
        for (size_t index = 0; index < scanUpTo; ++index) {
            if (!quickGroundScan(view.args[index], budget)) return false;
        }
        return true;
    }
    if (auto* let = std::get_if<Let>(&term->node)) {
        return quickGroundScan(let->value, budget)
            && quickGroundScan(let->body, budget);
    }
    return true;
}

// Canonical (positive, negative) presentation of a signed value.
std::pair<NaturalValue, NaturalValue> signedToParts(const NaturalValue& value) {
    if (value >= 0) return {value, NaturalValue(0)};
    return {NaturalValue(0), NaturalValue(-value)};
}

}  // namespace

// ── Ground ℕ reading ─────────────────────────────────────────────────

std::optional<NaturalValue> Elaborator::tryGroundNaturalValue(
        ExpressionPointer termOpened) {
    // Mirrors the kernel's accelerated-table reader: accept a literal,
    // `zero`, or a successor chain over either, in any mixture (reading
    // only literals would split defeq classes — see the Stage-2 record).
    NaturalValue offset = 0;
    ExpressionPointer argument = termOpened;
    for (int guard = 0; guard < 100000; ++guard) {
        if (auto* literal = std::get_if<NaturalLiteral>(&argument->node)) {
            return NaturalValue(offset + literal->value);
        }
        if (std::holds_alternative<BoundVariable>(argument->node)
            || std::holds_alternative<FreeVariable>(argument->node)) {
            return std::nullopt;
        }
        ExpressionPointer reduced = weakHeadNormalForm(environment_, argument);
        if (auto* literal = std::get_if<NaturalLiteral>(&reduced->node)) {
            return NaturalValue(offset + literal->value);
        }
        if (auto* constant = std::get_if<Constant>(&reduced->node)) {
            if (constant->name == "zero") return offset;
            return std::nullopt;
        }
        if (auto* application = std::get_if<Application>(&reduced->node)) {
            auto* head = std::get_if<Constant>(&application->function->node);
            if (head && head->name == "successor") {
                ++offset;
                argument = application->argument;
                continue;
            }
        }
        return std::nullopt;
    }
    return std::nullopt;
}

// ── Shared term/proof builders ───────────────────────────────────────

// `reflexivity(Carrier, value) : value = value`. All three ground
// carriers live in Type(0), so the universe argument is the constant 0.
static ExpressionPointer makeCarrierReflexivity(
        const std::string& carrierName, ExpressionPointer value) {
    return applyAll(
        makeConstant("reflexivity", {makeLevelConst(0)}),
        {makeConstant(carrierName), std::move(value)});
}

static ExpressionPointer makeFromDifferenceLiteral(
        const NaturalValue& positivePart, const NaturalValue& negativePart) {
    return applyAll(makeConstant("Integer.from_difference"),
                    {makeNaturalLiteral(positivePart),
                     makeNaturalLiteral(negativePart)});
}

// ── Ground ℕ relation witnesses ──────────────────────────────────────

ExpressionPointer Elaborator::makeGroundNaturalLessThanProof(
        const NaturalValue& smaller, const NaturalValue& larger) {
    if (!(smaller < larger)) return nullptr;
    if (!environment_.lookup("Natural.lt_intro")) return nullptr;
    // lt_intro(a, b, gap, h : a + (1 + gap) = b) with gap = b − a − 1;
    // the premise is a literal computation, so `reflexivity(b)` checks.
    NaturalValue gap = larger - smaller - 1;
    return applyAll(makeConstant("Natural.lt_intro"),
                    {makeNaturalLiteral(smaller),
                     makeNaturalLiteral(larger),
                     makeNaturalLiteral(gap),
                     makeCarrierReflexivity(
                         "Natural", makeNaturalLiteral(larger))});
}

ExpressionPointer Elaborator::makeGroundNaturalLessOrEqualProof(
        const NaturalValue& smaller, const NaturalValue& larger) {
    if (smaller == larger) {
        if (!environment_.lookup("Natural.LessOrEqual.reflexive"))
            return nullptr;
        return makeApplication(
            makeConstant("Natural.LessOrEqual.reflexive"),
            makeNaturalLiteral(smaller));
    }
    if (!(smaller < larger)) return nullptr;
    if (!environment_.lookup("Natural.LessThan.weaken")) return nullptr;
    ExpressionPointer strict = makeGroundNaturalLessThanProof(smaller, larger);
    if (!strict) return nullptr;
    return applyAll(makeConstant("Natural.LessThan.weaken"),
                    {makeNaturalLiteral(smaller),
                     makeNaturalLiteral(larger),
                     std::move(strict)});
}

ExpressionPointer Elaborator::makeGroundNaturalNotEqualProof(
        const NaturalValue& left, const NaturalValue& right) {
    if (left == right) return nullptr;
    const char* lemma = left < right ? "Natural.not_equal_of_less_than"
                                     : "Natural.not_equal_of_greater_than";
    if (!environment_.lookup(lemma)) return nullptr;
    ExpressionPointer strict =
        left < right ? makeGroundNaturalLessThanProof(left, right)
                     : makeGroundNaturalLessThanProof(right, left);
    if (!strict) return nullptr;
    return applyAll(makeConstant(lemma),
                    {makeNaturalLiteral(left),
                     makeNaturalLiteral(right),
                     std::move(strict)});
}

// ── Ground ℤ certificates ────────────────────────────────────────────

std::optional<Elaborator::GroundIntegerCertificate>
Elaborator::tryGroundIntegerCertificate(
        ExpressionPointer termOpened, int depth) {
    if (depth <= 0) return std::nullopt;
    SpineView spine = decomposeSpine(termOpened);
    if (spine.headName.empty()) return std::nullopt;

    auto leaf = [&](NaturalValue positivePart, NaturalValue negativePart)
            -> std::optional<GroundIntegerCertificate> {
        return GroundIntegerCertificate{
            std::move(positivePart), std::move(negativePart),
            makeCarrierReflexivity("Integer", termOpened)};
    };

    if (spine.headName == "Natural.to_integer" && spine.args.size() == 1) {
        auto value = tryGroundNaturalValue(spine.args[0]);
        if (!value) return std::nullopt;
        return leaf(*value, 0);
    }
    if (spine.headName == "Integer.zero" && spine.args.empty()) {
        return leaf(0, 0);
    }
    if (spine.headName == "Integer.one" && spine.args.empty()) {
        return leaf(1, 0);
    }
    if (spine.headName == "Integer.from_difference"
        && spine.args.size() == 2) {
        auto positive = tryGroundNaturalValue(spine.args[0]);
        auto negative = tryGroundNaturalValue(spine.args[1]);
        if (!positive || !negative) return std::nullopt;
        return leaf(*positive, *negative);
    }

    // Each operation case: certify the operands, then apply the matching
    // `*_evaluates` lemma. The lemma is instantiated with the operand
    // subterms and the operands' canonical literals; the kernel checks the
    // equation premises against the recursive proofs by defeq (their
    // stated `from_difference` arguments compute to the same literals).
    auto evaluatesApplication = [&](const char* lemma,
                                    ExpressionPointer x,
                                    ExpressionPointer y,
                                    const GroundIntegerCertificate& certX,
                                    const GroundIntegerCertificate& certY)
            -> ExpressionPointer {
        return applyAll(makeConstant(lemma),
                        {std::move(x), std::move(y),
                         makeNaturalLiteral(certX.positivePart),
                         makeNaturalLiteral(certX.negativePart),
                         makeNaturalLiteral(certY.positivePart),
                         makeNaturalLiteral(certY.negativePart),
                         certX.proof, certY.proof});
    };

    if (spine.headName == "Integer.negate" && spine.args.size() == 1) {
        if (!environment_.lookup("Integer.negate_evaluates"))
            return std::nullopt;
        auto certX = tryGroundIntegerCertificate(spine.args[0], depth - 1);
        if (!certX) return std::nullopt;
        ExpressionPointer proof = applyAll(
            makeConstant("Integer.negate_evaluates"),
            {spine.args[0],
             makeNaturalLiteral(certX->positivePart),
             makeNaturalLiteral(certX->negativePart),
             certX->proof});
        return GroundIntegerCertificate{
            certX->negativePart, certX->positivePart, std::move(proof)};
    }
    // Honest ℕ negation lands in ℤ: `Natural.negate(n)` is
    // `Integer.negate(to_integer(n))` by definition, so certify that body
    // shape — the certificate's stated type bridges to the original term
    // by defeq (the wrapper is a transparent definition).
    if (spine.headName == "Natural.negate" && spine.args.size() == 1) {
        ExpressionPointer body = makeApplication(
            makeConstant("Integer.negate"),
            makeApplication(makeConstant("Natural.to_integer"),
                            spine.args[0]));
        return tryGroundIntegerCertificate(body, depth - 1);
    }
    if ((spine.headName == "Integer.add"
         || spine.headName == "Integer.subtract"
         || spine.headName == "Integer.multiply")
        && spine.args.size() == 2) {
        const char* lemma =
            spine.headName == "Integer.add" ? "Integer.add_evaluates"
            : spine.headName == "Integer.subtract"
                ? "Integer.subtract_evaluates"
                : "Integer.multiply_evaluates";
        if (!environment_.lookup(lemma)) return std::nullopt;
        auto certX = tryGroundIntegerCertificate(spine.args[0], depth - 1);
        if (!certX) return std::nullopt;
        auto certY = tryGroundIntegerCertificate(spine.args[1], depth - 1);
        if (!certY) return std::nullopt;
        NaturalValue positivePart, negativePart;
        if (spine.headName == "Integer.add") {
            positivePart = certX->positivePart + certY->positivePart;
            negativePart = certX->negativePart + certY->negativePart;
        } else if (spine.headName == "Integer.subtract") {
            positivePart = certX->positivePart + certY->negativePart;
            negativePart = certX->negativePart + certY->positivePart;
        } else {
            positivePart = certX->positivePart * certY->positivePart
                         + certX->negativePart * certY->negativePart;
            negativePart = certX->positivePart * certY->negativePart
                         + certX->negativePart * certY->positivePart;
        }
        ExpressionPointer proof = evaluatesApplication(
            lemma, spine.args[0], spine.args[1], *certX, *certY);
        return GroundIntegerCertificate{
            std::move(positivePart), std::move(negativePart),
            std::move(proof)};
    }
    // Honest ℕ subtraction: `Natural.subtract(a, b)` is
    // `to_integer(a) - to_integer(b)` by definition; certify the body.
    if (spine.headName == "Natural.subtract" && spine.args.size() == 2) {
        ExpressionPointer body = applyAll(
            makeConstant("Integer.subtract"),
            {makeApplication(makeConstant("Natural.to_integer"),
                             spine.args[0]),
             makeApplication(makeConstant("Natural.to_integer"),
                             spine.args[1])});
        return tryGroundIntegerCertificate(body, depth - 1);
    }
    return std::nullopt;
}

ExpressionPointer Elaborator::makeGroundIntegerEqualityProof(
        ExpressionPointer leftOpened, ExpressionPointer rightOpened,
        int depth) {
    if (!environment_.lookup("Integer.ground_equal")) return nullptr;
    auto certX = tryGroundIntegerCertificate(leftOpened, depth);
    if (!certX) return nullptr;
    auto certY = tryGroundIntegerCertificate(rightOpened, depth);
    if (!certY) return nullptr;
    NaturalValue cross = certX->positivePart + certY->negativePart;
    if (cross != certX->negativePart + certY->positivePart) return nullptr;
    // crossEquation : a + d = b + c — both sides compute to the same
    // literal, so `reflexivity` at that literal checks.
    return applyAll(makeConstant("Integer.ground_equal"),
                    {leftOpened, rightOpened,
                     makeNaturalLiteral(certX->positivePart),
                     makeNaturalLiteral(certX->negativePart),
                     makeNaturalLiteral(certY->positivePart),
                     makeNaturalLiteral(certY->negativePart),
                     certX->proof, certY->proof,
                     makeCarrierReflexivity(
                         "Natural", makeNaturalLiteral(cross))});
}

ExpressionPointer Elaborator::makeGroundIntegerDisequalityProof(
        ExpressionPointer leftOpened, ExpressionPointer rightOpened,
        int depth) {
    if (!environment_.lookup("Integer.ground_not_equal")) return nullptr;
    auto certX = tryGroundIntegerCertificate(leftOpened, depth);
    if (!certX) return nullptr;
    auto certY = tryGroundIntegerCertificate(rightOpened, depth);
    if (!certY) return nullptr;
    ExpressionPointer crossDisequality = makeGroundNaturalNotEqualProof(
        certX->positivePart + certY->negativePart,
        certX->negativePart + certY->positivePart);
    if (!crossDisequality) return nullptr;
    return applyAll(makeConstant("Integer.ground_not_equal"),
                    {leftOpened, rightOpened,
                     makeNaturalLiteral(certX->positivePart),
                     makeNaturalLiteral(certX->negativePart),
                     makeNaturalLiteral(certY->positivePart),
                     makeNaturalLiteral(certY->negativePart),
                     certX->proof, certY->proof,
                     std::move(crossDisequality)});
}

ExpressionPointer Elaborator::makeGroundIntegerIsNonnegProof(
        ExpressionPointer termOpened, int depth) {
    if (!environment_.lookup("Integer.ground_is_nonneg")) return nullptr;
    auto cert = tryGroundIntegerCertificate(termOpened, depth);
    if (!cert) return nullptr;
    ExpressionPointer componentInequality = makeGroundNaturalLessOrEqualProof(
        cert->negativePart, cert->positivePart);
    if (!componentInequality) return nullptr;
    return applyAll(makeConstant("Integer.ground_is_nonneg"),
                    {termOpened,
                     makeNaturalLiteral(cert->positivePart),
                     makeNaturalLiteral(cert->negativePart),
                     cert->proof,
                     std::move(componentInequality)});
}

// ── Ground ℚ certificates ────────────────────────────────────────────

std::optional<Elaborator::GroundRationalCertificate>
Elaborator::tryGroundRationalCertificate(
        ExpressionPointer termOpened, int depth) {
    if (depth <= 0) return std::nullopt;
    SpineView spine = decomposeSpine(termOpened);
    if (spine.headName.empty()) return std::nullopt;

    auto signedNumerator = [](const GroundRationalCertificate& certificate) {
        return NaturalValue(certificate.numeratorPositive
                            - certificate.numeratorNegative);
    };
    auto signedDenominator = [](const GroundRationalCertificate& certificate) {
        return NaturalValue(certificate.denominatorPositive
                            - certificate.denominatorNegative);
    };

    // Leaf: a fraction-shaped term (`fraction(n, d, w)` itself, `a / b` at
    // two Integers — whose body is exactly that fraction — or a cast /
    // canonical constant, whose bodies are fractions over `Integer.one`).
    auto fractionLeaf = [&](ExpressionPointer numeratorTerm,
                            ExpressionPointer denominatorTerm,
                            ExpressionPointer denominatorNonzeroProof)
            -> std::optional<GroundRationalCertificate> {
        auto numerator = tryGroundIntegerCertificate(numeratorTerm, depth - 1);
        if (!numerator) return std::nullopt;
        auto denominator =
            tryGroundIntegerCertificate(denominatorTerm, depth - 1);
        if (!denominator) return std::nullopt;
        if (denominator->positivePart == denominator->negativePart)
            return std::nullopt;  // zero denominator can't be certified
        return GroundRationalCertificate{
            numerator->positivePart, numerator->negativePart,
            denominator->positivePart, denominator->negativePart,
            std::move(numeratorTerm), std::move(denominatorTerm),
            std::move(denominatorNonzeroProof),
            makeCarrierReflexivity("Rational", termOpened)};
    };

    if (spine.headName == "Rational.fraction" && spine.args.size() == 3) {
        return fractionLeaf(spine.args[0], spine.args[1], spine.args[2]);
    }
    if (spine.headName == "Integer.divide" && spine.args.size() == 3) {
        return fractionLeaf(spine.args[0], spine.args[1], spine.args[2]);
    }
    if (spine.headName == "Integer.to_rational" && spine.args.size() == 1) {
        if (!environment_.lookup("Integer.one_is_nonzero"))
            return std::nullopt;
        return fractionLeaf(spine.args[0], makeConstant("Integer.one"),
                            makeConstant("Integer.one_is_nonzero"));
    }
    if ((spine.headName == "Rational.zero" || spine.headName == "Rational.one")
        && spine.args.empty()) {
        if (!environment_.lookup("Integer.one_is_nonzero"))
            return std::nullopt;
        return fractionLeaf(
            makeConstant(spine.headName == "Rational.zero" ? "Integer.zero"
                                                           : "Integer.one"),
            makeConstant("Integer.one"),
            makeConstant("Integer.one_is_nonzero"));
    }

    if (spine.headName == "Rational.negate" && spine.args.size() == 1) {
        if (!environment_.lookup("Rational.negate_evaluates"))
            return std::nullopt;
        auto certX = tryGroundRationalCertificate(spine.args[0], depth - 1);
        if (!certX) return std::nullopt;
        ExpressionPointer negatedNumerator = makeApplication(
            makeConstant("Integer.negate"), certX->numeratorTerm);
        ExpressionPointer numeratorOut = makeFromDifferenceLiteral(
            certX->numeratorNegative, certX->numeratorPositive);
        ExpressionPointer numeratorEquation = makeGroundIntegerEqualityProof(
            negatedNumerator, numeratorOut, depth - 1);
        if (!numeratorEquation) return std::nullopt;
        ExpressionPointer proof = applyAll(
            makeConstant("Rational.negate_evaluates"),
            {spine.args[0], certX->numeratorTerm, certX->denominatorTerm,
             certX->denominatorNonzeroProof, certX->proof,
             numeratorOut, std::move(numeratorEquation)});
        return GroundRationalCertificate{
            certX->numeratorNegative, certX->numeratorPositive,
            certX->denominatorPositive, certX->denominatorNegative,
            std::move(numeratorOut), certX->denominatorTerm,
            certX->denominatorNonzeroProof, std::move(proof)};
    }

    if ((spine.headName == "Rational.add"
         || spine.headName == "Rational.subtract"
         || spine.headName == "Rational.multiply"
         || spine.headName == "Rational.divide")
        && spine.args.size() == (spine.headName == "Rational.divide" ? 3u
                                                                     : 2u)) {
        const char* lemma =
            spine.headName == "Rational.add"      ? "Rational.add_evaluates"
            : spine.headName == "Rational.subtract"
                ? "Rational.subtract_evaluates"
            : spine.headName == "Rational.multiply"
                ? "Rational.multiply_evaluates"
                : "Rational.divide_evaluates";
        if (!environment_.lookup(lemma)) return std::nullopt;
        auto certX = tryGroundRationalCertificate(spine.args[0], depth - 1);
        if (!certX) return std::nullopt;
        auto certY = tryGroundRationalCertificate(spine.args[1], depth - 1);
        if (!certY) return std::nullopt;

        // The computed numerator/denominator, as signed values and as the
        // exact expression the lemma's equation premises are stated over.
        NaturalValue numeratorSigned, denominatorSigned;
        ExpressionPointer numeratorExpression, denominatorExpression;
        auto multiplyTerms = [](ExpressionPointer a, ExpressionPointer b) {
            return applyAll(makeConstant("Integer.multiply"),
                            {std::move(a), std::move(b)});
        };
        if (spine.headName == "Rational.add"
            || spine.headName == "Rational.subtract") {
            ExpressionPointer crossLeft =
                multiplyTerms(certX->numeratorTerm, certY->denominatorTerm);
            ExpressionPointer crossRight =
                multiplyTerms(certY->numeratorTerm, certX->denominatorTerm);
            if (spine.headName == "Rational.add") {
                numeratorSigned =
                    signedNumerator(*certX) * signedDenominator(*certY)
                    + signedNumerator(*certY) * signedDenominator(*certX);
                numeratorExpression = applyAll(
                    makeConstant("Integer.add"),
                    {std::move(crossLeft), std::move(crossRight)});
            } else {
                numeratorSigned =
                    signedNumerator(*certX) * signedDenominator(*certY)
                    - signedNumerator(*certY) * signedDenominator(*certX);
                numeratorExpression = applyAll(
                    makeConstant("Integer.subtract"),
                    {std::move(crossLeft), std::move(crossRight)});
            }
            denominatorSigned =
                signedDenominator(*certX) * signedDenominator(*certY);
            denominatorExpression = multiplyTerms(
                certX->denominatorTerm, certY->denominatorTerm);
        } else if (spine.headName == "Rational.multiply") {
            numeratorSigned =
                signedNumerator(*certX) * signedNumerator(*certY);
            denominatorSigned =
                signedDenominator(*certX) * signedDenominator(*certY);
            numeratorExpression =
                multiplyTerms(certX->numeratorTerm, certY->numeratorTerm);
            denominatorExpression = multiplyTerms(
                certX->denominatorTerm, certY->denominatorTerm);
        } else {
            if (signedNumerator(*certY) == 0) return std::nullopt;
            numeratorSigned =
                signedNumerator(*certX) * signedDenominator(*certY);
            denominatorSigned =
                signedDenominator(*certX) * signedNumerator(*certY);
            numeratorExpression =
                multiplyTerms(certX->numeratorTerm, certY->denominatorTerm);
            denominatorExpression = multiplyTerms(
                certX->denominatorTerm, certY->numeratorTerm);
        }
        if (denominatorSigned == 0) return std::nullopt;

        auto [numeratorPositive, numeratorNegative] =
            signedToParts(numeratorSigned);
        auto [denominatorPositive, denominatorNegative] =
            signedToParts(denominatorSigned);
        ExpressionPointer numeratorOut =
            makeFromDifferenceLiteral(numeratorPositive, numeratorNegative);
        ExpressionPointer denominatorOut = makeFromDifferenceLiteral(
            denominatorPositive, denominatorNegative);
        ExpressionPointer numeratorEquation = makeGroundIntegerEqualityProof(
            numeratorExpression, numeratorOut, depth - 1);
        if (!numeratorEquation) return std::nullopt;
        ExpressionPointer denominatorEquation =
            makeGroundIntegerEqualityProof(
                denominatorExpression, denominatorOut, depth - 1);
        if (!denominatorEquation) return std::nullopt;
        ExpressionPointer denominatorNonzero = makeGroundIntegerDisequalityProof(
            denominatorOut, makeConstant("Integer.zero"), depth - 1);
        if (!denominatorNonzero) return std::nullopt;

        std::vector<ExpressionPointer> arguments = {
            spine.args[0], spine.args[1]};
        if (spine.headName == "Rational.divide") {
            // divide_evaluates(x, y, yNonzero, …): the wrapper's own proof
            // argument keeps the conclusion at the original term.
            arguments.push_back(spine.args[2]);
        }
        for (ExpressionPointer argument :
             {certX->numeratorTerm, certX->denominatorTerm,
              certX->denominatorNonzeroProof,
              certY->numeratorTerm, certY->denominatorTerm,
              certY->denominatorNonzeroProof,
              certX->proof, certY->proof}) {
            arguments.push_back(std::move(argument));
        }
        if (spine.headName == "Rational.divide") {
            ExpressionPointer numeratorNonzero =
                makeGroundIntegerDisequalityProof(
                    certY->numeratorTerm, makeConstant("Integer.zero"),
                    depth - 1);
            if (!numeratorNonzero) return std::nullopt;
            arguments.push_back(std::move(numeratorNonzero));
        }
        for (ExpressionPointer argument :
             {numeratorOut, denominatorOut, denominatorNonzero,
              std::move(numeratorEquation), std::move(denominatorEquation)}) {
            arguments.push_back(std::move(argument));
        }
        ExpressionPointer proof = makeConstant(lemma);
        for (ExpressionPointer& argument : arguments) {
            proof = makeApplication(std::move(proof), std::move(argument));
        }
        return GroundRationalCertificate{
            numeratorPositive, numeratorNegative,
            denominatorPositive, denominatorNegative,
            std::move(numeratorOut), std::move(denominatorOut),
            std::move(denominatorNonzero), std::move(proof)};
    }

    if (spine.headName == "Rational.reciprocal_function"
        && spine.args.size() == 1) {
        if (!environment_.lookup("Rational.reciprocal_evaluates"))
            return std::nullopt;
        auto certX = tryGroundRationalCertificate(spine.args[0], depth - 1);
        if (!certX) return std::nullopt;
        if (certX->numeratorPositive == certX->numeratorNegative)
            return std::nullopt;  // reciprocal of zero stays junk
        ExpressionPointer numeratorNonzero = makeGroundIntegerDisequalityProof(
            certX->numeratorTerm, makeConstant("Integer.zero"), depth - 1);
        if (!numeratorNonzero) return std::nullopt;
        ExpressionPointer proof = applyAll(
            makeConstant("Rational.reciprocal_evaluates"),
            {spine.args[0], certX->numeratorTerm, certX->denominatorTerm,
             certX->denominatorNonzeroProof, certX->proof, numeratorNonzero});
        return GroundRationalCertificate{
            certX->denominatorPositive, certX->denominatorNegative,
            certX->numeratorPositive, certX->numeratorNegative,
            certX->denominatorTerm, certX->numeratorTerm,
            std::move(numeratorNonzero), std::move(proof)};
    }

    // Honest ℕ division lands in ℚ.
    if (spine.headName == "Natural.divide" && spine.args.size() == 3) {
        if (!environment_.lookup("Natural.divide_evaluates"))
            return std::nullopt;
        auto numeratorValue = tryGroundNaturalValue(spine.args[0]);
        auto denominatorValue = tryGroundNaturalValue(spine.args[1]);
        if (!numeratorValue || !denominatorValue) return std::nullopt;
        if (*denominatorValue == 0) return std::nullopt;
        ExpressionPointer numeratorOut =
            makeFromDifferenceLiteral(*numeratorValue, 0);
        ExpressionPointer denominatorOut =
            makeFromDifferenceLiteral(*denominatorValue, 0);
        ExpressionPointer castDenominator = makeApplication(
            makeConstant("Natural.to_integer"), spine.args[1]);
        ExpressionPointer castDenominatorNonzero =
            makeGroundIntegerDisequalityProof(
                castDenominator, makeConstant("Integer.zero"), depth - 1);
        if (!castDenominatorNonzero) return std::nullopt;
        ExpressionPointer denominatorNonzero =
            makeGroundIntegerDisequalityProof(
                denominatorOut, makeConstant("Integer.zero"), depth - 1);
        if (!denominatorNonzero) return std::nullopt;
        ExpressionPointer numeratorEquation = makeGroundIntegerEqualityProof(
            applyAll(makeConstant("Integer.multiply"),
                     {makeApplication(makeConstant("Natural.to_integer"),
                                      spine.args[0]),
                      makeConstant("Integer.one")}),
            numeratorOut, depth - 1);
        if (!numeratorEquation) return std::nullopt;
        ExpressionPointer denominatorEquation = makeGroundIntegerEqualityProof(
            applyAll(makeConstant("Integer.multiply"),
                     {makeConstant("Integer.one"), castDenominator}),
            denominatorOut, depth - 1);
        if (!denominatorEquation) return std::nullopt;
        ExpressionPointer proof = applyAll(
            makeConstant("Natural.divide_evaluates"),
            {spine.args[0], spine.args[1], spine.args[2],
             std::move(castDenominatorNonzero),
             numeratorOut, denominatorOut, denominatorNonzero,
             std::move(numeratorEquation), std::move(denominatorEquation)});
        return GroundRationalCertificate{
            *numeratorValue, NaturalValue(0),
            *denominatorValue, NaturalValue(0),
            std::move(numeratorOut), std::move(denominatorOut),
            std::move(denominatorNonzero), std::move(proof)};
    }

    return std::nullopt;
}

// ── The relation dispatch ────────────────────────────────────────────

namespace {
constexpr int kGroundDepthLimit = 64;
constexpr int kGroundScanBudget = 4096;
}

ExpressionPointer Elaborator::trySynthesizeGroundNonzero(
        ExpressionPointer termOpened, const std::string& carrierName) {
    int budget = kGroundScanBudget;
    if (!quickGroundScan(termOpened, budget)) return nullptr;
    if (carrierName == "Integer") {
        return makeGroundIntegerDisequalityProof(
            termOpened, makeConstant("Integer.zero"), kGroundDepthLimit);
    }
    if (carrierName == "Rational") {
        if (!environment_.lookup("Rational.ground_not_equal")) return nullptr;
        auto certX =
            tryGroundRationalCertificate(termOpened, kGroundDepthLimit);
        if (!certX) return nullptr;
        NaturalValue numeratorSigned =
            certX->numeratorPositive - certX->numeratorNegative;
        if (numeratorSigned == 0) return nullptr;  // the term IS zero
        auto certY = tryGroundRationalCertificate(
            makeConstant("Rational.zero"), kGroundDepthLimit);
        if (!certY) return nullptr;
        ExpressionPointer crossDisequality = makeGroundIntegerDisequalityProof(
            applyAll(makeConstant("Integer.multiply"),
                     {certX->numeratorTerm, certY->denominatorTerm}),
            applyAll(makeConstant("Integer.multiply"),
                     {certY->numeratorTerm, certX->denominatorTerm}),
            kGroundDepthLimit);
        if (!crossDisequality) return nullptr;
        return applyAll(makeConstant("Rational.ground_not_equal"),
                        {termOpened, makeConstant("Rational.zero"),
                         certX->numeratorTerm, certX->denominatorTerm,
                         certX->denominatorNonzeroProof,
                         certY->numeratorTerm, certY->denominatorTerm,
                         certY->denominatorNonzeroProof,
                         certX->proof, certY->proof,
                         std::move(crossDisequality)});
    }
    if (carrierName == "Natural") {
        auto value = tryGroundNaturalValue(termOpened);
        if (!value || *value == 0) return nullptr;
        return makeGroundNaturalNotEqualProof(*value, 0);
    }
    return nullptr;
}

ExpressionPointer Elaborator::tryGroundRelationTier(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders) {
    int binderCount = static_cast<int>(localBinders.size());
    ExpressionPointer goal =
        openOverLocalBinders(goalClosed, localBinders, binderCount);

    // Recognize the relation shape first (cheap name checks), then insist
    // the operands are variable-free before any WHNF work happens.
    SpineView spine = decomposeSpine(goal);
    auto operandsGround = [&](std::initializer_list<ExpressionPointer> terms) {
        int budget = kGroundScanBudget;
        for (const ExpressionPointer& term : terms) {
            if (!quickGroundScan(term, budget)) return false;
        }
        return true;
    };

    ExpressionPointer proof = nullptr;

    if (spine.headName == "Natural.LessThan" && spine.args.size() == 2
        && operandsGround({spine.args[0], spine.args[1]})) {
        auto left = tryGroundNaturalValue(spine.args[0]);
        auto right = tryGroundNaturalValue(spine.args[1]);
        if (left && right) {
            proof = makeGroundNaturalLessThanProof(*left, *right);
        }
    } else if (spine.headName == "Natural.LessOrEqual"
               && spine.args.size() == 2
               && operandsGround({spine.args[0], spine.args[1]})) {
        auto left = tryGroundNaturalValue(spine.args[0]);
        auto right = tryGroundNaturalValue(spine.args[1]);
        if (left && right) {
            proof = makeGroundNaturalLessOrEqualProof(*left, *right);
        }
    } else if ((spine.headName == "Integer.LessOrEqual"
                || spine.headName == "Integer.LessThan")
               && spine.args.size() == 2
               && operandsGround({spine.args[0], spine.args[1]})) {
        bool strict = spine.headName == "Integer.LessThan";
        const char* lemma = strict ? "Integer.ground_less_than"
                                   : "Integer.ground_less_or_equal";
        if (environment_.lookup(lemma)) {
            auto certX =
                tryGroundIntegerCertificate(spine.args[0], kGroundDepthLimit);
            std::optional<GroundIntegerCertificate> certY;
            if (certX) {
                certY = tryGroundIntegerCertificate(spine.args[1],
                                                    kGroundDepthLimit);
            }
            if (certX && certY) {
                NaturalValue leftCross =
                    certX->positivePart + certY->negativePart;
                NaturalValue rightCross =
                    certY->positivePart + certX->negativePart;
                ExpressionPointer cross =
                    strict
                        ? makeGroundNaturalLessThanProof(leftCross, rightCross)
                        : makeGroundNaturalLessOrEqualProof(leftCross,
                                                            rightCross);
                if (cross) {
                    proof = applyAll(
                        makeConstant(lemma),
                        {spine.args[0], spine.args[1],
                         makeNaturalLiteral(certX->positivePart),
                         makeNaturalLiteral(certX->negativePart),
                         makeNaturalLiteral(certY->positivePart),
                         makeNaturalLiteral(certY->negativePart),
                         certX->proof, certY->proof, std::move(cross)});
                }
            }
        }
    } else if (spine.headName == "Integer.IsNonneg" && spine.args.size() == 1
               && operandsGround({spine.args[0]})) {
        proof = makeGroundIntegerIsNonnegProof(spine.args[0],
                                               kGroundDepthLimit);
    } else if ((spine.headName == "Rational.LessOrEqual"
                || spine.headName == "Rational.LessThan")
               && spine.args.size() == 2
               && operandsGround({spine.args[0], spine.args[1]})) {
        bool strict = spine.headName == "Rational.LessThan";
        const char* lemma = strict ? "Rational.ground_less_than"
                                   : "Rational.ground_less_or_equal";
        if (environment_.lookup(lemma)) {
            auto certX = tryGroundRationalCertificate(spine.args[0],
                                                      kGroundDepthLimit);
            std::optional<GroundRationalCertificate> certY;
            if (certX) {
                certY = tryGroundRationalCertificate(spine.args[1],
                                                     kGroundDepthLimit);
            }
            if (certX && certY) {
                NaturalValue n1 =
                    certX->numeratorPositive - certX->numeratorNegative;
                NaturalValue d1 =
                    certX->denominatorPositive - certX->denominatorNegative;
                NaturalValue n2 =
                    certY->numeratorPositive - certY->numeratorNegative;
                NaturalValue d2 =
                    certY->denominatorPositive - certY->denominatorNegative;
                NaturalValue product = (n2 * d1 - n1 * d2) * (d2 * d1);
                bool holds = strict ? product > 0 : product >= 0;
                if (holds) {
                    auto multiplyTerms = [](ExpressionPointer a,
                                            ExpressionPointer b) {
                        return applyAll(makeConstant("Integer.multiply"),
                                        {std::move(a), std::move(b)});
                    };
                    // Exactly the premise expression of ground_less_or_equal:
                    // (n2·d1 − n1·d2) · (d2·d1).
                    ExpressionPointer productTerm = multiplyTerms(
                        applyAll(
                            makeConstant("Integer.subtract"),
                            {multiplyTerms(certY->numeratorTerm,
                                           certX->denominatorTerm),
                             multiplyTerms(certX->numeratorTerm,
                                           certY->denominatorTerm)}),
                        multiplyTerms(certY->denominatorTerm,
                                      certX->denominatorTerm));
                    ExpressionPointer productNonneg =
                        makeGroundIntegerIsNonnegProof(productTerm,
                                                       kGroundDepthLimit);
                    ExpressionPointer crossDisequality =
                        strict ? makeGroundIntegerDisequalityProof(
                                     multiplyTerms(certX->numeratorTerm,
                                                   certY->denominatorTerm),
                                     multiplyTerms(certY->numeratorTerm,
                                                   certX->denominatorTerm),
                                     kGroundDepthLimit)
                               : nullptr;
                    if (productNonneg && (!strict || crossDisequality)) {
                        std::vector<ExpressionPointer> arguments = {
                            spine.args[0], spine.args[1],
                            certX->numeratorTerm, certX->denominatorTerm,
                            certX->denominatorNonzeroProof,
                            certY->numeratorTerm, certY->denominatorTerm,
                            certY->denominatorNonzeroProof,
                            certX->proof, certY->proof,
                            std::move(productNonneg)};
                        if (strict) {
                            arguments.push_back(std::move(crossDisequality));
                        }
                        proof = makeConstant(lemma);
                        for (ExpressionPointer& argument : arguments) {
                            proof = makeApplication(std::move(proof),
                                                    std::move(argument));
                        }
                    }
                }
            }
        }
    } else {
        // Equality / disequality: `Equality(T, x, y)` directly, `Not(…)`,
        // or the already-unfolded `(x = y) → False` Pi.
        ExpressionPointer equality = nullptr;
        bool negated = false;
        if (spine.headName == "Equality" && spine.args.size() == 3) {
            equality = goal;
        } else if (spine.headName == "Not" && spine.args.size() == 1) {
            equality = spine.args[0];
            negated = true;
        } else {
            ExpressionPointer goalWhnf = weakHeadNormalForm(environment_, goal);
            if (auto* pi = std::get_if<Pi>(&goalWhnf->node)) {
                if (!referencesBoundVariable(pi->codomain, 0)) {
                    ExpressionPointer codomain = weakHeadNormalForm(
                        environment_, shift(pi->codomain, -1));
                    auto* codomainConstant =
                        std::get_if<Constant>(&codomain->node);
                    if (codomainConstant
                        && codomainConstant->name == "False") {
                        equality = pi->domain;
                        negated = true;
                    }
                }
            }
        }
        if (equality) {
            EqualityComponents components;
            bool extracted = false;
            try {
                components = extractEqualityComponents(
                    equality, "ground relation", 0);
                extracted = true;
            } catch (const ElaborateError&) {
            } catch (const TypeError&) {
            }
            if (extracted
                && operandsGround({components.leftEndpoint,
                                   components.rightEndpoint})) {
                std::string carrier = headConstantName(components.carrierType);
                if (carrier == "Natural") {
                    auto left = tryGroundNaturalValue(components.leftEndpoint);
                    auto right =
                        tryGroundNaturalValue(components.rightEndpoint);
                    if (left && right) {
                        if (negated) {
                            proof = makeGroundNaturalNotEqualProof(*left,
                                                                   *right);
                        } else if (*left == *right) {
                            proof = makeCarrierReflexivity(
                                "Natural", makeNaturalLiteral(*left));
                        }
                    }
                } else if (carrier == "Integer") {
                    proof = negated
                        ? makeGroundIntegerDisequalityProof(
                              components.leftEndpoint,
                              components.rightEndpoint, kGroundDepthLimit)
                        : makeGroundIntegerEqualityProof(
                              components.leftEndpoint,
                              components.rightEndpoint, kGroundDepthLimit);
                } else if (carrier == "Rational") {
                    const char* lemma = negated ? "Rational.ground_not_equal"
                                                : "Rational.ground_equal";
                    if (environment_.lookup(lemma)) {
                        auto certX = tryGroundRationalCertificate(
                            components.leftEndpoint, kGroundDepthLimit);
                        std::optional<GroundRationalCertificate> certY;
                        if (certX) {
                            certY = tryGroundRationalCertificate(
                                components.rightEndpoint, kGroundDepthLimit);
                        }
                        if (certX && certY) {
                            NaturalValue crossLeft =
                                (certX->numeratorPositive
                                 - certX->numeratorNegative)
                                * (certY->denominatorPositive
                                   - certY->denominatorNegative);
                            NaturalValue crossRight =
                                (certY->numeratorPositive
                                 - certY->numeratorNegative)
                                * (certX->denominatorPositive
                                   - certX->denominatorNegative);
                            bool holds = negated ? crossLeft != crossRight
                                                 : crossLeft == crossRight;
                            if (holds) {
                                auto multiplyTerms =
                                    [](ExpressionPointer a,
                                       ExpressionPointer b) {
                                        return applyAll(
                                            makeConstant("Integer.multiply"),
                                            {std::move(a), std::move(b)});
                                    };
                                ExpressionPointer crossProof = negated
                                    ? makeGroundIntegerDisequalityProof(
                                          multiplyTerms(
                                              certX->numeratorTerm,
                                              certY->denominatorTerm),
                                          multiplyTerms(
                                              certY->numeratorTerm,
                                              certX->denominatorTerm),
                                          kGroundDepthLimit)
                                    : makeGroundIntegerEqualityProof(
                                          multiplyTerms(
                                              certX->numeratorTerm,
                                              certY->denominatorTerm),
                                          multiplyTerms(
                                              certY->numeratorTerm,
                                              certX->denominatorTerm),
                                          kGroundDepthLimit);
                                if (crossProof) {
                                    proof = applyAll(
                                        makeConstant(lemma),
                                        {components.leftEndpoint,
                                         components.rightEndpoint,
                                         certX->numeratorTerm,
                                         certX->denominatorTerm,
                                         certX->denominatorNonzeroProof,
                                         certY->numeratorTerm,
                                         certY->denominatorTerm,
                                         certY->denominatorNonzeroProof,
                                         certX->proof, certY->proof,
                                         std::move(crossProof)});
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    if (!proof) return nullptr;
    return closeOverLocalBinders(proof, localBinders, binderCount);
}
