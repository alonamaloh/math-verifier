#include "elaborator/internal.hpp"

#include <gmpxx.h>

#include <cerrno>
#include <cstdlib>
#include <limits>
#include <optional>
#include <string>
#include <vector>

namespace {

// Application spines are stored left-associated.  Return the head and the
// arguments in source order; finite_check uses this only for the two order
// premises in its expected goal.
struct ApplicationSpine {
    ExpressionPointer head;
    std::vector<ExpressionPointer> arguments;
};

ApplicationSpine applicationSpine(ExpressionPointer expression) {
    ApplicationSpine result;
    while (auto* application = std::get_if<Application>(&expression->node)) {
        result.arguments.push_back(application->argument);
        expression = application->function;
    }
    std::reverse(result.arguments.begin(), result.arguments.end());
    result.head = std::move(expression);
    return result;
}

std::string constantName(const ExpressionPointer& expression) {
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        return constant->name;
    }
    return {};
}

// Does `expression`, viewed at its present binder depth, refer to the bound
// variable `target`?  Descending under a binder shifts the target by one.
bool mentionsBoundVariable(const ExpressionPointer& expression, int target) {
    if (auto* variable = std::get_if<BoundVariable>(&expression->node)) {
        return variable->deBruijnIndex == target;
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return mentionsBoundVariable(application->function, target)
            || mentionsBoundVariable(application->argument, target);
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return mentionsBoundVariable(pi->domain, target)
            || mentionsBoundVariable(pi->codomain, target + 1);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return mentionsBoundVariable(lambda->domain, target)
            || mentionsBoundVariable(lambda->body, target + 1);
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return mentionsBoundVariable(let->type, target)
            || mentionsBoundVariable(let->value, target)
            || mentionsBoundVariable(let->body, target + 1);
    }
    return false;
}

std::optional<mpz_class> signedSurfaceLiteral(
        SurfaceExpressionPointer expression) {
    // An ascription only fixes the carrier; the range size is still read from
    // the underlying signed numeral.
    if (auto* ascription =
            std::get_if<SurfaceAscription>(&expression->node)) {
        return signedSurfaceLiteral(ascription->expression);
    }
    if (auto* numeral =
            std::get_if<SurfaceNumericLiteral>(&expression->node)) {
        mpz_class value;
        if (value.set_str(numeral->digits, 10) != 0) return std::nullopt;
        return value;
    }
    if (auto* unary =
            std::get_if<SurfaceUnaryOperation>(&expression->node)) {
        if (unary->opSymbol != "-") return std::nullopt;
        auto magnitude = signedSurfaceLiteral(unary->operand);
        if (!magnitude) return std::nullopt;
        return -*magnitude;
    }
    return std::nullopt;
}

ExpressionPointer applyMany(ExpressionPointer function,
                            const std::vector<ExpressionPointer>& arguments) {
    for (const auto& argument : arguments) {
        function = makeApplication(std::move(function), argument);
    }
    return function;
}

size_t finiteCheckCaseCap() {
    constexpr size_t defaultCap = 256;
    const char* raw = std::getenv("MATH_FINITE_CHECK_MAX_CASES");
    if (!raw || !*raw) return defaultCap;
    errno = 0;
    char* end = nullptr;
    unsigned long long parsed = std::strtoull(raw, &end, 10);
    if (errno != 0 || end == raw || *end != '\0' || parsed == 0
        || parsed > std::numeric_limits<size_t>::max()) {
        return defaultCap;
    }
    return static_cast<size_t>(parsed);
}

std::string integerForDiagnostic(const mpz_class& value) {
    return value.get_str(10);
}

}  // namespace

ExpressionPointer Elaborator::elaborateFiniteCheck(
        const SurfaceFiniteCheck& tactic,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
    (void)column;
    Frame frame(*this, "finite_check " + tactic.binderName
        + " from … until … at line " + std::to_string(line));

    auto lowerValue = signedSurfaceLiteral(tactic.lowerBound);
    auto upperValue = signedSurfaceLiteral(tactic.upperBound);
    if (!lowerValue || !upperValue) {
        throwElaborate(
            "finite_check bounds must be closed integer literals in this "
            "version (for example `0`, `7`, or `-3`)");
    }
    if (*upperValue <= *lowerValue) {
        throwElaborate(
            "finite_check requires a nonempty half-open range: the upper "
            "bound must be greater than the lower bound");
    }
    mpz_class caseCountBig = *upperValue - *lowerValue;
    const size_t cap = finiteCheckCaseCap();
    if (caseCountBig > mpz_class(cap)) {
        throwElaborate(
            "finite_check range has " + caseCountBig.get_str(10)
            + " cases, exceeding MATH_FINITE_CHECK_MAX_CASES="
            + std::to_string(cap));
    }
    const size_t caseCount = caseCountBig.get_ui();

    // Read exactly
    //   ∀ n : C. lower ≤ n → n < upper → P(n)
    // without unfolding either order relation.  The two proof premises may
    // not occur in P: the certificate records propositions indexed only by n.
    auto* valuePi = std::get_if<Pi>(&expectedType->node);
    if (!valuePi) {
        throwElaborate(
            "finite_check expects a goal of the form `∀ n. lo ≤ n → n < hi "
            "→ P(n)`");
    }
    if (!tactic.binderName.empty()
        && valuePi->displayHint != tactic.binderName) {
        throwElaborate(
            "finite_check names binder `" + tactic.binderName
            + "`, but the bounded universal goal binds `"
            + valuePi->displayHint + "`");
    }
    const std::string carrierName = headConstantName(valuePi->domain);
    const bool isNatural = carrierName == "Natural";
    const bool isInteger = carrierName == "Integer";
    if (!isNatural && !isInteger) {
        throwElaborate(
            "finite_check supports Natural and Integer binders; this goal "
            "binds `" + carrierName + "`");
    }
    const char* requiredBridge = isNatural
        ? "Natural.AllFrom_between" : "Integer.AllFrom_between";
    if (!environment_.lookup(requiredBridge)) {
        throwElaborate(
            std::string("finite_check on ") + carrierName
            + " requires `import "
            + (isNatural ? "Natural.finite_range"
                         : "Integer.finite_range")
            + "`");
    }
    if (isNatural && *lowerValue < 0) {
        throwElaborate("finite_check cannot use a negative Natural bound");
    }

    auto* lowerPi = std::get_if<Pi>(&valuePi->codomain->node);
    if (!lowerPi) {
        throwElaborate(
            "finite_check expected the lower-bound premise `lo ≤ "
            + tactic.binderName + "`");
    }
    auto* upperPi = std::get_if<Pi>(&lowerPi->codomain->node);
    if (!upperPi) {
        throwElaborate(
            "finite_check expected the upper-bound premise `"
            + tactic.binderName + " < hi`");
    }

    ApplicationSpine lowerRelation = applicationSpine(lowerPi->domain);
    ApplicationSpine upperRelation = applicationSpine(upperPi->domain);
    const std::string expectedLe = isNatural
        ? "Natural.LessOrEqual" : "Integer.LessOrEqual";
    const std::string expectedLt = isNatural
        ? "Natural.LessThan" : "Integer.LessThan";
    if (constantName(lowerRelation.head) != expectedLe
        || lowerRelation.arguments.size() != 2
        || constantName(upperRelation.head) != expectedLt
        || upperRelation.arguments.size() != 2) {
        throwElaborate(
            "finite_check expects premises in the order `lo ≤ "
            + tactic.binderName + "` and `" + tactic.binderName
            + " < hi`");
    }
    auto* lowerVariable =
        std::get_if<BoundVariable>(&lowerRelation.arguments[1]->node);
    auto* upperVariable =
        std::get_if<BoundVariable>(&upperRelation.arguments[0]->node);
    if (!lowerVariable || lowerVariable->deBruijnIndex != 0
        || !upperVariable || upperVariable->deBruijnIndex != 1) {
        throwElaborate(
            "finite_check bounds must constrain the quantified binder "
            "directly (`lo ≤ n` and `n < hi`)");
    }

    ExpressionPointer goalLower = lowerRelation.arguments[0];
    if (mentionsBoundVariable(goalLower, 0)) {
        throwElaborate("finite_check lower bound may not depend on its binder");
    }
    goalLower = liftBoundVariables(goalLower, -1, 1);

    ExpressionPointer goalUpper = upperRelation.arguments[1];
    if (mentionsBoundVariable(goalUpper, 0)
        || mentionsBoundVariable(goalUpper, 1)) {
        throwElaborate("finite_check upper bound may not depend on its premises");
    }
    goalUpper = liftBoundVariables(goalUpper, -1, 1);
    goalUpper = liftBoundVariables(goalUpper, -1, 1);

    ExpressionPointer propositionBody = upperPi->codomain;
    if (mentionsBoundVariable(propositionBody, 0)
        || mentionsBoundVariable(propositionBody, 1)) {
        throwElaborate(
            "finite_check's conclusion P(n) may not depend on the proofs "
            "of its two bounds");
    }
    propositionBody = liftBoundVariables(propositionBody, -1, 1);
    propositionBody = liftBoundVariables(propositionBody, -1, 1);
    ExpressionPointer predicate = makeLambda(
        tactic.binderName, valuePi->domain, propositionBody);

    // Use the ordinary numeral elaborator to retain the carrier's canonical
    // spelling (notably Integer.zero/one and Natural.to_integer for larger
    // values).  This is what makes P(2) match a fact stated with source `2`.
    auto numeralAtCarrier = [&](const mpz_class& value)
            -> ExpressionPointer {
        const bool negative = value < 0;
        mpz_class magnitude = negative ? -value : value;
        SurfaceExpressionPointer surface = makeSurfaceNumericLiteral(
            magnitude.get_str(10), line, column);
        if (negative) {
            surface = makeSurfaceUnaryOperation(
                "-", surface, line, column);
        }
        ExpressionPointer term = elaborateExpression(
            *surface, localBinders, valuePi->domain);
        return coerceToExpectedTypeViaRegistry(
            localBinders, std::move(term), valuePi->domain);
    };
    auto naturalLiteral = [&](size_t value) -> ExpressionPointer {
        return buildNaturalLiteralKernel(mpz_class(value));
    };

    ExpressionPointer writtenLower = elaborateExpression(
        *tactic.lowerBound, localBinders, valuePi->domain);
    ExpressionPointer writtenUpper = elaborateExpression(
        *tactic.upperBound, localBinders, valuePi->domain);
    writtenLower = coerceToExpectedTypeViaRegistry(
        localBinders, std::move(writtenLower), valuePi->domain);
    writtenUpper = coerceToExpectedTypeViaRegistry(
        localBinders, std::move(writtenUpper), valuePi->domain);
    Context context = buildContextFromLocalBinders(localBinders);
    const size_t localCount = localBinders.size();
    auto agreesWithGoal = [&](ExpressionPointer written,
                              ExpressionPointer goal) {
        return isDefinitionallyEqual(
            environment_, context,
            openOverLocalBinders(written, localBinders, localCount),
            openOverLocalBinders(goal, localBinders, localCount));
    };
    if (!agreesWithGoal(writtenLower, goalLower)
        || !agreesWithGoal(writtenUpper, goalUpper)) {
        throwElaborate(
            "finite_check's written bounds do not match the bounds in the "
            "goal (written lower `"
            + prettyPrintInLocalScope(writtenLower, localBinders)
            + "`, goal lower `"
            + prettyPrintInLocalScope(goalLower, localBinders)
            + "`; written upper `"
            + prettyPrintInLocalScope(writtenUpper, localBinders)
            + "`, goal upper `"
            + prettyPrintInLocalScope(goalUpper, localBinders) + "`)");
    }

    LevelPointer carrierLevel = typeUniverseOf(
        localBinders, numeralAtCarrier(*lowerValue));
    auto equalityType = [&](ExpressionPointer left,
                            ExpressionPointer right) {
        return applyMany(
            makeConstant("Equality", {carrierLevel}),
            {valuePi->domain, std::move(left), std::move(right)});
    };
    auto proveEquality = [&](ExpressionPointer left,
                             ExpressionPointer right) {
        return autoProveClaim(
            equalityType(std::move(left), std::move(right)),
            localBinders, line);
    };

    // Empty tail at the upper endpoint, then prepend cases backwards.  Each
    // constructor stores the equality `next = current + 1`; keeping it
    // explicit lets the certificate use canonical numeral spellings rather
    // than opaque addition chains.
    const char* emptyName = isNatural
        ? "Natural.AllFrom.empty" : "Integer.AllFrom.empty";
    const char* prependName = isNatural
        ? "Natural.AllFrom.prepend" : "Integer.AllFrom.prepend";
    struct CheckedCase {
        ExpressionPointer current;
        ExpressionPointer next;
        ExpressionPointer nextReads;
        ExpressionPointer leafProof;
    };
    std::vector<CheckedCase> checkedCases;
    checkedCases.reserve(caseCount);
    // Check in mathematical (ascending) order so the first diagnostic is the
    // first missing row in the user's table.  Certificate construction below
    // then folds this vector backwards.
    for (size_t offset = 0; offset < caseCount; ++offset) {
        mpz_class currentValue = *lowerValue + mpz_class(offset);
        mpz_class nextValue = currentValue + 1;
        ExpressionPointer current = numeralAtCarrier(currentValue);
        ExpressionPointer next = numeralAtCarrier(nextValue);
        ExpressionPointer one = numeralAtCarrier(1);
        ExpressionPointer currentPlusOne = applyMany(
            makeConstant(isNatural ? "Natural.add" : "Integer.add"),
            {current, one});
        ExpressionPointer nextReads;
        try {
            nextReads = proveEquality(next, currentPlusOne);
        } catch (const ElaborateError&) {
            throwElaborate(
                "finite_check could not certify the successor step at "
                + integerForDiagnostic(currentValue));
        }

        ExpressionPointer leafGoal = substitute(
            propositionBody, 0, current);
        ExpressionPointer leafProof;
        try {
            leafProof = autoProveClaim(leafGoal, localBinders, line);
        } catch (const ElaborateError&) {
            throwElaborate(
                "finite_check: case " + tactic.binderName + " = "
                + integerForDiagnostic(currentValue) + " did not close");
        } catch (const AutoProverBudgetError&) {
            throwElaborate(
                "finite_check: case " + tactic.binderName + " = "
                + integerForDiagnostic(currentValue)
                + " exceeded the auto-prover budget");
        }

        checkedCases.push_back(
            {std::move(current), std::move(next), std::move(nextReads),
             std::move(leafProof)});
    }

    ExpressionPointer tailStart = numeralAtCarrier(*upperValue);
    ExpressionPointer certificate = applyMany(
        makeConstant(emptyName), {predicate, tailStart});
    size_t remainingCount = 0;
    for (size_t reverse = caseCount; reverse > 0; --reverse) {
        const CheckedCase& checked = checkedCases[reverse - 1];
        certificate = applyMany(
            makeConstant(prependName),
            {predicate, checked.current, checked.next,
             naturalLiteral(remainingCount), checked.nextReads,
             checked.leafProof, certificate});
        ++remainingCount;
    }

    ExpressionPointer start = numeralAtCarrier(*lowerValue);
    ExpressionPointer upper = numeralAtCarrier(*upperValue);
    ExpressionPointer count = naturalLiteral(caseCount);
    ExpressionPointer countedAtCarrier = isNatural
        ? count
        : makeApplication(makeConstant("Natural.to_integer"), count);
    ExpressionPointer startPlusCount = applyMany(
        makeConstant(isNatural ? "Natural.add" : "Integer.add"),
        {start, countedAtCarrier});
    ExpressionPointer upperReads;
    try {
        upperReads = proveEquality(upper, startPlusCount);
    } catch (const ElaborateError&) {
        throwElaborate(
            "finite_check could not certify that the written range has "
            + std::to_string(caseCount) + " cases");
    }

    const char* bridgeName = isNatural
        ? "Natural.AllFrom_between" : "Integer.AllFrom_between";
    ExpressionPointer result = applyMany(
        makeConstant(bridgeName),
        {predicate, start, count, upper, upperReads, certificate});

    // The bridge should compute back to the user's original bounded goal.
    // Check this boundary here so future changes to either certificate
    // theorem fail locally rather than producing a distant kernel error.
    ExpressionPointer resultType = inferTypeInLocalContext(
        localBinders, result);
    ExpressionPointer goalOpened = openOverLocalBinders(
        expectedType, localBinders, localCount);
    if (!isDefinitionallyEqual(
            environment_, context, resultType, goalOpened)) {
        throwElaborate(
            "finite_check assembled a certificate whose bridge does not "
            "match the original goal (internal certificate mismatch)");
    }
    return result;
}
