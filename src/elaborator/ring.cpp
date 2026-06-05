// Out-of-line Elaborator method definitions: the `ring` / `field` tactic.
//
// Part of the elaborator split (see elaborator_internal.hpp): the class is
// declared in the header; each elaborator_*.cpp defines a topical slice of
// its methods as `Elaborator::method(...)`. This translation unit holds the
// commutative-ring normalisation tactic (`ring`), the field tactic
// (`field`), the `linear_combination` tactic, and their shared polynomial /
// proof-term machinery.

#include "elaborator/internal.hpp"

// ---- Numerical fast-fail fingerprints (GF(2^64 - 59)) --------------------
//
// Before the expensive symbolic normalise + polynomial-dict comparison,
// `ring`/`field` evaluate both sides at a random-ish point in GF(p) (atoms
// stand in via their subtree hash). If the two fingerprints disagree the
// identity is false and we can bail immediately (Schwartz-Zippel: a false
// polynomial identity collides only with probability ~degree/p).

uint64_t Elaborator::fingerprintAdd(uint64_t leftValue, uint64_t rightValue) const {
    // Both inputs are < p < 2^64, so sum fits in unsigned 64 with
    // at most one wraparound. Reduce mod p with a single conditional.
    uint64_t sum = leftValue + rightValue;
    // Overflow OR sum >= p both want reduction by p.
    if (sum < leftValue || sum >= kFingerprintModulus) {
        sum -= kFingerprintModulus;
    }
    return sum;
}

uint64_t Elaborator::fingerprintSubtract(
    uint64_t leftValue, uint64_t rightValue) const {
    return leftValue >= rightValue
        ? leftValue - rightValue
        : leftValue + (kFingerprintModulus - rightValue);
}

uint64_t Elaborator::fingerprintNegate(uint64_t value) const {
    return value == 0 ? 0 : kFingerprintModulus - value;
}

uint64_t Elaborator::fingerprintMultiply(
    uint64_t leftValue, uint64_t rightValue) const {
    // 64-bit × 64-bit needs 128 bits; rely on the compiler's
    // __int128 (clang / gcc on every platform this project targets).
    return (uint64_t)(((__uint128_t)leftValue
                        * (__uint128_t)rightValue)
                       % (__uint128_t)kFingerprintModulus);
}

uint64_t Elaborator::fingerprintModularPower(
    uint64_t base, uint64_t exponent) const {
    uint64_t result = 1;
    uint64_t current = base % kFingerprintModulus;
    while (exponent > 0) {
        if (exponent & 1ull) {
            result = fingerprintMultiply(result, current);
        }
        current = fingerprintMultiply(current, current);
        exponent >>= 1;
    }
    return result;
}

// Modular inverse via Fermat's little theorem: a^(p-2) mod p.
// Returns nullopt iff a == 0 (no inverse, division by zero).
std::optional<uint64_t> Elaborator::fingerprintModularInverse(uint64_t value) const {
    if (value % kFingerprintModulus == 0) return std::nullopt;
    return fingerprintModularPower(value, kFingerprintModulus - 2);
}

// Recursively evaluate an expression as an element of GF(p), with
// opaque atoms replaced by their cached subtree hash. Returns
// nullopt on division by zero (a `<C>.reciprocal_function` applied
// to something whose fingerprint is 0).
std::optional<uint64_t> Elaborator::evaluateFingerprint(
    ExpressionPointer expression,
    const std::string& carrierName) const {
    const std::string addName       = carrierName + ".add";
    const std::string subtractName  = carrierName + ".subtract";
    const std::string multiplyName  = carrierName + ".multiply";
    const std::string negateName    = carrierName + ".negate";
    const std::string zeroName      = carrierName + ".zero";
    const std::string oneName       = carrierName + ".one";
    const std::string reciprocalName
        = carrierName + ".reciprocal_function";
    // Constants.
    if (auto* head = std::get_if<Constant>(&expression->node)) {
        if (head->name == zeroName) return uint64_t{0};
        if (head->name == oneName) return uint64_t{1};
    }
    // Binary operators (peel two Application layers).
    if (auto* outer = std::get_if<Application>(&expression->node)) {
        if (auto* inner =
                std::get_if<Application>(&outer->function->node)) {
            if (auto* head =
                    std::get_if<Constant>(&inner->function->node)) {
                if (head->name == addName
                    || head->name == subtractName
                    || head->name == multiplyName) {
                    auto leftValue = evaluateFingerprint(
                        inner->argument, carrierName);
                    auto rightValue = evaluateFingerprint(
                        outer->argument, carrierName);
                    if (!leftValue || !rightValue) return std::nullopt;
                    if (head->name == addName) {
                        return fingerprintAdd(*leftValue, *rightValue);
                    }
                    if (head->name == subtractName) {
                        return fingerprintSubtract(
                            *leftValue, *rightValue);
                    }
                    return fingerprintMultiply(*leftValue, *rightValue);
                }
            }
        }
        // Unary operators (one Application layer).
        if (auto* head =
                std::get_if<Constant>(&outer->function->node)) {
            if (head->name == negateName) {
                auto value = evaluateFingerprint(
                    outer->argument, carrierName);
                if (!value) return std::nullopt;
                return fingerprintNegate(*value);
            }
            if (head->name == reciprocalName) {
                auto value = evaluateFingerprint(
                    outer->argument, carrierName);
                if (!value) return std::nullopt;
                return fingerprintModularInverse(*value);
            }
        }
    }
    // Otherwise: opaque atom. Use the cached subtree hash mod p.
    return expression->hash % kFingerprintModulus;
}

// Build the "(fingerprint mod (2^64 - 59): …)" diagnostic suffix
// to append onto a ring/field failure. Always returns a string —
// even when the evaluator gives up, the user learns something.
std::string Elaborator::buildFingerprintDiagnostic(
    ExpressionPointer leftEndpoint,
    ExpressionPointer rightEndpoint,
    const std::string& carrierName) const {
    auto leftValue =
        evaluateFingerprint(leftEndpoint, carrierName);
    auto rightValue =
        evaluateFingerprint(rightEndpoint, carrierName);
    if (!leftValue || !rightValue) {
        return "\n(fingerprint mod (2^64 - 59): division by zero "
               "during evaluation — either a denominator that "
               "needs a nonzero hypothesis, or a 1-in-2^64 hash "
               "collision; can't diagnose either way)";
    }
    if (*leftValue == *rightValue) {
        return "\n(fingerprint mod (2^64 - 59): LHS = RHS = "
             + std::to_string(*leftValue)
             + " — the identity is almost certainly true; this "
               "looks like a tactic limitation, not a real "
               "mathematical mismatch)";
    }
    return "\n(fingerprint mod (2^64 - 59): LHS = "
         + std::to_string(*leftValue) + ", RHS = "
         + std::to_string(*rightValue)
         + " — the identity is FALSE as a polynomial / field "
           "identity; the goal as stated is not provable)";
}

// ==== ring / field tactic + polynomial / proof machinery ====

bool Elaborator::flattenRingProduct(
        ExpressionPointer term,
        const std::string& carrierOpName,
        std::vector<ExpressionPointer>& factorsOut) {
        // Walk: if `term` is `<op>([prefix,] a, b)` (the structure prefix
        // is the leading bundle argument for a bundled commutative ring,
        // absent for a concrete carrier — `matchBinaryRingOp` handles
        // both), recursively flatten a and b. Otherwise treat as an atom.
        // `<op>` is "multiply" or "add" depending on which axiom-set the
        // ring tactic is using for this goal.
        ExpressionPointer left, right;
        if (matchBinaryRingOp(term, carrierOpName, left, right)) {
            if (!flattenRingProduct(left, carrierOpName, factorsOut)) {
                return false;
            }
            if (!flattenRingProduct(right, carrierOpName, factorsOut)) {
                return false;
            }
            return true;
        }
        factorsOut.push_back(term);
        return true;
    }

ExpressionPointer Elaborator::assembleLeftAssociatedProduct(
        const std::string& carrierMultiplyName,
        const std::vector<ExpressionPointer>& factors) {
        ExpressionPointer accumulator = factors[0];
        for (size_t i = 1; i < factors.size(); ++i) {
            // buildRingOp threads the active structure prefix (`[c]` for a
            // bundled commutative ring), so this matches the canonical
            // forms built elsewhere; for a concrete carrier the prefix is
            // empty and this is a plain `op(acc, factor)`.
            accumulator = buildRingOp(
                carrierMultiplyName, accumulator, factors[i]);
        }
        return accumulator;
    }

int Elaborator::compareExpressionStructure(
        ExpressionPointer left, ExpressionPointer right) {
        if (left.get() == right.get()) return 0;
        if (left->node.index() < right->node.index()) return -1;
        if (left->node.index() > right->node.index()) return 1;
        if (auto* a = std::get_if<BoundVariable>(&left->node)) {
            auto* b = std::get_if<BoundVariable>(&right->node);
            if (a->deBruijnIndex < b->deBruijnIndex) return -1;
            if (a->deBruijnIndex > b->deBruijnIndex) return 1;
            return 0;
        }
        if (auto* a = std::get_if<FreeVariable>(&left->node)) {
            auto* b = std::get_if<FreeVariable>(&right->node);
            int nameCmp = a->name.compare(b->name);
            if (nameCmp != 0) return nameCmp < 0 ? -1 : 1;
            return 0;
        }
        if (auto* a = std::get_if<Constant>(&left->node)) {
            auto* b = std::get_if<Constant>(&right->node);
            return a->name.compare(b->name) < 0 ? -1
                 : a->name.compare(b->name) > 0 ?  1 : 0;
        }
        if (auto* a = std::get_if<Application>(&left->node)) {
            auto* b = std::get_if<Application>(&right->node);
            int fcmp = compareExpressionStructure(
                a->function, b->function);
            if (fcmp != 0) return fcmp;
            return compareExpressionStructure(a->argument, b->argument);
        }
        if (auto* a = std::get_if<Lambda>(&left->node)) {
            auto* b = std::get_if<Lambda>(&right->node);
            int dcmp = compareExpressionStructure(a->domain, b->domain);
            if (dcmp != 0) return dcmp;
            return compareExpressionStructure(a->body, b->body);
        }
        if (auto* a = std::get_if<Pi>(&left->node)) {
            auto* b = std::get_if<Pi>(&right->node);
            int dcmp = compareExpressionStructure(a->domain, b->domain);
            if (dcmp != 0) return dcmp;
            return compareExpressionStructure(a->codomain, b->codomain);
        }
        // Other variants: treat as equal (shouldn't appear as atoms).
        return 0;
    }

uint64_t Elaborator::evalRingMod(
        ExpressionPointer expression,
        const std::string& carrierName,
        const std::string& addName,
        const std::string& multiplyName,
        const std::string& negateName,
        const std::string& subtractName,
        const std::string& zeroName,
        const std::string& oneName,
        uint64_t modulus) {
        if (matchRingZero(expression, zeroName)) return 0;
        if (matchRingOne(expression, oneName)) return 1 % modulus;
        ExpressionPointer left, right;
        if (matchBinaryRingOp(expression, addName, left, right)) {
            uint64_t l = evalRingMod(left, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            uint64_t r = evalRingMod(right, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            return (l + r) % modulus;
        }
        if (matchBinaryRingOp(expression, multiplyName, left, right)) {
            uint64_t l = evalRingMod(left, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            uint64_t r = evalRingMod(right, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            return (uint64_t)(((__uint128_t)l * r) % modulus);
        }
        if (matchBinaryRingOp(expression, subtractName, left, right)) {
            uint64_t l = evalRingMod(left, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            uint64_t r = evalRingMod(right, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            return (l + modulus - r) % modulus;
        }
        ExpressionPointer inner;
        if (matchUnaryRingNegate(expression, negateName, inner)) {
            uint64_t v = evalRingMod(inner, carrierName, addName,
                multiplyName, negateName, subtractName, zeroName,
                oneName, modulus);
            return (modulus - v) % modulus;
        }
        // Carrier-embedded Natural literal — must mirror the ring normaliser's
        // literal recognition (which itself depends on the carrier).
        // For Integer: Natural.to_integer(succ^k(zero)) → k.
        // For Rational: Integer.to_rational(Natural.to_integer(...)) → k.
        // For Real: Rational.to_real(Integer.to_rational(...)) → k.
        // At each level we also accept the outer carrier's named
        // zero/one constants (which the elaborator may produce in
        // place of the coercion application for literals 0 and 1).
        {
            // Pairs of (coercion fn name, outer carrier name) —
            // OUTERMOST FIRST.
            std::vector<std::pair<std::string, std::string>> outerChain;
            if (carrierName == "Integer") {
                outerChain = {{"Natural.to_integer", "Integer"}};
            } else if (carrierName == "Rational") {
                outerChain = {{"Integer.to_rational", "Rational"},
                              {"Natural.to_integer", "Integer"}};
            } else if (carrierName == "Real") {
                outerChain = {{"Rational.to_real", "Real"},
                              {"Integer.to_rational", "Rational"},
                              {"Natural.to_integer", "Integer"}};
            }
            if (!outerChain.empty()) {
                ExpressionPointer cursor = expression;
                bool matched = true;
                for (const auto& [coercion, outerCarrier] : outerChain) {
                    // Check current level's zero/one named constants.
                    if (auto* nameHead =
                            std::get_if<Constant>(&cursor->node)) {
                        if (nameHead->name == outerCarrier + ".zero") {
                            return 0;
                        }
                        if (nameHead->name == outerCarrier + ".one") {
                            return 1 % modulus;
                        }
                    }
                    auto* app =
                        std::get_if<Application>(&cursor->node);
                    if (!app) { matched = false; break; }
                    auto* head =
                        std::get_if<Constant>(&app->function->node);
                    if (!head || head->name != coercion) {
                        matched = false; break;
                    }
                    cursor = app->argument;
                }
                if (matched) {
                    int value = 0;
                    if (tryParseNaturalLiteral(cursor, value)) {
                        return ((uint64_t)value) % modulus;
                    }
                }
            }
        }
        // Scalar-multiply operator at non-Integer carriers — must
        // mirror tryParseScalarMultiplyOperator. We evaluate the inner
        // Integer scalar as if it were carrier-embedded (using its own
        // multi-step coercion via the same Integer→Rational chain that
        // wraps it inside the operator's δ-unfolded form).
        if (carrierName == "Rational" || carrierName == "Real") {
            std::string fromIntegerMultiplyName =
                carrierName + ".from_integer_multiply";
            std::string multiplyByIntegerName =
                carrierName + ".multiply_by_integer";
            if (auto* outerApp =
                    std::get_if<Application>(&expression->node)) {
                if (auto* innerApp =
                        std::get_if<Application>(&outerApp->function->node)) {
                    if (auto* head =
                            std::get_if<Constant>(&innerApp->function->node)) {
                        ExpressionPointer scalar, atom;
                        bool match = false;
                        if (head->name == fromIntegerMultiplyName) {
                            scalar = innerApp->argument;
                            atom = outerApp->argument;
                            match = true;
                        } else if (head->name == multiplyByIntegerName) {
                            atom = innerApp->argument;
                            scalar = outerApp->argument;
                            match = true;
                        }
                        if (match) {
                            // The Integer-typed scalar uses the
                            // Integer-carrier chain: just Natural.to_integer.
                            uint64_t s = evalRingMod(
                                scalar, "Integer",
                                "Integer.add", "Integer.multiply",
                                "Integer.negate", "Integer.subtract",
                                "Integer.zero", "Integer.one", modulus);
                            uint64_t a = evalRingMod(
                                atom, carrierName, addName,
                                multiplyName, negateName, subtractName,
                                zeroName, oneName, modulus);
                            return (uint64_t)(((__uint128_t)s * a) % modulus);
                        }
                    }
                }
            }
        }
        // Atom: use the cached bottom-up structural hash. Two
        // structurally-equal atoms have the same hash, so they get the
        // same Z/p value on both sides of the equation.
        return expression->hash % modulus;
    }

bool Elaborator::ringFastFailAgrees(
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        const std::string& carrierName,
        const std::string& opNamespace) {
        // 2^61 - 1, a Mersenne prime. Largest fitting comfortably in
        // uint64_t so (a * b) % p in __uint128_t stays sound.
        constexpr uint64_t kModulus = (1ULL << 61) - 1;
        const std::string addName       = opNamespace + ".add";
        const std::string multiplyName  = opNamespace + ".multiply";
        const std::string negateName    = opNamespace + ".negate";
        const std::string subtractName  = opNamespace + ".subtract";
        const std::string zeroName      = opNamespace + ".zero";
        const std::string oneName       = opNamespace + ".one";
        uint64_t leftValue = evalRingMod(
            leftEndpoint, carrierName, addName, multiplyName,
            negateName, subtractName, zeroName, oneName, kModulus);
        uint64_t rightValue = evalRingMod(
            rightEndpoint, carrierName, addName, multiplyName,
            negateName, subtractName, zeroName, oneName, kModulus);
        return leftValue == rightValue;
    }

Elaborator::CombinationEquation Elaborator::evalLinearCombinationTree(
        const SurfaceExpressionPointer& node,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer carrierType,
        LevelPointer carrierLevel,
        const std::string& opNamespace,
        const std::vector<ExpressionPointer>& structurePrefix,
        int line) {
        size_t binderCount = localBinders.size();
        // A bundled carrier's operations carry a leading structure argument
        // (`CommutativeRing.add(c)` not `Integer.add`); prepend it. Empty
        // for a concrete carrier, so this is the identity in the v1 case.
        auto opHead = [&](const std::string& opName) {
            ExpressionPointer head = makeConstant(opName);
            for (const auto& arg : structurePrefix) {
                head = makeApplication(std::move(head), arg);
            }
            return head;
        };
        auto opApply = [&](const std::string& opName,
                           ExpressionPointer x, ExpressionPointer y) {
            return makeApplication(
                makeApplication(opHead(opName), std::move(x)),
                std::move(y));
        };
        // Combine `op(a.left, b.left) = op(a.right, b.right)` from the
        // child proofs: rewrite the first operand (congruence on slot 1),
        // then the second (congruence on slot 2), chained by transitivity.
        auto combineBinary = [&](const std::string& opName,
                                 const CombinationEquation& a,
                                 const CombinationEquation& b)
                -> CombinationEquation {
            ExpressionPointer newLeft = opApply(opName, a.left, b.left);
            ExpressionPointer middle = opApply(opName, a.right, b.left);
            ExpressionPointer newRight = opApply(opName, a.right, b.right);
            ExpressionPointer lambda1 = makeLambda("_lc_z", carrierType,
                opApply(opName, makeBoundVariable(0),
                        liftBoundVariables(b.left, 1, 0)));
            ExpressionPointer step1 = buildEqualityCongruenceSameCarrier(
                carrierLevel, carrierType, lambda1, a.left, a.right, a.proof);
            ExpressionPointer lambda2 = makeLambda("_lc_z", carrierType,
                opApply(opName, liftBoundVariables(a.right, 1, 0),
                        makeBoundVariable(0)));
            ExpressionPointer step2 = buildEqualityCongruenceSameCarrier(
                carrierLevel, carrierType, lambda2, b.left, b.right, b.proof);
            ExpressionPointer proof = buildEqualityTransitivity(
                carrierLevel, carrierType, newLeft, middle, newRight,
                step1, step2);
            return {newLeft, newRight, proof};
        };
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&node->node)) {
            const std::string& sym = binary->opSymbol;
            if (sym == "+" || sym == "*" || sym == "-") {
                std::string opName = opNamespace
                    + (sym == "+" ? ".add"
                       : (sym == "*" ? ".multiply" : ".subtract"));
                CombinationEquation a = evalLinearCombinationTree(
                    binary->left, localBinders, carrierType, carrierLevel,
                    opNamespace, structurePrefix, line);
                CombinationEquation b = evalLinearCombinationTree(
                    binary->right, localBinders, carrierType, carrierLevel,
                    opNamespace, structurePrefix, line);
                return combineBinary(opName, a, b);
            }
        }
        if (auto* unary =
                std::get_if<SurfaceUnaryOperation>(&node->node)) {
            if (unary->opSymbol == "-") {
                CombinationEquation a = evalLinearCombinationTree(
                    unary->operand, localBinders, carrierType, carrierLevel,
                    opNamespace, structurePrefix, line);
                std::string negateName = opNamespace + ".negate";
                ExpressionPointer newLeft =
                    makeApplication(opHead(negateName), a.left);
                ExpressionPointer newRight =
                    makeApplication(opHead(negateName), a.right);
                ExpressionPointer lambda = makeLambda("_lc_z", carrierType,
                    makeApplication(opHead(negateName),
                                    makeBoundVariable(0)));
                ExpressionPointer proof = buildEqualityCongruenceSameCarrier(
                    carrierLevel, carrierType, lambda, a.left, a.right,
                    a.proof);
                return {newLeft, newRight, proof};
            }
        }
        // Leaf: elaborate and inspect its type. An equality proof is a
        // hypothesis (its endpoints are the equation); anything else is a
        // scalar ring value `v`, denoting the trivial equation `v = v`.
        ExpressionPointer leafClosed =
            elaborateExpression(*node, localBinders);
        ExpressionPointer leaf =
            openOverLocalBinders(leafClosed, localBinders, binderCount);
        ExpressionPointer leafType = weakHeadNormalForm(environment_,
            inferType(environment_,
                buildContextFromLocalBinders(localBinders), leaf));
        try {
            EqualityComponents eq = extractEqualityComponents(
                leafType, "linear_combination hypothesis", line);
            return {eq.leftEndpoint, eq.rightEndpoint, leaf};
        } catch (const ElaborateError&) {
            ExpressionPointer reflexivityProof = makeApplication(
                makeApplication(
                    makeConstant("reflexivity", {carrierLevel}),
                    carrierType),
                leaf);
            return {leaf, leaf, reflexivityProof};
        }
    }

ExpressionPointer Elaborator::elaborateLinearCombination(
        const SurfaceLinearCombination& tactic,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this,
            "linear_combination at line " + std::to_string(line),
            localBinders, expectedType, line, column);
        if (!expectedType) {
            throwElaborate("`linear_combination` needs an equality goal "
                           "from context");
        }
        size_t binderCount = localBinders.size();
        ExpressionPointer expectedOpened =
            openOverLocalBinders(expectedType, localBinders, binderCount);
        EqualityComponents goal = extractEqualityComponents(
            expectedOpened, "linear_combination", line);
        std::string carrierName = headConstantName(goal.carrierType);
        RingScheme scheme = computeRingScheme(goal.carrierType);
        // Resolve the carrier's ring operations + IsRing instance (matches
        // `ring`'s normalisation context). For a bundled carrier
        // `CommutativeRing.carrier(c)` the ops carry the leading structure
        // argument `c` (`scheme.structurePrefix`); for a concrete carrier
        // the prefix is empty and these are the plain named constants.
        auto requireConstantBare = [&](const std::string& name)
                -> ExpressionPointer {
            if (!environment_.lookup(name)) {
                throwElaborate("`linear_combination`: carrier `" + carrierName
                    + "` is missing `" + name
                    + "` (import the module that defines it)");
            }
            return makeConstant(name);
        };
        auto requireConstant = [&](const std::string& name)
                -> ExpressionPointer {
            ExpressionPointer head = requireConstantBare(name);
            for (const auto& arg : scheme.structurePrefix) {
                head = makeApplication(std::move(head), arg);
            }
            return head;
        };
        ExpressionPointer addOp = requireConstant(scheme.opNamespace + ".add");
        ExpressionPointer zeroOp =
            requireConstant(scheme.opNamespace + ".zero");
        ExpressionPointer negateOp =
            requireConstant(scheme.opNamespace + ".negate");
        ExpressionPointer multiplyOp =
            requireConstant(scheme.opNamespace + ".multiply");
        ExpressionPointer oneOp = requireConstant(scheme.opNamespace + ".one");
        ExpressionPointer isRingTerm =
            requireConstant(scheme.opNamespace + ".is_ring");
        requireConstantBare("Ring.equal_of_linear_combination");
        auto addApply = [&](ExpressionPointer x, ExpressionPointer y) {
            return makeApplication(makeApplication(addOp, x), y);
        };
        auto negateApply = [&](ExpressionPointer x) {
            return makeApplication(negateOp, x);
        };
        // Walk the combination tree: a `+`/`*`/`-` expression over
        // hypotheses (equality proofs) and scalar ring coefficients. Each
        // node denotes an equation; the walker returns the combined
        // `combLeft = combRight` and a proof of it. A bare hypothesis is
        // the degenerate single-leaf tree (the v1 case).
        CombinationEquation comb = evalLinearCombinationTree(
            tactic.combination, localBinders, goal.carrierType,
            goal.carrierUniverseLevel, scheme.opNamespace,
            scheme.structurePrefix, line);
        ExpressionPointer combProof = comb.proof;
        // Bridge: goalL − goalR = combL − combR, proved by the ring
        // normaliser (it is a pure ring identity — no hypotheses). β-reduce
        // the combination's endpoints first: a hypothesis built with
        // `congruenceOf(λz. …, h)`, or a scaled leaf, can leave combL/combR
        // as β-redexes the ring normaliser would otherwise treat as opaque
        // atoms.
        ExpressionPointer combLeftReduced =
            betaNormalizeForDisplay(comb.left);
        ExpressionPointer combRightReduced =
            betaNormalizeForDisplay(comb.right);
        ExpressionPointer bridgeLeft =
            addApply(goal.leftEndpoint, negateApply(goal.rightEndpoint));
        ExpressionPointer bridgeRight =
            addApply(combLeftReduced, negateApply(combRightReduced));
        ExpressionPointer bridgeProof = elaborateRingByNormalisation(
            /*localBinders*/{}, bridgeLeft, bridgeRight,
            goal.carrierType, goal.carrierUniverseLevel, carrierName, line);
        // Assemble Ring.equal_of_linear_combination(carrier, add, zero,
        // negate, multiply, one, isRing, goalL, goalR, combL, combR,
        // combProof, bridgeProof).
        ExpressionPointer result =
            makeConstant("Ring.equal_of_linear_combination");
        for (ExpressionPointer arg :
                {goal.carrierType, addOp, zeroOp, negateOp, multiplyOp, oneOp,
                 isRingTerm, goal.leftEndpoint, goal.rightEndpoint,
                 comb.left, comb.right, combProof,
                 bridgeProof}) {
            result = makeApplication(std::move(result), arg);
        }
        (void)column;
        return closeOverLocalBinders(result, localBinders, binderCount);
    }

ExpressionPointer Elaborator::elaborateRing(
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "ring at line " + std::to_string(line),
                    localBinders, expectedType, line, column);
        if (!expectedType) {
            throwElaborate(
                "`ring` needs an expected type from context — use it "
                "in a calc step or as the body of a theorem with a "
                "declared equality conclusion");
        }
        EqualityComponents goal =
            extractEqualityComponents(expectedType, "ring", line);
        std::string carrierName = headConstantName(goal.carrierType);
        // How operations/laws are named for this carrier, and the leading
        // structure argument they carry (`[s]` for a bundled-ring carrier
        // `Ring.carrier(s)`, empty for a concrete carrier). Installed for
        // the rest of this `ring` elaboration so the matchers and the
        // term/law builders thread `s` automatically.
        RingScheme scheme = computeRingScheme(goal.carrierType);
        RingStructurePrefixGuard prefixGuard(*this, scheme.structurePrefix);
        // Z/p numerical fast-fail. If the two sides disagree as
        // polynomials over Z/p, ring CANNOT prove them equal — bail
        // immediately without doing the expensive symbolic normalise
        // + polynomial-dict comparison work. See `evalRingMod` for
        // soundness rationale (Schwartz-Zippel).
        if (!ringFastFailAgrees(
                goal.leftEndpoint, goal.rightEndpoint, carrierName,
                scheme.opNamespace)) {
            throwElaborate(
                "`ring`: the two sides do not agree mod 2^61 - 1 — "
                "they are not equal as commutative-ring expressions"
                + buildFingerprintDiagnostic(
                      goal.leftEndpoint, goal.rightEndpoint,
                      carrierName));
        }
        // A bundled-ring carrier's operations carry a leading structure
        // argument, which the single-operator AC fast path below does not
        // model. Route it straight to the normaliser (which does). We
        // open the goal over the local binders first so the carrier index
        // (`c`) and the atoms become FREE variables: the structure prefix
        // `c` that the term/law builders thread is then stable under the
        // congruence lambdas the normaliser builds (a bound-variable
        // prefix would need shifting inside each lambda). The proof is
        // closed again before returning.
        if (!scheme.structurePrefix.empty()) {
            ExpressionPointer expectedTypeOpened = openOverLocalBinders(
                expectedType, localBinders, localBinders.size());
            EqualityComponents openedGoal = extractEqualityComponents(
                expectedTypeOpened, "ring", line);
            ExpressionPointer proof = elaborateRingByNormalisation(
                /*localBinders*/{},
                openedGoal.leftEndpoint, openedGoal.rightEndpoint,
                openedGoal.carrierType, openedGoal.carrierUniverseLevel,
                carrierName, line);
            return closeOverLocalBinders(
                proof, localBinders, localBinders.size());
        }
        // Try the multiplicative axioms first; if the goal isn't a
        // pure product, try the additive axioms. Either is acceptable
        // — both reduce to the same insertion-sort + reassociate
        // proof emitter parameterised by a RingAxiomNames triple.
        auto buildAxioms =
            [&](const std::string& opSuffix) -> RingAxiomNames {
            return RingAxiomNames{
                carrierName + "." + opSuffix,
                carrierName + "." + opSuffix + "_associative",
                carrierName + "." + opSuffix + "_commutative"};
        };
        auto axiomsAvailable =
            [&](const RingAxiomNames& a) -> bool {
            return environment_.lookup(a.op) != nullptr
                && environment_.lookup(a.associative) != nullptr
                && environment_.lookup(a.commutative) != nullptr;
        };
        std::vector<ExpressionPointer> leftFactors, rightFactors;
        RingAxiomNames axioms;
        // Helper: try one axiom set; succeed if the factor multisets
        // match (after sort).
        auto try_axioms =
            [&](const RingAxiomNames& candidate) -> bool {
            if (!axiomsAvailable(candidate)) return false;
            std::vector<ExpressionPointer> lf, rf;
            if (!flattenRingProduct(goal.leftEndpoint, candidate.op, lf)
                || !flattenRingProduct(goal.rightEndpoint,
                                           candidate.op, rf)) {
                return false;
            }
            if (lf.size() != rf.size()) return false;
            std::vector<ExpressionPointer> ls = lf;
            std::vector<ExpressionPointer> rs = rf;
            auto cmp = [this](ExpressionPointer a,
                                ExpressionPointer b) {
                return compareExpressionStructure(a, b) < 0;
            };
            std::sort(ls.begin(), ls.end(), cmp);
            std::sort(rs.begin(), rs.end(), cmp);
            for (size_t i = 0; i < ls.size(); ++i) {
                if (!structurallyEqual(ls[i], rs[i])) return false;
            }
            leftFactors = std::move(lf);
            rightFactors = std::move(rf);
            return true;
        };
        if (try_axioms(buildAxioms("multiply"))) {
            axioms = buildAxioms("multiply");
        } else if (try_axioms(buildAxioms("add"))) {
            axioms = buildAxioms("add");
        } else {
            // v1 (pure-AC for one operator) can't close the goal.
            // Fall through to v2, which normalises both sides to a
            // sum-of-monomials canonical form (handles distributivity,
            // 0/1 identity, negation, and like-term cancellation
            // within ±1 coefficient).
            return elaborateRingByNormalisation(
                /*localBinders*/{},
                goal.leftEndpoint, goal.rightEndpoint,
                goal.carrierType, goal.carrierUniverseLevel,
                carrierName, line);
        }
        if (leftFactors.size() != rightFactors.size()) {
            throwElaborate(
                "`ring`: left side has "
                + std::to_string(leftFactors.size())
                + " factors, right side has "
                + std::to_string(rightFactors.size())
                + " — multisets cannot match");
        }
        // Compute a sorted canonical order. Sort both sides by the
        // structural comparator; check the sorted vectors are
        // factor-wise structurally equal.
        std::vector<ExpressionPointer> leftSorted = leftFactors;
        std::vector<ExpressionPointer> rightSorted = rightFactors;
        auto cmp = [this](ExpressionPointer a, ExpressionPointer b) {
            return compareExpressionStructure(a, b) < 0;
        };
        std::sort(leftSorted.begin(), leftSorted.end(), cmp);
        std::sort(rightSorted.begin(), rightSorted.end(), cmp);
        for (size_t i = 0; i < leftSorted.size(); ++i) {
            if (!structurallyEqual(leftSorted[i], rightSorted[i])) {
                throwElaborate(
                    "`ring`: factor multisets differ — left and right "
                    "sides cannot be brought to the same canonical "
                    "product");
            }
        }
        // Build a kernel proof: LHS = canonical = RHS.
        // canonical = left-associated product of leftSorted.
        ExpressionPointer canonicalKernel =
            assembleLeftAssociatedProduct(axioms.op, leftSorted);
        ExpressionPointer leftProof =
            proveProductEqualsSorted(goal.leftEndpoint, leftFactors,
                                      leftSorted, axioms,
                                      goal.carrierType,
                                      goal.carrierUniverseLevel, line);
        ExpressionPointer rightProof =
            proveProductEqualsSorted(goal.rightEndpoint, rightFactors,
                                      rightSorted, axioms,
                                      goal.carrierType,
                                      goal.carrierUniverseLevel, line);
        // rightProof: RHS = canonical. We need canonical = RHS via
        // symmetry, then chain via transitivity.
        ExpressionPointer rightProofSymm = makeConstant(
            "Equality.symmetry", {goal.carrierUniverseLevel});
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           goal.carrierType);
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           goal.rightEndpoint);
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           canonicalKernel);
        rightProofSymm = makeApplication(std::move(rightProofSymm),
                                           std::move(rightProof));
        ExpressionPointer finalProof = makeConstant(
            "Equality.transitivity", {goal.carrierUniverseLevel});
        finalProof = makeApplication(std::move(finalProof),
                                       goal.carrierType);
        finalProof = makeApplication(std::move(finalProof),
                                       goal.leftEndpoint);
        finalProof = makeApplication(std::move(finalProof),
                                       canonicalKernel);
        finalProof = makeApplication(std::move(finalProof),
                                       goal.rightEndpoint);
        finalProof = makeApplication(std::move(finalProof),
                                       std::move(leftProof));
        finalProof = makeApplication(std::move(finalProof),
                                       std::move(rightProofSymm));
        return finalProof;
    }

Elaborator::RingScheme Elaborator::computeRingScheme(ExpressionPointer carrierType) {
        RingScheme scheme;
        scheme.carrierHead = headConstantName(carrierType);
        scheme.opNamespace = scheme.carrierHead;
        // Bundled commutative-ring carrier `CommutativeRing.carrier(c)`:
        // operations/laws are the `CommutativeRing.*` projections applied
        // to `c`. This is the only sound `ring` target among the bundles,
        // since `ring` needs multiplicative commutativity (a plain
        // `Ring.carrier(s)` has no `multiply_commutative`); see
        // Algebra/commutative_ring_algebra.math.
        if (scheme.carrierHead == "CommutativeRing.carrier") {
            if (auto* app =
                    std::get_if<Application>(&carrierType->node)) {
                scheme.opNamespace = "CommutativeRing";
                scheme.structurePrefix = { app->argument };
            }
        }
        return scheme;
    }

ExpressionPointer Elaborator::ringConst(const std::string& name) {
        ExpressionPointer head = makeConstant(name);
        for (const auto& prefixArg : ringStructurePrefix_) {
            head = makeApplication(std::move(head), prefixArg);
        }
        return head;
    }

ExpressionPointer Elaborator::buildRingOp(
        const std::string& opName,
        ExpressionPointer left, ExpressionPointer right) {
        ExpressionPointer call = ringConst(opName);
        call = makeApplication(std::move(call), std::move(left));
        call = makeApplication(std::move(call), std::move(right));
        return call;
    }

ExpressionPointer Elaborator::buildRingMultiply(
        const std::string& carrierName,
        ExpressionPointer left, ExpressionPointer right) {
        return buildRingOp(carrierName + ".multiply",
                            std::move(left), std::move(right));
    }

ExpressionPointer Elaborator::buildRingAssoc(
        const RingAxiomNames& axioms,
        ExpressionPointer P, ExpressionPointer a, ExpressionPointer b) {
        ExpressionPointer call =
            ringConst(axioms.associative);
        call = makeApplication(std::move(call), std::move(P));
        call = makeApplication(std::move(call), std::move(a));
        call = makeApplication(std::move(call), std::move(b));
        return call;
    }

ExpressionPointer Elaborator::buildRingCommute(
        const RingAxiomNames& axioms,
        ExpressionPointer a, ExpressionPointer b) {
        ExpressionPointer call =
            ringConst(axioms.commutative);
        call = makeApplication(std::move(call), std::move(a));
        call = makeApplication(std::move(call), std::move(b));
        return call;
    }

ExpressionPointer Elaborator::buildAdjacentSwapProof(
        const RingAxiomNames& axioms,
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        const std::vector<ExpressionPointer>& factors,
        size_t swapPosition) {
        // swapPosition is the index of the SECOND of the two factors
        // being swapped (so factors[swapPosition - 1] and
        // factors[swapPosition] get exchanged). 1 <= swapPosition < n.
        size_t k = swapPosition;
        const ExpressionPointer& a = factors[k - 1];
        const ExpressionPointer& b = factors[k];
        // Step A: build the base swap proof at the level just enclosing
        // factors a and b.
        ExpressionPointer baseProof;
        ExpressionPointer baseLHS;  // left-assoc of factors[0..k]
        ExpressionPointer baseRHS;  // left-assoc with k-1 and k swapped
        if (k == 1) {
            // No prefix; the level-1 subtree is just `a op b`.
            // Proof: commutative(a, b) : a op b = b op a.
            baseProof = buildRingCommute(axioms, a, b);
            baseLHS = buildRingOp(axioms.op, a, b);
            baseRHS = buildRingOp(axioms.op, b, a);
        } else {
            // Prefix P = left-assoc of factors[0..k-1] (positions 0
            // through k-2). Then base subtree = (P op a) op b.
            std::vector<ExpressionPointer> prefixFactors(
                factors.begin(),
                factors.begin() + static_cast<long>(k - 1));
            ExpressionPointer P = assembleLeftAssociatedProduct(
                axioms.op, prefixFactors);
            // Step 1: (P op a) op b = P op (a op b) by associative
            ExpressionPointer pTimesAB =
                buildRingOp(axioms.op, P,
                    buildRingOp(axioms.op, a, b));
            ExpressionPointer pTimesA_TimesB =
                buildRingOp(axioms.op,
                    buildRingOp(axioms.op, P, a), b);
            ExpressionPointer step1 =
                buildRingAssoc(axioms, P, a, b);
            // Step 2: P op (a op b) = P op (b op a) via congruence with
            // λz. P op z. Lift P's bound-vars into the new lambda scope.
            ExpressionPointer plift = liftBoundVariables(P, 1, 0);
            ExpressionPointer lambdaBody = buildRingOp(
                axioms.op, plift, makeBoundVariable(0));
            ExpressionPointer lambdaPTimesZ = makeLambda(
                "_ring_swap_z", carrierType, lambdaBody);
            ExpressionPointer commutProof =
                buildRingCommute(axioms, a, b);
            ExpressionPointer aTimesB =
                buildRingOp(axioms.op, a, b);
            ExpressionPointer bTimesA =
                buildRingOp(axioms.op, b, a);
            ExpressionPointer step2 = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambdaPTimesZ,
                aTimesB, bTimesA, commutProof);
            // Step 3: P op (b op a) = (P op b) op a via sym associative
            ExpressionPointer pTimesBA =
                buildRingOp(axioms.op, P,
                    buildRingOp(axioms.op, b, a));
            ExpressionPointer pTimesB_TimesA =
                buildRingOp(axioms.op,
                    buildRingOp(axioms.op, P, b), a);
            ExpressionPointer assocPBA =
                buildRingAssoc(axioms, P, b, a);
            ExpressionPointer step3 = buildEqualitySymmetry(
                universeLevel, carrierType,
                pTimesB_TimesA, pTimesBA, assocPBA);
            // Chain: transitivity(step1, transitivity(step2, step3))
            ExpressionPointer step23 = buildEqualityTransitivity(
                universeLevel, carrierType,
                pTimesAB, pTimesBA, pTimesB_TimesA, step2, step3);
            baseProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                pTimesA_TimesB, pTimesAB, pTimesB_TimesA,
                step1, step23);
            baseLHS = pTimesA_TimesB;
            baseRHS = pTimesB_TimesA;
        }
        // Step B: lift through factors[k+1..n-1] via congruences
        // λz. z op factors[j] for each j > k.
        ExpressionPointer currentProof = baseProof;
        ExpressionPointer currentLHS = baseLHS;
        ExpressionPointer currentRHS = baseRHS;
        for (size_t j = k + 1; j < factors.size(); ++j) {
            ExpressionPointer fjLifted =
                liftBoundVariables(factors[j], 1, 0);
            ExpressionPointer lambdaBody = buildRingOp(
                axioms.op, makeBoundVariable(0), fjLifted);
            ExpressionPointer lambda = makeLambda(
                "_ring_lift_z", carrierType, lambdaBody);
            ExpressionPointer newLHS = buildRingOp(
                axioms.op, currentLHS, factors[j]);
            ExpressionPointer newRHS = buildRingOp(
                axioms.op, currentRHS, factors[j]);
            currentProof = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambda,
                currentLHS, currentRHS, currentProof);
            currentLHS = std::move(newLHS);
            currentRHS = std::move(newRHS);
        }
        return currentProof;
    }

ExpressionPointer Elaborator::buildLeftAssocReassocProof(
        const RingAxiomNames& axioms,
        LevelPointer universeLevel,
        ExpressionPointer carrierType,
        ExpressionPointer expression) {
        const std::string& opName = axioms.op;
        std::vector<ExpressionPointer> factors;
        if (!flattenRingProduct(expression, opName, factors)) {
            // Shouldn't happen — caller already flattened.
            throwElaborate("ring: internal reassociate failure");
        }
        ExpressionPointer canonical =
            assembleLeftAssociatedProduct(opName, factors);
        if (structurallyEqual(expression, canonical)) {
            return buildReflexivity(universeLevel, carrierType,
                                      expression);
        }
        // Recursive case: expression = A * B where B is itself a
        // product. We re-associate: A * B = ... we want (left part of
        // A's factors plus the first factor of B) * (rest of B). The
        // cleanest path: structurally process.
        //
        // Walk expression: if it's leftFactor * rightFactor where
        // rightFactor is `X * Y` (a product), then:
        //   leftFactor * (X * Y) = (leftFactor * X) * Y  by sym assoc.
        //   recurse on the new form, prefix with that one assoc step.
        // Else if leftFactor is itself a product, recurse on leftFactor:
        //   leftFactor * rightFactor: combine leftFactor's reassoc
        //   proof with congruenceOf(λx. x * rightFactor, ...).
        // Else (both atoms): we'd be at single-element case, handled
        // by the equality check above.
        // Decompose `expression = L op R` (prefix-aware via the matcher,
        // so a bundled `op(c, L, R)` works as well as a concrete
        // `op(L, R)`).
        ExpressionPointer leftSubExpr, rightSubExpr;
        if (!matchBinaryRingOp(expression, opName, leftSubExpr,
                                  rightSubExpr)) {
            throwElaborate("ring: unexpected non-op head in reassociate");
        }
        // Check if rightSubExpr is itself `<op>(X, Y)`.
        ExpressionPointer X, Y;
        if (matchBinaryRingOp(rightSubExpr, opName, X, Y)) {
            // expression = L op (X op Y).
            // Step: L op (X op Y) = (L op X) op Y
            // by sym associative(L, X, Y).
            ExpressionPointer assocProof = buildRingAssoc(
                axioms, leftSubExpr, X, Y);
            ExpressionPointer LXTimesY = buildRingOp(
                axioms.op,
                buildRingOp(
                    axioms.op, leftSubExpr, X),
                Y);
            ExpressionPointer LTimesXY = buildRingOp(
                axioms.op, leftSubExpr,
                buildRingOp(axioms.op, X, Y));
            ExpressionPointer symAssoc = buildEqualitySymmetry(
                universeLevel, carrierType,
                LXTimesY, LTimesXY, assocProof);
            ExpressionPointer recProof =
                buildLeftAssocReassocProof(
                    axioms, universeLevel, carrierType,
                    LXTimesY);
            return buildEqualityTransitivity(
                universeLevel, carrierType,
                expression, LXTimesY, canonical,
                symAssoc, recProof);
        }
        // Right is atomic. Recurse on the left subexpression.
        ExpressionPointer leftCanonical;
        {
            std::vector<ExpressionPointer> leftFactors;
            if (!flattenRingProduct(leftSubExpr, opName,
                                      leftFactors)) {
                throwElaborate(
                    "ring: internal flatten failure (left)");
            }
            leftCanonical = assembleLeftAssociatedProduct(
                opName, leftFactors);
        }
        ExpressionPointer leftProof = buildLeftAssocReassocProof(
            axioms, universeLevel, carrierType, leftSubExpr);
        // Build lambda: λ z. z op rightSubExpr.
        ExpressionPointer rightLifted =
            liftBoundVariables(rightSubExpr, 1, 0);
        ExpressionPointer lambdaBody = buildRingOp(
            axioms.op, makeBoundVariable(0), rightLifted);
        ExpressionPointer lambda = makeLambda(
            "_ring_assoc_z", carrierType, lambdaBody);
        return buildEqualityCongruenceSameCarrier(
            universeLevel, carrierType, lambda,
            leftSubExpr, leftCanonical, leftProof);
    }

ExpressionPointer Elaborator::proveProductEqualsSorted(
        ExpressionPointer original,
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingAxiomNames& axioms,
        ExpressionPointer carrierType,
        LevelPointer carrierUniverseLevel,
        int line) {
        (void)line;
        const std::string& opName = axioms.op;
        ExpressionPointer canonical =
            assembleLeftAssociatedProduct(opName, sortedFactors);
        if (sortedFactors.size() <= 1) {
            if (structurallyEqual(original, canonical)) {
                return buildReflexivity(carrierUniverseLevel,
                                          carrierType, original);
            }
            throwElaborate(
                "ring: single-factor case but factors don't match");
        }
        ExpressionPointer reassocProof = buildLeftAssocReassocProof(
            axioms, carrierUniverseLevel, carrierType, original);
        ExpressionPointer leftAssocOriginal =
            assembleLeftAssociatedProduct(opName, originalFactors);
        std::vector<ExpressionPointer> current = originalFactors;
        ExpressionPointer sortProof = buildReflexivity(
            carrierUniverseLevel, carrierType, leftAssocOriginal);
        ExpressionPointer currentExpr = leftAssocOriginal;
        for (size_t i = 0; i < sortedFactors.size(); ++i) {
            size_t j = i;
            while (j < current.size()
                   && !structurallyEqual(current[j],
                                            sortedFactors[i])) {
                ++j;
            }
            if (j >= current.size()) {
                throwElaborate(
                    "ring: factor multiset matched but element not "
                    "found during sort — internal error");
            }
            while (j > i) {
                ExpressionPointer swapProof = buildAdjacentSwapProof(
                    axioms, carrierUniverseLevel, carrierType,
                    current, j);
                std::vector<ExpressionPointer> newCurrent = current;
                std::swap(newCurrent[j - 1], newCurrent[j]);
                ExpressionPointer newExpr =
                    assembleLeftAssociatedProduct(
                        opName, newCurrent);
                sortProof = buildEqualityTransitivity(
                    carrierUniverseLevel, carrierType,
                    leftAssocOriginal, currentExpr, newExpr,
                    sortProof, swapProof);
                current = std::move(newCurrent);
                currentExpr = std::move(newExpr);
                --j;
            }
        }
        if (!structurallyEqual(currentExpr, canonical)) {
            throwElaborate(
                "ring: insertion sort ended with mismatched form — "
                "internal error");
        }
        return buildEqualityTransitivity(
            carrierUniverseLevel, carrierType,
            original, leftAssocOriginal, canonical,
            reassocProof, sortProof);
    }

void Elaborator::ringPolynomialCompact(RingPolynomial& polynomial) {
        for (auto iter = polynomial.begin(); iter != polynomial.end(); ) {
            if (iter->second == 0) {
                iter = polynomial.erase(iter);
            } else {
                ++iter;
            }
        }
    }

void Elaborator::ringPolynomialAccumulate(
        RingPolynomial& polynomial,
        const RingPolynomial& other) {
        for (const auto& entry : other) {
            polynomial[entry.first] += entry.second;
        }
        ringPolynomialCompact(polynomial);
    }

void Elaborator::ringPolynomialSubtract(
        RingPolynomial& polynomial,
        const RingPolynomial& other) {
        for (const auto& entry : other) {
            polynomial[entry.first] -= entry.second;
        }
        ringPolynomialCompact(polynomial);
    }

void Elaborator::ringPolynomialNegate(RingPolynomial& polynomial) {
        for (auto& entry : polynomial) {
            entry.second = -entry.second;
        }
    }

Elaborator::RingPolynomial Elaborator::ringPolynomialMultiply(
        const RingPolynomial& left, const RingPolynomial& right) {
        RingPolynomial result;
        for (const auto& leftEntry : left) {
            for (const auto& rightEntry : right) {
                // Merged signature = sorted concat of the two factor
                // lists. Both inputs are sorted, so a merge keeps it
                // sorted in linear time.
                RingMonomialSignature mergedSignature;
                mergedSignature.reserve(
                    leftEntry.first.size() + rightEntry.first.size());
                std::merge(
                    leftEntry.first.begin(), leftEntry.first.end(),
                    rightEntry.first.begin(), rightEntry.first.end(),
                    std::back_inserter(mergedSignature));
                result[mergedSignature] += leftEntry.second
                                            * rightEntry.second;
            }
        }
        ringPolynomialCompact(result);
        return result;
    }

Elaborator::RingPolynomial Elaborator::ringPolynomialOne() {
        RingPolynomial polynomial;
        polynomial[RingMonomialSignature{}] = 1;
        return polynomial;
    }

Elaborator::RingPolynomial Elaborator::ringPolynomialAtom(
        RingNormalisationContext& context, ExpressionPointer atom) {
        uint64_t atomHash = atom->hash;
        auto insertion = context.atoms.emplace(atomHash, atom);
        (void)insertion;  // first writer wins; subsequent hits reuse
                            // the existing pointer (assumed
                            // structurally equal modulo hash collision)
        RingPolynomial polynomial;
        polynomial[RingMonomialSignature{atomHash}] = 1;
        return polynomial;
    }

void Elaborator::peelSpine(ExpressionPointer expression,
                   ExpressionPointer& headOut,
                   std::vector<ExpressionPointer>& argsOut) {
        std::vector<ExpressionPointer> reversed;
        ExpressionPointer cursor = expression;
        while (auto* app = std::get_if<Application>(&cursor->node)) {
            reversed.push_back(app->argument);
            cursor = app->function;
        }
        headOut = cursor;
        argsOut.assign(reversed.rbegin(), reversed.rend());
    }

bool Elaborator::structurePrefixMatches(
        const std::vector<ExpressionPointer>& args) {
        if (args.size() < ringStructurePrefix_.size()) return false;
        for (size_t i = 0; i < ringStructurePrefix_.size(); ++i) {
            if (!structurallyEqual(args[i], ringStructurePrefix_[i])) {
                return false;
            }
        }
        return true;
    }

bool Elaborator::matchBinaryRingOp(
        ExpressionPointer expression,
        const std::string& opName,
        ExpressionPointer& leftOut,
        ExpressionPointer& rightOut) {
        ExpressionPointer head;
        std::vector<ExpressionPointer> args;
        peelSpine(expression, head, args);
        auto* headConstant = std::get_if<Constant>(&head->node);
        if (!headConstant || headConstant->name != opName) return false;
        if (args.size() != ringStructurePrefix_.size() + 2) return false;
        if (!structurePrefixMatches(args)) return false;
        leftOut = args[ringStructurePrefix_.size()];
        rightOut = args[ringStructurePrefix_.size() + 1];
        return true;
    }

bool Elaborator::matchUnaryRingNegate(
        ExpressionPointer expression,
        const std::string& negateName,
        ExpressionPointer& innerOut) {
        ExpressionPointer head;
        std::vector<ExpressionPointer> args;
        peelSpine(expression, head, args);
        auto* headConstant = std::get_if<Constant>(&head->node);
        if (!headConstant || headConstant->name != negateName) return false;
        if (args.size() != ringStructurePrefix_.size() + 1) return false;
        if (!structurePrefixMatches(args)) return false;
        innerOut = args[ringStructurePrefix_.size()];
        return true;
    }

bool Elaborator::matchRingZero(ExpressionPointer expression,
                          const std::string& zeroName) {
        ExpressionPointer head;
        std::vector<ExpressionPointer> args;
        peelSpine(expression, head, args);
        auto* headConstant = std::get_if<Constant>(&head->node);
        if (!headConstant || headConstant->name != zeroName) return false;
        return args.size() == ringStructurePrefix_.size()
            && structurePrefixMatches(args);
    }

bool Elaborator::matchRingOne(ExpressionPointer expression,
                         const std::string& oneName) {
        ExpressionPointer head;
        std::vector<ExpressionPointer> args;
        peelSpine(expression, head, args);
        auto* headConstant = std::get_if<Constant>(&head->node);
        if (!headConstant || headConstant->name != oneName) return false;
        return args.size() == ringStructurePrefix_.size()
            && structurePrefixMatches(args);
    }

bool Elaborator::tryParseNaturalLiteral(
        ExpressionPointer expression, int& value) {
        int count = 0;
        ExpressionPointer cursor = expression;
        while (auto* app = std::get_if<Application>(&cursor->node)) {
            auto* head =
                std::get_if<Constant>(&app->function->node);
            if (!head || head->name != "successor") return false;
            ++count;
            cursor = app->argument;
        }
        auto* head = std::get_if<Constant>(&cursor->node);
        if (!head || head->name != "zero") return false;
        value = count;
        return true;
    }

bool Elaborator::tryParseCarrierEmbeddedNaturalLiteral(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        int& value) {
        if (context.embeddingChain.empty()) return false;
        ExpressionPointer cursor = expression;
        // Walk outermost-to-innermost. embeddingChain is INNERMOST
        // FIRST, so we iterate it in reverse.
        for (auto it = context.embeddingChain.rbegin();
             it != context.embeddingChain.rend(); ++it) {
            // At each level, BEFORE peeling, check if cursor is the
            // current outer carrier's zero or one constant.
            if (auto* nameHead = std::get_if<Constant>(&cursor->node)) {
                if (nameHead->name == it->outerZeroName) {
                    value = 0; return true;
                }
                if (nameHead->name == it->outerOneName) {
                    value = 1; return true;
                }
            }
            auto* app = std::get_if<Application>(&cursor->node);
            if (!app) return false;
            auto* head = std::get_if<Constant>(&app->function->node);
            if (!head || head->name != it->coercionFunctionName) {
                return false;
            }
            cursor = app->argument;
        }
        return tryParseNaturalLiteral(cursor, value);
    }

void Elaborator::populateRingEmbeddingChain(RingNormalisationContext& context) {
        auto buildStep =
            [&](const std::string& coercionName,
                const std::string& outerCarrier) -> RingEmbeddingStep {
            RingEmbeddingStep step;
            step.coercionFunctionName = coercionName;
            step.zeroPreservesName = coercionName + ".zero_preserves";
            step.onePreservesName = coercionName + ".one_preserves";
            step.addPreservesName = coercionName + ".add_preserves";
            step.outerCarrierName = outerCarrier;
            step.outerCarrierType = makeConstant(outerCarrier);
            step.outerCarrierUniverseLevel = makeLevelConst(0);
            step.outerAddName = outerCarrier + ".add";
            step.outerZeroName = outerCarrier + ".zero";
            step.outerOneName = outerCarrier + ".one";
            return step;
        };
        // INNERMOST FIRST.
        if (context.carrierName == "Integer") {
            context.embeddingChain.push_back(
                buildStep("Natural.to_integer", "Integer"));
        } else if (context.carrierName == "Rational") {
            context.embeddingChain.push_back(
                buildStep("Natural.to_integer", "Integer"));
            context.embeddingChain.push_back(
                buildStep("Integer.to_rational", "Rational"));
            context.fromIntegerMultiplyName =
                "Rational.from_integer_multiply";
            context.multiplyByIntegerName =
                "Rational.multiply_by_integer";
        } else if (context.carrierName == "Real") {
            context.embeddingChain.push_back(
                buildStep("Natural.to_integer", "Integer"));
            context.embeddingChain.push_back(
                buildStep("Integer.to_rational", "Rational"));
            context.embeddingChain.push_back(
                buildStep("Rational.to_real", "Real"));
            context.fromIntegerMultiplyName =
                "Real.from_integer_multiply";
            context.multiplyByIntegerName =
                "Real.multiply_by_integer";
        }
        // Carriers we don't know about (PAdic, Natural) get an empty
        // chain — literal-recognition simply doesn't fire.
    }

ExpressionPointer Elaborator::buildNaturalLiteralKernel(int value) {
        ExpressionPointer expr = makeConstant("zero");
        for (int i = 0; i < value; ++i) {
            expr = makeApplication(
                makeConstant("successor"), std::move(expr));
        }
        return expr;
    }

Elaborator::RingPolynomial Elaborator::normaliseToRingPolynomial(
        ExpressionPointer expression, RingNormalisationContext& context) {
        // zero — empty polynomial.
        if (matchRingZero(expression, context.zeroName)) {
            return RingPolynomial{};
        }
        // one — single empty-factor monomial.
        if (matchRingOne(expression, context.oneName)) {
            return ringPolynomialOne();
        }
        // add — recurse + accumulate.
        ExpressionPointer left;
        ExpressionPointer right;
        if (matchBinaryRingOp(expression, context.addName,
                                 left, right)) {
            RingPolynomial polynomial =
                normaliseToRingPolynomial(left, context);
            RingPolynomial rightPolynomial =
                normaliseToRingPolynomial(right, context);
            ringPolynomialAccumulate(polynomial, rightPolynomial);
            return polynomial;
        }
        // multiply — recurse + multiply.
        if (matchBinaryRingOp(expression, context.multiplyName,
                                 left, right)) {
            RingPolynomial leftPolynomial =
                normaliseToRingPolynomial(left, context);
            RingPolynomial rightPolynomial =
                normaliseToRingPolynomial(right, context);
            return ringPolynomialMultiply(
                leftPolynomial, rightPolynomial);
        }
        // subtract — recurse + subtract. The carrier's `subtract` is
        // defined as `x + -y`, so this is delta-equivalent to the
        // add/negate path; we handle it directly so the surface syntax
        // `a - b` works without the user having to expand it.
        if (matchBinaryRingOp(expression, context.subtractName,
                                 left, right)) {
            RingPolynomial leftPolynomial =
                normaliseToRingPolynomial(left, context);
            RingPolynomial rightPolynomial =
                normaliseToRingPolynomial(right, context);
            ringPolynomialSubtract(leftPolynomial, rightPolynomial);
            return leftPolynomial;
        }
        // negate — recurse + flip.
        ExpressionPointer inner;
        if (matchUnaryRingNegate(expression, context.negateName,
                                    inner)) {
            RingPolynomial polynomial =
                normaliseToRingPolynomial(inner, context);
            ringPolynomialNegate(polynomial);
            return polynomial;
        }
        // Carrier-embedded Natural literal: `Natural.to_integer(succ^k(zero))`
        // normalises to poly [{}: k] (k unit copies of the carrier's
        // one). proveMultiplyMerge's unit-strip pass takes care of
        // collapsing the `Integer.one * x` products that arise when
        // distributing `(2 : Integer) * x` into `x + x`.
        {
            int literalValue = 0;
            if (tryParseCarrierEmbeddedNaturalLiteral(
                    expression, context, literalValue)) {
                RingPolynomial polynomial;
                if (literalValue > 0) {
                    polynomial[RingMonomialSignature{}] = literalValue;
                }
                return polynomial;
            }
        }
        // Scalar-multiply operator: `R.from_integer_multiply(n, x)` or
        // `R.multiply_by_integer(x, n)`. Definitionally δ-reduces to
        // `(n : R) * x` or `x * (n : R)` respectively. Multiplication is
        // commutative for polynomials so we can normalize either order
        // identically.
        {
            ExpressionPointer scalarInteger;
            ExpressionPointer atomExpression;
            bool scalarOnLeft = false;
            if (tryParseScalarMultiplyOperator(
                    expression, context, scalarInteger, atomExpression,
                    scalarOnLeft)) {
                (void)scalarOnLeft;
                ExpressionPointer coercedScalar =
                    buildCoercedScalarForCarrier(scalarInteger, context);
                RingPolynomial scalarPoly =
                    normaliseToRingPolynomial(coercedScalar, context);
                RingPolynomial atomPoly =
                    normaliseToRingPolynomial(atomExpression, context);
                return ringPolynomialMultiply(scalarPoly, atomPoly);
            }
        }
        // Otherwise: an opaque atom.
        return ringPolynomialAtom(context, expression);
    }

bool Elaborator::tryParseScalarMultiplyOperator(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        ExpressionPointer& scalarOut,
        ExpressionPointer& atomOut,
        bool& scalarOnLeftOut) {
        if (context.fromIntegerMultiplyName.empty()) return false;
        auto* outerApp = std::get_if<Application>(&expression->node);
        if (!outerApp) return false;
        auto* innerApp =
            std::get_if<Application>(&outerApp->function->node);
        if (!innerApp) return false;
        auto* head = std::get_if<Constant>(&innerApp->function->node);
        if (!head) return false;
        if (head->name == context.fromIntegerMultiplyName) {
            scalarOut = innerApp->argument;
            atomOut = outerApp->argument;
            scalarOnLeftOut = true;
            return true;
        }
        if (head->name == context.multiplyByIntegerName) {
            atomOut = innerApp->argument;
            scalarOut = outerApp->argument;
            scalarOnLeftOut = false;
            return true;
        }
        return false;
    }

ExpressionPointer Elaborator::buildCoercedScalarForCarrier(
        ExpressionPointer scalarInteger,
        const RingNormalisationContext& context) {
        ExpressionPointer cursor = scalarInteger;
        // chain[0] is Natural→Integer; subsequent steps are Integer→
        // higher carriers. Wrap with chain[1..n].
        for (size_t i = 1; i < context.embeddingChain.size(); ++i) {
            cursor = makeApplication(
                makeConstant(
                    context.embeddingChain[i].coercionFunctionName),
                cursor);
        }
        return cursor;
    }

ExpressionPointer Elaborator::buildRingCoefficientExpression(
        int count, const RingNormalisationContext& context) {
        ExpressionPointer one = ringConst(context.oneName);
        if (count == 1) return one;
        ExpressionPointer accumulator = one;
        for (int i = 1; i < count; ++i) {
            ExpressionPointer onePlus = ringConst(context.oneName);
            accumulator = buildRingOp(context.addName,
                                        std::move(accumulator),
                                        std::move(onePlus));
        }
        return accumulator;
    }

ExpressionPointer Elaborator::buildCanonicalMonomial(
        const RingMonomialSignature& factors,
        int coefficient,
        const RingNormalisationContext& context) {
        const int magnitude = coefficient > 0 ? coefficient : -coefficient;
        ExpressionPointer factorProduct;
        if (!factors.empty()) {
            std::vector<ExpressionPointer> atomTerms;
            atomTerms.reserve(factors.size());
            for (uint64_t factorHash : factors) {
                auto found = context.atoms.find(factorHash);
                if (found == context.atoms.end()) {
                    throwElaborate(
                        "ring (normalisation): internal error — atom hash missing "
                        "from atom table");
                }
                atomTerms.push_back(found->second);
            }
            factorProduct = assembleLeftAssociatedProduct(
                context.multiplyName, atomTerms);
        }
        ExpressionPointer monomial;
        if (magnitude == 1) {
            // No explicit coefficient. If no factors, the monomial is
            // just `one`.
            monomial = factorProduct ? factorProduct
                                      : ringConst(context.oneName);
        } else {
            ExpressionPointer coefficientExpr =
                buildRingCoefficientExpression(magnitude, context);
            monomial = factorProduct
                ? buildRingOp(context.multiplyName,
                                std::move(coefficientExpr),
                                std::move(factorProduct))
                : std::move(coefficientExpr);
        }
        if (coefficient < 0) {
            ExpressionPointer negate = ringConst(context.negateName);
            monomial = makeApplication(std::move(negate),
                                          std::move(monomial));
        }
        return monomial;
    }

ExpressionPointer Elaborator::buildCanonicalPolynomial(
        const RingPolynomial& polynomial,
        const RingNormalisationContext& context) {
        if (polynomial.empty()) {
            return ringConst(context.zeroName);
        }
        std::vector<ExpressionPointer> monomials;
        for (const auto& entry : polynomial) {
            int coef = entry.second;
            int sign = coef > 0 ? +1 : -1;
            int magnitude = coef > 0 ? coef : -coef;
            for (int i = 0; i < magnitude; ++i) {
                monomials.push_back(buildCanonicalMonomial(
                    entry.first, sign, context));
            }
        }
        ExpressionPointer accumulator = monomials[0];
        for (size_t i = 1; i < monomials.size(); ++i) {
            accumulator = buildRingOp(context.addName,
                                        std::move(accumulator),
                                        monomials[i]);
        }
        return accumulator;
    }

bool Elaborator::ringPolynomialsAgree(
        const RingPolynomial& left, const RingPolynomial& right) {
        if (left.size() != right.size()) return false;
        auto leftIter = left.begin();
        auto rightIter = right.begin();
        while (leftIter != left.end()) {
            if (leftIter->first != rightIter->first) return false;
            if (leftIter->second != rightIter->second) return false;
            ++leftIter;
            ++rightIter;
        }
        return true;
    }

std::string Elaborator::pickAxiomName(const std::string& candidateOne,
                                 const std::string& candidateTwo) {
        if (environment_.lookup(candidateOne) != nullptr) {
            return candidateOne;
        }
        if (environment_.lookup(candidateTwo) != nullptr) {
            return candidateTwo;
        }
        return std::string{};
    }

Elaborator::RingLawNames Elaborator::resolveRingLawNames(
        const std::string& opNamespace) {
        RingLawNames names;
        names.zeroAddLeft = pickAxiomName(
            opNamespace + ".zero_add",
            opNamespace + ".add_identity_left");
        names.addZeroRight = pickAxiomName(
            opNamespace + ".add_zero",
            opNamespace + ".add_identity_right");
        names.oneMultiplyLeft = pickAxiomName(
            opNamespace + ".one_multiply",
            opNamespace + ".multiply_identity_left");
        names.multiplyOneRight = pickAxiomName(
            opNamespace + ".multiply_one",
            opNamespace + ".multiply_identity_right");
        names.multiplyZeroLeft = pickAxiomName(
            opNamespace + ".multiply_zero_left",
            opNamespace + ".zero_multiply");
        names.multiplyZeroRight = pickAxiomName(
            opNamespace + ".multiply_zero_right",
            opNamespace + ".multiply_zero");
        names.addNegateRight = pickAxiomName(
            opNamespace + ".add_negate_right",
            opNamespace + ".add_negate_right");
        names.addNegateLeft = pickAxiomName(
            opNamespace + ".add_negate_left",
            opNamespace + ".add_negate_left");
        names.negateNegate = pickAxiomName(
            opNamespace + ".negate_negate",
            opNamespace + ".negate_negate");
        names.negateAdd = pickAxiomName(
            opNamespace + ".negate_add",
            opNamespace + ".negate_add");
        names.multiplyNegateLeft = pickAxiomName(
            opNamespace + ".multiply_negate_left",
            opNamespace + ".multiply_negate_left");
        names.multiplyNegateRight = pickAxiomName(
            opNamespace + ".multiply_negate_right",
            opNamespace + ".multiply_negate_right");
        names.distributivityLeft = opNamespace + ".distributivity_left";
        names.distributivityRight = opNamespace + ".distributivity_right";
        names.addAssociative = opNamespace + ".add_associative";
        names.addCommutative = opNamespace + ".add_commutative";
        names.multiplyAssociative = opNamespace + ".multiply_associative";
        names.multiplyCommutative = opNamespace + ".multiply_commutative";
        return names;
    }

void Elaborator::demandAxiomName(const std::string& axiomName,
                            const std::string& description,
                            const std::string& carrierName) {
        if (axiomName.empty()
            || environment_.lookup(axiomName) == nullptr) {
            throwElaborate(
                "`ring`: carrier `" + carrierName
                + "` is missing axiom `" + description
                + "` — required for this goal");
        }
    }

ExpressionPointer Elaborator::buildRingNegate(
        const std::string& negateName, ExpressionPointer inner) {
        return makeApplication(ringConst(negateName), std::move(inner));
    }

ExpressionPointer Elaborator::buildSignedMonomialKernel(
        const RingMonomialSignature& signature,
        int sign,
        const RingNormalisationContext& context) {
        return buildCanonicalMonomial(signature, sign, context);
    }

std::vector<Elaborator::SignedMonomial> Elaborator::polynomialToSignedMonomials(
        const RingPolynomial& polynomial) {
        std::vector<SignedMonomial> output;
        for (const auto& entry : polynomial) {
            int coef = entry.second;
            int sign = coef > 0 ? +1 : -1;
            int magnitude = coef > 0 ? coef : -coef;
            for (int i = 0; i < magnitude; ++i) {
                output.push_back({entry.first, sign});
            }
        }
        return output;
    }

ExpressionPointer Elaborator::assembleLeftAssociatedSum(
        const std::string& addName,
        const std::vector<ExpressionPointer>& summands) {
        ExpressionPointer accumulator = summands[0];
        for (size_t i = 1; i < summands.size(); ++i) {
            accumulator = buildRingOp(
                addName, std::move(accumulator), summands[i]);
        }
        return accumulator;
    }

ExpressionPointer Elaborator::reassociateSumLeftProof(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        RingAxiomNames addAxioms{
            context.addName,
            axiomNames.addAssociative,
            axiomNames.addCommutative};
        return buildLeftAssocReassocProof(
            addAxioms, context.carrierUniverseLevel,
            context.carrierType, expression);
    }

ExpressionPointer Elaborator::sortSumLeftAssocProof(
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        RingAxiomNames addAxioms{
            context.addName,
            axiomNames.addAssociative,
            axiomNames.addCommutative};
        ExpressionPointer original = assembleLeftAssociatedProduct(
            context.addName, originalFactors);
        return proveProductEqualsSorted(
            original, originalFactors, sortedFactors,
            addAxioms, context.carrierType,
            context.carrierUniverseLevel, /*line*/0);
    }

ExpressionPointer Elaborator::sortMultiplyLeftAssocProof(
        const std::vector<ExpressionPointer>& originalFactors,
        const std::vector<ExpressionPointer>& sortedFactors,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        RingAxiomNames multiplyAxioms{
            context.multiplyName,
            axiomNames.multiplyAssociative,
            axiomNames.multiplyCommutative};
        ExpressionPointer original = assembleLeftAssociatedProduct(
            context.multiplyName, originalFactors);
        return proveProductEqualsSorted(
            original, originalFactors, sortedFactors,
            multiplyAxioms, context.carrierType,
            context.carrierUniverseLevel, /*line*/0);
    }

ExpressionPointer Elaborator::reassociateMultiplyLeftProof(
        ExpressionPointer expression,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        RingAxiomNames multiplyAxioms{
            context.multiplyName,
            axiomNames.multiplyAssociative,
            axiomNames.multiplyCommutative};
        return buildLeftAssocReassocProof(
            multiplyAxioms, context.carrierUniverseLevel,
            context.carrierType, expression);
    }

ExpressionPointer Elaborator::proveEqualsCanonical_impl(
        ExpressionPointer expression,
        RingNormalisationContext& context,
        const RingLawNames& axiomNames,
        RingPolynomial& polynomialOut) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // Match zero.
        if (matchRingZero(expression, context.zeroName)) {
            polynomialOut = RingPolynomial{};
            return buildReflexivity(universeLevel, carrierType, expression);
        }
        // Match one.
        if (matchRingOne(expression, context.oneName)) {
            polynomialOut = ringPolynomialOne();
            return buildReflexivity(universeLevel, carrierType, expression);
        }
        // Match negate(inner).
        {
            ExpressionPointer inner;
            if (matchUnaryRingNegate(expression, context.negateName, inner)) {
                RingPolynomial innerPoly;
                ExpressionPointer innerProof = proveEqualsCanonical(
                    inner, context, axiomNames, innerPoly);
                // Build proof: negate(inner) = negate(canonical(innerPoly))
                // via congruence with λz. negate(z).
                ExpressionPointer innerCanonical =
                    buildCanonicalPolynomial(innerPoly, context);
                // λ z : T. negate(z). z has de-Bruijn index 0.
                ExpressionPointer lambdaBody = buildRingNegate(
                    context.negateName, makeBoundVariable(0));
                ExpressionPointer lambda = makeLambda(
                    "_ring_negate_z", carrierType, lambdaBody);
                ExpressionPointer congrProof =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        inner, innerCanonical, innerProof);
                // Now: negate(inner) = negate(canonical(innerPoly)).
                // Compose with negate-merge:
                //   negate(canonical(innerPoly)) = canonical(-innerPoly).
                RingPolynomial negatedPoly = innerPoly;
                ringPolynomialNegate(negatedPoly);
                polynomialOut = negatedPoly;
                ExpressionPointer mergeProof = proveNegateMerge(
                    innerPoly, context, axiomNames);
                ExpressionPointer canonicalNegated =
                    buildCanonicalPolynomial(negatedPoly, context);
                ExpressionPointer fullProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingNegate(context.negateName, innerCanonical),
                    canonicalNegated,
                    congrProof, mergeProof);
                return fullProof;
            }
        }
        // Match subtract(left, right) — bridge to add(left, negate(right))
        // via reflexivity (the carrier's `subtract` is defined as
        // `x + -y`, so the kernel collapses them under δ).
        {
            ExpressionPointer left, right;
            if (matchBinaryRingOp(expression, context.subtractName,
                                     left, right)) {
                ExpressionPointer equivalent = buildRingOp(
                    context.addName,
                    left,
                    buildRingNegate(context.negateName, right));
                ExpressionPointer equivalentProof =
                    proveEqualsCanonical(
                        equivalent, context, axiomNames,
                        polynomialOut);
                ExpressionPointer canonical =
                    buildCanonicalPolynomial(polynomialOut, context);
                ExpressionPointer bridge =
                    buildReflexivity(universeLevel, carrierType,
                                       expression);
                return buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression, equivalent, canonical,
                    bridge, equivalentProof);
            }
        }
        // Match add(left, right).
        {
            ExpressionPointer left, right;
            if (matchBinaryRingOp(expression, context.addName,
                                     left, right)) {
                RingPolynomial leftPoly, rightPoly;
                ExpressionPointer leftProof = proveEqualsCanonical(
                    left, context, axiomNames, leftPoly);
                ExpressionPointer rightProof = proveEqualsCanonical(
                    right, context, axiomNames, rightPoly);
                ExpressionPointer leftCanonical =
                    buildCanonicalPolynomial(leftPoly, context);
                ExpressionPointer rightCanonical =
                    buildCanonicalPolynomial(rightPoly, context);
                // Step 1: add(left, right) = add(leftCanonical, right)
                // via congruence λz. z + right.
                ExpressionPointer rightLifted =
                    liftBoundVariables(right, 1, 0);
                ExpressionPointer lambdaLeftBody = buildRingOp(
                    context.addName, makeBoundVariable(0), rightLifted);
                ExpressionPointer lambdaLeft = makeLambda(
                    "_ring_add_z", carrierType, lambdaLeftBody);
                ExpressionPointer step1 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaLeft,
                        left, leftCanonical, leftProof);
                // Step 2: add(leftCanonical, right)
                //          = add(leftCanonical, rightCanonical)
                // via congruence λz. leftCanonical + z.
                ExpressionPointer leftCanLifted =
                    liftBoundVariables(leftCanonical, 1, 0);
                ExpressionPointer lambdaRightBody = buildRingOp(
                    context.addName, leftCanLifted, makeBoundVariable(0));
                ExpressionPointer lambdaRight = makeLambda(
                    "_ring_add_z", carrierType, lambdaRightBody);
                ExpressionPointer step2 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaRight,
                        right, rightCanonical, rightProof);
                ExpressionPointer step12 = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.addName, leftCanonical, right),
                    buildRingOp(context.addName, leftCanonical,
                                  rightCanonical),
                    step1, step2);
                // Step 3 (merge): add(leftCanonical, rightCanonical)
                //                  = canonical(leftPoly + rightPoly)
                RingPolynomial mergedPoly = leftPoly;
                ringPolynomialAccumulate(mergedPoly, rightPoly);
                polynomialOut = mergedPoly;
                ExpressionPointer mergeProof = proveAddMerge(
                    leftPoly, rightPoly, context, axiomNames);
                ExpressionPointer mergedCanonical =
                    buildCanonicalPolynomial(mergedPoly, context);
                return buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.addName, leftCanonical,
                                  rightCanonical),
                    mergedCanonical,
                    step12, mergeProof);
            }
        }
        // Match multiply(left, right).
        {
            ExpressionPointer left, right;
            if (matchBinaryRingOp(expression, context.multiplyName,
                                     left, right)) {
                RingPolynomial leftPoly, rightPoly;
                ExpressionPointer leftProof = proveEqualsCanonical(
                    left, context, axiomNames, leftPoly);
                ExpressionPointer rightProof = proveEqualsCanonical(
                    right, context, axiomNames, rightPoly);
                ExpressionPointer leftCanonical =
                    buildCanonicalPolynomial(leftPoly, context);
                ExpressionPointer rightCanonical =
                    buildCanonicalPolynomial(rightPoly, context);
                ExpressionPointer rightLifted =
                    liftBoundVariables(right, 1, 0);
                ExpressionPointer lambdaLeftBody = buildRingOp(
                    context.multiplyName, makeBoundVariable(0),
                    rightLifted);
                ExpressionPointer lambdaLeft = makeLambda(
                    "_ring_mul_z", carrierType, lambdaLeftBody);
                ExpressionPointer step1 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaLeft,
                        left, leftCanonical, leftProof);
                ExpressionPointer leftCanLifted =
                    liftBoundVariables(leftCanonical, 1, 0);
                ExpressionPointer lambdaRightBody = buildRingOp(
                    context.multiplyName, leftCanLifted,
                    makeBoundVariable(0));
                ExpressionPointer lambdaRight = makeLambda(
                    "_ring_mul_z", carrierType, lambdaRightBody);
                ExpressionPointer step2 =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambdaRight,
                        right, rightCanonical, rightProof);
                ExpressionPointer step12 = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.multiplyName, leftCanonical, right),
                    buildRingOp(context.multiplyName, leftCanonical,
                                  rightCanonical),
                    step1, step2);
                RingPolynomial mergedPoly =
                    ringPolynomialMultiply(leftPoly, rightPoly);
                polynomialOut = mergedPoly;
                ExpressionPointer mergeProof = proveMultiplyMerge(
                    leftPoly, rightPoly, context, axiomNames);
                ExpressionPointer mergedCanonical =
                    buildCanonicalPolynomial(mergedPoly, context);
                return buildEqualityTransitivity(
                    universeLevel, carrierType,
                    expression,
                    buildRingOp(context.multiplyName, leftCanonical,
                                  rightCanonical),
                    mergedCanonical,
                    step12, mergeProof);
            }
        }
        // Carrier-embedded Natural literal: build the polynomial as
        // [{}: k] and the proof inductively.
        {
            int literalValue = 0;
            if (tryParseCarrierEmbeddedNaturalLiteral(
                    expression, context, literalValue)) {
                RingPolynomial polynomial;
                if (literalValue > 0) {
                    polynomial[RingMonomialSignature{}] = literalValue;
                }
                polynomialOut = polynomial;
                return proveIntegerLiteralEqualsCanonical(
                    literalValue, context);
            }
        }
        // Scalar-multiply operator: `R.from_integer_multiply(n, x)` δ-
        // reduces to `(n : R) * x`; `R.multiply_by_integer(x, n)` to
        // `x * (n : R)`. Bridge via reflexivity to the unfolded form so
        // the returned proof's STORED type names the original operator
        // (callers' downstream unification doesn't have to chase the
        // δ-reduction).
        {
            ExpressionPointer scalarInteger;
            ExpressionPointer atomExpression;
            bool scalarOnLeft = false;
            if (tryParseScalarMultiplyOperator(
                    expression, context, scalarInteger, atomExpression,
                    scalarOnLeft)) {
                ExpressionPointer coercedScalar =
                    buildCoercedScalarForCarrier(scalarInteger, context);
                ExpressionPointer unfolded = scalarOnLeft
                    ? buildRingOp(context.multiplyName, coercedScalar,
                                    atomExpression)
                    : buildRingOp(context.multiplyName, atomExpression,
                                    coercedScalar);
                ExpressionPointer unfoldProof = proveEqualsCanonical(
                    unfolded, context, axiomNames, polynomialOut);
                ExpressionPointer canonicalKernel =
                    buildCanonicalPolynomial(polynomialOut, context);
                // expression ≡ unfolded definitionally; reflexivity at
                // `expression` has stored type `expression = expression`,
                // which the kernel accepts as `expression = unfolded` at
                // any application boundary that has to unify the type.
                ExpressionPointer reflBridge = buildReflexivity(
                    context.carrierUniverseLevel,
                    context.carrierType, expression);
                return buildEqualityTransitivity(
                    context.carrierUniverseLevel, context.carrierType,
                    expression, unfolded, canonicalKernel,
                    reflBridge, unfoldProof);
            }
        }
        // Otherwise: an opaque atom. Its canonical kernel is itself.
        polynomialOut = ringPolynomialAtom(context, expression);
        ExpressionPointer canonicalKernel =
            buildCanonicalPolynomial(polynomialOut, context);
        if (!structurallyEqual(expression, canonicalKernel)) {
            throwElaborate(
                "`ring`: atom's canonical kernel mismatched the "
                "atom itself (internal error)");
        }
        return buildReflexivity(universeLevel, carrierType, expression);
    }

ExpressionPointer Elaborator::buildSumOfOnesKernel(
        int k,
        const std::string& addName,
        const std::string& zeroName,
        const std::string& oneName) {
        if (k == 0) return makeConstant(zeroName);
        ExpressionPointer accumulator = makeConstant(oneName);
        for (int j = 1; j < k; ++j) {
            accumulator = buildRingOp(
                addName, std::move(accumulator),
                makeConstant(oneName));
        }
        return accumulator;
    }

ExpressionPointer Elaborator::proveNaturalLiteralPushThroughStep(
        int literalValue,
        const RingEmbeddingStep& step) {
        LevelPointer universeLevel = step.outerCarrierUniverseLevel;
        ExpressionPointer carrierType = step.outerCarrierType;
        ExpressionPointer oneConst = makeConstant(step.outerOneName);
        if (literalValue == 0) {
            return makeConstant(step.zeroPreservesName);
        }
        if (literalValue == 1) {
            return makeConstant(step.onePreservesName);
        }
        ExpressionPointer cJ = oneConst;
        ExpressionPointer currentProof = makeConstant(
            step.onePreservesName);
        for (int j = 1; j < literalValue; ++j) {
            ExpressionPointer naturalJ = buildNaturalLiteralKernel(j);
            ExpressionPointer naturalOne = buildNaturalLiteralKernel(1);
            ExpressionPointer toOuterJ = makeApplication(
                makeConstant(step.coercionFunctionName), naturalJ);
            ExpressionPointer toOuterOne = makeApplication(
                makeConstant(step.coercionFunctionName), naturalOne);
            ExpressionPointer addPreserves = makeApplication(
                makeApplication(
                    makeConstant(step.addPreservesName), naturalJ),
                naturalOne);
            ExpressionPointer formA = makeApplication(
                makeConstant(step.coercionFunctionName),
                buildNaturalLiteralKernel(j + 1));
            ExpressionPointer formB = buildRingOp(
                step.outerAddName, toOuterJ, toOuterOne);
            ExpressionPointer toOuterJLifted =
                liftBoundVariables(toOuterJ, 1, 0);
            ExpressionPointer lambdaRight = makeLambda(
                "_lit_z", carrierType,
                buildRingOp(step.outerAddName, toOuterJLifted,
                              makeBoundVariable(0)));
            ExpressionPointer onePreserves = makeConstant(
                step.onePreservesName);
            ExpressionPointer congrRight =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaRight,
                    toOuterOne, oneConst, onePreserves);
            ExpressionPointer formC = buildRingOp(
                step.outerAddName, toOuterJ, oneConst);
            ExpressionPointer oneLifted =
                liftBoundVariables(oneConst, 1, 0);
            ExpressionPointer lambdaLeft = makeLambda(
                "_lit_z", carrierType,
                buildRingOp(step.outerAddName,
                              makeBoundVariable(0), oneLifted));
            ExpressionPointer congrLeft =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaLeft,
                    toOuterJ, cJ, currentProof);
            ExpressionPointer formD = buildRingOp(
                step.outerAddName, cJ, oneConst);
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                formA, formB, formC,
                addPreserves, congrRight);
            currentProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                formA, formC, formD,
                stepAB, congrLeft);
            cJ = formD;
        }
        return currentProof;
    }

ExpressionPointer Elaborator::proveCoercionThroughSumOfOnes(
        int literalValue,
        const RingEmbeddingStep& step,
        const std::string& innerAddName,
        const std::string& innerZeroName,
        const std::string& innerOneName) {
        LevelPointer universeLevel = step.outerCarrierUniverseLevel;
        ExpressionPointer carrierType = step.outerCarrierType;
        ExpressionPointer outerOne = makeConstant(step.outerOneName);
        (void)innerZeroName;  // only used implicitly in zero_preserves
        if (literalValue == 0) {
            return makeConstant(step.zeroPreservesName);
        }
        if (literalValue == 1) {
            return makeConstant(step.onePreservesName);
        }
        ExpressionPointer innerOne = makeConstant(innerOneName);
        ExpressionPointer innerCJ = innerOne;     // k=1 canonical at inner.
        ExpressionPointer outerCJ = outerOne;     // k=1 canonical at outer.
        ExpressionPointer currentProof = makeConstant(
            step.onePreservesName);
        for (int j = 1; j < literalValue; ++j) {
            // formA = step.coercion(innerCJ + innerOne)
            ExpressionPointer innerSum = buildRingOp(
                innerAddName, innerCJ, innerOne);
            ExpressionPointer formA = makeApplication(
                makeConstant(step.coercionFunctionName), innerSum);
            ExpressionPointer coercInnerCJ = makeApplication(
                makeConstant(step.coercionFunctionName), innerCJ);
            ExpressionPointer coercInnerOne = makeApplication(
                makeConstant(step.coercionFunctionName), innerOne);
            ExpressionPointer formB = buildRingOp(
                step.outerAddName, coercInnerCJ, coercInnerOne);
            ExpressionPointer addPreserves = makeApplication(
                makeApplication(
                    makeConstant(step.addPreservesName), innerCJ),
                innerOne);
            // Rewrite right summand via one_preserves under λz. coercInnerCJ + z.
            ExpressionPointer coercInnerCJLifted =
                liftBoundVariables(coercInnerCJ, 1, 0);
            ExpressionPointer lambdaRight = makeLambda(
                "_chain_z", carrierType,
                buildRingOp(step.outerAddName, coercInnerCJLifted,
                              makeBoundVariable(0)));
            ExpressionPointer onePreserves = makeConstant(
                step.onePreservesName);
            ExpressionPointer congrRight =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaRight,
                    coercInnerOne, outerOne, onePreserves);
            ExpressionPointer formC = buildRingOp(
                step.outerAddName, coercInnerCJ, outerOne);
            // Rewrite left summand via currentProof under λz. z + outerOne.
            ExpressionPointer outerOneLifted =
                liftBoundVariables(outerOne, 1, 0);
            ExpressionPointer lambdaLeft = makeLambda(
                "_chain_z", carrierType,
                buildRingOp(step.outerAddName,
                              makeBoundVariable(0), outerOneLifted));
            ExpressionPointer congrLeft =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaLeft,
                    coercInnerCJ, outerCJ, currentProof);
            ExpressionPointer formD = buildRingOp(
                step.outerAddName, outerCJ, outerOne);
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                formA, formB, formC,
                addPreserves, congrRight);
            currentProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                formA, formC, formD,
                stepAB, congrLeft);
            innerCJ = innerSum;
            outerCJ = formD;
        }
        return currentProof;
    }

ExpressionPointer Elaborator::proveIntegerLiteralEqualsCanonical(
        int literalValue, const RingNormalisationContext& context) {
        const auto& chain = context.embeddingChain;
        if (chain.empty()) {
            throwElaborate(
                "`ring`: internal error — proveIntegerLiteralEqualsCanonical "
                "called with empty embedding chain");
        }
        // Step 0: Natural→Integer (or whatever the innermost step is).
        ExpressionPointer currentProof =
            proveNaturalLiteralPushThroughStep(literalValue, chain[0]);
        // currentExpression: chain[0].coercion(succ^k(zero))
        // currentCanonical: k copies of chain[0].outerOne added.
        ExpressionPointer currentExpression = makeApplication(
            makeConstant(chain[0].coercionFunctionName),
            buildNaturalLiteralKernel(literalValue));
        ExpressionPointer currentCanonical = buildSumOfOnesKernel(
            literalValue,
            chain[0].outerAddName,
            chain[0].outerZeroName,
            chain[0].outerOneName);
        // Iterate remaining steps: lift through each coercion.
        for (size_t i = 1; i < chain.size(); ++i) {
            const RingEmbeddingStep& step = chain[i];
            const RingEmbeddingStep& innerStep = chain[i - 1];
            // Step A: congruence under λz. step.coercion(z) lifts
            //   currentProof : currentExpression = currentCanonical
            // to
            //   step.coercion(currentExpression) = step.coercion(currentCanonical)
            ExpressionPointer innerCarrierType = innerStep.outerCarrierType;
            LevelPointer innerCarrierLevel =
                innerStep.outerCarrierUniverseLevel;
            ExpressionPointer coercionLambdaBody = makeApplication(
                makeConstant(step.coercionFunctionName),
                makeBoundVariable(0));
            ExpressionPointer coercionLambda = makeLambda(
                "_chain_outer_z", innerCarrierType, coercionLambdaBody);
            ExpressionPointer congruenceProof =
                buildEqualityCongruence(
                    innerCarrierLevel,
                    innerCarrierType,
                    step.outerCarrierUniverseLevel,
                    step.outerCarrierType,
                    coercionLambda,
                    currentExpression, currentCanonical,
                    currentProof);
            // Step B: push the coercion through the inner sum of ones.
            ExpressionPointer pushProof = proveCoercionThroughSumOfOnes(
                literalValue, step,
                innerStep.outerAddName,
                innerStep.outerZeroName,
                innerStep.outerOneName);
            // Combine via transitivity.
            ExpressionPointer newExpression = makeApplication(
                makeConstant(step.coercionFunctionName),
                currentExpression);
            ExpressionPointer newCanonical = buildSumOfOnesKernel(
                literalValue,
                step.outerAddName,
                step.outerZeroName,
                step.outerOneName);
            ExpressionPointer coercedInnerCanonical = makeApplication(
                makeConstant(step.coercionFunctionName),
                currentCanonical);
            currentProof = buildEqualityTransitivity(
                step.outerCarrierUniverseLevel,
                step.outerCarrierType,
                newExpression, coercedInnerCanonical, newCanonical,
                congruenceProof, pushProof);
            currentExpression = newExpression;
            currentCanonical = newCanonical;
        }
        return currentProof;
    }

ExpressionPointer Elaborator::proveEqualsCanonical(
        ExpressionPointer expression,
        RingNormalisationContext& context,
        const RingLawNames& axiomNames,
        RingPolynomial& polynomialOut) {
        return proveEqualsCanonical_impl(
            expression, context, axiomNames, polynomialOut);
    }

ExpressionPointer Elaborator::proveAddMerge(
        const RingPolynomial& leftPoly,
        const RingPolynomial& rightPoly,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        ExpressionPointer leftCanonical =
            buildCanonicalPolynomial(leftPoly, context);
        ExpressionPointer rightCanonical =
            buildCanonicalPolynomial(rightPoly, context);
        ExpressionPointer leftPlusRight = buildRingOp(
            context.addName, leftCanonical, rightCanonical);
        RingPolynomial mergedPoly = leftPoly;
        ringPolynomialAccumulate(mergedPoly, rightPoly);
        ExpressionPointer mergedCanonical =
            buildCanonicalPolynomial(mergedPoly, context);
        if (leftPoly.empty() && rightPoly.empty()) {
            // zero + zero = zero. Use zero_add(zero) :  0 + 0 = 0.
            demandAxiomName(axiomNames.zeroAddLeft, "zero_add/add_identity_left",
                              context.carrierName);
            ExpressionPointer zeroConst = ringConst(context.zeroName);
            ExpressionPointer call =
                makeApplication(ringConst(axiomNames.zeroAddLeft),
                                  zeroConst);
            return call;
        }
        if (leftPoly.empty()) {
            // zero + canonical(rightPoly) = canonical(rightPoly).
            demandAxiomName(axiomNames.zeroAddLeft, "zero_add/add_identity_left",
                              context.carrierName);
            ExpressionPointer call =
                makeApplication(ringConst(axiomNames.zeroAddLeft),
                                  rightCanonical);
            return call;
        }
        if (rightPoly.empty()) {
            // canonical(leftPoly) + zero = canonical(leftPoly).
            demandAxiomName(axiomNames.addZeroRight, "add_zero/add_identity_right",
                              context.carrierName);
            ExpressionPointer call =
                makeApplication(ringConst(axiomNames.addZeroRight),
                                  leftCanonical);
            return call;
        }
        // Both non-empty.  Build the flat summand list from leftPoly
        // and rightPoly's canonical forms.  Each entry is a fully-
        // rendered signed monomial kernel.  We use
        // polynomialToSignedMonomials on BOTH sides so coefficient-k
        // entries explode into k unit monomials; the right side used
        // to push raw (sig, coef) pairs, which broke the bySig
        // bookkeeping below for k > 1.
        std::vector<SignedMonomial> combinedMonomials =
            polynomialToSignedMonomials(leftPoly);
        {
            std::vector<SignedMonomial> rightSigned =
                polynomialToSignedMonomials(rightPoly);
            combinedMonomials.insert(combinedMonomials.end(),
                                       rightSigned.begin(),
                                       rightSigned.end());
        }
        std::vector<ExpressionPointer> combinedKernels;
        combinedKernels.reserve(combinedMonomials.size());
        for (const auto& m : combinedMonomials) {
            combinedKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Step 1: re-associate `leftCanonical + rightCanonical` into a
        // flat left-associated chain over `combinedKernels`. Treat each
        // monomial kernel as opaque. We do this by reassociateSumLeftProof.
        ExpressionPointer leftAssocCombined = assembleLeftAssociatedSum(
            context.addName, combinedKernels);
        ExpressionPointer reassocProof = reassociateSumLeftProof(
            leftPlusRight, context, axiomNames);
        // Step 2: insertion-sort by structural order so that all merged-
        // poly monomials' kernel forms appear in std::map signature
        // order, with cancelling (M, -M) pairs becoming adjacent.
        //
        // We want the sorted order to MATCH the canonical-of-merged
        // form's iteration order (std::map signature ascending). We do
        // this by computing the target sorted vector as the canonical
        // sequence of monomial kernels INTERSPERSED with the cancelling
        // pairs that should disappear.
        //
        // Concretely: walk combinedMonomials sorted by signature. Group
        // entries with the same signature; if the group has two entries
        // with opposite signs, they cancel — place them adjacent in the
        // target list. Otherwise (single entry, or two entries with the
        // same sign which would mean coefficient ±2, ruled out by the
        // coefficient guard), the entry survives in the canonical form
        // and is placed at its canonical position.
        //
        // Build:
        //   * sortedKernels: a vector of ExpressionPointers in the order
        //     we want after sorting. Surviving monomials first/in-order,
        //     cancelled-pairs grouped at the end. Actually simpler:
        //     emit pairs first (so we can cancel from the right), then
        //     survivors. But that re-orders the survivors w.r.t.
        //     canonical. Alternative: emit survivors and pairs in
        //     positional order, and during cancellation we walk back
        //     through.
        //
        // Easier approach: place ALL surviving monomials at the head of
        // the sorted vector (in canonical sig order), then all cancel-
        // pairs at the tail (each pair as (M, -M) adjacent). After
        // sort, cancel each pair right-to-left, applying add_negate_*
        // and dropping the resulting zero.
        std::vector<SignedMonomial> sortedSignedMonomials;
        // Group by signature.
        std::map<RingMonomialSignature, std::vector<int>> bySig;
        for (const auto& m : combinedMonomials) {
            bySig[m.signature].push_back(m.sign);
        }
        // Survivors first, in canonical signature order. Cancel pairs
        // collected to the side.
        //
        // Each group's `signs` vector consists of ±1 entries (one per
        // unit monomial). Count positives vs negatives: min(p, n)
        // pairs cancel, leaving |p - n| copies of sign(p - n) as
        // survivors. The merged polynomial's coefficient for this
        // signature is exactly (p - n), so the survivor count agrees
        // with mergedPoly[sig].
        std::vector<std::pair<RingMonomialSignature, int>> cancelPairs;
        for (const auto& [sig, signs] : bySig) {
            int positives = 0;
            int negatives = 0;
            for (int s : signs) {
                if (s > 0) ++positives;
                else if (s < 0) ++negatives;
            }
            int net = positives - negatives;
            int cancellations = std::min(positives, negatives);
            int survivorSign = (net > 0) ? +1 : -1;
            int survivorCount = (net > 0) ? net : -net;
            for (int i = 0; i < survivorCount; ++i) {
                sortedSignedMonomials.push_back({sig, survivorSign});
            }
            for (int i = 0; i < cancellations; ++i) {
                cancelPairs.push_back({sig, +1});
            }
        }
        // Verify: surviving monomials, in std::map signature order,
        // EXACTLY match canonicalMergedPoly's order.
        std::vector<SignedMonomial> mergedMonomials =
            polynomialToSignedMonomials(mergedPoly);
        if (sortedSignedMonomials.size() != mergedMonomials.size()) {
            throwElaborate(
                "`ring`: proveAddMerge: survivor count mismatched "
                "merged polynomial size (internal error)");
        }
        for (size_t i = 0; i < mergedMonomials.size(); ++i) {
            if (sortedSignedMonomials[i].signature
                    != mergedMonomials[i].signature
                || sortedSignedMonomials[i].sign
                    != mergedMonomials[i].sign) {
                throwElaborate(
                    "`ring`: proveAddMerge: survivors don't match "
                    "merged polynomial entry-by-entry (internal error)");
            }
        }
        // Append cancellation pairs.
        for (const auto& [sig, _] : cancelPairs) {
            sortedSignedMonomials.push_back({sig, +1});
            sortedSignedMonomials.push_back({sig, -1});
        }
        // Convert sortedSignedMonomials to kernels and sort the
        // *combinedKernels* into that order via insertion-sort proof.
        std::vector<ExpressionPointer> sortedKernels;
        sortedKernels.reserve(sortedSignedMonomials.size());
        for (const auto& m : sortedSignedMonomials) {
            sortedKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // The sortSumLeftAssocProof expects a vector that's a
        // permutation of combinedKernels (treated as the "factor
        // multiset"). proveProductEqualsSorted does insertion-sort
        // using compareExpressionStructure for direction. But we
        // want a SPECIFIC target permutation, not the
        // structurally-sorted one. proveProductEqualsSorted accepts
        // arbitrary sorted targets — let me check.
        //
        // Looking at proveProductEqualsSorted: it walks i = 0..n-1,
        // for each i finds the first j with current[j] = sorted[i],
        // and swaps it down to position i via adjacent swaps. So
        // ANY permutation of the original factor multiset works as
        // the "sorted" target.
        ExpressionPointer sortProof = sortSumLeftAssocProof(
            combinedKernels, sortedKernels, context, axiomNames);
        ExpressionPointer leftAssocSorted = assembleLeftAssociatedProduct(
            context.addName, sortedKernels);
        // Chain so far: leftPlusRight = leftAssocCombined (via
        // reassocProof) = leftAssocSorted (via sortProof).
        ExpressionPointer chainSoFar = buildEqualityTransitivity(
            universeLevel, carrierType,
            leftPlusRight, leftAssocCombined, leftAssocSorted,
            reassocProof, sortProof);
        if (cancelPairs.empty()) {
            // Surviving monomials only: leftAssocSorted == mergedCanonical.
            // Check that and return chainSoFar.
            if (!structurallyEqual(leftAssocSorted, mergedCanonical)) {
                throwElaborate(
                    "`ring`: proveAddMerge expected leftAssocSorted "
                    "to match canonical(mergedPoly) (no cancellations) "
                    "but they differ (internal error)");
            }
            return chainSoFar;
        }
        // Cancellations needed. Walk sortedKernels from right to left,
        // collapsing each (M, -M) tail-pair via:
        //   1. associativity: (((prefix + M) + -M) + tail) — no, after
        //      sort we already placed pairs at the very tail. The
        //      current form is `((prefix) + M_p) + (-M_p)` (for the
        //      rightmost pair). We use:
        //      add_associative(prefix, M, -M) :
        //        prefix + M + -M = prefix + (M + -M)
        //      add_negate_right(M) : M + -M = 0
        //      congruence with λz. prefix + z to get
        //        prefix + (M + -M) = prefix + 0
        //      add_zero_right(prefix) (i.e. add_zero) : prefix + 0 = prefix
        //   2. Then iterate: drop the next pair from the tail.
        demandAxiomName(axiomNames.addNegateRight, "add_negate_right",
                          context.carrierName);
        demandAxiomName(axiomNames.addZeroRight, "add_zero/add_identity_right",
                          context.carrierName);
        // current: ExpressionPointer for the current form. Starts as
        // leftAssocSorted. Each cancellation step removes the last two
        // summands (the (M, -M) pair).
        ExpressionPointer currentForm = leftAssocSorted;
        ExpressionPointer chainProof = chainSoFar;
        std::vector<ExpressionPointer> remainingKernels = sortedKernels;
        for (size_t pairIndex = 0; pairIndex < cancelPairs.size();
             ++pairIndex) {
            // Pop the last two from remainingKernels: they are (M, -M).
            if (remainingKernels.size() < 2) {
                throwElaborate(
                    "`ring`: cancellation underrun (internal error)");
            }
            ExpressionPointer negM = remainingKernels.back();
            remainingKernels.pop_back();
            ExpressionPointer M = remainingKernels.back();
            remainingKernels.pop_back();
            // Total-cancellation tail: the final pair has no prefix
            // before it. currentForm is just `M + (-M)`; reduce
            // directly to `0` via add_negate_right(M), no
            // associativity / add_zero needed.
            if (remainingKernels.empty()) {
                ExpressionPointer addNegProof = ringConst(axiomNames.addNegateRight);
                addNegProof = makeApplication(addNegProof, M);
                ExpressionPointer zeroConst = ringConst(context.zeroName);
                chainProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftPlusRight, currentForm, zeroConst,
                    chainProof, addNegProof);
                currentForm = zeroConst;
                continue;
            }
            ExpressionPointer prefix;
            bool prefixSingle = (remainingKernels.size() == 1);
            if (prefixSingle) {
                prefix = remainingKernels[0];
            } else {
                prefix = assembleLeftAssociatedProduct(
                    context.addName, remainingKernels);
            }
            // currentForm has shape:
            //   ((prefix) + M) + (-M)
            // Step A: associativity. (prefix + M) + (-M) = prefix + (M + (-M)).
            ExpressionPointer assocProof = ringConst(axiomNames.addAssociative);
            assocProof = makeApplication(assocProof, prefix);
            assocProof = makeApplication(assocProof, M);
            assocProof = makeApplication(assocProof, negM);
            ExpressionPointer formA = buildRingOp(
                context.addName, prefix,
                buildRingOp(context.addName, M, negM));
            // Step B: congruence with λz. prefix + z, where the inner
            // step is `add_negate_right(M) : M + (-M) = 0`.
            ExpressionPointer addNegProof = ringConst(axiomNames.addNegateRight);
            addNegProof = makeApplication(addNegProof, M);
            ExpressionPointer prefixLifted =
                liftBoundVariables(prefix, 1, 0);
            ExpressionPointer lambdaBodyB = buildRingOp(
                context.addName, prefixLifted, makeBoundVariable(0));
            ExpressionPointer lambdaB = makeLambda(
                "_ring_cancel_z", carrierType, lambdaBodyB);
            ExpressionPointer zeroConst = ringConst(context.zeroName);
            ExpressionPointer congrB =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaB,
                    buildRingOp(context.addName, M, negM),
                    zeroConst,
                    addNegProof);
            ExpressionPointer formB = buildRingOp(
                context.addName, prefix, zeroConst);
            // Step C: add_zero_right(prefix) : prefix + 0 = prefix.
            ExpressionPointer addZeroProof = ringConst(axiomNames.addZeroRight);
            addZeroProof = makeApplication(addZeroProof, prefix);
            // Compose: currentForm → formA via assocProof,
            //          formA → formB via congrB,
            //          formB → prefix via addZeroProof.
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formA, formB,
                assocProof, congrB);
            ExpressionPointer stepABC = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formB, prefix,
                stepAB, addZeroProof);
            // Now chain with chainProof.
            chainProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                leftPlusRight, currentForm, prefix,
                chainProof, stepABC);
            currentForm = prefix;
        }
        // After all cancellations, currentForm should be the merged
        // canonical form. For partial cancellation: sortedKernels of
        // just the survivors, left-associated. For total cancellation
        // (all summands cancel): the zero constant, set by the
        // final-pair branch above. Either way, structural equality
        // with mergedCanonical should hold.
        if (!structurallyEqual(currentForm, mergedCanonical)) {
            throwElaborate(
                "`ring`: proveAddMerge ended with shape mismatched "
                "with canonical(mergedPoly) (internal error)");
        }
        return chainProof;
    }

ExpressionPointer Elaborator::proveSignedMonomialSumEqualsCanonical(
        const std::vector<SignedMonomial>& combinedMonomials,
        const std::vector<ExpressionPointer>& combinedKernels,
        const RingPolynomial& mergedPoly,
        ExpressionPointer mergedCanonical,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        ExpressionPointer leftAssocCombined = assembleLeftAssociatedSum(
            context.addName, combinedKernels);
        std::vector<SignedMonomial> sortedSignedMonomials;
        // Group by signature.
        std::map<RingMonomialSignature, std::vector<int>> bySig;
        for (const auto& m : combinedMonomials) {
            bySig[m.signature].push_back(m.sign);
        }
        // Survivors first, in canonical signature order. Cancel pairs
        // collected to the side.
        //
        // Each group's `signs` vector consists of ±1 entries (one per
        // unit monomial). Count positives vs negatives: min(p, n)
        // pairs cancel, leaving |p - n| copies of sign(p - n) as
        // survivors. The merged polynomial's coefficient for this
        // signature is exactly (p - n), so the survivor count agrees
        // with mergedPoly[sig].
        std::vector<std::pair<RingMonomialSignature, int>> cancelPairs;
        for (const auto& [sig, signs] : bySig) {
            int positives = 0;
            int negatives = 0;
            for (int s : signs) {
                if (s > 0) ++positives;
                else if (s < 0) ++negatives;
            }
            int net = positives - negatives;
            int cancellations = std::min(positives, negatives);
            int survivorSign = (net > 0) ? +1 : -1;
            int survivorCount = (net > 0) ? net : -net;
            for (int i = 0; i < survivorCount; ++i) {
                sortedSignedMonomials.push_back({sig, survivorSign});
            }
            for (int i = 0; i < cancellations; ++i) {
                cancelPairs.push_back({sig, +1});
            }
        }
        // Verify: surviving monomials, in std::map signature order,
        // EXACTLY match canonicalMergedPoly's order.
        std::vector<SignedMonomial> mergedMonomials =
            polynomialToSignedMonomials(mergedPoly);
        if (sortedSignedMonomials.size() != mergedMonomials.size()) {
            throwElaborate(
                "`ring`: proveAddMerge: survivor count mismatched "
                "merged polynomial size (internal error)");
        }
        for (size_t i = 0; i < mergedMonomials.size(); ++i) {
            if (sortedSignedMonomials[i].signature
                    != mergedMonomials[i].signature
                || sortedSignedMonomials[i].sign
                    != mergedMonomials[i].sign) {
                throwElaborate(
                    "`ring`: proveAddMerge: survivors don't match "
                    "merged polynomial entry-by-entry (internal error)");
            }
        }
        // Append cancellation pairs.
        for (const auto& [sig, _] : cancelPairs) {
            sortedSignedMonomials.push_back({sig, +1});
            sortedSignedMonomials.push_back({sig, -1});
        }
        // Convert sortedSignedMonomials to kernels and sort the
        // *combinedKernels* into that order via insertion-sort proof.
        std::vector<ExpressionPointer> sortedKernels;
        sortedKernels.reserve(sortedSignedMonomials.size());
        for (const auto& m : sortedSignedMonomials) {
            sortedKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // The sortSumLeftAssocProof expects a vector that's a
        // permutation of combinedKernels (treated as the "factor
        // multiset"). proveProductEqualsSorted does insertion-sort
        // using compareExpressionStructure for direction. But we
        // want a SPECIFIC target permutation, not the
        // structurally-sorted one. proveProductEqualsSorted accepts
        // arbitrary sorted targets — let me check.
        //
        // Looking at proveProductEqualsSorted: it walks i = 0..n-1,
        // for each i finds the first j with current[j] = sorted[i],
        // and swaps it down to position i via adjacent swaps. So
        // ANY permutation of the original factor multiset works as
        // the "sorted" target.
        ExpressionPointer sortProof = sortSumLeftAssocProof(
            combinedKernels, sortedKernels, context, axiomNames);
        ExpressionPointer leftAssocSorted = assembleLeftAssociatedProduct(
            context.addName, sortedKernels);
        // Chain so far: leftAssocCombined = leftAssocCombined (via
        // reassocProof) = leftAssocSorted (via sortProof).
        // (helper) chainProof starts at the post-sort form; the caller
        // owns the base-to-leftAssocCombined step.
        ExpressionPointer chainSoFar = sortProof;
        if (cancelPairs.empty()) {
            // Surviving monomials only: leftAssocSorted == mergedCanonical.
            // Check that and return chainSoFar.
            if (!structurallyEqual(leftAssocSorted, mergedCanonical)) {
                throwElaborate(
                    "`ring`: proveAddMerge expected leftAssocSorted "
                    "to match canonical(mergedPoly) (no cancellations) "
                    "but they differ (internal error)");
            }
            return chainSoFar;
        }
        // Cancellations needed. Walk sortedKernels from right to left,
        // collapsing each (M, -M) tail-pair via:
        //   1. associativity: (((prefix + M) + -M) + tail) — no, after
        //      sort we already placed pairs at the very tail. The
        //      current form is `((prefix) + M_p) + (-M_p)` (for the
        //      rightmost pair). We use:
        //      add_associative(prefix, M, -M) :
        //        prefix + M + -M = prefix + (M + -M)
        //      add_negate_right(M) : M + -M = 0
        //      congruence with λz. prefix + z to get
        //        prefix + (M + -M) = prefix + 0
        //      add_zero_right(prefix) (i.e. add_zero) : prefix + 0 = prefix
        //   2. Then iterate: drop the next pair from the tail.
        demandAxiomName(axiomNames.addNegateRight, "add_negate_right",
                          context.carrierName);
        demandAxiomName(axiomNames.addZeroRight, "add_zero/add_identity_right",
                          context.carrierName);
        // current: ExpressionPointer for the current form. Starts as
        // leftAssocSorted. Each cancellation step removes the last two
        // summands (the (M, -M) pair).
        ExpressionPointer currentForm = leftAssocSorted;
        ExpressionPointer chainProof = chainSoFar;
        std::vector<ExpressionPointer> remainingKernels = sortedKernels;
        for (size_t pairIndex = 0; pairIndex < cancelPairs.size();
             ++pairIndex) {
            // Pop the last two from remainingKernels: they are (M, -M).
            if (remainingKernels.size() < 2) {
                throwElaborate(
                    "`ring`: cancellation underrun (internal error)");
            }
            ExpressionPointer negM = remainingKernels.back();
            remainingKernels.pop_back();
            ExpressionPointer M = remainingKernels.back();
            remainingKernels.pop_back();
            // Total-cancellation tail: the final pair has no prefix
            // before it. currentForm is just `M + (-M)`; reduce
            // directly to `0` via add_negate_right(M), no
            // associativity / add_zero needed.
            if (remainingKernels.empty()) {
                ExpressionPointer addNegProof = ringConst(axiomNames.addNegateRight);
                addNegProof = makeApplication(addNegProof, M);
                ExpressionPointer zeroConst = ringConst(context.zeroName);
                chainProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftAssocCombined, currentForm, zeroConst,
                    chainProof, addNegProof);
                currentForm = zeroConst;
                continue;
            }
            ExpressionPointer prefix;
            bool prefixSingle = (remainingKernels.size() == 1);
            if (prefixSingle) {
                prefix = remainingKernels[0];
            } else {
                prefix = assembleLeftAssociatedProduct(
                    context.addName, remainingKernels);
            }
            // currentForm has shape:
            //   ((prefix) + M) + (-M)
            // Step A: associativity. (prefix + M) + (-M) = prefix + (M + (-M)).
            ExpressionPointer assocProof = ringConst(axiomNames.addAssociative);
            assocProof = makeApplication(assocProof, prefix);
            assocProof = makeApplication(assocProof, M);
            assocProof = makeApplication(assocProof, negM);
            ExpressionPointer formA = buildRingOp(
                context.addName, prefix,
                buildRingOp(context.addName, M, negM));
            // Step B: congruence with λz. prefix + z, where the inner
            // step is `add_negate_right(M) : M + (-M) = 0`.
            ExpressionPointer addNegProof = ringConst(axiomNames.addNegateRight);
            addNegProof = makeApplication(addNegProof, M);
            ExpressionPointer prefixLifted =
                liftBoundVariables(prefix, 1, 0);
            ExpressionPointer lambdaBodyB = buildRingOp(
                context.addName, prefixLifted, makeBoundVariable(0));
            ExpressionPointer lambdaB = makeLambda(
                "_ring_cancel_z", carrierType, lambdaBodyB);
            ExpressionPointer zeroConst = ringConst(context.zeroName);
            ExpressionPointer congrB =
                buildEqualityCongruenceSameCarrier(
                    universeLevel, carrierType, lambdaB,
                    buildRingOp(context.addName, M, negM),
                    zeroConst,
                    addNegProof);
            ExpressionPointer formB = buildRingOp(
                context.addName, prefix, zeroConst);
            // Step C: add_zero_right(prefix) : prefix + 0 = prefix.
            ExpressionPointer addZeroProof = ringConst(axiomNames.addZeroRight);
            addZeroProof = makeApplication(addZeroProof, prefix);
            // Compose: currentForm → formA via assocProof,
            //          formA → formB via congrB,
            //          formB → prefix via addZeroProof.
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formA, formB,
                assocProof, congrB);
            ExpressionPointer stepABC = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formB, prefix,
                stepAB, addZeroProof);
            // Now chain with chainProof.
            chainProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                leftAssocCombined, currentForm, prefix,
                chainProof, stepABC);
            currentForm = prefix;
        }
        // After all cancellations, currentForm should be the merged
        // canonical form. For partial cancellation: sortedKernels of
        // just the survivors, left-associated. For total cancellation
        // (all summands cancel): the zero constant, set by the
        // final-pair branch above. Either way, structural equality
        // with mergedCanonical should hold.
        if (!structurallyEqual(currentForm, mergedCanonical)) {
            throwElaborate(
                "`ring`: proveAddMerge ended with shape mismatched "
                "with canonical(mergedPoly) (internal error)");
        }
        return chainProof;
    }

void Elaborator::appendIsRingInstanceArgs(
        ExpressionPointer& call,
        const RingNormalisationContext& context) {
        // Every operation/constant carries the structure prefix (`c` for
        // a bundled commutative ring). These are RAW kernel terms — the
        // elaborator's implicit-argument insertion does NOT run here — so
        // even the binary ops must be applied to the prefix explicitly
        // (`CommutativeRing.add(c)`), not left bare. For a concrete
        // carrier the prefix is empty, so `ringConst` is just the bare
        // constant, exactly as before.
        call = makeApplication(call, context.carrierType);
        call = makeApplication(call, ringConst(context.addName));
        call = makeApplication(call, ringConst(context.zeroName));
        call = makeApplication(call, ringConst(context.negateName));
        call = makeApplication(call, ringConst(context.multiplyName));
        call = makeApplication(call, ringConst(context.oneName));
        call = makeApplication(call, ringConst(context.isRingName));
    }

ExpressionPointer Elaborator::buildAbstractRingLemmaApplication(
        const std::string& abstractLemmaName,
        const std::string& fallbackPerCarrierName,
        const std::string& fallbackHumanName,
        const std::vector<ExpressionPointer>& args,
        const RingNormalisationContext& context) {
        if (environment_.lookup(abstractLemmaName) != nullptr
            && environment_.lookup(context.isRingName) != nullptr) {
            ExpressionPointer call = makeConstant(abstractLemmaName);
            appendIsRingInstanceArgs(call, context);
            for (const auto& arg : args) {
                call = makeApplication(call, arg);
            }
            return call;
        }
        // Fall back to a per-carrier wrapper (concrete carriers only).
        demandAxiomName(fallbackPerCarrierName, fallbackHumanName,
                          context.carrierName);
        ExpressionPointer call = ringConst(fallbackPerCarrierName);
        for (const auto& arg : args) {
            call = makeApplication(call, arg);
        }
        return call;
    }

ExpressionPointer Elaborator::buildRingAnnihilatorProof(
        bool onLeft,
        ExpressionPointer x,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        return buildAbstractRingLemmaApplication(
            onLeft ? "Ring.zero_multiply" : "Ring.multiply_zero",
            onLeft ? axiomNames.multiplyZeroLeft
                    : axiomNames.multiplyZeroRight,
            onLeft ? "multiply_zero_left / zero_multiply"
                    : "multiply_zero_right / multiply_zero",
            {x}, context);
    }

ExpressionPointer Elaborator::buildRingMultiplyNegateProof(
        bool onLeft,
        ExpressionPointer a, ExpressionPointer b,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        return buildAbstractRingLemmaApplication(
            onLeft ? "Ring.multiply_negate_left"
                    : "Ring.multiply_negate_right",
            onLeft ? axiomNames.multiplyNegateLeft
                    : axiomNames.multiplyNegateRight,
            onLeft ? "multiply_negate_left"
                    : "multiply_negate_right",
            {a, b}, context);
    }

ExpressionPointer Elaborator::proveMultiplyMerge(
        const RingPolynomial& leftPoly,
        const RingPolynomial& rightPoly,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        ExpressionPointer leftCanonical =
            buildCanonicalPolynomial(leftPoly, context);
        ExpressionPointer rightCanonical =
            buildCanonicalPolynomial(rightPoly, context);
        ExpressionPointer leftTimesRight = buildRingOp(
            context.multiplyName, leftCanonical, rightCanonical);
        RingPolynomial mergedPoly = ringPolynomialMultiply(
            leftPoly, rightPoly);
        ExpressionPointer mergedCanonical =
            buildCanonicalPolynomial(mergedPoly, context);
        // Edge: one side empty. Then leftPoly · rightPoly = empty,
        // and we need the multiplicative-annihilation axiom on the
        // appropriate side. We get this from the abstract
        // `Ring.zero_multiply` / `Ring.multiply_zero` lemmas (proved
        // once over IsRing in `Algebra/ring_lemmas.math`) applied to
        // the carrier's `is_ring` instance.
        //
        // Falls back to the per-carrier name (`<C>.multiply_zero_left`
        // / `<C>.zero_multiply`) when that's the only thing in scope —
        // useful for Integer, which has rep-level reflexivity proofs
        // shorter than the abstract derivation would compile to.
        if (leftPoly.empty()) {
            return buildRingAnnihilatorProof(
                /*onLeft=*/true, rightCanonical, context, axiomNames);
        }
        if (rightPoly.empty()) {
            return buildRingAnnihilatorProof(
                /*onLeft=*/false, leftCanonical, context, axiomNames);
        }
        // Like-term collisions across the p*q products (cross-pair
        // cancellation, e.g. (a+b)(a−b): the +ab and −ba collapse) are
        // handled in the final phase below by the shared signed-monomial-
        // sum merge, exactly as the additive path cancels like terms — so
        // no special-case bail here.
        // Build the "naively expanded" sum:
        //   sum_{i,j} (L_i * R_j)
        // in the order (i, j) = (0, 0..q-1), (1, 0..q-1), ..., (p-1, ...).
        // Render each L_i and R_j as canonical monomial kernels.
        std::vector<SignedMonomial> leftSigned =
            polynomialToSignedMonomials(leftPoly);
        std::vector<SignedMonomial> rightSigned =
            polynomialToSignedMonomials(rightPoly);
        std::vector<ExpressionPointer> leftMonomialKernels;
        for (const auto& m : leftSigned) {
            leftMonomialKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        std::vector<ExpressionPointer> rightMonomialKernels;
        for (const auto& m : rightSigned) {
            rightMonomialKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Step 1: prove leftCanonical * rightCanonical = sum_{i,j} L_i * R_j.
        // We do this in two sub-phases:
        //   1a: leftCanonical * rightCanonical
        //         = sum_i (L_i * rightCanonical)      via distributivity_right (peel rows)
        //   1b: each L_i * rightCanonical
        //         = sum_j (L_i * R_j)                via distributivity_left
        //   1c: combine inner sums into the flat outer form.
        //
        // For implementation we use a simpler iterative approach:
        // expand row-by-row applying distributivity_right.
        demandAxiomName(axiomNames.distributivityRight,
                          "distributivity_right", context.carrierName);
        demandAxiomName(axiomNames.distributivityLeft,
                          "distributivity_left", context.carrierName);
        // Phase 1a: expand the outer left into a sum of (L_i * rightCanonical).
        // We achieve this by peeling the leftmost group from the
        // left-associated `L_1 + ... + L_p`. Each peel uses
        // distributivity_right(prefix, L_i, rightCanonical):
        //   (prefix + L_i) * R = prefix*R + L_i*R.
        //
        // For p = 1: leftCanonical = L_0, so leftCanonical * rightCanonical
        //            = L_0 * rightCanonical — no peeling needed.
        // For p > 1: leftCanonical = (((L_0 + L_1) + L_2) + ... + L_{p-1}),
        //            we peel right-to-left.
        //
        // Track current form (an ExpressionPointer) and current proof
        // (leftTimesRight = currentForm). Start with currentForm = leftTimesRight,
        // currentProof = reflexivity.
        ExpressionPointer currentForm = leftTimesRight;
        ExpressionPointer currentProof = buildReflexivity(
            universeLevel, carrierType, currentForm);
        // Helper: given a left-associated sum of length n (kernels in
        // `summands`), return the left-associated kernel.
        auto leftAssoc = [&](const std::vector<ExpressionPointer>& v)
            -> ExpressionPointer {
            return assembleLeftAssociatedProduct(context.addName, v);
        };
        // We peel from the right: at each step, we have
        //   currentForm = (sum_of_first_i_terms) * rightCanonical
        //                  + (already-peeled tail summands)
        // The tail is a left-associated sum: (L_i*R) + (L_{i+1}*R) + ...
        // After all peels, currentForm becomes
        //   L_0 * R + L_1 * R + ... + L_{p-1} * R   (left-associated).
        if (leftSigned.size() == 1) {
            // No peeling needed for this phase.
        } else {
            // Walk i from p-1 down to 1; at each step, peel L_i out of
            // the leftmost factor.
            // Initial form of "leftFactor": leftCanonical (full).
            ExpressionPointer leftFactor = leftCanonical;
            for (size_t i = leftSigned.size(); i > 1; --i) {
                // leftFactor at this iteration = leftAssoc(L_0..L_{i-1}).
                // It has shape (smallerLeftFactor + L_{i-1}) by left-assoc.
                size_t lastIdx = i - 1;
                // smallerLeftFactor = leftAssoc(L_0..L_{i-2}).
                std::vector<ExpressionPointer> smallerKernels(
                    leftMonomialKernels.begin(),
                    leftMonomialKernels.begin()
                        + static_cast<long>(lastIdx));
                ExpressionPointer smallerLeftFactor;
                if (smallerKernels.size() == 1) {
                    smallerLeftFactor = smallerKernels[0];
                } else {
                    smallerLeftFactor = leftAssoc(smallerKernels);
                }
                ExpressionPointer Li = leftMonomialKernels[lastIdx];
                // distributivity_right(smallerLeftFactor, L_{lastIdx}, R)
                //   : (smallerLeftFactor + L_{lastIdx}) * R
                //     = smallerLeftFactor * R + L_{lastIdx} * R
                ExpressionPointer distRightCall = ringConst(axiomNames.distributivityRight);
                distRightCall = makeApplication(distRightCall,
                                                  smallerLeftFactor);
                distRightCall = makeApplication(distRightCall, Li);
                distRightCall = makeApplication(distRightCall,
                                                  rightCanonical);
                // The LHS of distRightCall:
                //   (smallerLeftFactor + L_{lastIdx}) * R = leftFactor * R
                // RHS: smallerLeftFactor * R + L_{lastIdx} * R.
                ExpressionPointer lhsExpanded = buildRingOp(
                    context.multiplyName, leftFactor, rightCanonical);
                ExpressionPointer rhsExpanded = buildRingOp(
                    context.addName,
                    buildRingOp(context.multiplyName, smallerLeftFactor,
                                  rightCanonical),
                    buildRingOp(context.multiplyName, Li, rightCanonical));
                // currentForm at this point has shape:
                //   leftFactor * R                         (if i == p)
                //   or (leftFactor * R) + tail              (if i < p)
                ExpressionPointer stepProof;
                ExpressionPointer newForm;
                if (i == leftSigned.size()) {
                    // currentForm == lhsExpanded.
                    stepProof = distRightCall;
                    newForm = rhsExpanded;
                } else {
                    // currentForm has shape: lhsExpanded LEFT-ASSOCIATED
                    // with previously-peeled summands on the right —
                    //   ((((lhsExpanded + T_i) + T_{i+1}) + ...) + T_{p-1})
                    // where T_k = L_k * R. The lambda for congruence
                    // must wrap z with each T_k via repeated left-
                    // associated adds (not as a single right-leaning
                    // sum, which doesn't match the actual structure).
                    ExpressionPointer lambdaBody = makeBoundVariable(0);
                    for (size_t k = i; k < leftSigned.size(); ++k) {
                        ExpressionPointer tk = liftBoundVariables(
                            buildRingOp(
                                context.multiplyName,
                                leftMonomialKernels[k], rightCanonical),
                            1, 0);
                        lambdaBody = buildRingOp(
                            context.addName, lambdaBody, tk);
                    }
                    ExpressionPointer lambda = makeLambda(
                        "_ring_distR_z", carrierType, lambdaBody);
                    stepProof = buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        lhsExpanded, rhsExpanded, distRightCall);
                    // Build newForm = ((((rhsExpanded + T_i) + ...) + T_{p-1})).
                    newForm = rhsExpanded;
                    for (size_t k = i; k < leftSigned.size(); ++k) {
                        newForm = buildRingOp(
                            context.addName,
                            newForm,
                            buildRingOp(
                                context.multiplyName,
                                leftMonomialKernels[k], rightCanonical));
                    }
                }
                // currentProof was: leftTimesRight = currentForm.
                // stepProof: currentForm = newForm.
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, newForm,
                    currentProof, stepProof);
                currentForm = newForm;
                leftFactor = smallerLeftFactor;
            }
            // After this loop currentForm has shape:
            //   ((L_0 * R) + (L_1 * R)) + ... + (L_{p-1} * R)
            // but possibly with a non-flat shape (the loop produced
            // a "rhsExpanded + tail" nested structure, not a flat left-
            // associated sum). Need to reassociate.
            //
            // Reassociate to left-associated form (treating L_i * R as
            // opaque atoms).
            std::vector<ExpressionPointer> phase1ATargetSummands;
            for (size_t k = 0; k < leftSigned.size(); ++k) {
                phase1ATargetSummands.push_back(buildRingOp(
                    context.multiplyName,
                    leftMonomialKernels[k], rightCanonical));
            }
            ExpressionPointer phase1ATargetKernel = leftAssoc(
                phase1ATargetSummands);
            if (!structurallyEqual(currentForm, phase1ATargetKernel)) {
                // Reassociate via add-AC.
                ExpressionPointer reassocProof = reassociateSumLeftProof(
                    currentForm, context, axiomNames);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, phase1ATargetKernel,
                    currentProof, reassocProof);
                currentForm = phase1ATargetKernel;
            }
        }
        // currentForm now equals the left-associated sum of (L_i * R)
        // for i=0..p-1, where R = rightCanonical.
        // Phase 1b: for each i, expand L_i * R into sum over j of L_i * R_j.
        // We do this one row at a time. After expanding row i, the
        // current form has shape:
        //   [already-expanded rows 0..i-1]   (flat sum of L_k * R_l)
        //     + [(L_i * R_0) + (L_i * R_1) + ... + (L_i * R_{q-1})]   (this row)
        //     + [unexpanded rows i+1..p-1]   (each as L_k * R)
        // All wrapped into a left-associated chain.
        //
        // For simplicity we expand all rows then reassociate, similar
        // to phase 1a but on the inner level.
        //
        // To expand L_i * (R_0 + ... + R_{q-1}) into a sum of L_i * R_j
        // via distributivity_left, we peel the rightmost R from the
        // sum (mirror of phase 1a):
        //   L_i * (smallerRSum + R_{q-1})
        //     = L_i * smallerRSum + L_i * R_{q-1}     via distributivity_left
        //
        // Result list of summands after both phases:
        std::vector<ExpressionPointer> phase1BAllSummands;
        for (size_t i = 0; i < leftSigned.size(); ++i) {
            for (size_t j = 0; j < rightSigned.size(); ++j) {
                phase1BAllSummands.push_back(buildRingOp(
                    context.multiplyName,
                    leftMonomialKernels[i],
                    rightMonomialKernels[j]));
            }
        }
        // We need to transform currentForm into the left-assoc of
        // phase1BAllSummands. Approach: walk each row and apply
        // distributivity_left + congruence to expand it in place.
        if (rightSigned.size() > 1) {
            // For each row i (in order), apply distributivity_left to
            // its (L_i * R) factor. We use congruence with a motive that
            // targets exactly position i in the left-associated sum.
            // To avoid the complexity of building a motive that
            // surgically modifies a position deep in a left-associated
            // sum, we use a per-row chain:
            //
            //   For row i: locate (L_i * R) somewhere in currentForm,
            //   replace it with the expansion (L_i*R_0 + ... + L_i*R_{q-1}).
            //   The replacement is an opaque-equal transformation —
            //   `congruenceOf(motive, proofOfL_iR=expansion)`.
            //
            // We'll handle this by recursively walking the current form
            // and emitting congruences as we go.
            // Implementation: build a helper that, given the row index
            // and a kernel-form representation, finds the unique
            // structural occurrence of (L_i * R) in the current form
            // and applies the expansion. We exploit the fact that we
            // KNOW the current form's structure exactly (it's the left-
            // assoc of all L_k * R), so we can target it precisely.
            //
            // Strategy: process rows left-to-right. After processing
            // rows 0..i-1, currentForm has shape:
            //   ((((expanded_0) + ... + expanded_{i-1}) + (L_i * R))
            //     + (L_{i+1} * R)) + ... + (L_{p-1} * R)
            // where each expanded_k is the left-assoc of L_k*R_0..L_k*R_{q-1}.
            //
            // To expand row i: locate (L_i * R) in the position
            // described above. Build a motive that wraps z at that
            // position. Apply congruence with proof: L_i * R = expanded_i.
            //
            // To build the proof L_i * R = expanded_i (where R = R_0 + R_1 + ... + R_{q-1}):
            // Apply distributivity_left repeatedly. Specifically:
            //   L_i * (smallerR + R_{q-1}) = L_i * smallerR + L_i * R_{q-1}
            // recurse on the left side. We'll do this in a small helper.
            for (size_t i = 0; i < leftSigned.size(); ++i) {
                // Build proof for the row expansion.
                ExpressionPointer Li = leftMonomialKernels[i];
                // Build "L_i * R_j" summands.
                std::vector<ExpressionPointer> rowSummands;
                for (size_t j = 0; j < rightSigned.size(); ++j) {
                    rowSummands.push_back(buildRingOp(
                        context.multiplyName, Li,
                        rightMonomialKernels[j]));
                }
                // Expansion: left-assoc of rowSummands.
                ExpressionPointer expandedRow;
                if (rowSummands.size() == 1) {
                    expandedRow = rowSummands[0];
                } else {
                    expandedRow = leftAssoc(rowSummands);
                }
                // Build proof Li * R = expandedRow.
                // Iterative peel from the right: at each step k
                // (k = q-1 down to 1), we expand Li * (smallerR + R_k).
                ExpressionPointer rowCurrent = buildRingOp(
                    context.multiplyName, Li, rightCanonical);
                ExpressionPointer rowProof = buildReflexivity(
                    universeLevel, carrierType, rowCurrent);
                if (rightSigned.size() > 1) {
                    ExpressionPointer rightFactor = rightCanonical;
                    for (size_t k = rightSigned.size(); k > 1; --k) {
                        size_t lastIdx = k - 1;
                        std::vector<ExpressionPointer> smallerRKernels(
                            rightMonomialKernels.begin(),
                            rightMonomialKernels.begin()
                                + static_cast<long>(lastIdx));
                        ExpressionPointer smallerR;
                        if (smallerRKernels.size() == 1) {
                            smallerR = smallerRKernels[0];
                        } else {
                            smallerR = leftAssoc(smallerRKernels);
                        }
                        ExpressionPointer Rk =
                            rightMonomialKernels[lastIdx];
                        // distributivity_left(Li, smallerR, Rk):
                        //   Li * (smallerR + Rk) = Li * smallerR + Li * Rk
                        ExpressionPointer distLeftCall = ringConst(axiomNames.distributivityLeft);
                        distLeftCall = makeApplication(distLeftCall, Li);
                        distLeftCall = makeApplication(distLeftCall,
                                                          smallerR);
                        distLeftCall = makeApplication(distLeftCall, Rk);
                        ExpressionPointer lhsExpanded = buildRingOp(
                            context.multiplyName, Li, rightFactor);
                        ExpressionPointer rhsExpanded = buildRingOp(
                            context.addName,
                            buildRingOp(context.multiplyName, Li,
                                          smallerR),
                            buildRingOp(context.multiplyName, Li, Rk));
                        ExpressionPointer stepProof;
                        ExpressionPointer newRowForm;
                        if (k == rightSigned.size()) {
                            stepProof = distLeftCall;
                            newRowForm = rhsExpanded;
                        } else {
                            // rowCurrent has shape lhsExpanded + tail.
                            std::vector<ExpressionPointer> tailSummands(
                                rowSummands.begin()
                                    + static_cast<long>(k),
                                rowSummands.end());
                            ExpressionPointer tailKernel;
                            if (tailSummands.size() == 1) {
                                tailKernel = tailSummands[0];
                            } else {
                                tailKernel = leftAssoc(tailSummands);
                            }
                            ExpressionPointer tailLifted =
                                liftBoundVariables(tailKernel, 1, 0);
                            ExpressionPointer lambdaBody = buildRingOp(
                                context.addName,
                                makeBoundVariable(0), tailLifted);
                            ExpressionPointer lambda = makeLambda(
                                "_ring_distL_z", carrierType, lambdaBody);
                            stepProof =
                                buildEqualityCongruenceSameCarrier(
                                    universeLevel, carrierType, lambda,
                                    lhsExpanded, rhsExpanded, distLeftCall);
                            newRowForm = buildRingOp(
                                context.addName, rhsExpanded, tailKernel);
                        }
                        rowProof = buildEqualityTransitivity(
                            universeLevel, carrierType,
                            buildRingOp(context.multiplyName, Li,
                                          rightCanonical),
                            rowCurrent, newRowForm,
                            rowProof, stepProof);
                        rowCurrent = newRowForm;
                        rightFactor = smallerR;
                    }
                    // Reassociate rowCurrent → expandedRow.
                    if (!structurallyEqual(rowCurrent, expandedRow)) {
                        ExpressionPointer reassocProof =
                            reassociateSumLeftProof(
                                rowCurrent, context, axiomNames);
                        rowProof = buildEqualityTransitivity(
                            universeLevel, carrierType,
                            buildRingOp(context.multiplyName, Li,
                                          rightCanonical),
                            rowCurrent, expandedRow,
                            rowProof, reassocProof);
                        rowCurrent = expandedRow;
                    }
                }
                // rowProof : Li * R = expandedRow.
                // Apply this rewrite in currentForm by building a
                // congruence. Position of (Li * R) in currentForm:
                // after processing rows 0..i-1, currentForm has the
                // shape described above. We'll build a motive lambda
                // tailored to that exact position.
                //
                // Concretely: the form is
                //   ((((expanded_0 + ... + expanded_{i-1}) + (L_i * R))
                //     + (L_{i+1} * R)) + ...) + (L_{p-1} * R)
                // We need a motive `λ z. (((expanded_0 + ... + expanded_{i-1}) + z) + (L_{i+1}*R)) + ... + (L_{p-1}*R)`.
                ExpressionPointer postExpansionPrefix;  // expanded rows
                std::vector<ExpressionPointer> postPrefixSummands;
                for (size_t k = 0; k < i; ++k) {
                    // expanded_k = left-assoc of (L_k * R_0..R_{q-1}).
                    std::vector<ExpressionPointer> kSummands;
                    for (size_t jj = 0; jj < rightSigned.size(); ++jj) {
                        kSummands.push_back(buildRingOp(
                            context.multiplyName,
                            leftMonomialKernels[k],
                            rightMonomialKernels[jj]));
                    }
                    ExpressionPointer kKernel;
                    if (kSummands.size() == 1) {
                        kKernel = kSummands[0];
                    } else {
                        kKernel = leftAssoc(kSummands);
                    }
                    postPrefixSummands.push_back(kKernel);
                }
                std::vector<ExpressionPointer> tailSummands;
                for (size_t k = i + 1; k < leftSigned.size(); ++k) {
                    tailSummands.push_back(buildRingOp(
                        context.multiplyName,
                        leftMonomialKernels[k], rightCanonical));
                }
                // Build lambda body. The pattern:
                //   ... ( ((postPrefixSums) + z) + tailSums[0] ) + tailSums[1] ...
                // First, build the "left part" = left-assoc of
                // postPrefixSums, then `+ z` to it.
                ExpressionPointer lambdaInner;
                {
                    // Build left part with proper bound-variable lift.
                    // postPrefixSums are kernel expressions from the
                    // OUTER context — they don't reference the lambda's
                    // bound variable, so we lift them by 1.
                    std::vector<ExpressionPointer> liftedPrefix;
                    for (const auto& s : postPrefixSummands) {
                        liftedPrefix.push_back(liftBoundVariables(s, 1, 0));
                    }
                    ExpressionPointer leftPart;
                    if (liftedPrefix.empty()) {
                        // No prefix; the body starts with z.
                        leftPart = makeBoundVariable(0);
                    } else {
                        if (liftedPrefix.size() == 1) {
                            leftPart = buildRingOp(
                                context.addName, liftedPrefix[0],
                                makeBoundVariable(0));
                        } else {
                            ExpressionPointer prefixKernel =
                                leftAssoc(liftedPrefix);
                            leftPart = buildRingOp(
                                context.addName, prefixKernel,
                                makeBoundVariable(0));
                        }
                    }
                    // Now extend with `+ tailSummands[0] + ... + tailSummands[last]`.
                    for (const auto& tk : tailSummands) {
                        ExpressionPointer tkLifted =
                            liftBoundVariables(tk, 1, 0);
                        leftPart = buildRingOp(
                            context.addName, leftPart, tkLifted);
                    }
                    lambdaInner = leftPart;
                }
                ExpressionPointer lambda = makeLambda(
                    "_ring_rowexp_z", carrierType, lambdaInner);
                // x = Li * R; y = expandedRow.
                ExpressionPointer xExpr = buildRingOp(
                    context.multiplyName, Li, rightCanonical);
                ExpressionPointer congrProof =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        xExpr, expandedRow, rowProof);
                // The proof: currentForm (which equals λ(xExpr) by
                // beta-reduction of the application of lambda to xExpr)
                // = λ(expandedRow).
                // Substitute into the lambda body to get the new form.
                auto substituteBV0 = [&](ExpressionPointer body,
                                            ExpressionPointer arg)
                    -> ExpressionPointer {
                    return substituteBoundVariable(body, arg, 0);
                };
                ExpressionPointer newForm = substituteBV0(
                    lambdaInner, expandedRow);
                // Sanity: currentForm should equal substituteBV0(lambdaInner, xExpr).
                ExpressionPointer expectedCurrent = substituteBV0(
                    lambdaInner, xExpr);
                if (!structurallyEqual(currentForm, expectedCurrent)) {
                    throwElaborate(
                        "`ring` phase1b: motive's xExpr-form does "
                        "not match currentForm (internal error)");
                }
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, newForm,
                    currentProof, congrProof);
                currentForm = newForm;
            }
            // After all rows, currentForm = nested expansion. Reassociate
            // to flat sum of all L_i * R_j.
            ExpressionPointer phase1BFlatKernel = leftAssoc(
                phase1BAllSummands);
            if (!structurallyEqual(currentForm, phase1BFlatKernel)) {
                ExpressionPointer reassocProof = reassociateSumLeftProof(
                    currentForm, context, axiomNames);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, phase1BFlatKernel,
                    currentProof, reassocProof);
                currentForm = phase1BFlatKernel;
            }
        }
        // currentForm is now the left-associated sum of all p*q
        // pairs L_i * R_j (in row-major order).
        // Phase 2: for each summand L_i * R_j, transform it into the
        // canonical monomial form for the merged-signature monomial.
        // The merged monomial sig is sort(L_i.sig ++ R_j.sig), and
        // its sign is L_i.sign * R_j.sign.
        //
        // L_i * R_j as a kernel is:
        //   * if both positive: leftProduct * rightProduct
        //   * if one negative: negate(positive_one) * positive_other
        //                       — needs multiply_negate_left/right
        //                       to push outside
        //   * if both negative: negate(...) * negate(...)
        //                       — needs both rules + negate_negate
        //
        // Then the factors of the resulting product need to be
        // re-associated and sorted (sort by hash) to canonical order.
        //
        // We rewrite each summand position-by-position via congruence.
        for (size_t i = 0; i < leftSigned.size(); ++i) {
            for (size_t j = 0; j < rightSigned.size(); ++j) {
                size_t flatIndex = i * rightSigned.size() + j;
                // The current summand at flatIndex is buildRingOp(*, Li, Rj).
                ExpressionPointer Li = leftMonomialKernels[i];
                ExpressionPointer Rj = rightMonomialKernels[j];
                ExpressionPointer summandKernel = buildRingOp(
                    context.multiplyName, Li, Rj);
                // Compute the target monomial:
                RingMonomialSignature mergedSig;
                mergedSig.reserve(leftSigned[i].signature.size()
                                    + rightSigned[j].signature.size());
                std::merge(leftSigned[i].signature.begin(),
                            leftSigned[i].signature.end(),
                            rightSigned[j].signature.begin(),
                            rightSigned[j].signature.end(),
                            std::back_inserter(mergedSig));
                int mergedSign = leftSigned[i].sign * rightSigned[j].sign;
                ExpressionPointer targetMonomial =
                    buildSignedMonomialKernel(
                        mergedSig, mergedSign, context);
                if (structurallyEqual(summandKernel, targetMonomial)) {
                    // No transformation needed.
                    continue;
                }
                // Build a proof: summandKernel = targetMonomial.
                ExpressionPointer summandProof = proveSignedProductEqualsMonomial(
                    Li, Rj,
                    leftSigned[i], rightSigned[j],
                    mergedSig, mergedSign,
                    targetMonomial, context, axiomNames);
                // Apply at position flatIndex in currentForm. We need a
                // motive that targets exactly that position in the flat
                // left-associated sum.
                ExpressionPointer congrProof =
                    rewriteFlatSummandAtPositionProof(
                        currentForm, flatIndex,
                        leftSigned.size() * rightSigned.size(),
                        summandKernel, targetMonomial,
                        summandProof, context);
                ExpressionPointer newCurrent =
                    rewriteFlatSummandAtPosition(
                        currentForm, flatIndex,
                        leftSigned.size() * rightSigned.size(),
                        targetMonomial, context);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    leftTimesRight, currentForm, newCurrent,
                    currentProof, congrProof);
                currentForm = newCurrent;
            }
        }
        // currentForm is now a flat sum of the p*q canonical monomials
        // L_i*R_j in row-major order. Merge them into the canonical
        // merged form — sorting AND cancelling opposite-sign like terms
        // (cross-pair cancellation, and combining same-sign duplicates) —
        // via the shared signed-monomial-sum merge the additive path
        // uses.
        std::vector<SignedMonomial> productMonomials;
        std::vector<ExpressionPointer> productKernels;
        for (size_t i = 0; i < leftSigned.size(); ++i) {
            for (size_t j = 0; j < rightSigned.size(); ++j) {
                RingMonomialSignature sig;
                std::merge(
                    leftSigned[i].signature.begin(),
                    leftSigned[i].signature.end(),
                    rightSigned[j].signature.begin(),
                    rightSigned[j].signature.end(),
                    std::back_inserter(sig));
                int sign = leftSigned[i].sign * rightSigned[j].sign;
                productMonomials.push_back({sig, sign});
                productKernels.push_back(
                    buildSignedMonomialKernel(sig, sign, context));
            }
        }
        // mergeProof : leftAssoc(productKernels) = mergedCanonical, and
        // currentForm is structurally that left-associated sum.
        ExpressionPointer mergeProof =
            proveSignedMonomialSumEqualsCanonical(
                productMonomials, productKernels, mergedPoly,
                mergedCanonical, context, axiomNames);
        currentProof = buildEqualityTransitivity(
            universeLevel, carrierType,
            leftTimesRight, currentForm, mergedCanonical,
            currentProof, mergeProof);
        return currentProof;
    }

ExpressionPointer Elaborator::rewriteFlatSummandAtPosition(
        ExpressionPointer currentForm,
        size_t position, size_t totalCount,
        ExpressionPointer replacement,
        const RingNormalisationContext& context) {
        std::vector<ExpressionPointer> summands;
        flattenRingProduct(currentForm, context.addName, summands);
        if (summands.size() != totalCount) {
            throwElaborate(
                "`ring`: rewriteFlatSummandAtPosition: flatten "
                "count " + std::to_string(summands.size())
                + " != expected " + std::to_string(totalCount));
        }
        summands[position] = replacement;
        return assembleLeftAssociatedProduct(context.addName, summands);
    }

ExpressionPointer Elaborator::rewriteFlatSummandAtPositionProof(
        ExpressionPointer currentForm,
        size_t position, size_t totalCount,
        ExpressionPointer oldSummand,
        ExpressionPointer newSummand,
        ExpressionPointer summandProof,
        const RingNormalisationContext& context) {
        std::vector<ExpressionPointer> summands;
        flattenRingProduct(currentForm, context.addName, summands);
        if (summands.size() != totalCount) {
            throwElaborate(
                "`ring`: rewriteFlatSummandAtPositionProof: flatten "
                "count " + std::to_string(summands.size())
                + " != expected " + std::to_string(totalCount));
        }
        // Build the motive lambda. The body has the form of the flat
        // sum with summands[position] replaced by BoundVariable(0).
        // Lift other summands by 1 to account for the new binder.
        std::vector<ExpressionPointer> bodySummands;
        for (size_t k = 0; k < summands.size(); ++k) {
            if (k == position) {
                bodySummands.push_back(makeBoundVariable(0));
            } else {
                bodySummands.push_back(liftBoundVariables(summands[k], 1, 0));
            }
        }
        ExpressionPointer body = assembleLeftAssociatedProduct(
            context.addName, bodySummands);
        ExpressionPointer lambda = makeLambda(
            "_ring_summand_z", context.carrierType, body);
        return buildEqualityCongruenceSameCarrier(
            context.carrierUniverseLevel, context.carrierType, lambda,
            oldSummand, newSummand, summandProof);
    }

ExpressionPointer Elaborator::proveSignedProductEqualsMonomial(
        ExpressionPointer Li, ExpressionPointer Rj,
        const SignedMonomial& leftMono, const SignedMonomial& rightMono,
        const RingMonomialSignature& /*mergedSig*/, int mergedSign,
        ExpressionPointer targetMonomial,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // The "positive" base monomial kernels (no negate wrapper):
        ExpressionPointer Mi = buildSignedMonomialKernel(
            leftMono.signature, +1, context);
        ExpressionPointer Mj = buildSignedMonomialKernel(
            rightMono.signature, +1, context);
        // Start: Li * Rj. Goal: targetMonomial.
        // Move outer negates inside step by step until we have
        // (Mi * Mj) wrapped in 0..2 negates. Each negate-push is a
        // multiply_negate_left/right rewrite. Two negates collapse via
        // negate_negate.
        ExpressionPointer currentForm = buildRingOp(
            context.multiplyName, Li, Rj);
        ExpressionPointer currentProof = buildReflexivity(
            universeLevel, carrierType, currentForm);
        ExpressionPointer startForm = currentForm;
        // Both-negative fast path: (-Mi) * (-Mj) = Mi * Mj via
        // `Ring.negate_multiply_negate` applied to <carrier>.is_ring.
        // Falls through to the per-side multiply_negate_left/right +
        // negate_negate chain when the abstract isn't in scope.
        bool handledBothNegative = false;
        {
            if (leftMono.sign < 0 && rightMono.sign < 0
                && environment_.lookup("Ring.negate_multiply_negate") != nullptr
                && environment_.lookup(context.isRingName) != nullptr) {
                ExpressionPointer call = makeConstant(
                    "Ring.negate_multiply_negate");
                appendIsRingInstanceArgs(call, context);
                call = makeApplication(call, Mi);
                call = makeApplication(call, Mj);
                // call : (-Mi) * (-Mj) = Mi * Mj
                ExpressionPointer newForm = buildRingOp(
                    context.multiplyName, Mi, Mj);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, call);
                currentForm = newForm;
                handledBothNegative = true;
            }
        }
        // Step S1: if Li is -Mi, push the outer negate of Li outside the
        // product: Li * Rj = (-Mi) * Rj = -(Mi * Rj) via
        // multiply_negate_left.
        if (!handledBothNegative && leftMono.sign < 0) {
            ExpressionPointer call = buildRingMultiplyNegateProof(
                /*onLeft=*/true, Mi, Rj, context, axiomNames);
            // call : (-Mi) * Rj = -(Mi * Rj)
            ExpressionPointer newForm = buildRingNegate(
                context.negateName,
                buildRingOp(context.multiplyName, Mi, Rj));
            currentProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                startForm, currentForm, newForm,
                currentProof, call);
            currentForm = newForm;
        }
        // Step S2: if Rj is -Mj, push the negate around the product
        // outside as well.
        if (!handledBothNegative && rightMono.sign < 0) {
            // Two cases: the current "product part" is either
            //   Mi * Rj    (if Li was positive)
            //   Mi * Rj inside a negate wrapper (if Li was negative).
            if (leftMono.sign > 0) {
                // currentForm == Mi * Rj. Apply multiply_negate_right(Mi, Mj):
                // Mi * (-Mj) = -(Mi * Mj).
                ExpressionPointer call = buildRingMultiplyNegateProof(
                    /*onLeft=*/false, Mi, Mj, context, axiomNames);
                ExpressionPointer newForm = buildRingNegate(
                    context.negateName,
                    buildRingOp(context.multiplyName, Mi, Mj));
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, call);
                currentForm = newForm;
            } else {
                // currentForm == -(Mi * Rj) where Rj == -Mj.
                // Use congruence λz. -z, with proof Mi * Rj = -(Mi * Mj)
                // via multiply_negate_right.
                ExpressionPointer call = buildRingMultiplyNegateProof(
                    /*onLeft=*/false, Mi, Mj, context, axiomNames);
                ExpressionPointer innerOld = buildRingOp(
                    context.multiplyName, Mi, Rj);
                ExpressionPointer innerNew = buildRingNegate(
                    context.negateName,
                    buildRingOp(context.multiplyName, Mi, Mj));
                ExpressionPointer lambdaBody = buildRingNegate(
                    context.negateName, makeBoundVariable(0));
                ExpressionPointer lambda = makeLambda(
                    "_ring_negouter_z", carrierType, lambdaBody);
                ExpressionPointer congr =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        innerOld, innerNew, call);
                // newForm = -(- (Mi * Mj))
                ExpressionPointer newForm = buildRingNegate(
                    context.negateName, innerNew);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, congr);
                currentForm = newForm;
                // Then collapse via negate_negate.
                demandAxiomName(axiomNames.negateNegate,
                                  "negate_negate", context.carrierName);
                ExpressionPointer nnCall = ringConst(axiomNames.negateNegate);
                nnCall = makeApplication(nnCall,
                                            buildRingOp(context.multiplyName,
                                                          Mi, Mj));
                // nnCall : -(-(Mi*Mj)) = Mi*Mj
                ExpressionPointer collapsedForm = buildRingOp(
                    context.multiplyName, Mi, Mj);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, collapsedForm,
                    currentProof, nnCall);
                currentForm = collapsedForm;
            }
        }
        // After steps S1/S2, currentForm has one of:
        //   Mi * Mj                  (mergedSign == +1)
        //   -(Mi * Mj)               (mergedSign == -1)
        // (The (--) case landed at Mi*Mj after the two pushes + negate_negate.)
        // Now sort the factors of the inner product.
        // Get the inner product expression.
        ExpressionPointer innerProductForm;
        bool wrappedInNegate;
        if (mergedSign > 0) {
            innerProductForm = currentForm;
            wrappedInNegate = false;
        } else {
            // currentForm = -(Mi * Mj)
            auto* outerApp =
                std::get_if<Application>(&currentForm->node);
            if (!outerApp) {
                throwElaborate(
                    "`ring`: proveSignedProductEqualsMonomial: "
                    "negative branch has malformed shape");
            }
            innerProductForm = outerApp->argument;
            wrappedInNegate = true;
        }
        // Unit-strip: if either Mi or Mj is `oneConst` (built from an
        // empty signature), the inner product `Mi * Mj` simplifies via
        // multiply_one_left/right. The flatten/sort path below assumes
        // both factors are honest atom-products of equal arity to the
        // target; the unit case breaks that (Mi or Mj contributes zero
        // factors), so we handle it here and return early.
        //
        // This is what lets ring goals like `Integer.one * x = x`
        // elaborate -- and, transitively, what unblocks numeric-literal
        // recognition in the normaliser, since a literal `k` reduces
        // to `Integer.one + ... + Integer.one` and multiplies into
        // `Integer.one * x + ... + Integer.one * x`.
        {
            bool leftIsUnit = leftMono.signature.empty();
            bool rightIsUnit = rightMono.signature.empty();
            if (leftIsUnit || rightIsUnit) {
                ExpressionPointer newInner;
                ExpressionPointer rewriteProof;
                if (leftIsUnit) {
                    // `Integer.one * Mj = Mj` via one_multiply(Mj).
                    // (Also covers leftIsUnit && rightIsUnit: Mj is
                    // itself `Integer.one`, and the lemma still applies.)
                    demandAxiomName(axiomNames.oneMultiplyLeft,
                                      "one_multiply", context.carrierName);
                    rewriteProof = makeApplication(
                        ringConst(axiomNames.oneMultiplyLeft), Mj);
                    newInner = Mj;
                } else {
                    // `Mi * Integer.one = Mi` via multiply_one(Mi).
                    demandAxiomName(axiomNames.multiplyOneRight,
                                      "multiply_one", context.carrierName);
                    rewriteProof = makeApplication(
                        ringConst(axiomNames.multiplyOneRight), Mi);
                    newInner = Mi;
                }
                ExpressionPointer newForm;
                ExpressionPointer chainStep;
                if (wrappedInNegate) {
                    ExpressionPointer lambdaBody = buildRingNegate(
                        context.negateName, makeBoundVariable(0));
                    ExpressionPointer lambda = makeLambda(
                        "_ring_unitstrip_z", carrierType, lambdaBody);
                    chainStep = buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        innerProductForm, newInner, rewriteProof);
                    newForm = buildRingNegate(
                        context.negateName, newInner);
                } else {
                    chainStep = rewriteProof;
                    newForm = newInner;
                }
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, chainStep);
                currentForm = newForm;
                if (!structurallyEqual(currentForm, targetMonomial)) {
                    throwElaborate(
                        "`ring`: unit-strip produced form does not "
                        "match canonical target (internal error)");
                }
                return currentProof;
            }
        }
        // Flatten the inner product and sort factors.
        std::vector<ExpressionPointer> innerFactors;
        if (!flattenRingProduct(innerProductForm, context.multiplyName,
                                   innerFactors)) {
            throwElaborate(
                "`ring`: inner product not pure-multiply (internal)");
        }
        // The target product is built by buildCanonicalMonomial from
        // mergedSig and +1 sign. Use it to get the factor order we want.
        // (mergedSig is sort(Li.sig ++ Rj.sig).) Read off the canonical
        // factor list by flattening targetMonomial's "inner product" too.
        ExpressionPointer targetInner;
        if (mergedSign > 0) {
            targetInner = targetMonomial;
        } else {
            auto* outerApp =
                std::get_if<Application>(&targetMonomial->node);
            if (!outerApp) {
                throwElaborate(
                    "`ring`: target signed monomial malformed");
            }
            targetInner = outerApp->argument;
        }
        std::vector<ExpressionPointer> targetFactors;
        if (!flattenRingProduct(targetInner, context.multiplyName,
                                   targetFactors)) {
            throwElaborate(
                "`ring`: target inner product not pure-multiply");
        }
        if (innerFactors.size() != targetFactors.size()) {
            throwElaborate(
                "`ring`: factor count mismatch in monomial merge "
                "(internal error)");
        }
        // Reassociate innerProductForm to left-associated.
        ExpressionPointer innerLeftAssoc =
            assembleLeftAssociatedProduct(
                context.multiplyName, innerFactors);
        ExpressionPointer innerReassocProof;
        if (structurallyEqual(innerProductForm, innerLeftAssoc)) {
            innerReassocProof = buildReflexivity(
                universeLevel, carrierType, innerProductForm);
        } else {
            innerReassocProof = reassociateMultiplyLeftProof(
                innerProductForm, context, axiomNames);
        }
        // Sort innerFactors to target order.
        ExpressionPointer innerSortProof = sortMultiplyLeftAssocProof(
            innerFactors, targetFactors, context, axiomNames);
        ExpressionPointer innerSortedKernel = assembleLeftAssociatedProduct(
            context.multiplyName, targetFactors);
        ExpressionPointer innerChain = buildEqualityTransitivity(
            universeLevel, carrierType,
            innerProductForm, innerLeftAssoc, innerSortedKernel,
            innerReassocProof, innerSortProof);
        // Now innerChain : innerProductForm = innerSortedKernel.
        // If wrappedInNegate: apply congruence with λz. -z.
        ExpressionPointer outerChain;
        ExpressionPointer outerNewForm;
        if (wrappedInNegate) {
            ExpressionPointer lambdaBody = buildRingNegate(
                context.negateName, makeBoundVariable(0));
            ExpressionPointer lambda = makeLambda(
                "_ring_finalneg_z", carrierType, lambdaBody);
            outerChain = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambda,
                innerProductForm, innerSortedKernel, innerChain);
            outerNewForm = buildRingNegate(
                context.negateName, innerSortedKernel);
        } else {
            outerChain = innerChain;
            outerNewForm = innerSortedKernel;
        }
        currentProof = buildEqualityTransitivity(
            universeLevel, carrierType,
            startForm, currentForm, outerNewForm,
            currentProof, outerChain);
        currentForm = outerNewForm;
        if (!structurallyEqual(currentForm, targetMonomial)) {
            throwElaborate(
                "`ring`: signed-product merge ended with mismatch "
                "(internal error)");
        }
        return currentProof;
    }

ExpressionPointer Elaborator::proveNegateMerge(
        const RingPolynomial& innerPoly,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        if (innerPoly.empty()) {
            demandAxiomName(axiomNames.addZeroRight,
                              "add_zero/add_identity_right",
                              context.carrierName);
            demandAxiomName(axiomNames.addNegateLeft,
                              "add_negate_left", context.carrierName);
            ExpressionPointer zeroConst =
                ringConst(context.zeroName);
            ExpressionPointer negateZero = buildRingNegate(
                context.negateName, zeroConst);
            ExpressionPointer addZeroAtNegZero =
                makeApplication(
                    ringConst(axiomNames.addZeroRight), negateZero);
            ExpressionPointer negZeroPlusZero = buildRingOp(
                context.addName, negateZero, zeroConst);
            ExpressionPointer step1 = buildEqualitySymmetry(
                universeLevel, carrierType,
                negZeroPlusZero, negateZero, addZeroAtNegZero);
            ExpressionPointer step2 =
                makeApplication(
                    ringConst(axiomNames.addNegateLeft), zeroConst);
            return buildEqualityTransitivity(
                universeLevel, carrierType,
                negateZero, negZeroPlusZero, zeroConst,
                step1, step2);
        }
        ExpressionPointer innerCanonical =
            buildCanonicalPolynomial(innerPoly, context);
        RingPolynomial negatedPoly = innerPoly;
        ringPolynomialNegate(negatedPoly);
        ExpressionPointer negatedCanonical =
            buildCanonicalPolynomial(negatedPoly, context);
        ExpressionPointer startForm = buildRingNegate(
            context.negateName, innerCanonical);
        std::vector<SignedMonomial> innerSigned =
            polynomialToSignedMonomials(innerPoly);
        std::vector<ExpressionPointer> innerKernels;
        for (const auto& m : innerSigned) {
            innerKernels.push_back(buildSignedMonomialKernel(
                m.signature, m.sign, context));
        }
        // Phase 1: push outer negate inward through all `+`.
        // After phase 1: form = negate(s_0) + negate(s_1) + ... + negate(s_{k-1})
        //                  (left-associated)
        // Special case: k == 1, no `+` to push through.
        ExpressionPointer currentForm = startForm;
        ExpressionPointer currentProof = buildReflexivity(
            universeLevel, carrierType, currentForm);
        if (innerSigned.size() > 1) {
            demandAxiomName(axiomNames.negateAdd, "negate_add",
                              context.carrierName);
            // Build running prefixes: prefix[i] = s_0 + ... + s_i for
            // i = 0..k-1. prefix[k-1] = innerCanonical.
            std::vector<ExpressionPointer> runningPrefix;
            runningPrefix.push_back(innerKernels[0]);
            for (size_t i = 1; i < innerSigned.size(); ++i) {
                runningPrefix.push_back(buildRingOp(
                    context.addName, runningPrefix[i - 1], innerKernels[i]));
            }
            // Walk i from k-1 down to 1: push negate through the
            // outermost `+` of `negate(prefix[i])`.
            //
            // At step i, currentForm has the shape:
            //   negate(prefix[i]) + negate(s_{i+1}) + ... + negate(s_{k-1})
            //                                       (left-associated)
            // (For i == k-1, it's just negate(prefix[k-1]) = negate(innerCanonical).)
            //
            // Apply negate_add(prefix[i-1], s_i) :
            //   negate(prefix[i-1] + s_i) = negate(prefix[i-1]) + negate(s_i)
            // i.e. negate(prefix[i]) = negate(prefix[i-1]) + negate(s_i).
            // Lift via congruence with λz. z + tail.
            for (size_t i = innerSigned.size(); i > 1; --i) {
                size_t idx = i - 1;  // index of s_i in innerKernels
                ExpressionPointer subjectPrefix = runningPrefix[idx - 1];
                ExpressionPointer subjectSi = innerKernels[idx];
                ExpressionPointer negAddCall = ringConst(axiomNames.negateAdd);
                negAddCall = makeApplication(negAddCall, subjectPrefix);
                negAddCall = makeApplication(negAddCall, subjectSi);
                // negAddCall has type
                //   negate(prefix[idx-1] + s_idx) = negate(prefix[idx-1]) + negate(s_idx)
                ExpressionPointer xExpr = buildRingNegate(
                    context.negateName, runningPrefix[idx]);
                ExpressionPointer yExpr = buildRingOp(
                    context.addName,
                    buildRingNegate(context.negateName, runningPrefix[idx - 1]),
                    buildRingNegate(context.negateName, innerKernels[idx]));
                // Tail (already-pushed summands): negate(s_{idx+1}) + ... + negate(s_{k-1})
                std::vector<ExpressionPointer> tail;
                for (size_t j = idx + 1; j < innerSigned.size(); ++j) {
                    tail.push_back(buildRingNegate(
                        context.negateName, innerKernels[j]));
                }
                ExpressionPointer stepProof;
                ExpressionPointer newForm;
                if (tail.empty()) {
                    stepProof = negAddCall;
                    newForm = yExpr;
                } else {
                    // `currentForm` is LEFT-associated:
                    //   ((negate(prefix[idx]) + tail[0]) + tail[1]) + …
                    // so the element being rewritten (negate(prefix[idx]),
                    // = xExpr) sits at the BOTTOM-LEFT of the spine, not as
                    // the left child of the top `+`. The congruence lambda
                    // must therefore rebuild that same left spine around the
                    // hole — `((z + tail[0]) + tail[1]) + …` — NOT `z + tail`.
                    // The old `z + tail` form attached the whole tail as one
                    // right subtree, which mis-associates the moment the tail
                    // has ≥2 elements (≥3 unit monomials, i.e. coefficients >
                    // 1 across multiple monomials): the step proof's type then
                    // failed to match the left-associated `currentForm`. Both
                    // `lambdaBody` (over the lifted tail) and `newForm` (over
                    // the tail) fold left, matching the invariant.
                    ExpressionPointer lambdaBody = makeBoundVariable(0);
                    for (const auto& tailSummand : tail) {
                        lambdaBody = buildRingOp(
                            context.addName, lambdaBody,
                            liftBoundVariables(tailSummand, 1, 0));
                    }
                    ExpressionPointer lambda = makeLambda(
                        "_ring_negpush_z", carrierType, lambdaBody);
                    stepProof = buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        xExpr, yExpr, negAddCall);
                    newForm = yExpr;
                    for (const auto& tailSummand : tail) {
                        newForm = buildRingOp(
                            context.addName, newForm, tailSummand);
                    }
                }
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newForm,
                    currentProof, stepProof);
                currentForm = newForm;
            }
            // Reassociate currentForm to flat left-associated sum of
            // negate(innerKernels[i]) for i=0..k-1.
            std::vector<ExpressionPointer> flatNeg;
            for (const auto& ik : innerKernels) {
                flatNeg.push_back(buildRingNegate(context.negateName, ik));
            }
            ExpressionPointer flatNegLeftAssoc = assembleLeftAssociatedProduct(
                context.addName, flatNeg);
            if (!structurallyEqual(currentForm, flatNegLeftAssoc)) {
                ExpressionPointer reassoc = reassociateSumLeftProof(
                    currentForm, context, axiomNames);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, flatNegLeftAssoc,
                    currentProof, reassoc);
                currentForm = flatNegLeftAssoc;
            }
        } else {
            // k == 1; currentForm == negate(innerKernels[0]) already.
            // Continue.
        }
        // Phase 2: simplify each summand. innerKernels[i] is either:
        //   * positive monomial M (sign = +1): negate(M) is canonical
        //     form of -M. No further work.
        //   * negative monomial -M = negate(M) (sign = -1, the kernel
        //     starts with `negate`). Then negate(negate(M)) = M via
        //     negate_negate.
        for (size_t i = 0; i < innerSigned.size(); ++i) {
            if (innerSigned[i].sign > 0) continue;
            demandAxiomName(axiomNames.negateNegate, "negate_negate",
                              context.carrierName);
            // The kernel innerKernels[i] is `negate(M_pos)` where M_pos
            // is the positive form. So negate(negate(M_pos)) → M_pos.
            ExpressionPointer M_pos = buildSignedMonomialKernel(
                innerSigned[i].signature, +1, context);
            ExpressionPointer oldSummand = buildRingNegate(
                context.negateName, innerKernels[i]);
            ExpressionPointer newSummand = M_pos;
            // The proof: negate(negate(M_pos)) = M_pos via negate_negate(M_pos).
            ExpressionPointer nnCall = ringConst(axiomNames.negateNegate);
            nnCall = makeApplication(nnCall, M_pos);
            // Apply at position i in the flat sum.
            if (innerSigned.size() == 1) {
                // currentForm == oldSummand. Direct.
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newSummand,
                    currentProof, nnCall);
                currentForm = newSummand;
            } else {
                ExpressionPointer congrProof =
                    rewriteFlatSummandAtPositionProof(
                        currentForm, i, innerSigned.size(),
                        oldSummand, newSummand, nnCall, context);
                ExpressionPointer newCurrent =
                    rewriteFlatSummandAtPosition(
                        currentForm, i, innerSigned.size(),
                        newSummand, context);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    startForm, currentForm, newCurrent,
                    currentProof, congrProof);
                currentForm = newCurrent;
            }
        }
        // Now each summand is the canonical signed form of the
        // sign-flipped monomial — directly the kernel of -innerPoly's
        // monomials, in the same signature order.
        if (!structurallyEqual(currentForm, negatedCanonical)) {
            throwElaborate(
                "`ring`: proveNegateMerge final form mismatched "
                "negated canonical (internal error)");
        }
        return currentProof;
    }

ExpressionPointer Elaborator::elaborateRingByNormalisation(
        const std::vector<LocalBinder>& /*localBinders*/,
        ExpressionPointer leftEndpoint,
        ExpressionPointer rightEndpoint,
        ExpressionPointer carrierType,
        LevelPointer carrierUniverseLevel,
        const std::string& carrierName,
        int line) {
        RingScheme scheme = computeRingScheme(carrierType);
        RingStructurePrefixGuard prefixGuard(*this, scheme.structurePrefix);
        RingNormalisationContext context;
        context.carrierName = carrierName;
        context.carrierType = carrierType;
        context.carrierUniverseLevel = carrierUniverseLevel;
        context.opNamespace   = scheme.opNamespace;
        context.isRingName    = scheme.opNamespace + ".is_ring";
        context.addName       = scheme.opNamespace + ".add";
        context.multiplyName  = scheme.opNamespace + ".multiply";
        context.negateName    = scheme.opNamespace + ".negate";
        context.subtractName  = scheme.opNamespace + ".subtract";
        context.zeroName      = scheme.opNamespace + ".zero";
        context.oneName       = scheme.opNamespace + ".one";
        populateRingEmbeddingChain(context);
        // Sanity-check the carrier supports the v2 vocabulary. We only
        // require add + multiply at the moment — zero, one, and negate
        // are optional (a goal that doesn't mention them won't need
        // them).
        if (environment_.lookup(context.addName) == nullptr
            || environment_.lookup(context.multiplyName) == nullptr) {
            throwElaborate(
                "`ring`: carrier `" + carrierName
                + "` does not have both `.add` and `.multiply` in scope");
        }
        RingPolynomial leftPolynomial =
            normaliseToRingPolynomial(leftEndpoint, context);
        RingPolynomial rightPolynomial =
            normaliseToRingPolynomial(rightEndpoint, context);
        if (!ringPolynomialsAgree(leftPolynomial, rightPolynomial)) {
            throwElaborate(
                "`ring`: the two sides do not have equal polynomial "
                "canonical forms over `" + carrierName + "` — they "
                "are not equal as commutative-ring expressions"
                + buildFingerprintDiagnostic(
                      leftEndpoint, rightEndpoint, carrierName));
        }
        // No coefficient guard: the canonical form expands every
        // (sig, coef) entry into |coef| unit monomials, so the
        // proof generators only ever see signs in {-1, +1}.
        // Resolve carrier-specific axiom names. Names that aren't
        // needed for this particular goal are allowed to remain
        // unresolved; the merge helpers `demandAxiomName` only what
        // they actually use.
        RingLawNames axiomNames =
            resolveRingLawNames(scheme.opNamespace);
        // We always need add/multiply assoc and commute (used by
        // every non-trivial merge step).
        demandAxiomName(axiomNames.addAssociative,
                          "add_associative", carrierName);
        demandAxiomName(axiomNames.addCommutative,
                          "add_commutative", carrierName);
        demandAxiomName(axiomNames.multiplyAssociative,
                          "multiply_associative", carrierName);
        demandAxiomName(axiomNames.multiplyCommutative,
                          "multiply_commutative", carrierName);
        // Build per-side proofs that each endpoint equals canonical.
        RingPolynomial leftPolyOut, rightPolyOut;
        ExpressionPointer leftProof = proveEqualsCanonical(
            leftEndpoint, context, axiomNames, leftPolyOut);
        ExpressionPointer rightProof = proveEqualsCanonical(
            rightEndpoint, context, axiomNames, rightPolyOut);
        ExpressionPointer canonicalKernel =
            buildCanonicalPolynomial(leftPolynomial, context);
        // canonicalKernel built from leftPolynomial — equal to the
        // one produced from rightPolynomial since the polynomials
        // agree (we just checked).
        // rightProof : rightEndpoint = canonicalKernel; flip via sym.
        ExpressionPointer rightProofSymm = buildEqualitySymmetry(
            carrierUniverseLevel, carrierType,
            rightEndpoint, canonicalKernel, std::move(rightProof));
        ExpressionPointer finalProof = buildEqualityTransitivity(
            carrierUniverseLevel, carrierType,
            leftEndpoint, canonicalKernel, rightEndpoint,
            std::move(leftProof), std::move(rightProofSymm));
        (void)line;
        return finalProof;
    }

Elaborator::RingMonomialSignature Elaborator::contractMonomialSignature(
        const RingMonomialSignature& signature,
        const std::vector<FieldReciprocalPair>& pairs,
        std::vector<int>& pairsRemovedOut) {
        // Count occurrences of each atom hash in the signature.
        std::unordered_map<uint64_t, int> counts;
        for (uint64_t hash : signature) ++counts[hash];
        pairsRemovedOut.assign(pairs.size(), 0);
        // For each pair, contract.
        for (size_t i = 0; i < pairs.size(); ++i) {
            int baseCount = counts[pairs[i].baseHash];
            int reciprocalCount = counts[pairs[i].reciprocalHash];
            int toRemove = std::min(baseCount, reciprocalCount);
            if (toRemove > 0) {
                counts[pairs[i].baseHash] -= toRemove;
                counts[pairs[i].reciprocalHash] -= toRemove;
                pairsRemovedOut[i] = toRemove;
            }
        }
        // Rebuild signature from counts. Preserve the order of distinct
        // hashes from the original signature (deduplicating).
        RingMonomialSignature result;
        result.reserve(signature.size());
        std::unordered_map<uint64_t, int> emitted;
        for (uint64_t hash : signature) {
            int targetCount = counts[hash];
            int& alreadyEmitted = emitted[hash];
            if (alreadyEmitted < targetCount) {
                result.push_back(hash);
                ++alreadyEmitted;
            }
        }
        // The signature must remain sorted (since `RingMonomialSignature`
        // is sorted by hash). The original signature was sorted; rebuild
        // by walking sorted-hash to count.
        std::sort(result.begin(), result.end());
        return result;
    }

Elaborator::RingPolynomial Elaborator::buildContractedPolynomial(
        const RingPolynomial& original,
        const std::vector<FieldReciprocalPair>& pairs,
        std::vector<FieldMonomialContraction>& contractionRecords) {
        RingPolynomial contracted;
        contractionRecords.clear();
        for (const auto& entry : original) {
            std::vector<int> pairsRemoved;
            RingMonomialSignature newSig =
                contractMonomialSignature(entry.first, pairs, pairsRemoved);
            contracted[newSig] += entry.second;
            contractionRecords.push_back({
                entry.first, entry.second,
                newSig, std::move(pairsRemoved)});
        }
        ringPolynomialCompact(contracted);
        return contracted;
    }

ExpressionPointer Elaborator::buildFactorContractionProof(
        const std::vector<ExpressionPointer>& factorList,
        const std::vector<FieldReciprocalPair>& pairs,
        const std::vector<int>& pairsRemoved,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        const std::string& multiplyName = context.multiplyName;
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        if (factorList.empty()) {
            throwElaborate(
                "`field`: factor list empty in contraction proof "
                "(internal error)");
        }
        // Step 1: build surviving factor list.
        //
        // Remove instances of (t_i, r_i) from factorList — we remove
        // pairsRemoved[i] copies of t_i and pairsRemoved[i] copies of
        // r_i. Use a multiset count.
        std::vector<bool> keep(factorList.size(), true);
        std::vector<size_t> removedTIndices;       // indices in factorList of removed t_i's
        std::vector<size_t> removedRIndices;       // indices in factorList of removed r_i's
        std::vector<size_t> pairIndexForRemovedT;  // pair index per removed t (parallel to removedTIndices)
        for (size_t pi = 0; pi < pairs.size(); ++pi) {
            int toRemove = pairsRemoved[pi];
            if (toRemove <= 0) continue;
            int removed = 0;
            for (size_t fi = 0; fi < factorList.size() && removed < toRemove; ++fi) {
                if (!keep[fi]) continue;
                if (factorList[fi]->hash == pairs[pi].baseHash) {
                    keep[fi] = false;
                    removedTIndices.push_back(fi);
                    pairIndexForRemovedT.push_back(pi);
                    ++removed;
                }
            }
            if (removed < toRemove) {
                throwElaborate(
                    "`field`: requested removal of more `t` copies than "
                    "present (internal error)");
            }
            removed = 0;
            for (size_t fi = 0; fi < factorList.size() && removed < toRemove; ++fi) {
                if (!keep[fi]) continue;
                if (factorList[fi]->hash == pairs[pi].reciprocalHash) {
                    keep[fi] = false;
                    removedRIndices.push_back(fi);
                    ++removed;
                }
            }
            if (removed < toRemove) {
                throwElaborate(
                    "`field`: requested removal of more `r` copies than "
                    "present (internal error)");
            }
        }
        // Build the surviving factor list and the rearranged list.
        std::vector<ExpressionPointer> survivors;
        for (size_t fi = 0; fi < factorList.size(); ++fi) {
            if (keep[fi]) survivors.push_back(factorList[fi]);
        }
        // The rearranged list: survivors first, then for each removed
        // pair the (t, r) pair appended.
        std::vector<ExpressionPointer> rearranged = survivors;
        // Walk removedTIndices in order; each corresponds to a pair.
        for (size_t k = 0; k < removedTIndices.size(); ++k) {
            size_t pi = pairIndexForRemovedT[k];
            rearranged.push_back(pairs[pi].baseAtom);
            rearranged.push_back(pairs[pi].reciprocalAtom);
        }
        if (rearranged.size() != factorList.size()) {
            throwElaborate(
                "`field`: rearranged factor count mismatch (internal error)");
        }
        // Step 3: prove factorList-product = rearranged-product.
        RingAxiomNames multiplyAxioms{
            multiplyName, axiomNames.multiplyAssociative,
            axiomNames.multiplyCommutative};
        ExpressionPointer originalProduct =
            assembleLeftAssociatedProduct(multiplyName, factorList);
        ExpressionPointer rearrangedProduct =
            assembleLeftAssociatedProduct(multiplyName, rearranged);
        ExpressionPointer reassocProof;
        if (factorList.size() == 1) {
            // Single factor, no cancellations should be possible
            // (a single factor can be either t or r alone, not both).
            if (removedTIndices.size() != 0) {
                throwElaborate(
                    "`field`: single-factor monomial with pair removal "
                    "(internal error)");
            }
            return buildReflexivity(universeLevel, carrierType, originalProduct);
        } else {
            reassocProof = proveProductEqualsSorted(
                originalProduct, factorList, rearranged,
                multiplyAxioms, carrierType, universeLevel, /*line*/0);
        }
        // Step 4: cancel pairs from the tail.
        // Current form: rearrangedProduct =
        //     (((survivors-product) * t_1) * r_1) * t_2 * r_2 * ... * t_k * r_k
        // (all left-associated). We peel right-to-left.
        //
        // If there are zero removed pairs, we should match survivors == rearranged
        // == factorList exactly, and reassocProof : factorList-product = survivors-product.
        if (removedTIndices.empty()) {
            return reassocProof;
        }
        // Need: at least one survivor (so the cancellation has a prefix
        // to land in). If there are zero survivors, the contracted form
        // is `1`, but we still need to handle the cancellation against
        // `1`. We handle this by using the survivor list including a
        // synthetic `1` at the front when needed.
        //
        // Concretely: if survivors is empty, the original factor list
        // was entirely (t, r) pairs. Then we need to prove that
        // `t_1 * r_1 * ... * t_k * r_k = 1`. We use a sequence of
        // collapses, starting with `(t_1 * r_1) = 1` (the innermost pair)
        // and lifting outward.
        ExpressionPointer survivorsProduct;
        bool noSurvivors = survivors.empty();
        ExpressionPointer oneConst = ringConst(context.oneName);
        if (noSurvivors) {
            // We'll start with the trick: rearranged-product =
            // 1 * (t_1 * r_1 * ... * t_k * r_k). Hmm, but rearranged-product
            // is just t_1 * r_1 * ... * t_k * r_k (no leading 1). We'd
            // need to insert a 1 — that's a `one_multiply` reverse.
            //
            // Cleanest: prove the equality by induction-style:
            //   first pair: t_1 * r_1 = 1, by multipliesProof of the matching pair.
            //   subsequent pairs (k > 1): we have current form
            //     (((t_1 * r_1) * t_2) * r_2) * ... * t_k * r_k
            //     associativity collapse: (... * t_k) * r_k = ... * (t_k * r_k)
            //     simplify (t_k * r_k) → 1
            //     simplify (... * 1) → ...
            //   recurse.
            //
            // Since there are at least 2 factors in `rearranged`, and the
            // first 2 are a (t, r) pair, the base case can be: leave
            // the (t_1, r_1) prefix intact while we collapse pairs to the
            // right; at the very end, collapse the last remaining pair
            // (t_1, r_1) to 1.
            //
            // Simpler implementation: do exactly the same cancellation
            // loop as the survivor case, but treat the first (t_1, r_1)
            // pair as a "synthetic survivor" — i.e. start by collapsing
            // pairs 2..k, leaving prefix = t_1 * r_1. Then a final step
            // collapses (t_1 * r_1) = 1.
            //
            // Implementation: start `currentForm = rearrangedProduct =
            //  (((t_1*r_1)*t_2)*r_2)*...*t_k*r_k`. Collapse pairs from
            // the right.
            survivorsProduct =
                assembleLeftAssociatedProduct(multiplyName,
                    {pairs[pairIndexForRemovedT[0]].baseAtom,
                     pairs[pairIndexForRemovedT[0]].reciprocalAtom});
        } else if (survivors.size() == 1) {
            survivorsProduct = survivors[0];
        } else {
            survivorsProduct = assembleLeftAssociatedProduct(
                multiplyName, survivors);
        }
        // The `currentForm` represents the kernel-level current shape.
        ExpressionPointer currentForm = rearrangedProduct;
        ExpressionPointer chainProof = reassocProof;
        // We need `multiply_associative`, `multiply_one`/`one_multiply`,
        // and the cancellation lemma (the `multipliesProof` per pair).
        demandAxiomName(axiomNames.multiplyOneRight,
                          "multiply_one/multiply_identity_right",
                          context.carrierName);
        demandAxiomName(axiomNames.multiplyAssociative,
                          "multiply_associative", context.carrierName);
        // Track remaining (t, r) suffix: how many pairs still need to
        // be cancelled. Walk right-to-left.
        // The number of pairs total:
        size_t totalPairs = removedTIndices.size();
        // After cancellation k pairs, current form is:
        //   prefix * (remaining_pairs_t1) * (remaining_pairs_r1) * ...
        // We index pairs in REVERSE order of cancellation, from the
        // rightmost (last appended) to the leftmost.
        for (size_t step = 0; step < totalPairs; ++step) {
            // The rightmost remaining pair index in pairIndexForRemovedT
            // is `totalPairs - 1 - step`. Get t and r.
            size_t pairListIdx = totalPairs - 1 - step;
            // The "prefix" (left of the trailing (t, r) pair) is:
            //   if noSurvivors and this is the last (innermost) pair:
            //     no prefix — `currentForm` is exactly `t * r`
            //   else:
            //     prefix is whatever sits to the left of the last (t, r)
            //
            // Build prefix as a left-associated product of the relevant
            // pieces.
            std::vector<ExpressionPointer> prefixPieces;
            if (!noSurvivors) {
                for (const auto& s : survivors) prefixPieces.push_back(s);
            }
            // Append remaining pairs (those still to be cancelled,
            // before this step's pair).
            for (size_t earlier = 0; earlier < pairListIdx; ++earlier) {
                size_t epi = pairIndexForRemovedT[earlier];
                prefixPieces.push_back(pairs[epi].baseAtom);
                prefixPieces.push_back(pairs[epi].reciprocalAtom);
            }
            size_t curPairIdx = pairIndexForRemovedT[pairListIdx];
            ExpressionPointer tExpr = pairs[curPairIdx].baseAtom;
            ExpressionPointer rExpr = pairs[curPairIdx].reciprocalAtom;
            ExpressionPointer multipliesProof =
                pairs[curPairIdx].multipliesProof;
            // Case A: prefix is empty. currentForm == t * r.
            if (prefixPieces.empty()) {
                // currentForm should equal `t * r`. Apply multiplies
                // proof to get `1`.
                ExpressionPointer tTimesR = buildRingOp(
                    multiplyName, tExpr, rExpr);
                if (!structurallyEqual(currentForm, tTimesR)) {
                    throwElaborate(
                        "`field`: cancellation step expected `t*r` "
                        "form but got different shape (internal error)");
                }
                // currentForm = t * r, multipliesProof : t * r = 1.
                chainProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    originalProduct, currentForm, oneConst,
                    chainProof, multipliesProof);
                currentForm = oneConst;
                continue;
            }
            // Case B: prefix non-empty. currentForm has shape
            //   ((prefix-product) * t) * r
            // (because all factors are left-associated, and this pair
            // is at the very end).
            ExpressionPointer prefixProduct;
            if (prefixPieces.size() == 1) {
                prefixProduct = prefixPieces[0];
            } else {
                prefixProduct = assembleLeftAssociatedProduct(
                    multiplyName, prefixPieces);
            }
            // Expected currentForm = ((prefixProduct) * t) * r.
            ExpressionPointer expectedShape = buildRingOp(
                multiplyName,
                buildRingOp(multiplyName, prefixProduct, tExpr),
                rExpr);
            if (!structurallyEqual(currentForm, expectedShape)) {
                throwElaborate(
                    "`field`: cancellation step expected "
                    "`(prefix * t) * r` form (internal error)");
            }
            // Step B.1: associativity:
            //   (prefixProduct * t) * r = prefixProduct * (t * r)
            ExpressionPointer assocProof = ringConst(axiomNames.multiplyAssociative);
            assocProof = makeApplication(assocProof, prefixProduct);
            assocProof = makeApplication(assocProof, tExpr);
            assocProof = makeApplication(assocProof, rExpr);
            ExpressionPointer formA = buildRingOp(
                multiplyName, prefixProduct,
                buildRingOp(multiplyName, tExpr, rExpr));
            // Step B.2: congruence with λz. prefix * z, substitute
            //   t * r ← 1 via multipliesProof.
            ExpressionPointer prefixLifted =
                liftBoundVariables(prefixProduct, 1, 0);
            ExpressionPointer lambdaBody = buildRingOp(
                multiplyName, prefixLifted, makeBoundVariable(0));
            ExpressionPointer lambda = makeLambda(
                "_field_cancel_z", carrierType, lambdaBody);
            ExpressionPointer tTimesR = buildRingOp(
                multiplyName, tExpr, rExpr);
            ExpressionPointer congrB = buildEqualityCongruenceSameCarrier(
                universeLevel, carrierType, lambda,
                tTimesR, oneConst, multipliesProof);
            ExpressionPointer formB = buildRingOp(
                multiplyName, prefixProduct, oneConst);
            // Step B.3: multiply_one(prefixProduct) : prefix * 1 = prefix.
            ExpressionPointer multOneProof = ringConst(axiomNames.multiplyOneRight);
            multOneProof = makeApplication(multOneProof, prefixProduct);
            // Compose: currentForm = formA = formB = prefixProduct.
            ExpressionPointer stepAB = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formA, formB,
                assocProof, congrB);
            ExpressionPointer stepABC = buildEqualityTransitivity(
                universeLevel, carrierType,
                currentForm, formB, prefixProduct,
                stepAB, multOneProof);
            // Chain with `originalProduct = currentForm`.
            chainProof = buildEqualityTransitivity(
                universeLevel, carrierType,
                originalProduct, currentForm, prefixProduct,
                chainProof, stepABC);
            currentForm = prefixProduct;
        }
        // After all cancellations, currentForm should equal
        // survivorsProduct (or, if noSurvivors and we cancelled all
        // pairs, `oneConst`).
        ExpressionPointer expectedFinal;
        if (noSurvivors) {
            expectedFinal = oneConst;
        } else if (survivors.size() == 1) {
            expectedFinal = survivors[0];
        } else {
            expectedFinal = assembleLeftAssociatedProduct(
                multiplyName, survivors);
        }
        if (!structurallyEqual(currentForm, expectedFinal)) {
            throwElaborate(
                "`field`: cancellation ended at unexpected form "
                "(internal error)");
        }
        return chainProof;
    }

ExpressionPointer Elaborator::buildMonomialContractionProof(
        const RingMonomialSignature& originalSignature,
        int coefficient,
        const RingMonomialSignature& contractedSignature,
        const std::vector<int>& pairsRemoved,
        const std::vector<FieldReciprocalPair>& pairs,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // No pair removals: nothing to do.
        bool anyRemoval = false;
        for (int n : pairsRemoved) if (n > 0) { anyRemoval = true; break; }
        ExpressionPointer monomialKernel = buildCanonicalMonomial(
            originalSignature, coefficient, context);
        if (!anyRemoval) {
            return buildReflexivity(universeLevel, carrierType, monomialKernel);
        }
        ExpressionPointer contractedKernel = buildCanonicalMonomial(
            contractedSignature, coefficient, context);
        // Build the factor list (kernel terms) for the original
        // monomial. The signature is sorted by hash; look up each.
        std::vector<ExpressionPointer> originalFactors;
        originalFactors.reserve(originalSignature.size());
        for (uint64_t h : originalSignature) {
            auto it = context.atoms.find(h);
            if (it == context.atoms.end()) {
                throwElaborate(
                    "`field`: atom hash missing during contraction "
                    "(internal error)");
            }
            originalFactors.push_back(it->second);
        }
        // Build the contracted factor list.
        std::vector<ExpressionPointer> contractedFactors;
        contractedFactors.reserve(contractedSignature.size());
        for (uint64_t h : contractedSignature) {
            auto it = context.atoms.find(h);
            if (it == context.atoms.end()) {
                throwElaborate(
                    "`field`: atom hash missing during contraction "
                    "(internal error)");
            }
            contractedFactors.push_back(it->second);
        }
        // Factor-product proof: original-product = contracted-product.
        // Use buildFactorContractionProof.
        if (originalFactors.empty()) {
            throwElaborate(
                "`field`: empty original factor list with removals "
                "(internal error)");
        }
        ExpressionPointer factorProof = buildFactorContractionProof(
            originalFactors, pairs, pairsRemoved, context, axiomNames);
        // Now lift through the coefficient/sign wrap.
        // buildCanonicalMonomial structure:
        //   magnitude 1 + non-empty factors: monomial = factor-product.
        //   magnitude 1 + empty factors:     monomial = `one`.
        // Coefficient < 0 wraps in negate.
        //
        // Our case: anyRemoval == true means original had >= 2 factors
        // (at least one (t, r) pair). So originalFactors non-empty,
        // monomialKernel = factor-product or -factor-product.
        // The contracted may have empty factor list (everything cancelled).
        //
        // Case 1: coefficient = +1, both non-empty.
        //   monomialKernel = original-factor-product.
        //   contractedKernel = contracted-factor-product.
        //   Proof = factorProof.
        // Case 2: coefficient = +1, contracted factors empty.
        //   monomialKernel = original-factor-product.
        //   contractedKernel = `one`.
        //   factorProof : original-product = `one`. ✓
        // Case 3: coefficient = -1, both non-empty.
        //   monomialKernel = -(original-factor-product).
        //   contractedKernel = -(contracted-factor-product).
        //   Apply congruence λz. -z to factorProof.
        // Case 4: coefficient = -1, contracted empty.
        //   monomialKernel = -(original-factor-product).
        //   contractedKernel = -(one).
        //   Apply congruence λz. -z.
        if (coefficient == 1) {
            // monomialKernel is the original factor product (or `one`
            // if empty original factors — but we asserted non-empty).
            // The contracted kernel is contracted-factor-product (or
            // `one` if empty). buildFactorContractionProof returns the
            // proof at the factor-product level, which matches.
            //
            // However: buildCanonicalMonomial(empty, +1) returns `one`,
            // and our contracted-factor-product when empty is also `one`
            // since assembleLeftAssociatedProduct isn't called on empty.
            // We need to verify the shapes match what buildCanonicalMonomial
            // produces.
            //
            // Verify by comparing structurally.
            ExpressionPointer originalProduct =
                assembleLeftAssociatedProduct(
                    context.multiplyName, originalFactors);
            ExpressionPointer contractedProduct;
            if (contractedFactors.empty()) {
                contractedProduct = ringConst(context.oneName);
            } else if (contractedFactors.size() == 1) {
                contractedProduct = contractedFactors[0];
            } else {
                contractedProduct = assembleLeftAssociatedProduct(
                    context.multiplyName, contractedFactors);
            }
            // buildFactorContractionProof returns proof of
            //   originalProduct = contractedProduct
            // (or = oneConst if everything cancelled). Match.
            if (!structurallyEqual(monomialKernel, originalProduct)) {
                throwElaborate(
                    "`field`: monomial kernel mismatch (coeff +1) "
                    "(internal error)");
            }
            if (!structurallyEqual(contractedKernel, contractedProduct)) {
                throwElaborate(
                    "`field`: contracted kernel mismatch (coeff +1) "
                    "(internal error)");
            }
            return factorProof;
        }
        // coefficient == -1.
        ExpressionPointer originalProduct =
            assembleLeftAssociatedProduct(
                context.multiplyName, originalFactors);
        ExpressionPointer contractedProduct;
        if (contractedFactors.empty()) {
            contractedProduct = ringConst(context.oneName);
        } else if (contractedFactors.size() == 1) {
            contractedProduct = contractedFactors[0];
        } else {
            contractedProduct = assembleLeftAssociatedProduct(
                context.multiplyName, contractedFactors);
        }
        // Lambda: λz. negate(z).
        ExpressionPointer lambdaBody = buildRingNegate(
            context.negateName, makeBoundVariable(0));
        ExpressionPointer lambda = makeLambda(
            "_field_neg_z", carrierType, lambdaBody);
        ExpressionPointer negCongr = buildEqualityCongruenceSameCarrier(
            universeLevel, carrierType, lambda,
            originalProduct, contractedProduct, factorProof);
        return negCongr;
    }

ExpressionPointer Elaborator::buildPolynomialContractionProof(
        const RingPolynomial& originalPoly,
        const RingPolynomial& contractedPoly,
        const std::vector<FieldMonomialContraction>& contractionRecords,
        const std::vector<FieldReciprocalPair>& pairs,
        const RingNormalisationContext& context,
        const RingLawNames& axiomNames) {
        ExpressionPointer carrierType = context.carrierType;
        LevelPointer universeLevel = context.carrierUniverseLevel;
        // No-collision assumption: contractedPoly has the same number
        // of monomials as the original (since each original monomial
        // maps to a unique contracted signature, with the same coefficient).
        if (originalPoly.size() != contractedPoly.size()) {
            throwElaborate(
                "`field`: contracted polynomial has like-term "
                "collisions across distinct original monomials — not "
                "yet supported by the field tactic. (This happens "
                "when the equation requires combining contracted "
                "monomials.)");
        }
        // Edge case: empty polynomial.
        if (originalPoly.empty()) {
            // canonical of empty = zero. Reflexivity.
            return buildReflexivity(universeLevel, carrierType,
                                      ringConst(context.zeroName));
        }
        // Build per-monomial kernels and per-monomial contraction proofs.
        // Iterate originalPoly in canonical order (std::map order on signature).
        std::vector<ExpressionPointer> originalMonomialKernels;
        std::vector<ExpressionPointer> contractedMonomialKernels;
        std::vector<ExpressionPointer> perMonomialProofs;
        // Build a lookup: original sig → contraction record.
        std::map<RingMonomialSignature, size_t> recordIndex;
        for (size_t i = 0; i < contractionRecords.size(); ++i) {
            recordIndex[contractionRecords[i].originalSignature] = i;
        }
        for (const auto& entry : originalPoly) {
            auto it = recordIndex.find(entry.first);
            if (it == recordIndex.end()) {
                throwElaborate(
                    "`field`: contraction record missing for original "
                    "signature (internal error)");
            }
            const FieldMonomialContraction& rec =
                contractionRecords[it->second];
            ExpressionPointer originalKernel = buildCanonicalMonomial(
                rec.originalSignature, rec.originalCoefficient, context);
            ExpressionPointer contractedKernel = buildCanonicalMonomial(
                rec.contractedSignature, rec.originalCoefficient, context);
            ExpressionPointer proof = buildMonomialContractionProof(
                rec.originalSignature, rec.originalCoefficient,
                rec.contractedSignature, rec.pairsRemoved, pairs,
                context, axiomNames);
            originalMonomialKernels.push_back(originalKernel);
            contractedMonomialKernels.push_back(contractedKernel);
            perMonomialProofs.push_back(proof);
        }
        // canonical(originalPoly) is left-assoc sum of originalMonomialKernels.
        // We need a proof that it equals left-assoc sum of contractedMonomialKernels.
        //
        // We chain n proofs (one per monomial), each being a congruence
        // step that rewrites the i-th monomial's slot in the sum.
        //
        // BUT — the canonical of contracted may iterate in a DIFFERENT
        // order from the original (the std::map signature order may
        // shuffle after contraction). We need to handle that: after
        // per-position rewrites, the result is
        //   left_assoc(contractedMonomialKernels_in_original_order)
        // but `canonical(contractedPoly)` is
        //   left_assoc(contractedMonomialKernels_in_canonical_order).
        // These may differ in summand order.
        //
        // To bridge: apply the single-operator AC sorter on the additive operator to sort
        // the summands.
        //
        // Step 1: per-position rewrites → contracted-monomials-in-original-order.
        // Step 2: AC sort → canonical(contractedPoly).
        ExpressionPointer originalCanonical =
            assembleLeftAssociatedSum(context.addName, originalMonomialKernels);
        ExpressionPointer afterPerPos =
            assembleLeftAssociatedSum(context.addName, contractedMonomialKernels);
        // Per-position rewrite chain.
        ExpressionPointer chainProof;
        if (originalMonomialKernels.size() == 1) {
            chainProof = perMonomialProofs[0];
        } else {
            // Build chain: for each i, congruence with a motive that
            // surgically replaces the i-th summand in the left-assoc
            // chain.
            //
            // The current form after k rewrites is:
            //   contracted_0 + contracted_1 + ... + contracted_{k-1}
            //     + original_k + original_{k+1} + ... + original_{n-1}
            // (all left-associated). To rewrite the k-th slot we use
            // congruenceOf(λz. ..., perMonomialProofs[k]).
            ExpressionPointer currentForm = originalCanonical;
            ExpressionPointer currentProof = buildReflexivity(
                universeLevel, carrierType, originalCanonical);
            size_t n = originalMonomialKernels.size();
            for (size_t k = 0; k < n; ++k) {
                // Build the motive: λz. <left-assoc with z in slot k>.
                // The pieces: contracted_0..contracted_{k-1}, then z,
                // then original_{k+1}..original_{n-1}.
                std::vector<ExpressionPointer> liftedPrefix;
                for (size_t i = 0; i < k; ++i) {
                    liftedPrefix.push_back(
                        liftBoundVariables(
                            contractedMonomialKernels[i], 1, 0));
                }
                std::vector<ExpressionPointer> liftedSuffix;
                for (size_t i = k + 1; i < n; ++i) {
                    liftedSuffix.push_back(
                        liftBoundVariables(
                            originalMonomialKernels[i], 1, 0));
                }
                // Build the motive expression.
                ExpressionPointer motive;
                if (k == 0) {
                    motive = makeBoundVariable(0);
                } else if (liftedPrefix.size() == 1) {
                    motive = buildRingOp(
                        context.addName, liftedPrefix[0],
                        makeBoundVariable(0));
                } else {
                    ExpressionPointer prefixSum =
                        assembleLeftAssociatedSum(
                            context.addName, liftedPrefix);
                    motive = buildRingOp(
                        context.addName, prefixSum,
                        makeBoundVariable(0));
                }
                for (const auto& s : liftedSuffix) {
                    motive = buildRingOp(
                        context.addName, motive, s);
                }
                ExpressionPointer lambda = makeLambda(
                    "_field_poly_z", carrierType, motive);
                // The "new form" after rewriting slot k.
                std::vector<ExpressionPointer> newSummands;
                for (size_t i = 0; i < k; ++i) {
                    newSummands.push_back(contractedMonomialKernels[i]);
                }
                newSummands.push_back(contractedMonomialKernels[k]);
                for (size_t i = k + 1; i < n; ++i) {
                    newSummands.push_back(originalMonomialKernels[i]);
                }
                ExpressionPointer newForm =
                    assembleLeftAssociatedSum(
                        context.addName, newSummands);
                ExpressionPointer congrProof =
                    buildEqualityCongruenceSameCarrier(
                        universeLevel, carrierType, lambda,
                        originalMonomialKernels[k],
                        contractedMonomialKernels[k],
                        perMonomialProofs[k]);
                currentProof = buildEqualityTransitivity(
                    universeLevel, carrierType,
                    originalCanonical, currentForm, newForm,
                    currentProof, congrProof);
                currentForm = newForm;
            }
            chainProof = currentProof;
        }
        // Now we have proof: originalCanonical = afterPerPos
        // (i.e. left-assoc sum of contractedMonomialKernels in
        // original-order).
        ExpressionPointer canonicalContracted =
            buildCanonicalPolynomial(contractedPoly, context);
        if (structurallyEqual(afterPerPos, canonicalContracted)) {
            return chainProof;
        }
        // Need to reorder via the single-operator AC sorter on add.
        std::vector<ExpressionPointer> contractedMonomialKernelsCanonical;
        for (const auto& entry : contractedPoly) {
            contractedMonomialKernelsCanonical.push_back(
                buildCanonicalMonomial(entry.first, entry.second, context));
        }
        RingAxiomNames addAxioms{
            context.addName, axiomNames.addAssociative,
            axiomNames.addCommutative};
        // Sort `contractedMonomialKernels` (original order) into
        // `contractedMonomialKernelsCanonical` (canonical order) — same
        // multiset of monomials, different orders.
        ExpressionPointer sortProof = proveProductEqualsSorted(
            afterPerPos, contractedMonomialKernels,
            contractedMonomialKernelsCanonical,
            addAxioms, carrierType, universeLevel, /*line*/0);
        return buildEqualityTransitivity(
            universeLevel, carrierType,
            originalCanonical, afterPerPos, canonicalContracted,
            chainProof, sortProof);
    }

void Elaborator::collectReciprocalArguments(
        ExpressionPointer expression,
        const std::string& reciprocalFunctionName,
        std::unordered_map<uint64_t, ExpressionPointer>& argumentsOut) {
        if (auto* app = std::get_if<Application>(&expression->node)) {
            if (auto* head =
                    std::get_if<Constant>(&app->function->node)) {
                if (head->name == reciprocalFunctionName) {
                    argumentsOut.emplace(
                        app->argument->hash, app->argument);
                    // Continue into the argument too (nested
                    // reciprocals would be unusual but possible).
                }
            }
            collectReciprocalArguments(
                app->function, reciprocalFunctionName, argumentsOut);
            collectReciprocalArguments(
                app->argument, reciprocalFunctionName, argumentsOut);
            return;
        }
        if (auto* lam = std::get_if<Lambda>(&expression->node)) {
            collectReciprocalArguments(
                lam->domain, reciprocalFunctionName, argumentsOut);
            collectReciprocalArguments(
                lam->body, reciprocalFunctionName, argumentsOut);
            return;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            collectReciprocalArguments(
                pi->domain, reciprocalFunctionName, argumentsOut);
            collectReciprocalArguments(
                pi->codomain, reciprocalFunctionName, argumentsOut);
            return;
        }
        // Other variants: no children to walk.
    }

ExpressionPointer Elaborator::elaborateField(
        const SurfaceField& fieldTactic,
        const std::vector<LocalBinder>& localBinders,
        ExpressionPointer expectedType,
        int line, int column) {
        Frame frame(*this, "field at line " + std::to_string(line),
                    localBinders, expectedType, line, column);
        if (!expectedType) {
            throwElaborate(
                "`field` needs an expected type from context — use it "
                "as the body of a theorem with a declared equality "
                "conclusion");
        }
        // Open the expected type over local binders so that local
        // variables appear as FreeVariables — this lets us match
        // against hypothesis types (which arrive opened).
        ExpressionPointer expectedTypeOpened = openOverLocalBinders(
            expectedType, localBinders, localBinders.size());
        EqualityComponents goal =
            extractEqualityComponents(expectedTypeOpened, "field", line);
        std::string carrierName = headConstantName(goal.carrierType);
        // Set up the ring normaliser context. (The `field` tactic is
        // only used over concrete carriers, so the operation namespace is
        // the carrier head and there is no structure prefix; the bundled-
        // ring path is exercised through `ring`.)
        RingScheme scheme = computeRingScheme(goal.carrierType);
        RingStructurePrefixGuard prefixGuard(*this, scheme.structurePrefix);
        RingNormalisationContext context;
        context.carrierName = carrierName;
        context.carrierType = goal.carrierType;
        context.carrierUniverseLevel = goal.carrierUniverseLevel;
        context.opNamespace   = scheme.opNamespace;
        context.isRingName    = scheme.opNamespace + ".is_ring";
        context.addName       = scheme.opNamespace + ".add";
        context.multiplyName  = scheme.opNamespace + ".multiply";
        context.negateName    = scheme.opNamespace + ".negate";
        context.subtractName  = scheme.opNamespace + ".subtract";
        context.zeroName      = scheme.opNamespace + ".zero";
        context.oneName       = scheme.opNamespace + ".one";
        populateRingEmbeddingChain(context);
        if (environment_.lookup(context.addName) == nullptr
            || environment_.lookup(context.multiplyName) == nullptr) {
            throwElaborate(
                "`field`: carrier `" + carrierName
                + "` does not have both `.add` and `.multiply` in scope");
        }
        std::string reciprocalFunctionName =
            carrierName + ".reciprocal_function";
        std::string reciprocalMultipliesName =
            carrierName + ".reciprocal_function_multiplies";
        if (environment_.lookup(reciprocalFunctionName) == nullptr) {
            throwElaborate(
                "`field`: carrier `" + carrierName
                + "` does not have `reciprocal_function` in scope");
        }
        if (environment_.lookup(reciprocalMultipliesName) == nullptr) {
            throwElaborate(
                "`field`: carrier `" + carrierName
                + "` does not have `reciprocal_function_multiplies` in scope");
        }
        // Collect reciprocal_function arguments from both sides.
        std::unordered_map<uint64_t, ExpressionPointer> recipArgsMap;
        collectReciprocalArguments(
            goal.leftEndpoint, reciprocalFunctionName, recipArgsMap);
        collectReciprocalArguments(
            goal.rightEndpoint, reciprocalFunctionName, recipArgsMap);
        // Elaborate user hypotheses. Each h_i should have type
        // ¬(t_i = zero) ≡ (t_i = zero) → False.
        std::vector<FieldReciprocalPair> pairs;
        std::vector<bool> matchedArguments;
        std::vector<uint64_t> recipArgHashes;
        std::vector<ExpressionPointer> recipArgKernels;
        for (const auto& kv : recipArgsMap) {
            recipArgHashes.push_back(kv.first);
            recipArgKernels.push_back(kv.second);
        }
        matchedArguments.assign(recipArgHashes.size(), false);
        for (const auto& hypothesisSurface :
                 fieldTactic.nonzeroHypotheses) {
            ExpressionPointer hypothesisKernel = elaborateExpression(
                *hypothesisSurface, localBinders);
            // Open the hypothesis kernel so it lives in the same
            // FreeVariable namespace as our opened goal.
            ExpressionPointer hypothesisKernelOpened = openOverLocalBinders(
                hypothesisKernel, localBinders, localBinders.size());
            // Infer type: should be (t = zero) → False.
            ExpressionPointer hypothesisType;
            try {
                hypothesisType = weakHeadNormalForm(environment_,
                    inferTypeInLocalContext(localBinders, hypothesisKernel));
            } catch (const TypeError& kernelError) {
                rethrowKernelError(kernelError);
            }
            // Walk hypothesisType: expect Pi(_ : Equality(carrier, t, zero), _, False).
            // Surface form `¬(t = zero)` is `(t = zero) → False`,
            // which kernel-side is Pi(_ : Equality(carrier, t, zero), False).
            auto* piNode = std::get_if<Pi>(&hypothesisType->node);
            if (!piNode) {
                throwElaborate(
                    "`field`: hypothesis is not a `¬(t = Rational.zero)` "
                    "(not a function type)");
            }
            ExpressionPointer domain = weakHeadNormalForm(
                environment_, piNode->domain);
            EqualityComponents domainComponents;
            try {
                domainComponents = extractEqualityComponents(
                    domain, "field hypothesis", line);
            } catch (const ElaborateError&) {
                throwElaborate(
                    "`field`: hypothesis domain is not an equality");
            }
            // Check carrier matches.
            if (!structurallyEqual(
                    domainComponents.carrierType, goal.carrierType)) {
                throwElaborate(
                    "`field`: hypothesis carrier doesn't match goal "
                    "carrier");
            }
            // Check the RHS of the equality is `zero`. We accept the
            // bare Constant before WHNF (definitions unfold under
            // delta-reduction, so `Rational.zero` would reduce away;
            // the user almost always writes the literal name).
            ExpressionPointer rhsRaw = domainComponents.rightEndpoint;
            auto* rhsConst = std::get_if<Constant>(&rhsRaw->node);
            if (!rhsConst || rhsConst->name != context.zeroName) {
                throwElaborate(
                    "`field`: hypothesis is not of shape `¬(t = "
                    + context.zeroName + ")`");
            }
            // Locate which recipArg matches.
            ExpressionPointer baseAtom = domainComponents.leftEndpoint;
            uint64_t baseHash = baseAtom->hash;
            // Find recipArg with same hash.
            size_t matchedIndex = recipArgHashes.size();
            for (size_t i = 0; i < recipArgHashes.size(); ++i) {
                if (recipArgHashes[i] == baseHash) {
                    matchedIndex = i;
                    break;
                }
            }
            if (matchedIndex == recipArgHashes.size()) {
                // Hypothesis doesn't correspond to any
                // reciprocal_function call. Tolerate (ignore).
                continue;
            }
            if (matchedArguments[matchedIndex]) continue;  // duplicate
            matchedArguments[matchedIndex] = true;
            // Build the reciprocal_function(t) kernel.
            ExpressionPointer reciprocalAtom = makeApplication(
                makeConstant(reciprocalFunctionName), baseAtom);
            // Build proof `multipliesProof : t * reciprocal_function(t) = 1`.
            // Call: reciprocal_function_multiplies(t, hypothesisKernel).
            // Use the opened hypothesis kernel so it composes with the
            // opened goal terms.
            ExpressionPointer multipliesProof = makeConstant(
                reciprocalMultipliesName);
            multipliesProof = makeApplication(multipliesProof, baseAtom);
            multipliesProof = makeApplication(multipliesProof,
                                                hypothesisKernelOpened);
            FieldReciprocalPair pair;
            pair.baseAtom = baseAtom;
            pair.reciprocalAtom = reciprocalAtom;
            pair.multipliesProof = multipliesProof;
            pair.baseHash = baseHash;
            pair.reciprocalHash = reciprocalAtom->hash;
            pairs.push_back(pair);
        }
        // Check we matched all reciprocal_function arguments.
        for (size_t i = 0; i < recipArgHashes.size(); ++i) {
            if (!matchedArguments[i]) {
                throwElaborate(
                    "`field`: no nonzero hypothesis supplied for one "
                    "of the `reciprocal_function` arguments — pass a "
                    "hypothesis `¬(t = " + context.zeroName + ")` for "
                    "every distinct `t` appearing inside "
                    "`reciprocal_function(t)` on either side of the "
                    "goal");
            }
        }
        // Normalize both sides to ring polynomials.
        RingPolynomial leftPolynomial =
            normaliseToRingPolynomial(goal.leftEndpoint, context);
        RingPolynomial rightPolynomial =
            normaliseToRingPolynomial(goal.rightEndpoint, context);
        // Make sure that for each (t_i, r_i) pair we have the atoms
        // registered in the context atom table — they must have been
        // registered by the normalization above (assuming both atoms
        // appear in at least one side). Pre-register them here to be safe.
        for (const auto& p : pairs) {
            context.atoms.emplace(p.baseHash, p.baseAtom);
            context.atoms.emplace(p.reciprocalHash, p.reciprocalAtom);
        }
        // Contract polynomials.
        std::vector<FieldMonomialContraction> leftContractionRecords;
        RingPolynomial leftContracted = buildContractedPolynomial(
            leftPolynomial, pairs, leftContractionRecords);
        std::vector<FieldMonomialContraction> rightContractionRecords;
        RingPolynomial rightContracted = buildContractedPolynomial(
            rightPolynomial, pairs, rightContractionRecords);
        if (!ringPolynomialsAgree(leftContracted, rightContracted)) {
            throwElaborate(
                "`field`: after clearing reciprocals, the two sides "
                "still don't agree as polynomials — the goal is not a "
                "valid field identity (or the hypothesis set is "
                "insufficient)"
                + buildFingerprintDiagnostic(
                      goal.leftEndpoint, goal.rightEndpoint,
                      carrierName));
        }
        // Coefficient guard: ±1 throughout.
        for (const auto& entry : leftContracted) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`field`: the canonical form has a monomial with "
                    "coefficient " + std::to_string(entry.second)
                    + " — the underlying ring normaliser only handles "
                    "coefficients in {-1, +1}");
            }
        }
        for (const auto& entry : leftPolynomial) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`field`: the LHS polynomial has a monomial with "
                    "coefficient " + std::to_string(entry.second)
                    + " — the underlying ring normaliser only handles "
                    "coefficients in {-1, +1}");
            }
        }
        for (const auto& entry : rightPolynomial) {
            if (entry.second != -1 && entry.second != 1) {
                throwElaborate(
                    "`field`: the RHS polynomial has a monomial with "
                    "coefficient " + std::to_string(entry.second)
                    + " — the underlying ring normaliser only handles "
                    "coefficients in {-1, +1}");
            }
        }
        // Resolve axiom names.
        RingLawNames axiomNames =
            resolveRingLawNames(scheme.opNamespace);
        demandAxiomName(axiomNames.addAssociative,
                          "add_associative", carrierName);
        demandAxiomName(axiomNames.addCommutative,
                          "add_commutative", carrierName);
        demandAxiomName(axiomNames.multiplyAssociative,
                          "multiply_associative", carrierName);
        demandAxiomName(axiomNames.multiplyCommutative,
                          "multiply_commutative", carrierName);
        // Step 1: LHS = ring-canonical(LHS) via proveEqualsCanonical.
        RingPolynomial leftPolyOut, rightPolyOut;
        ExpressionPointer leftRingProof = proveEqualsCanonical(
            goal.leftEndpoint, context, axiomNames, leftPolyOut);
        ExpressionPointer rightRingProof = proveEqualsCanonical(
            goal.rightEndpoint, context, axiomNames, rightPolyOut);
        ExpressionPointer leftRingCanonical =
            buildCanonicalPolynomial(leftPolynomial, context);
        ExpressionPointer rightRingCanonical =
            buildCanonicalPolynomial(rightPolynomial, context);
        // Step 2: ring-canonical(LHS) = field-canonical(LHS) via
        //         buildPolynomialContractionProof.
        ExpressionPointer leftContractedCanonical =
            buildCanonicalPolynomial(leftContracted, context);
        ExpressionPointer rightContractedCanonical =
            buildCanonicalPolynomial(rightContracted, context);
        ExpressionPointer leftContractionProof =
            buildPolynomialContractionProof(
                leftPolynomial, leftContracted,
                leftContractionRecords, pairs, context, axiomNames);
        ExpressionPointer rightContractionProof =
            buildPolynomialContractionProof(
                rightPolynomial, rightContracted,
                rightContractionRecords, pairs, context, axiomNames);
        // Step 3: field-canonical(LHS) = field-canonical(RHS). The two
        // canonical kernels must be structurally equal (the polynomials
        // are equal, and buildCanonicalPolynomial is deterministic).
        if (!structurallyEqual(leftContractedCanonical,
                                  rightContractedCanonical)) {
            throwElaborate(
                "`field`: field-canonical kernels differ even though "
                "polynomials agreed (internal error)");
        }
        // Step 4: symmetric of step 2 for RHS.
        ExpressionPointer rightContractionProofSym = buildEqualitySymmetry(
            goal.carrierUniverseLevel, goal.carrierType,
            rightRingCanonical, rightContractedCanonical,
            rightContractionProof);
        // Step 5: symmetric of step 1 for RHS.
        ExpressionPointer rightRingProofSym = buildEqualitySymmetry(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.rightEndpoint, rightRingCanonical,
            rightRingProof);
        // Compose chain: LHS = leftRingCanonical = leftContractedCanonical
        //   = rightRingCanonical = RHS.
        ExpressionPointer chain12 = buildEqualityTransitivity(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.leftEndpoint, leftRingCanonical,
            leftContractedCanonical,
            leftRingProof, leftContractionProof);
        // leftContractedCanonical and rightContractedCanonical are
        // structurally equal, so we can chain via either kernel as the
        // bridge.
        ExpressionPointer chain1234 = buildEqualityTransitivity(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.leftEndpoint, leftContractedCanonical,
            rightRingCanonical,
            chain12, rightContractionProofSym);
        ExpressionPointer chain12345 = buildEqualityTransitivity(
            goal.carrierUniverseLevel, goal.carrierType,
            goal.leftEndpoint, rightRingCanonical, goal.rightEndpoint,
            chain1234, rightRingProofSym);
        // The proof is built in OPENED form (over local-binder
        // FreeVariables). Close it before returning so the caller's
        // BoundVariable-form expectedType matches.
        return closeOverLocalBinders(
            chain12345, localBinders, localBinders.size());
    }

