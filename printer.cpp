#include "printer.hpp"

#include <algorithm>
#include <optional>
#include <sstream>
#include <string>
#include <vector>

namespace {

// Operator precedences used when collapsing known function calls into
// infix / prefix notation. Higher = binds tighter. Caller passes its
// own precedence; child wraps in parens iff `child < parent`.
constexpr int kPrecedenceLogical        = 0;  // ∨ (binds loosest)
constexpr int kPrecedenceRelation       = 1;  // = ≤ <
constexpr int kPrecedenceAdditive       = 2;  // + -
constexpr int kPrecedenceMultiplicative = 3;  // * ·
constexpr int kPrecedencePrefix         = 4;  // unary -
constexpr int kPrecedencePostfix        = 5;  // postfix ⁻¹

struct BinaryOperatorInfo {
    const char* symbol;
    int precedence;
    // Right-associative operators (`∨`) print a same-operator right operand
    // without redundant parens: `A ∨ B ∨ C`, not `A ∨ (B ∨ C)`.
    bool rightAssociative = false;
};

// Detect the conventional `<Carrier>.<op>` shape used throughout the
// library so the printer can render `Real.add a b` as `a + b`. We
// match by suffix rather than consulting a registry — every carrier
// in the library uses the same names. False positives (a user-defined
// `Foo.add` that isn't addition) are syntactic prettification only —
// it never changes the kernel's view of the term.
std::optional<BinaryOperatorInfo>
classifyBinaryOperator(const std::string& name) {
    auto endsWith = [&](const char* suffix) -> bool {
        std::string s(suffix);
        return name.size() >= s.size()
            && name.compare(name.size() - s.size(), s.size(), s) == 0;
    };
    if (endsWith(".add"))
        return BinaryOperatorInfo{"+", kPrecedenceAdditive};
    if (endsWith(".subtract"))
        return BinaryOperatorInfo{"-", kPrecedenceAdditive};
    if (endsWith(".multiply"))
        return BinaryOperatorInfo{"*", kPrecedenceMultiplicative};
    // The order relations on Natural are bare top-level inductives
    // (`LessOrEqual` / `LessThan`, no `Carrier.` prefix); every other
    // carrier namespaces them (`Rational.LessOrEqual`, …). Match both the
    // suffixed and the bare names so all of them render infix.
    if (endsWith(".LessOrEqual") || name == "LessOrEqual")
        return BinaryOperatorInfo{"≤", kPrecedenceRelation};
    if (endsWith(".LessThan") || name == "LessThan")
        return BinaryOperatorInfo{"<", kPrecedenceRelation};
    // Logical disjunction `Or(A, B)` → `A ∨ B`. Right-associative, loosest.
    if (name == "Or")
        return BinaryOperatorInfo{"∨", kPrecedenceLogical, /*rightAssoc=*/true};
    return std::nullopt;
}

bool isPrefixNegate(const std::string& name) {
    constexpr const char* suffix = ".negate";
    constexpr std::size_t suffixSize = 7;
    return name.size() >= suffixSize
        && name.compare(name.size() - suffixSize, suffixSize, suffix) == 0;
}

} // namespace

namespace {

bool nameInStack(const std::vector<std::string>& stack, const std::string& name) {
    return std::find(stack.begin(), stack.end(), name) != stack.end();
}

std::string freshenAgainstStack(const std::vector<std::string>& stack,
                                const std::string& displayHint) {
    std::string base = displayHint.empty() ? "x" : displayHint;
    if (!nameInStack(stack, base)) return base;
    for (int suffix = 1;; ++suffix) {
        std::string candidate = base + "_" + std::to_string(suffix);
        if (!nameInStack(stack, candidate)) return candidate;
    }
}

// Precedence levels used to decide where to insert parentheses.
//   0 = top-level (no parens needed)
//   1 = inside an application's function position (binders need parens)
//   2 = inside an application's argument position (binders and
//       applications both need parens — only "atomic" forms are
//       unparenthesized).
void writeAtPrecedence(std::ostringstream& output,
                       ExpressionPointer expression,
                       std::vector<std::string>& stack,
                       int precedence);

// Does de Bruijn index `target` occur free in `expression`? Used to
// decide whether a Pi is a plain function type (`A → B`) or a dependent
// one (`(x : A) → B`). `maxFreeBoundVariable` gives an O(1) reject for the
// common closed-codomain case, so this is cheap on real terms.
bool mentionsBoundVariable(const ExpressionPointer& expression, int target) {
    if (!expression) return false;
    if (expression->maxFreeBoundVariable < target) return false;
    if (auto* bv = std::get_if<BoundVariable>(&expression->node)) {
        return bv->deBruijnIndex == target;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return mentionsBoundVariable(pi->domain, target)
            || mentionsBoundVariable(pi->codomain, target + 1);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return mentionsBoundVariable(lambda->domain, target)
            || mentionsBoundVariable(lambda->body, target + 1);
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return mentionsBoundVariable(application->function, target)
            || mentionsBoundVariable(application->argument, target);
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return mentionsBoundVariable(let->type, target)
            || mentionsBoundVariable(let->value, target)
            || mentionsBoundVariable(let->body, target + 1);
    }
    return false;  // FreeVariable, Sort, Constant
}

void writeAtomic(std::ostringstream& output,
                 ExpressionPointer expression,
                 std::vector<std::string>& stack) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        int index = boundVariable->deBruijnIndex;
        if (index < 0 || static_cast<std::size_t>(index) >= stack.size()) {
            output << "<bound " << index << ">";
        } else {
            output << stack[stack.size() - 1 - index];
        }
        return;
    }
    if (auto* freeVariable = std::get_if<FreeVariable>(&expression->node)) {
        // Kernel-internal free variables are prefixed with '@' on display
        // so that any accidental leak into user-facing output is obvious.
        if (freeVariable->origin == FreeVariableOrigin::Internal) {
            output << "@";
        }
        output << freeVariable->name;
        return;
    }
    if (auto* sort = std::get_if<Sort>(&expression->node)) {
        if (auto concreteLevel = levelAsConstant(sort->level)) {
            if (*concreteLevel == 0) {
                output << "Proposition";
            } else {
                output << "Type " << (*concreteLevel - 1);
            }
        } else if (auto* successor =
                        std::get_if<LevelSuccessor>(&sort->level->node)) {
            // Sort (LevelSuccessor x) is Type x — render symbolic
            // Type for non-constant levels.
            output << "Type " << prettyPrintLevel(successor->base);
        } else {
            output << "Sort " << prettyPrintLevel(sort->level);
        }
        return;
    }
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        output << constant->name;
        if (!constant->universeArguments.empty()) {
            output << ".{";
            for (std::size_t i = 0; i < constant->universeArguments.size(); ++i) {
                if (i > 0) output << ", ";
                output << prettyPrintLevel(constant->universeArguments[i]);
            }
            output << "}";
        }
        return;
    }
    output << "(";
    writeAtPrecedence(output, expression, stack, 0);
    output << ")";
}

void writeAtPrecedence(std::ostringstream& output,
                       ExpressionPointer expression,
                       std::vector<std::string>& stack,
                       int precedence) {
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        // Render function types in the surface form the language uses,
        // never the CIC `Π`. Non-dependent (the binder is unused in the
        // codomain) prints as `A → B`; dependent as `(x : A) → B`. The
        // arrow binds loosest (like the old Π), so it parenthesises
        // exactly when `precedence > 0`.
        bool needsParentheses = precedence > 0;
        if (needsParentheses) output << "(";
        auto displayName = freshenAgainstStack(stack, pi->displayHint);
        bool dependent = mentionsBoundVariable(pi->codomain, 0);
        if (dependent) {
            output << "(" << displayName << " : ";
            writeAtPrecedence(output, pi->domain, stack, 0);
            output << ") → ";
        } else {
            // Left of `→`: parenthesise a nested arrow (precedence 0) but
            // leave tighter forms bare, and print the domain `→`-free.
            writeAtPrecedence(output, pi->domain, stack, 1);
            output << " → ";
        }
        // Push the binder name even when unused so de Bruijn indices in
        // the codomain still resolve against the right stack depth.
        stack.push_back(displayName);
        writeAtPrecedence(output, pi->codomain, stack, 0);
        stack.pop_back();
        if (needsParentheses) output << ")";
        return;
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        bool needsParentheses = precedence > 0;
        if (needsParentheses) output << "(";
        auto displayName = freshenAgainstStack(stack, lambda->displayHint);
        output << "λ(" << displayName << " : ";
        writeAtPrecedence(output, lambda->domain, stack, 0);
        output << "). ";
        stack.push_back(displayName);
        writeAtPrecedence(output, lambda->body, stack, 0);
        stack.pop_back();
        if (needsParentheses) output << ")";
        return;
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        // Try infix / prefix rendering for the well-known operator
        // shapes before falling through to the bare `f x y` form.
        //
        // Equality.{u}(T, x, y) → x = y. Three application layers.
        if (auto* mid =
                std::get_if<Application>(&application->function->node)) {
            if (auto* base =
                    std::get_if<Application>(&mid->function->node)) {
                if (auto* head =
                        std::get_if<Constant>(&base->function->node)) {
                    if (head->name == "Equality") {
                        bool wrap = precedence > kPrecedenceRelation;
                        if (wrap) output << "(";
                        writeAtPrecedence(output, mid->argument, stack,
                                          kPrecedenceRelation + 1);
                        output << " = ";
                        writeAtPrecedence(output, application->argument,
                                          stack,
                                          kPrecedenceRelation + 1);
                        if (wrap) output << ")";
                        return;
                    }
                    // Bundled group operation: Group.operation(G, a, b)
                    // → a · b. The leading group argument (base->argument)
                    // is dropped from display.
                    if (head->name == "Group.operation") {
                        bool wrap = precedence > kPrecedenceMultiplicative;
                        if (wrap) output << "(";
                        writeAtPrecedence(output, mid->argument, stack,
                                          kPrecedenceMultiplicative);
                        output << " · ";
                        writeAtPrecedence(output, application->argument,
                                          stack,
                                          kPrecedenceMultiplicative + 1);
                        if (wrap) output << ")";
                        return;
                    }
                }
            }
        }
        // <Carrier>.OP(x, y) → x SYMBOL y. Two application layers.
        if (auto* inner =
                std::get_if<Application>(&application->function->node)) {
            if (auto* head =
                    std::get_if<Constant>(&inner->function->node)) {
                if (auto info = classifyBinaryOperator(head->name)) {
                    bool wrap = precedence > info->precedence;
                    if (wrap) output << "(";
                    writeAtPrecedence(output, inner->argument, stack,
                                      info->precedence);
                    output << " " << info->symbol << " ";
                    int rightPrecedence = info->rightAssociative
                        ? info->precedence : info->precedence + 1;
                    writeAtPrecedence(output, application->argument,
                                      stack, rightPrecedence);
                    if (wrap) output << ")";
                    return;
                }
                // Bundled group inverse: Group.inverse(G, a) → a⁻¹. The
                // leading group argument (inner->argument) is dropped.
                if (head->name == "Group.inverse") {
                    bool wrap = precedence > kPrecedencePostfix;
                    if (wrap) output << "(";
                    writeAtPrecedence(output, application->argument, stack,
                                      kPrecedencePostfix);
                    output << "⁻¹";
                    if (wrap) output << ")";
                    return;
                }
            }
        }
        // <Carrier>.negate(x) → -x. One application layer.
        if (auto* head =
                std::get_if<Constant>(&application->function->node)) {
            if (isPrefixNegate(head->name)) {
                bool wrap = precedence > kPrecedencePrefix;
                if (wrap) output << "(";
                output << "-";
                writeAtPrecedence(output, application->argument, stack,
                                  kPrecedencePrefix + 1);
                if (wrap) output << ")";
                return;
            }
        }
        // Fall through: bare function-application rendering.
        bool needsParentheses = precedence > 1;
        if (needsParentheses) output << "(";
        writeAtPrecedence(output, application->function, stack, 1);
        output << " ";
        writeAtomic(output, application->argument, stack);
        if (needsParentheses) output << ")";
        return;
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        bool needsParentheses = precedence > 0;
        if (needsParentheses) output << "(";
        auto displayName = freshenAgainstStack(stack, let->displayHint);
        output << "let " << displayName << " : ";
        writeAtPrecedence(output, let->type, stack, 0);
        output << " := ";
        writeAtPrecedence(output, let->value, stack, 0);
        output << " in ";
        stack.push_back(displayName);
        writeAtPrecedence(output, let->body, stack, 0);
        stack.pop_back();
        if (needsParentheses) output << ")";
        return;
    }
    writeAtomic(output, expression, stack);
}

} // namespace

std::string prettyPrint(ExpressionPointer expression) {
    std::ostringstream output;
    std::vector<std::string> stack;
    writeAtPrecedence(output, expression, stack, 0);
    return output.str();
}
