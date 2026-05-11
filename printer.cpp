#include "printer.hpp"

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

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
                output << "Prop";
            } else {
                output << "Type " << (*concreteLevel - 1);
            }
        } else if (auto* succ = std::get_if<LevelSucc>(&sort->level->node)) {
            // Sort (succ x) is Type x — render symbolic Type for non-const u.
            output << "Type " << prettyPrintLevel(succ->base);
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
        bool needsParentheses = precedence > 0;
        if (needsParentheses) output << "(";
        auto displayName = freshenAgainstStack(stack, pi->displayHint);
        output << "Π(" << displayName << " : ";
        writeAtPrecedence(output, pi->domain, stack, 0);
        output << "). ";
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
