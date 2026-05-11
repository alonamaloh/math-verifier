#pragma once

#include <memory>
#include <string>
#include <type_traits>
#include <variant>

struct Expression;
using ExpressionPointer = std::shared_ptr<Expression>;

struct BoundVariable { int deBruijnIndex; };
struct FreeVariable  { std::string name; };
struct Sort          { int universeLevel; };
struct Pi            { std::string displayHint; ExpressionPointer domain; ExpressionPointer codomain; };
struct Lambda        { std::string displayHint; ExpressionPointer domain; ExpressionPointer body; };
struct Application   { ExpressionPointer function; ExpressionPointer argument; };
struct Constant      { std::string name; };
struct Let           { std::string displayHint;
                       ExpressionPointer type;
                       ExpressionPointer value;
                       ExpressionPointer body; };

struct Expression {
    std::variant<BoundVariable, FreeVariable, Sort, Pi, Lambda, Application, Constant, Let> node;

    Expression() = default;

    template <typename Alternative,
              typename = std::enable_if_t<
                  !std::is_same_v<std::decay_t<Alternative>, Expression>>>
    Expression(Alternative&& alternative)
        : node(std::forward<Alternative>(alternative)) {}
};

inline ExpressionPointer makeBoundVariable(int index) {
    return std::make_shared<Expression>(BoundVariable{index});
}
inline ExpressionPointer makeFreeVariable(std::string name) {
    return std::make_shared<Expression>(FreeVariable{std::move(name)});
}
// Sort with raw universe level. Level 0 is Prop; level n+1 is "Type n"
// (the user-facing universe of small types at index n). Prefer makeProp()
// or makeType(n) at call sites; this is the kernel-internal constructor.
inline ExpressionPointer makeSort(int level) {
    return std::make_shared<Expression>(Sort{level});
}
inline ExpressionPointer makeProp() {
    return makeSort(0);
}
inline ExpressionPointer makeType(int index) {
    return makeSort(index + 1);
}
inline ExpressionPointer makePi(std::string displayHint,
                            ExpressionPointer domain,
                            ExpressionPointer codomain) {
    return std::make_shared<Expression>(
        Pi{std::move(displayHint), std::move(domain), std::move(codomain)});
}
inline ExpressionPointer makeLambda(std::string displayHint,
                                ExpressionPointer domain,
                                ExpressionPointer body) {
    return std::make_shared<Expression>(
        Lambda{std::move(displayHint), std::move(domain), std::move(body)});
}
inline ExpressionPointer makeApplication(ExpressionPointer function,
                                     ExpressionPointer argument) {
    return std::make_shared<Expression>(
        Application{std::move(function), std::move(argument)});
}
inline ExpressionPointer makeConstant(std::string name) {
    return std::make_shared<Expression>(Constant{std::move(name)});
}
inline ExpressionPointer makeLet(std::string displayHint,
                                 ExpressionPointer type,
                                 ExpressionPointer value,
                                 ExpressionPointer body) {
    return std::make_shared<Expression>(
        Let{std::move(displayHint), std::move(type),
            std::move(value), std::move(body)});
}
