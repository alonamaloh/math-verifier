#pragma once

#include "level.hpp"
#include "subtree_hash.hpp"

#include <cstdint>
#include <memory>
#include <string>
#include <type_traits>
#include <variant>
#include <vector>

struct Expression;
using ExpressionPointer = std::shared_ptr<Expression>;

// Distinguishes free variables introduced by the user (via makeFreeVariable
// and ContextEntry) from those introduced by the kernel internally — for
// example, the placeholder names used by isDefinitionallyEqual when it
// opens a Pi/Lambda binder for structural comparison, or the placeholders
// used by buildCaseType / buildRecursorType during recursor construction.
// Two FreeVariables are identified by *both* their name and their origin,
// so the kernel's internal names cannot collide with anything the user can
// construct.
enum class FreeVariableOrigin { User, Internal };

struct BoundVariable { int deBruijnIndex; };
struct FreeVariable  { std::string name;
                       FreeVariableOrigin origin = FreeVariableOrigin::User; };
struct Sort          { LevelPointer level; };
struct Pi            { std::string displayHint; ExpressionPointer domain; ExpressionPointer codomain; };
struct Lambda        { std::string displayHint; ExpressionPointer domain; ExpressionPointer body; };
struct Application   { ExpressionPointer function; ExpressionPointer argument; };
struct Constant      { std::string name;
                       std::vector<LevelPointer> universeArguments; };
struct Let           { std::string displayHint;
                       ExpressionPointer type;
                       ExpressionPointer value;
                       ExpressionPointer body; };

struct Expression {
    std::variant<BoundVariable, FreeVariable, Sort, Pi, Lambda, Application, Constant, Let> node;
    // Bottom-up structural hash, populated by the make* helpers below.
    // 0 means uninitialised — kernel code goes through the helpers so
    // this should never appear in well-formed terms. Used as a
    // constant-time fast-reject in structurallyEqual.
    uint64_t hash = 0;

    Expression() = default;

    template <typename Alternative,
              typename = std::enable_if_t<
                  !std::is_same_v<std::decay_t<Alternative>, Expression>>>
    Expression(Alternative&& alternative)
        : node(std::forward<Alternative>(alternative)) {}
};

inline ExpressionPointer makeBoundVariable(int index) {
    auto expression = std::make_shared<Expression>(BoundVariable{index});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(subtree_hash::kSeed,
                           subtree_hash::kTagBoundVariable),
        static_cast<uint64_t>(index));
    return expression;
}
inline ExpressionPointer makeFreeVariable(std::string name) {
    uint64_t nameHash = subtree_hash::hashString(name);
    auto expression = std::make_shared<Expression>(
        FreeVariable{std::move(name)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagFreeVariable),
            nameHash),
        static_cast<uint64_t>(FreeVariableOrigin::User));
    return expression;
}
// Note: no public builder exists for Internal-origin FreeVariables — they
// are an implementation detail of the kernel (isDefinitionallyEqual binder
// opening, buildCaseType/buildRecursorType placeholders) and the User
// origin is the only one client code should construct.
// Sort taking a level expression. Universe-polymorphic code passes a Level
// containing a LevelParam; concrete code uses LevelConst (via the int
// overload below). Level 0 is Proposition; level n+1 is "Type n".
inline ExpressionPointer makeSort(LevelPointer level) {
    uint64_t levelHash = level->hash;
    auto expression = std::make_shared<Expression>(
        Sort{std::move(level)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(subtree_hash::kSeed,
                           subtree_hash::kTagSort),
        levelHash);
    return expression;
}
inline ExpressionPointer makeSort(int rawLevel) {
    return makeSort(makeLevelConst(rawLevel));
}
inline ExpressionPointer makeProposition() {
    return makeSort(0);
}
inline ExpressionPointer makeType(int index) {
    return makeSort(index + 1);
}
// Polymorphic Type universe: `Type u` lives at Sort (u+1).
inline ExpressionPointer makeType(LevelPointer level) {
    return makeSort(makeLevelSuccessor(std::move(level)));
}
inline ExpressionPointer makePi(std::string displayHint,
                            ExpressionPointer domain,
                            ExpressionPointer codomain) {
    // displayHint is cosmetic and intentionally excluded from the hash
    // (structurallyEqual ignores it for the same reason).
    uint64_t domainHash = domain->hash;
    uint64_t codomainHash = codomain->hash;
    auto expression = std::make_shared<Expression>(
        Pi{std::move(displayHint), std::move(domain),
           std::move(codomain)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagPi),
            domainHash),
        codomainHash);
    return expression;
}
inline ExpressionPointer makeLambda(std::string displayHint,
                                ExpressionPointer domain,
                                ExpressionPointer body) {
    uint64_t domainHash = domain->hash;
    uint64_t bodyHash = body->hash;
    auto expression = std::make_shared<Expression>(
        Lambda{std::move(displayHint), std::move(domain),
               std::move(body)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagLambda),
            domainHash),
        bodyHash);
    return expression;
}
inline ExpressionPointer makeApplication(ExpressionPointer function,
                                     ExpressionPointer argument) {
    uint64_t functionHash = function->hash;
    uint64_t argumentHash = argument->hash;
    auto expression = std::make_shared<Expression>(
        Application{std::move(function), std::move(argument)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagApplication),
            functionHash),
        argumentHash);
    return expression;
}
inline ExpressionPointer makeConstant(std::string name,
                                      std::vector<LevelPointer> universeArguments) {
    uint64_t nameHash = subtree_hash::hashString(name);
    uint64_t universeHash = subtree_hash::kSeed;
    for (const auto& universeArgument : universeArguments) {
        universeHash = subtree_hash::mix(universeHash,
                                            universeArgument->hash);
    }
    auto expression = std::make_shared<Expression>(
        Constant{std::move(name), std::move(universeArguments)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagConstant),
            nameHash),
        universeHash);
    return expression;
}
inline ExpressionPointer makeConstant(std::string name) {
    return makeConstant(std::move(name), {});
}
inline ExpressionPointer makeLet(std::string displayHint,
                                 ExpressionPointer type,
                                 ExpressionPointer value,
                                 ExpressionPointer body) {
    uint64_t typeHash = type->hash;
    uint64_t valueHash = value->hash;
    uint64_t bodyHash = body->hash;
    auto expression = std::make_shared<Expression>(
        Let{std::move(displayHint), std::move(type),
            std::move(value), std::move(body)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(
                subtree_hash::mix(subtree_hash::kSeed,
                                   subtree_hash::kTagLet),
                typeHash),
            valueHash),
        bodyHash);
    return expression;
}
