#pragma once

// Surface AST for the .math language. Produced by the parser, consumed
// by the elaborator. Distinct from the kernel's Expression because the
// surface form carries source positions, qualified names with unresolved
// universe arguments, operator nodes (resolved by the elaborator), and
// other surface-only features. Conversion to a kernel Expression is the
// elaborator's job.

#include <memory>
#include <string>
#include <variant>
#include <vector>

struct SurfaceExpression;
using SurfaceExpressionPointer = std::shared_ptr<const SurfaceExpression>;

struct SurfaceLevel;
using SurfaceLevelPointer = std::shared_ptr<const SurfaceLevel>;

struct SurfacePattern;
using SurfacePatternPointer = std::shared_ptr<const SurfacePattern>;

// One clause of a `cases` expression. Defined up-front (before
// SurfaceExpression) so SurfaceExpression's std::variant can hold a
// SurfaceCases that owns a std::vector<SurfaceCasesClause>.
struct SurfaceCasesClause {
    SurfacePatternPointer pattern;
    SurfaceExpressionPointer body;
    int line = 0;
    int column = 0;
};

// -------- universe levels --------

struct SurfaceLevelNumeric { int value; };
struct SurfaceLevelName    { std::string name; };
struct SurfaceLevelMax     { SurfaceLevelPointer left, right; };
struct SurfaceLevelImax    { SurfaceLevelPointer left, right; };
struct SurfaceLevelAdd     { SurfaceLevelPointer base; int amount; };
// A level that the surface author has left unspecified — `Type` without
// `(level)`. The elaborator generates a fresh universe metavariable for
// each occurrence; unresolved metavariables become auto-bound universe
// parameters of the enclosing declaration (Stage 3).
struct SurfaceLevelMeta    { };

struct SurfaceLevel {
    std::variant<SurfaceLevelNumeric, SurfaceLevelName,
                 SurfaceLevelMax, SurfaceLevelImax,
                 SurfaceLevelAdd, SurfaceLevelMeta> node;
    int line = 0;
    int column = 0;
};

inline SurfaceLevelPointer makeSurfaceLevelNumeric(int value,
                                                   int line, int column) {
    return std::make_shared<const SurfaceLevel>(
        SurfaceLevel{SurfaceLevelNumeric{value}, line, column});
}
inline SurfaceLevelPointer makeSurfaceLevelName(std::string name,
                                                 int line, int column) {
    return std::make_shared<const SurfaceLevel>(
        SurfaceLevel{SurfaceLevelName{std::move(name)}, line, column});
}
inline SurfaceLevelPointer makeSurfaceLevelMax(SurfaceLevelPointer left,
                                                SurfaceLevelPointer right,
                                                int line, int column) {
    return std::make_shared<const SurfaceLevel>(
        SurfaceLevel{SurfaceLevelMax{std::move(left), std::move(right)},
                     line, column});
}
inline SurfaceLevelPointer makeSurfaceLevelImax(SurfaceLevelPointer left,
                                                 SurfaceLevelPointer right,
                                                 int line, int column) {
    return std::make_shared<const SurfaceLevel>(
        SurfaceLevel{SurfaceLevelImax{std::move(left), std::move(right)},
                     line, column});
}
inline SurfaceLevelPointer makeSurfaceLevelAdd(SurfaceLevelPointer base,
                                                int amount,
                                                int line, int column) {
    return std::make_shared<const SurfaceLevel>(
        SurfaceLevel{SurfaceLevelAdd{std::move(base), amount},
                     line, column});
}
inline SurfaceLevelPointer makeSurfaceLevelMeta(int line, int column) {
    return std::make_shared<const SurfaceLevel>(
        SurfaceLevel{SurfaceLevelMeta{}, line, column});
}

// -------- expressions --------

// A binder appearing in a Pi type or a lambda. Multiple names share one
// type: `(x y z : T)` is one binder with three names. An anonymous
// binder (the `T → U` form of Pi) has an empty `names` vector.
// `isImplicit` is true for `{x : T}` form binders — the elaborator
// infers them at call sites rather than expecting the caller to spell
// them out. For Phase 2.1, implicit binders must appear consecutively
// at the leading positions of a declaration's parameter list.
struct SurfaceBinder {
    std::vector<std::string> names;
    SurfaceExpressionPointer type;
    bool isImplicit = false;
};

struct SurfaceIdentifier {
    std::string qualifiedName;                       // dotted, e.g. "Natural.add"
    std::vector<SurfaceLevelPointer> universeArgs;   // empty if no .{...}
};
struct SurfaceNumericLiteral { std::string digits; };
struct SurfaceApplication {
    SurfaceExpressionPointer function;
    std::vector<SurfaceExpressionPointer> arguments;
};
struct SurfacePiType {
    SurfaceBinder binder;
    SurfaceExpressionPointer codomain;
};
struct SurfaceLambda {
    SurfaceBinder binder;
    SurfaceExpressionPointer body;
};
struct SurfaceLet {
    std::string name;
    SurfaceExpressionPointer type;
    SurfaceExpressionPointer value;
    SurfaceExpressionPointer body;
};
struct SurfaceAscription {
    SurfaceExpressionPointer expression;
    SurfaceExpressionPointer type;
};
struct SurfaceType { SurfaceLevelPointer level; };
struct SurfaceProposition { };
// Binary operator node. The elaborator resolves `opSymbol` against the
// active `using` declarations to a concrete kernel function.
struct SurfaceBinaryOperation {
    std::string opSymbol;
    SurfaceExpressionPointer left;
    SurfaceExpressionPointer right;
};
struct SurfaceUnaryOperation {
    std::string opSymbol;
    SurfaceExpressionPointer operand;
};

// Anonymous tuple expression `⟨a, b, ...⟩`. The elaborator picks the
// constructor based on the expected type — `And.introduction(a, b)` when
// the goal is `And(_, _)`, `Exists.introduce(a, b)` for `Exists(_, _)`,
// and the unique constructor for any other single-constructor inductive.
// N-ary tuples right-associate: `⟨a, b, c⟩` ≡ `⟨a, ⟨b, c⟩⟩`.
struct SurfaceAnonymousTuple {
    std::vector<SurfaceExpressionPointer> components;
};

// `cases scrutinee { | pattern => body  | pattern => body  ... }`. The
// elaborator picks the inductive's recursor and builds the motive from
// the surrounding expected type. Patterns may be constructor patterns,
// tuple patterns, or bare names (variable binding for a one-constructor
// inductive).
struct SurfaceCases {
    SurfaceExpressionPointer scrutinee;
    std::vector<SurfaceCasesClause> clauses;
};

// `?` — placeholder for a proof the elaborator should fill in. Phase 3
// tries simple hammer steps: hypothesis match against local binders
// and reflexivity-match for `Equality(A, x, x)` goals. Requires an
// expected type from context.
struct SurfaceHammer { };

struct SurfaceExpression {
    std::variant<
        SurfaceIdentifier, SurfaceNumericLiteral,
        SurfaceApplication, SurfacePiType, SurfaceLambda,
        SurfaceLet, SurfaceAscription, SurfaceType, SurfaceProposition,
        SurfaceBinaryOperation, SurfaceUnaryOperation,
        SurfaceAnonymousTuple, SurfaceCases, SurfaceHammer
    > node;
    int line = 0;
    int column = 0;
};

// -------- builders --------

inline SurfaceExpressionPointer makeSurfaceIdentifier(
    std::string qualifiedName,
    std::vector<SurfaceLevelPointer> universeArgs,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceIdentifier{std::move(qualifiedName), std::move(universeArgs)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceNumericLiteral(
    std::string digits, int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceNumericLiteral{std::move(digits)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceApplication(
    SurfaceExpressionPointer function,
    std::vector<SurfaceExpressionPointer> arguments,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceApplication{std::move(function), std::move(arguments)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfacePiType(
    SurfaceBinder binder, SurfaceExpressionPointer codomain,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfacePiType{std::move(binder), std::move(codomain)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceLambda(
    SurfaceBinder binder, SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceLambda{std::move(binder), std::move(body)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceLet(
    std::string name, SurfaceExpressionPointer type,
    SurfaceExpressionPointer value, SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceLet{std::move(name), std::move(type),
                   std::move(value), std::move(body)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceAscription(
    SurfaceExpressionPointer expression, SurfaceExpressionPointer type,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceAscription{std::move(expression), std::move(type)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceType(
    SurfaceLevelPointer level, int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceType{std::move(level)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceProposition(int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceProposition{}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceBinaryOperation(
    std::string opSymbol, SurfaceExpressionPointer left,
    SurfaceExpressionPointer right, int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceBinaryOperation{std::move(opSymbol),
                                std::move(left), std::move(right)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceUnaryOperation(
    std::string opSymbol, SurfaceExpressionPointer operand,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceUnaryOperation{std::move(opSymbol), std::move(operand)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceAnonymousTuple(
    std::vector<SurfaceExpressionPointer> components,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceAnonymousTuple{std::move(components)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceHammer(int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceHammer{}, line, column});
}
// Forward-declared above; full SurfaceCasesClause type lives later in
// this header (it depends on SurfacePattern). The builder is defined
// alongside the type.

// -------- patterns --------

// A pattern in a pattern-match definition case. Either a name (variable
// binding, or a nullary constructor — resolved by the elaborator) or a
// constructor application like `successor(k)` (always a constructor
// pattern). A name of just "_" is a wildcard.
// (SurfacePattern is forward-declared up top so SurfaceCasesClause can
// reference it.)

struct SurfacePatternBareName {
    std::string name;  // "_" for wildcard
};
struct SurfacePatternConstructor {
    std::string constructorName;
    std::vector<SurfacePatternPointer> arguments;
};
// Tuple pattern `⟨pat, pat, ...⟩`. The elaborator picks the destructuring
// constructor (e.g. And.introduction, Exists.introduce) based on the
// scrutinee's type, matching the same logic as SurfaceAnonymousTuple.
struct SurfacePatternTuple {
    std::vector<SurfacePatternPointer> components;
};
struct SurfacePattern {
    std::variant<SurfacePatternBareName, SurfacePatternConstructor,
                 SurfacePatternTuple> node;
    int line = 0;
    int column = 0;
};

inline SurfacePatternPointer makeSurfacePatternBareName(
    std::string name, int line, int column) {
    return std::make_shared<const SurfacePattern>(
        SurfacePattern{SurfacePatternBareName{std::move(name)}, line, column});
}
inline SurfacePatternPointer makeSurfacePatternConstructor(
    std::string constructorName,
    std::vector<SurfacePatternPointer> arguments,
    int line, int column) {
    return std::make_shared<const SurfacePattern>(SurfacePattern{
        SurfacePatternConstructor{std::move(constructorName),
                                  std::move(arguments)},
        line, column});
}
inline SurfacePatternPointer makeSurfacePatternTuple(
    std::vector<SurfacePatternPointer> components,
    int line, int column) {
    return std::make_shared<const SurfacePattern>(
        SurfacePattern{SurfacePatternTuple{std::move(components)},
                       line, column});
}

// SurfaceCasesClause is defined near the top of the file (before
// SurfaceExpression) so SurfaceCases can store a vector of clauses.

inline SurfaceExpressionPointer makeSurfaceCases(
    SurfaceExpressionPointer scrutinee,
    std::vector<SurfaceCasesClause> clauses,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceCases{std::move(scrutinee), std::move(clauses)},
        line, column});
}

// One case of a pattern-match definition: a list of patterns (one per
// function argument) and the body expression.
struct SurfacePatternCase {
    std::vector<SurfacePatternPointer> patterns;
    SurfaceExpressionPointer body;
    int line = 0;
    int column = 0;
};

// -------- declarations --------

// One constructor of an inductive type. Its `type` is the constructor's
// declared type starting AFTER the inductive's parameter binders — the
// elaborator wraps the parameters back in when constructing the kernel
// declaration.
struct SurfaceConstructorSpec {
    std::string name;
    SurfaceExpressionPointer type;
};

// `inductive Name.{u, v} (p1 : T1) (p2 : T2) : Kind where | ctor : ...`.
struct SurfaceInductiveDeclaration {
    std::string name;
    std::vector<std::string> universeParameters;
    std::vector<SurfaceBinder> parameters;
    SurfaceExpressionPointer kind;
    std::vector<SurfaceConstructorSpec> constructors;
};

// `axiom Name.{u} : Type`.
struct SurfaceAxiomDeclaration {
    std::string name;
    std::vector<std::string> universeParameters;
    SurfaceExpressionPointer type;
};

// `definition Name.{u} (arguments) : Type := body`  OR
// `definition Name.{u} : T1 → ... → Tn  | p1, ..., pn => body | ...`.
// One of `body` / `cases` is populated; the other is empty.
// `isTheorem` is true if the source used the `theorem` keyword.
struct SurfaceDefinitionDeclaration {
    std::string name;
    std::vector<std::string> universeParameters;
    std::vector<SurfaceBinder> arguments;
    SurfaceExpressionPointer type;
    SurfaceExpressionPointer body;   // null if pattern form
    std::vector<SurfacePatternCase> cases;
    bool isTheorem = false;
};

struct SurfaceImportDeclaration  { std::string moduleName; };
// using <namespace>.operators / .literals / .{name, name, ...}
struct SurfaceUsingDeclaration {
    std::string namespacePath;       // e.g. "Natural"
    std::string target;              // "operators" / "literals" / "names"
    std::vector<std::string> names;  // populated when target == "names"
};

using SurfaceTopStatement = std::variant<
    SurfaceImportDeclaration, SurfaceUsingDeclaration,
    SurfaceInductiveDeclaration, SurfaceAxiomDeclaration, SurfaceDefinitionDeclaration
>;

struct SurfaceModule {
    std::string moduleName;
    std::vector<SurfaceTopStatement> statements;
};

