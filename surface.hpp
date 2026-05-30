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
// An argument in a function call. `name` is empty for positional
// arguments and holds the parameter name for `name := value` named
// arguments. The elaborator uses the function's Pi-binder displayHints
// to reorder named arguments into positional order before the rest of
// the application-dispatch logic fires.
struct SurfaceArgument {
    std::string name;                       // empty = positional
    SurfaceExpressionPointer value;
};

struct SurfaceApplication {
    SurfaceExpressionPointer function;
    std::vector<SurfaceArgument> arguments;
};
struct SurfacePiType {
    SurfaceBinder binder;
    SurfaceExpressionPointer codomain;
};
struct SurfaceLambda {
    SurfaceBinder binder;
    SurfaceExpressionPointer body;
    // True when this lambda was synthesised by the parser from a
    // statement-level introduction (`suppose P as h;`). Used by the
    // elaborator's unused-name warning: a `function (x : T) => ...`
    // that doesn't reference `x` is often intentional (constant
    // functions, e.g.), but a `suppose P as h;` whose body ignores
    // `h` is almost always a leftover from a refactor.
    bool fromStatementIntro = false;
};
struct SurfaceLet {
    std::string name;
    SurfaceExpressionPointer type;
    SurfaceExpressionPointer value;
    SurfaceExpressionPointer body;
    // True when this binding came from `calc … as NAME;` with an
    // explicit user-supplied NAME (not from the anonymous
    // `calc …;` form, whose synthesised `_calc_<line>_<col>` name
    // is already excluded from unused-name checks). The auto-prover
    // can discharge subsequent calc-step `by`s via type-match
    // against the let-binder, satisfying the kernel-level BV(0)
    // reference even when the body never *textually* references
    // NAME — so the surface-text check below catches the case
    // where the `as NAME` adds noise without adding readability.
    bool fromCalcAsBinding = false;
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
    // `cases X with equalityHypothesisName { … }` — when non-empty,
    // each arm gets an additional binder
    //   `equalityHypothesisName : X = <constructor pattern>`
    // in scope, generated via the standard convoy desugaring.
    std::string equalityHypothesisName;
    // `cases X refining h1, h2, … { … }` — when non-empty, each listed
    // in-scope binder gets its type refined per arm (the scrutinee in
    // its type is substituted by the constructor pattern). Implemented
    // by wrapping the goal in a Π over the listed binders, wrapping
    // each arm body in `function (h1) (h2) … =>`, and applying the
    // resulting cases to (h1, h2, …) from the outer context. Compatible
    // with `with equalityHypothesisName` (both can be used together).
    std::vector<std::string> refiningNames;
};

// `sorry` — placeholder for an unwritten proof. Desugars at elaboration
// time to `Internal.sorry.{u}(<expectedType>)` and emits a warning at
// the use site so the build log surfaces the gap.
struct SurfaceSorry { };

// `note goal : T;` and `note <proposition>;` — elaboration-time
// assertions that don't change the proof state but cause a check.
// `note goal : T` asserts that the current expected type is
// definitionally equal to `T` (math-prose "we need to show that …");
// `note <proposition>` asserts that the proposition is closable by
// the auto-prover (math-prose "note that …" / "observe that …").
//
// Exactly one of `goalType` and `proposition` is non-null. `body`
// is the remainder of the block — elaborated at the unchanged
// expected type once the check passes.
struct SurfaceNote {
    SurfaceExpressionPointer goalType;       // `note goal : T;`
    SurfaceExpressionPointer proposition;    // `note P;`
    SurfaceExpressionPointer body;
};

// `decide P { | yes m => arm_yes  | no n => arm_no }` —
// classical case-split on whether P holds. Elaborates by binding
// `_decideScrutinee := Logic.classical_decidable(P)`, abstracting
// every structural occurrence of that scrutinee in the expected type
// to form a motive, and applying Logic.Decidable_recursor with the
// two arms. The arm body's expected type is the goal with the
// constructor (yes(m) / no(n)) substituted in — so the kernel
// ι-reduces any wrapping like `bisectionStepWithDec(…, decision)`
// against the constructor form, and the user just writes the math
// witness.
//
// Either binder may be `_` (the unused-marker name); we still bind a
// fresh identifier internally so the constructor application is
// well-typed.
struct SurfaceDecide {
    SurfaceExpressionPointer proposition;
    std::string yesBinderName;
    SurfaceExpressionPointer yesBody;
    std::string noBinderName;
    SurfaceExpressionPointer noBody;
};

// `ring` — closes an equality goal in a known commutative-ring carrier
// (Integer, Rational, …) by reifying both sides as polynomial
// expressions, normalizing them to a canonical sum-of-products form,
// and emitting an explicit proof using the carrier's
// associativity / commutativity / distributivity lemmas.
struct SurfaceRing { };

// `field(h1, h2, ...)` — closes an equality goal in a field by clearing
// `reciprocal_function(t)` occurrences with the user-supplied nonzero
// hypotheses `h_i : ¬(t_i = zero)`, then deferring to `ring` on the
// cleared expression. Built on top of ring v2.
struct SurfaceField {
    std::vector<SurfaceExpressionPointer> nonzeroHypotheses;
};

// `by_induction on scrutinee using inductionLemma with subjectName,
// ihName { body }`. The elaborator constructs the motive by
// abstracting the surrounding expected type over the scrutinee
// variable, extracts the induction-hypothesis type from the lemma's
// step signature, and applies the lemma with motive, step (the user's
// body wrapped in lambdas), and scrutinee.
struct SurfaceByInductionUsing {
    SurfaceExpressionPointer scrutinee;
    SurfaceExpressionPointer inductionLemma;
    std::string subjectName;
    std::string ihName;
    SurfaceExpressionPointer body;
};

// Which relation a calc step asserts between the previous expression
// and `nextExpression`. A chain may mix relations subject to the
// TODO.md "Mixed-relation calc chains" rules:
//
//   | Proving | Allowed in the chain   |
//   | =       | =                      |
//   | ≤       | ≤, =                   |
//   | <       | <, ≤, =                |
//   | ≥       | ≥, =                   |
//   | >       | >, ≥, =                |
//
// Strictness escalates: any < or > step makes the whole chain strict.
// Mixing a "forward" direction step (<, ≤) with a "backward" direction
// step (>, ≥) is rejected at elaboration; = goes either way.
enum class CalcRelation {
    Equality,
    LessOrEqual,
    LessThan,
    GreaterOrEqual,
    GreaterThan,
};

// One step of a `calc` block: the relation that step asserts, a target
// expression the previous expression stands in that relation to, plus
// the proof of that single step.
struct SurfaceCalcStep {
    CalcRelation relation = CalcRelation::Equality;
    SurfaceExpressionPointer nextExpression;
    SurfaceExpressionPointer stepProof;
    int line = 0;
    int column = 0;
};

// `calc <initial> R1 <next1> by <p1> R2 <next2> by <p2> ...`. Each step
// asserts `<previous> Rₖ <nextₖ>` with proof `pₖ`. Currently Rₖ ∈ {=, ≤};
// see CalcRelation. The elaborator composes the chain via
// Equality.transitivity / <T>.LessOrEqual.transitive, upgrading `=` to
// `≤` by rewrite-of-reflexivity wherever the chain mixes relations.
struct SurfaceCalc {
    SurfaceExpressionPointer initialExpression;
    std::vector<SurfaceCalcStep> steps;
};

// One arm of a `claim by cases` block. `in (T) [as name]: body`
// opens an arm where a hypothesis of type `T` is in scope while the
// body proves the surrounding goal. `as name` binds the hypothesis
// under a user-chosen identifier; otherwise it's anonymous and
// reachable only via `given (T)` or the Step 5 lookup.
struct SurfaceStructuredClaimArm {
    SurfaceExpressionPointer disjunctType;
    std::string binderName;            // empty if anonymous
    SurfaceExpressionPointer body;
    int line = 0;
    int column = 0;
};

// `given (P)` — refers to the unique in-scope hypothesis of type P.
// Elaborates to a BoundVariable pointing at the matching local binder
// (errors on zero matches or ambiguity). Useful inside structured-
// proof arm bodies to cite the disjunct-hypothesis by its proposition
// rather than by an internal binder name.
struct SurfaceGiven {
    SurfaceExpressionPointer proposition;
};

// `goal` — refers to the elaborator's current expected type. Reads
// as math: "claim goal by cases { … }", "(some_proof : goal)". The
// elaborator maintains a stack of expected types pushed at every
// elaborateExpression entry with a non-null expectedType; `goal`
// resolves to the most-recent push. Errors when the stack is empty
// (used in a position with no propagating expected type).
struct SurfaceGoal {};

// `?` — placeholder for an argument the elaborator should infer.
// At a function call `f(?, b, c)`, asks the elaborator to fill in
// the first argument by unification against the goal type, against
// the supplied arguments' inferred types, and against in-scope
// hypotheses by type-match. Lets the user write
// `Natural.successor_injective(?, ?, eq)` and have the two
// Natural arguments inferred from the goal.
struct SurfaceHole {};

// `unfold <name> in <body>` — temporarily flips `<name>`'s opacity
// from Opaque to Transparent for the duration of elaborating
// `<body>`. The kernel then δ-unfolds `<name>` freely, so reductions
// the opacity normally blocked fire as if the definition were
// transparent. Restored on return so other proofs still see the
// opaque view. Used at proof sites that need to peek inside an
// otherwise-abstract definition (typically to discharge a kernel-
// computation step like `reflexivity(myDouble(2)) : myDouble(2) =
// 4` when myDouble is opaque). When applied to a transparent
// definition the form is a no-op.
struct SurfaceUnfold {
    std::vector<std::string> names;   // 1+ names to unfold
    SurfaceExpressionPointer body;
};

// `by_strong_induction on <scrutinee> with <subject>, <ih> { body }`
// — single-step strong induction. The elaborator looks up
// `<CarrierType>.strong_induction` (where CarrierType is the head
// of the scrutinee's type) and uses it as the induction lemma.
// IH binder type is `(k : T) → succ(k) ≤ subject → P(k)` (or
// whatever the strong-induction lemma's step signature dictates).
// Body is a single expression proving the conclusion, NOT case-
// clauses (use the existing `by_induction on E with IH { case … }`
// for Peano-style case-split).
struct SurfaceByStrongInduction {
    SurfaceExpressionPointer scrutinee;
    std::string subjectName;
    std::string ihName;
    SurfaceExpressionPointer body;
};

// `choose <name> such that <predicate>;` — Exists-elimination via
// scope lookup. At elaboration:
//   1. Scan local binders last-first for a hypothesis whose type
//      WHNFs to `Exists(T, motive)`.
//   2. Bind `<name> : T` temporarily; elaborate `<predicate>` under
//      the extended scope; compare to `motive(<name>)` modulo defeq.
//   3. First match wins (most-recent rule); destructure to bind
//      `<name>` and an anonymous predicate hypothesis, then continue
//      elaborating the body.
// User can prepend an explicit `claim Exists(...)` to disambiguate
// when multiple existentials are in scope.
struct SurfaceChoose {
    std::string name;
    SurfaceExpressionPointer predicate;
    SurfaceExpressionPointer body;
};

// `claim` — a structured-proof step in mathematician style. Forms:
//   - `claim P`               : assert P (lookup proof from scope).
//   - `claim P by Hint`       : prove P from Hint (auto-fills args).
//   - `claim P by cases { in (A): body  in (B): body }`
//                             : prove P by case-split on an in-scope
//                               disjunction whose disjuncts match the
//                               arm headers.
//   - `claim by Hint`         : discharge current goal from Hint.
//   - `claim by cases { … }`  : discharge current goal by cases.
//   - `claim`                 : discharge current goal by lookup.
// In a structured-proof sequence (multiple claims one after another),
// each non-terminal claim is wrapped at parse time into a SurfaceLet
// that introduces its proof as an anonymous binder for the following
// statements. The final claim becomes the block's value.
struct SurfaceStructuredClaim {
    SurfaceExpressionPointer proposition;       // null for bare `claim`
    std::string label;                          // empty if no label
    SurfaceExpressionPointer byHint;            // null if no `by`
    bool byCases = false;                       // `by cases { … }`
    std::vector<SurfaceStructuredClaimArm> arms; // arms when byCases
    // `by induction on E [with ih] [refining …] { case … }` packages
    // a SurfaceCases (or SurfaceCasesWithRefining) into byHint and
    // sets byInduction=true. The elaborator dispatches by passing the
    // claim's proposition as the expected type so the cases-block
    // motive abstracts over E correctly. The IH name (when given)
    // and refining list are already baked into the SurfaceCases at
    // parse time.
    bool byInduction = false;                   // `by induction on … { … }`
    // `by substitution` (no arg) — auto-find equality + body via the
    // unified equality bridge. `by substituting <eqExpression>` —
    // narrow the search to the supplied equality. The eqExpression
    // (if any) is stored in `byHint`; bySubstitution=true is the
    // discriminator.
    bool bySubstitution = false;
};

struct SurfaceExpression {
    std::variant<
        SurfaceIdentifier, SurfaceNumericLiteral,
        SurfaceApplication, SurfacePiType, SurfaceLambda,
        SurfaceLet, SurfaceAscription, SurfaceType, SurfaceProposition,
        SurfaceBinaryOperation, SurfaceUnaryOperation,
        SurfaceAnonymousTuple, SurfaceCases, SurfaceSorry,
        SurfaceRing, SurfaceField, SurfaceCalc, SurfaceByInductionUsing,
        SurfaceStructuredClaim, SurfaceGiven, SurfaceChoose,
        SurfaceByStrongInduction, SurfaceGoal, SurfaceUnfold,
        SurfaceDecide, SurfaceNote, SurfaceHole
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
    std::vector<SurfaceArgument> arguments,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceApplication{std::move(function), std::move(arguments)},
        line, column});
}

// Backward-compat overload: accepts a positional-only argument list
// (wraps each value in a `SurfaceArgument` with an empty name).
inline SurfaceExpressionPointer makeSurfaceApplication(
    SurfaceExpressionPointer function,
    std::vector<SurfaceExpressionPointer> positionalArguments,
    int line, int column) {
    std::vector<SurfaceArgument> arguments;
    arguments.reserve(positionalArguments.size());
    for (auto& value : positionalArguments) {
        arguments.push_back({"", std::move(value)});
    }
    return makeSurfaceApplication(
        std::move(function), std::move(arguments), line, column);
}
inline SurfaceExpressionPointer makeSurfacePiType(
    SurfaceBinder binder, SurfaceExpressionPointer codomain,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfacePiType{std::move(binder), std::move(codomain)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceLambda(
    SurfaceBinder binder, SurfaceExpressionPointer body,
    int line, int column, bool fromStatementIntro = false) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceLambda{std::move(binder), std::move(body),
                        fromStatementIntro},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceLet(
    std::string name, SurfaceExpressionPointer type,
    SurfaceExpressionPointer value, SurfaceExpressionPointer body,
    int line, int column,
    bool fromCalcAsBinding = false) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceLet{std::move(name), std::move(type),
                   std::move(value), std::move(body),
                   fromCalcAsBinding},
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
inline SurfaceExpressionPointer makeSurfaceSorry(int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceSorry{}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceNote(
    SurfaceExpressionPointer goalType,
    SurfaceExpressionPointer proposition,
    SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceNote{std::move(goalType), std::move(proposition),
                     std::move(body)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceDecide(
    SurfaceExpressionPointer proposition,
    std::string yesBinderName,
    SurfaceExpressionPointer yesBody,
    std::string noBinderName,
    SurfaceExpressionPointer noBody,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceDecide{std::move(proposition),
                       std::move(yesBinderName), std::move(yesBody),
                       std::move(noBinderName), std::move(noBody)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceRing(int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceRing{}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceField(
    std::vector<SurfaceExpressionPointer> nonzeroHypotheses,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceField{std::move(nonzeroHypotheses)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceCalc(
    SurfaceExpressionPointer initialExpression,
    std::vector<SurfaceCalcStep> steps,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceCalc{std::move(initialExpression), std::move(steps)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceByInductionUsing(
    SurfaceExpressionPointer scrutinee,
    SurfaceExpressionPointer inductionLemma,
    std::string subjectName,
    std::string ihName,
    SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceByInductionUsing{std::move(scrutinee),
                                 std::move(inductionLemma),
                                 std::move(subjectName),
                                 std::move(ihName),
                                 std::move(body)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceGiven(
    SurfaceExpressionPointer proposition, int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceGiven{std::move(proposition)}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceGoal(int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceGoal{}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceHole(int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceHole{}, line, column});
}
inline SurfaceExpressionPointer makeSurfaceUnfold(
    std::vector<std::string> names,
    SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceUnfold{std::move(names), std::move(body)},
        line, column});
}
inline SurfaceExpressionPointer makeSurfaceStructuredClaim(
    SurfaceExpressionPointer proposition,
    std::string label,
    SurfaceExpressionPointer byHint,
    bool byCases,
    std::vector<SurfaceStructuredClaimArm> arms,
    int line, int column,
    bool byInduction = false,
    bool bySubstitution = false) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceStructuredClaim{std::move(proposition), std::move(label),
                                std::move(byHint), byCases,
                                std::move(arms), byInduction,
                                bySubstitution},
        line, column});
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
        SurfaceCases{std::move(scrutinee), std::move(clauses), {}, {}},
        line, column});
}

inline SurfaceExpressionPointer makeSurfaceChoose(
    std::string name,
    SurfaceExpressionPointer predicate,
    SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceChoose{std::move(name), std::move(predicate),
                       std::move(body)},
        line, column});
}

inline SurfaceExpressionPointer makeSurfaceByStrongInduction(
    SurfaceExpressionPointer scrutinee,
    std::string subjectName,
    std::string ihName,
    SurfaceExpressionPointer body,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceByStrongInduction{std::move(scrutinee),
                                  std::move(subjectName),
                                  std::move(ihName),
                                  std::move(body)},
        line, column});
}

inline SurfaceExpressionPointer makeSurfaceCasesWithEqualityHypothesis(
    SurfaceExpressionPointer scrutinee,
    std::vector<SurfaceCasesClause> clauses,
    std::string equalityHypothesisName,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceCases{std::move(scrutinee), std::move(clauses),
                      std::move(equalityHypothesisName), {}},
        line, column});
}

inline SurfaceExpressionPointer makeSurfaceCasesWithRefining(
    SurfaceExpressionPointer scrutinee,
    std::vector<SurfaceCasesClause> clauses,
    std::string equalityHypothesisName,
    std::vector<std::string> refiningNames,
    int line, int column) {
    return std::make_shared<const SurfaceExpression>(SurfaceExpression{
        SurfaceCases{std::move(scrutinee), std::move(clauses),
                      std::move(equalityHypothesisName),
                      std::move(refiningNames)},
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
    // `opaque definition Name … := body` blocks the kernel from
    // δ-unfolding `Name` during reduction. Proofs needing the body
    // must invoke `unfold Name` or rely on named characterising
    // lemmas. Not allowed on theorems (theorems' bodies are
    // proofs; proof irrelevance already gives a stronger form of
    // opacity). Forwarded to the kernel via `addDefinition`'s
    // Opacity parameter.
    bool opaque = false;
    // `construction Name(args) : T := body` — a transparent definition
    // additionally registered as a *canonical constructor* (a named
    // quotient-introduction form). Elaborates identically to a
    // definition; the flag drives registration in the elaborator's
    // canonical-constructor registry, which `by_representatives` and the
    // printer use to fold representative terms back to `Name(args)`.
    bool isConstruction = false;
};

struct SurfaceImportDeclaration  { std::string moduleName; };
// using <namespace>.operators / .literals / .{name, name, ...}
struct SurfaceUsingDeclaration {
    std::string namespacePath;       // e.g. "Natural"
    std::string target;              // "operators" / "literals" / "names"
    std::vector<std::string> names;  // populated when target == "names"
};

// `operator (<symbol>) on (<leftTypeName>, <rightTypeName>) := <function>`
// Registers a function as the dispatch target for an arithmetic /
// comparison operator on the given pair of operand head-type names. The
// types are referenced by their head Constant name only — so
// `Rational` is fine, but a structural type expression like
// `Quotient(...)` is not. Result type is whatever the function returns.
struct SurfaceOperatorDeclaration {
    std::string operatorSymbol;
    std::string leftTypeName;
    std::string rightTypeName;
    std::string functionName;
};

// `overload <alias> := <function>` — registers `function` as a member of
// the overload set named `alias`. Multiple `overload alias := F1;` and
// `overload alias := F2;` declarations build up the set; the elaborator
// resolves `alias(args…)` by matching argument types against each
// member's parameter types and picking the unique match.
struct SurfaceOverloadDeclaration {
    std::string aliasName;
    std::string functionName;
};

// `convention <name+> : <type> [with <propBinder>+];` — name-bound
// implicit binders. Any subsequent definition or theorem that
// mentions a convention-bound name as a free identifier in its
// signature gets `{name : type} {hypName : prop1} ...` prepended to
// its binder list as implicit binders. This is the file-level
// equivalent of math books saying "throughout this chapter, p and q
// denote prime numbers."
//
// Each `with` clause is one of:
//   - `<prop>`            — anonymous hypothesis (auto-named `_convention_hN`)
//   - `<name> : <prop>`   — named hypothesis the body can refer to
struct SurfaceConventionProposition {
    std::string name;            // empty for anonymous
    SurfaceExpressionPointer proposition;
};
struct SurfaceConventionDeclaration {
    std::vector<std::string> names;          // e.g. ["p", "q"]
    SurfaceExpressionPointer type;           // e.g. Natural
    std::vector<SurfaceConventionProposition> propositions;
};

// `coercion (<sourceTypeName>, <targetTypeName>) := <function>` —
// registers `function` (which must have type `source → target`) as the
// canonical embedding from `source` into `target`. Triggered by
// `(expr : target)` ascription when `expr` has type `source`. The
// elaborator computes the transitive closure at registration time, so a
// chain `Natural → Integer → Rational` exposes `(n : Rational)` as one
// step; a registration that would create a diamond (two distinct paths
// from the same source to the same target) is rejected.
struct SurfaceCoercionDeclaration {
    std::string sourceTypeName;
    std::string targetTypeName;
    std::string functionName;
};

using SurfaceTopStatement = std::variant<
    SurfaceImportDeclaration, SurfaceUsingDeclaration,
    SurfaceInductiveDeclaration, SurfaceAxiomDeclaration,
    SurfaceDefinitionDeclaration,
    SurfaceOperatorDeclaration, SurfaceOverloadDeclaration,
    SurfaceCoercionDeclaration,
    SurfaceConventionDeclaration
>;

struct SurfaceModule {
    std::string moduleName;
    std::vector<SurfaceTopStatement> statements;
};

