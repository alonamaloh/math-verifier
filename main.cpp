#include "elaborator.hpp"
#include "expression.hpp"
#include "kernel.hpp"
#include "lexer.hpp"
#include "parser.hpp"
#include "printer.hpp"
#include "surface.hpp"

#include <fstream>
#include <iostream>
#include <random>
#include <sstream>
#include <string>

namespace {

int passed = 0;
int failed = 0;

void runExample(const Environment& environment,
                const std::string& title,
                ExpressionPointer term) {
    std::cout << title << "\n";
    std::cout << "  term: " << prettyPrint(term) << "\n";
    try {
        auto type = inferType(environment, {}, term);
        std::cout << "  type: " << prettyPrint(type) << "\n";
    } catch (const TypeError& error) {
        std::cout << "  TYPE ERROR: " << error.what() << "\n";
    }
    std::cout << "\n";
}

void expectTrue(bool condition, const char* description, int line) {
    if (condition) {
        ++passed;
    } else {
        ++failed;
        std::cerr << "FAIL (line " << line << "): " << description << "\n";
    }
}

template <typename Thunk>
void expectThrow(Thunk thunk, const char* description, int line) {
    bool threw = false;
    try {
        thunk();
    } catch (const TypeError&) {
        threw = true;
    }
    if (threw) {
        ++passed;
    } else {
        ++failed;
        std::cerr << "FAIL (line " << line << "): expected TypeError from "
                  << description << "\n";
    }
}

void expectEqualStrings(const std::string& actual, const std::string& expected,
                        const char* description, int line) {
    if (actual == expected) {
        ++passed;
    } else {
        ++failed;
        std::cerr << "FAIL (line " << line << "): " << description << "\n"
                  << "  expected: \"" << expected << "\"\n"
                  << "  actual:   \"" << actual   << "\"\n";
    }
}

#define EXPECT_TRUE(condition)   expectTrue((condition), #condition, __LINE__)
#define EXPECT_FALSE(condition)  expectTrue(!(condition), "not " #condition, __LINE__)
#define EXPECT_THROW(expression) expectThrow([&]{ (void)(expression); }, \
                                             #expression, __LINE__)
#define EXPECT_PRINTS(expression, expected) \
    expectEqualStrings(prettyPrint(expression), (expected), #expression, __LINE__)
#define EXPECT_LEVEL_PRINTS(level, expected) \
    expectEqualStrings(prettyPrintLevel(level), (expected), #level, __LINE__)

void runCoreTests() {
    std::cout << "--- core tests ---\n";

    Environment environment;

    // Type level : Type (level+1) for several levels.
    for (int level = 0; level < 3; ++level) {
        auto inferredType = inferType(environment, {}, makeSort(level));
        auto* sort = std::get_if<Sort>(&inferredType->node);
        EXPECT_TRUE(sort != nullptr &&
                    levelAsConstant(sort->level) &&
                    *levelAsConstant(sort->level) == level + 1);
    }

    EXPECT_THROW(inferType(environment, {}, makeFreeVariable("nope")));
    EXPECT_THROW(inferType(environment, {},
                           makeApplication(makeType(0), makeType(0))));

    {
        Context context = {{"y", makeType(1)}};
        auto identityAtType0 = makeLambda("x", makeType(0), makeBoundVariable(0));
        EXPECT_THROW(inferType(environment, context,
                               makeApplication(identityAtType0,
                                               makeFreeVariable("y"))));
    }

    {
        auto applied = makeApplication(
            makeLambda("A", makeType(1), makeBoundVariable(0)),
            makeType(0));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {}, applied, makeType(0)));
    }

    {
        auto identityA = makeLambda("A", makeType(0), makeBoundVariable(0));
        auto identityB = makeLambda("B", makeType(0), makeBoundVariable(0));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {}, identityA, identityB));
    }

    {
        auto polymorphicIdentity = makeLambda(
            "A", makeType(0),
            makeLambda("x", makeBoundVariable(0), makeBoundVariable(0)));
        auto polymorphicIdentityType =
            inferType(environment, {}, polymorphicIdentity);
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          polymorphicIdentityType,
                                          polymorphicIdentityType));
    }

    {
        Context context = {{"T", makeType(0)}, {"n", makeFreeVariable("T")}};
        EXPECT_THROW(inferType(environment, context,
                               makePi("z", makeFreeVariable("n"), makeType(0))));
    }
}

// Build an environment populated with a tiny natural-numbers theory plus
// propositional equality. Returns the environment so tests can reuse it.
Environment buildArithmeticEnvironment() {
    Environment environment;

    // Natural as a real inductive type with constructors zero and successor.
    // Adds Natural, zero, successor, and Natural_recursor to the environment
    // atomically. zero and successor become Constructor declarations; the
    // recursor is an auto-generated kernel-recognised Recursor declaration
    // that participates in ι-reduction.
    addInductive(environment, "Natural", makeType(0), {
        {"zero", makeConstant("Natural")},
        {"successor",
            makePi("n", makeConstant("Natural"), makeConstant("Natural"))},
    });

    // Equality as an inductive type:
    //
    //   inductive Equality.{u} (A : Type u) (x : A) : A → Proposition
    //     | reflexivity : Equality A x x
    //
    // This subsumes the older axiomatic Equality + reflexivity pair. Now
    // that Equality is inductive, the kernel auto-generates
    // Equality_recursor (with motive at any universe — singleton
    // elimination applies since there is exactly one constructor with no
    // non-parameter arguments), which is what derived lemmas like
    // Equality.symmetry and Equality.transitivity use to reason by
    // induction on a proof of equality.
    addInductive(environment, "Equality", {"u"},
        makePi("A", makeType(makeLevelParam("u")),
          makePi("x", makeBoundVariable(0),
            makePi("y", makeBoundVariable(1),
              makeProposition()))),
        /*numParameters=*/ 2,
        {{
            "reflexivity",
            makePi("A", makeType(makeLevelParam("u")),
              makePi("x", makeBoundVariable(0),
                makeApplication(
                  makeApplication(
                    makeApplication(
                        makeConstant("Equality", {makeLevelParam("u")}),
                        makeBoundVariable(1) /* A */),
                    makeBoundVariable(0) /* x */),
                  makeBoundVariable(0) /* x */)))
        }});

    // one : Natural := successor zero
    addDefinition(environment, "one",
        makeConstant("Natural"),
        makeApplication(makeConstant("successor"), makeConstant("zero")));

    // two : Natural := successor one
    addDefinition(environment, "two",
        makeConstant("Natural"),
        makeApplication(makeConstant("successor"), makeConstant("one")));

    // oneAlias : Natural := one      (used to test δ-reduction chains)
    addDefinition(environment, "oneAlias",
        makeConstant("Natural"),
        makeConstant("one"));

    // add : Π(n : Natural). Π(m : Natural). Natural
    //
    //   add n m = Natural_recursor
    //               (λ_ : Natural. Natural → Natural)        -- motive
    //               (λm : Natural. m)                        -- case_zero
    //               (λk recK m. successor (recK m))          -- case_successor
    //               n m
    //
    // We use the recursor's result (a Natural → Natural) and apply it to m.
    // ι-reduction will collapse add zero m to m, and add (successor k) m to
    // successor (add k m).
    {
        auto naturalToNatural = makePi(
            "_", makeConstant("Natural"), makeConstant("Natural"));

        auto motive = makeLambda("_", makeConstant("Natural"), naturalToNatural);
        auto caseZero = makeLambda("m", makeConstant("Natural"),
                                   makeBoundVariable(0));
        auto caseSuccessor = makeLambda("k", makeConstant("Natural"),
            makeLambda("recK", naturalToNatural,
              makeLambda("m", makeConstant("Natural"),
                makeApplication(
                    makeConstant("successor"),
                    makeApplication(makeBoundVariable(1) /* recK */,
                                    makeBoundVariable(0) /* m */)))));

        auto addBody = makeLambda("n", makeConstant("Natural"),
            makeLambda("m", makeConstant("Natural"),
              makeApplication(
                makeApplication(
                  makeApplication(
                    makeApplication(
                      makeApplication(makeConstant("Natural_recursor", {makeLevelConst(1)}),
                                      motive),
                      caseZero),
                    caseSuccessor),
                  makeBoundVariable(1) /* n */),
                makeBoundVariable(0) /* m */)));

        auto addType = makePi("n", makeConstant("Natural"),
                          makePi("m", makeConstant("Natural"),
                            makeConstant("Natural")));

        addDefinition(environment, "add", addType, addBody);
    }

    return environment;
}

void runEnvironmentTests(const Environment& environment) {
    std::cout << "--- environment tests ---\n";

    // Looking up a constant: zero : Natural.
    {
        auto inferredType = inferType(environment, {}, makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          inferredType,
                                          makeConstant("Natural")));
    }

    // successor : Natural -> Natural
    {
        auto inferredType = inferType(environment, {}, makeConstant("successor"));
        auto expected = makePi("_", makeConstant("Natural"), makeConstant("Natural"));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {}, inferredType, expected));
    }

    // successor zero : Natural
    {
        auto inferredType = inferType(
            environment, {},
            makeApplication(makeConstant("successor"), makeConstant("zero")));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          inferredType,
                                          makeConstant("Natural")));
    }

    // reflexivity Natural zero : Equality Natural zero zero  — a real proof.
    {
        auto proof = makeApplication(
            makeApplication(makeConstant("reflexivity", {makeLevelConst(0)}), makeConstant("Natural")),
            makeConstant("zero"));
        auto inferredType = inferType(environment, {}, proof);
        auto expected = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}), makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {}, inferredType, expected));
    }

    // δ-unfolding: oneAlias unfolds through one to (successor zero).
    {
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          makeConstant("oneAlias"),
                                          makeConstant("one")));
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeConstant("oneAlias"),
            makeApplication(makeConstant("successor"), makeConstant("zero"))));
    }

    // two and one are NOT definitionally equal.
    {
        EXPECT_TRUE(!isDefinitionallyEqual(environment, {},
                                           makeConstant("two"),
                                           makeConstant("one")));
    }

    // Over-application of reflexivity is rejected: after two arguments, the
    // result has type Equality Natural zero zero, which is not a Pi.
    {
        auto overApplied = makeApplication(
            makeApplication(
                makeApplication(makeConstant("reflexivity", {makeLevelConst(0)}), makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("one"));
        EXPECT_THROW(inferType(environment, {}, overApplied));
    }

    // addAxiom rejects duplicate names.
    {
        Environment localEnvironment = environment;
        EXPECT_THROW(addAxiom(localEnvironment, "Natural", makeType(0)));
    }

    // addDefinition rejects a body whose type does not match the declared
    // type. Declare "bad : Natural := reflexivity Natural zero" — but the
    // body has type Equality Natural zero zero, not Natural.
    {
        Environment localEnvironment = environment;
        EXPECT_THROW(addDefinition(
            localEnvironment, "bad", makeConstant("Natural"),
            makeApplication(
                makeApplication(makeConstant("reflexivity", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero"))));
    }

    // Undefined constants throw.
    EXPECT_THROW(inferType(environment, {}, makeConstant("does_not_exist")));

    // Let bindings: let n : Natural := zero in successor n.
    // After ζ-reduction the body is "successor zero", which has type Natural.
    {
        auto letExpression = makeLet(
            "n", makeConstant("Natural"), makeConstant("zero"),
            makeApplication(makeConstant("successor"), makeBoundVariable(0)));
        auto inferredType = inferType(environment, {}, letExpression);
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          inferredType,
                                          makeConstant("Natural")));
        // The whole let-expression is definitionally equal to successor zero.
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {}, letExpression,
            makeApplication(makeConstant("successor"), makeConstant("zero"))));
    }

    // Let rejects a value whose type does not match the declared type:
    //   let n : Natural := reflexivity Natural zero in zero
    {
        auto bogusLet = makeLet(
            "n", makeConstant("Natural"),
            makeApplication(
                makeApplication(makeConstant("reflexivity", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        EXPECT_THROW(inferType(environment, {}, bogusLet));
    }

    // η-conversion: λ(n : Natural). successor n  ≡  successor.
    {
        auto etaLambda = makeLambda(
            "n", makeConstant("Natural"),
            makeApplication(makeConstant("successor"), makeBoundVariable(0)));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          etaLambda,
                                          makeConstant("successor")));
    }

    // η does not equate distinct functions: λ(n : Natural). zero  ≢  successor.
    {
        auto constantZero = makeLambda(
            "n", makeConstant("Natural"), makeConstant("zero"));
        EXPECT_TRUE(!isDefinitionallyEqual(environment, {},
                                           constantZero,
                                           makeConstant("successor")));
    }

    // Proposition and impredicativity: Equality lives in Proposition. Reflexivity's full
    // type therefore also lives in Proposition:
    //   reflexivity : ∀(A : Type 0). ∀(x : A). Equality A x x   : Proposition
    {
        auto reflexivityType =
            inferType(environment, {}, makeConstant("reflexivity", {makeLevelConst(0)}));
        auto reflexivityKind =
            weakHeadNormalForm(environment,
                               inferType(environment, {}, reflexivityType));
        auto* sort = std::get_if<Sort>(&reflexivityKind->node);
        EXPECT_TRUE(sort != nullptr &&
                    levelAsConstant(sort->level) &&
                    *levelAsConstant(sort->level) == 0);
    }

    // Π(P : Proposition). P — quantifying over all propositions, itself a Proposition.
    // This is the impredicative encoding of False (and of any quantifier
    // that ranges over Proposition). Impredicativity fires here because the
    // codomain P has type Proposition (universe 0), so imax(_, 0) = 0.
    {
        auto term = makePi("P", makeProposition(), makeBoundVariable(0));
        auto kind = weakHeadNormalForm(environment,
                                       inferType(environment, {}, term));
        auto* sort = std::get_if<Sort>(&kind->node);
        EXPECT_TRUE(sort != nullptr &&
                    levelAsConstant(sort->level) &&
                    *levelAsConstant(sort->level) == 0);  // Proposition
    }

    // Π(_ : Proposition). Proposition is NOT in Proposition — its codomain is the *type* Proposition
    // (which lives in Type 0), not a proposition. Result is Type 0.
    {
        auto term = makePi("_", makeProposition(), makeProposition());
        auto kind = weakHeadNormalForm(environment,
                                       inferType(environment, {}, term));
        auto* sort = std::get_if<Sort>(&kind->node);
        EXPECT_TRUE(sort != nullptr &&
                    levelAsConstant(sort->level) &&
                    *levelAsConstant(sort->level) == 1);  // Type 0
    }

    // Π(_ : Type 0). Type 0 lives in Type 1.
    {
        auto term = makePi("_", makeType(0), makeType(0));
        auto kind = weakHeadNormalForm(environment,
                                       inferType(environment, {}, term));
        auto* sort = std::get_if<Sort>(&kind->node);
        EXPECT_TRUE(sort != nullptr &&
                    levelAsConstant(sort->level) &&
                    *levelAsConstant(sort->level) == 2);  // Type 1
    }

    // Universe cumulativity: a function expecting Type 1 accepts a Type 0
    // argument. Natural : Type 0, but Type 0 <: Type 1, so passing Natural
    // where a Type 1 is expected is fine.
    {
        // f := λ(t : Type 1). zero  has type Π(t : Type 1). Natural.
        auto f = makeLambda("t", makeType(1), makeConstant("zero"));
        // Apply f to Natural (which has type Type 0).
        auto applied = makeApplication(f, makeConstant("Natural"));
        auto inferredType = inferType(environment, {}, applied);
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          inferredType,
                                          makeConstant("Natural")));
    }

    // But cumulativity is one-way: Type 1 is NOT a subtype of Type 0. So a
    // function expecting Type 0 rejects a Type 1 argument.
    {
        auto f = makeLambda("t", makeType(0), makeConstant("zero"));
        // Type 0 itself has type Type 1 (a level too high), so this fails.
        auto applied = makeApplication(f, makeType(1));
        EXPECT_THROW(inferType(environment, {}, applied));
    }

    // Cumulativity on definitions: declaring  alias : Type 1 := Natural
    // works because Natural : Type 0 <: Type 1.
    {
        Environment localEnvironment = environment;
        addDefinition(localEnvironment, "natAtTypeOne",
                      makeType(1), makeConstant("Natural"));
        auto inferredType = inferType(localEnvironment, {},
                                      makeConstant("natAtTypeOne"));
        EXPECT_TRUE(isDefinitionallyEqual(localEnvironment, {}, inferredType,
                                          makeType(1)));
    }

    // Proof irrelevance. In a context with two proofs p and q of the same
    // proposition Equality Natural zero zero, the proofs are definitionally
    // equal even though they are structurally distinct free variables.
    {
        auto propositionType = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        Context contextWithProofs = {
            {"p", propositionType},
            {"q", propositionType},
        };
        EXPECT_TRUE(isDefinitionallyEqual(environment, contextWithProofs,
                                          makeFreeVariable("p"),
                                          makeFreeVariable("q")));
    }

    // Proof irrelevance does NOT equate distinct values whose type is not
    // in Proposition. Two distinct free Naturals are not definitionally equal.
    {
        Context contextWithNaturals = {
            {"a", makeConstant("Natural")},
            {"b", makeConstant("Natural")},
        };
        EXPECT_TRUE(!isDefinitionallyEqual(environment, contextWithNaturals,
                                           makeFreeVariable("a"),
                                           makeFreeVariable("b")));
    }

    // The auto-generated Natural_recursor exists and has the expected type
    // structure (a Π beginning with the motive).
    {
        auto recursorType =
            inferType(environment, {}, makeConstant("Natural_recursor", {makeLevelConst(1)}));
        auto recursorTypeReduced =
            weakHeadNormalForm(environment, recursorType);
        EXPECT_TRUE(std::holds_alternative<Pi>(recursorTypeReduced->node));
    }

    // ι-reduction: add zero zero  ≡  zero.
    //   add zero m unfolds and ι-reduces to (λm. m) m which β-reduces to m.
    {
        auto addZeroZero = makeApplication(
            makeApplication(makeConstant("add"), makeConstant("zero")),
            makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          addZeroZero,
                                          makeConstant("zero")));
    }

    // ι-reduction step on the successor case: add one zero  ≡  one.
    //   add (successor zero) zero
    //   → successor (add zero zero)            (ι on successor)
    //   → successor zero                       (ι on zero + β)
    {
        auto one = makeApplication(makeConstant("successor"),
                                   makeConstant("zero"));
        auto addOneZero = makeApplication(
            makeApplication(makeConstant("add"), one), makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          addOneZero, one));
    }

    // Multi-step ι: add two one ≡ three.
    {
        auto one = makeApplication(makeConstant("successor"),
                                   makeConstant("zero"));
        auto two = makeApplication(makeConstant("successor"), one);
        auto three = makeApplication(makeConstant("successor"), two);
        auto addTwoOne = makeApplication(
            makeApplication(makeConstant("add"), two), one);
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          addTwoOne, three));
    }

    // add zero is the identity function on Natural (η plus ι):
    //   add zero  ≡  λm. m
    // After β-reducing add's outer lambda we get λm. Natural_recursor ... zero m,
    // which ι-reduces to (λm. m) m = m, so the whole lambda is η-equal to id.
    {
        auto addZero = makeApplication(
            makeConstant("add"), makeConstant("zero"));
        auto identity = makeLambda("m", makeConstant("Natural"),
                                   makeBoundVariable(0));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          addZero, identity));
    }

    // Universe polymorphism. Equality.{u} can be instantiated at any
    // universe; at Type 0 it asserts equality of small values, at Type 1
    // it asserts equality of Types. Reflexivity proves both.
    {
        // Equality.{0} Natural zero zero  : Proposition
        auto small = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        auto smallKind = weakHeadNormalForm(
            environment, inferType(environment, {}, small));
        auto* smallSort = std::get_if<Sort>(&smallKind->node);
        EXPECT_TRUE(smallSort && levelAsConstant(smallSort->level) &&
                    *levelAsConstant(smallSort->level) == 0);

        // Equality.{1} (Type 0) Natural Natural  : Proposition
        // (Natural : Type 0, so we're stating that the type Natural equals
        // itself.) Lives in Proposition just like Equality.{0} — propositions are
        // always in Proposition regardless of u.
        auto big = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(1)}),
                                makeType(0)),
                makeConstant("Natural")),
            makeConstant("Natural"));
        auto bigKind = weakHeadNormalForm(
            environment, inferType(environment, {}, big));
        auto* bigSort = std::get_if<Sort>(&bigKind->node);
        EXPECT_TRUE(bigSort && levelAsConstant(bigSort->level) &&
                    *levelAsConstant(bigSort->level) == 0);
    }

    // reflexivity.{1} (Type 0) Natural  :  Equality.{1} (Type 0) Natural Natural
    {
        auto proof = makeApplication(
            makeApplication(makeConstant("reflexivity", {makeLevelConst(1)}),
                            makeType(0)),
            makeConstant("Natural"));
        auto inferredType = inferType(environment, {}, proof);
        auto expected = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(1)}),
                                makeType(0)),
                makeConstant("Natural")),
            makeConstant("Natural"));
        EXPECT_TRUE(isDefinitionallyEqual(environment, {},
                                          inferredType, expected));
    }

    // Mismatched universe arity is rejected: Equality declares one universe
    // parameter, so supplying zero arguments must throw.
    {
        EXPECT_THROW(
            inferType(environment, {}, makeConstant("Equality")));
    }
}

// ----------------------------------------------------------------------------
// Level arithmetic: the universe-level expression layer in level.{hpp,cpp}.
// ----------------------------------------------------------------------------

void runLevelArithmeticTests() {
    std::cout << "--- level arithmetic tests ---\n";

    // makeLevelSuccessor folds over concrete levels.
    EXPECT_TRUE(*levelAsConstant(makeLevelSuccessor(makeLevelConst(0))) == 1);
    EXPECT_TRUE(*levelAsConstant(makeLevelSuccessor(makeLevelConst(7))) == 8);

    // makeLevelSuccessor stays symbolic for parameters.
    {
        auto successorOfU = makeLevelSuccessor(makeLevelParam("u"));
        EXPECT_FALSE(levelAsConstant(successorOfU).has_value());
        EXPECT_LEVEL_PRINTS(successorOfU, "u+1");
    }

    // makeLevelMax: concrete vs concrete is folded.
    EXPECT_TRUE(*levelAsConstant(
        makeLevelMax(makeLevelConst(2), makeLevelConst(3))) == 3);
    EXPECT_TRUE(*levelAsConstant(
        makeLevelMax(makeLevelConst(5), makeLevelConst(5))) == 5);

    // makeLevelMax: 0 is the identity on either side.
    {
        auto u = makeLevelParam("u");
        EXPECT_TRUE(levelsDefinitionallyEqual(
            makeLevelMax(makeLevelConst(0), u), u));
        EXPECT_TRUE(levelsDefinitionallyEqual(
            makeLevelMax(u, makeLevelConst(0)), u));
    }

    // makeLevelMax: same level on both sides collapses.
    {
        auto u = makeLevelParam("u");
        EXPECT_TRUE(levelsDefinitionallyEqual(makeLevelMax(u, u), u));
    }

    // makeLevelIMax: codomain 0 collapses the whole thing to 0.
    EXPECT_TRUE(*levelAsConstant(
        makeLevelIMax(makeLevelParam("u"), makeLevelConst(0))) == 0);

    // makeLevelIMax: codomain successor(_) is never 0, so becomes max.
    {
        auto u = makeLevelParam("u");
        auto imaxResult = makeLevelIMax(u, makeLevelSuccessor(makeLevelParam("v")));
        // Should be max(u, successor(v)) — folded.
        EXPECT_LEVEL_PRINTS(imaxResult, "max(u, v+1)");
    }

    // makeLevelIMax stays symbolic when codomain is an unknown parameter.
    {
        auto u = makeLevelParam("u");
        auto v = makeLevelParam("v");
        auto imaxResult = makeLevelIMax(u, v);
        EXPECT_LEVEL_PRINTS(imaxResult, "imax(u, v)");
    }

    // Equality of levels — concrete and symbolic.
    EXPECT_TRUE(levelsDefinitionallyEqual(
        makeLevelConst(3), makeLevelConst(3)));
    EXPECT_FALSE(levelsDefinitionallyEqual(
        makeLevelConst(3), makeLevelConst(4)));
    EXPECT_TRUE(levelsDefinitionallyEqual(
        makeLevelParam("u"), makeLevelParam("u")));
    EXPECT_FALSE(levelsDefinitionallyEqual(
        makeLevelParam("u"), makeLevelParam("v")));
    EXPECT_FALSE(levelsDefinitionallyEqual(
        makeLevelParam("u"), makeLevelConst(0)));

    // levelLessOrEqual on concrete pairs.
    EXPECT_TRUE(levelLessOrEqual(makeLevelConst(0), makeLevelConst(0)));
    EXPECT_TRUE(levelLessOrEqual(makeLevelConst(0), makeLevelConst(3)));
    EXPECT_TRUE(levelLessOrEqual(makeLevelConst(2), makeLevelConst(2)));
    EXPECT_FALSE(levelLessOrEqual(makeLevelConst(4), makeLevelConst(3)));

    // levelLessOrEqual: same parameter is reflexive.
    EXPECT_TRUE(levelLessOrEqual(
        makeLevelParam("u"), makeLevelParam("u")));
    // Different parameters: conservatively false.
    EXPECT_FALSE(levelLessOrEqual(
        makeLevelParam("u"), makeLevelParam("v")));

    // levelLessOrEqual: x <= max(x, y).
    {
        auto u = makeLevelParam("u");
        auto v = makeLevelParam("v");
        EXPECT_TRUE(levelLessOrEqual(u, makeLevelMax(u, v)));
        EXPECT_TRUE(levelLessOrEqual(v, makeLevelMax(u, v)));
    }

    // levelLessOrEqual: successor(a) <= successor(b) iff a <= b.
    EXPECT_TRUE(levelLessOrEqual(
        makeLevelSuccessor(makeLevelConst(2)), makeLevelSuccessor(makeLevelConst(3))));
    EXPECT_FALSE(levelLessOrEqual(
        makeLevelSuccessor(makeLevelConst(3)), makeLevelSuccessor(makeLevelConst(2))));

    // Substitution: replacing the param appears throughout, others are
    // untouched.
    {
        auto level = makeLevelMax(
            makeLevelParam("u"),
            makeLevelSuccessor(makeLevelParam("v")));
        auto substituted = substituteLevelParameter(
            level, "u", makeLevelConst(5));
        EXPECT_LEVEL_PRINTS(substituted, "max(5, v+1)");
    }

    // Substitution on a non-matching name is a no-op.
    {
        auto level = makeLevelParam("v");
        auto substituted = substituteLevelParameter(
            level, "u", makeLevelConst(7));
        EXPECT_TRUE(levelsDefinitionallyEqual(substituted, level));
    }
}

// ----------------------------------------------------------------------------
// Low-level expression operations: shift, substitute, openBinder, closeBinder.
// ----------------------------------------------------------------------------

void runDeBruijnOperationTests() {
    std::cout << "--- shift / substitute / open / close tests ---\n";

    // shift on a bare BoundVariable.
    {
        auto result = shift(makeBoundVariable(0), 1, 0);
        auto* bv = std::get_if<BoundVariable>(&result->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 1);
    }
    {
        auto result = shift(makeBoundVariable(5), 2, 0);
        auto* bv = std::get_if<BoundVariable>(&result->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 7);
    }

    // shift respects the cutoff: indices below cutoff don't move.
    {
        auto result = shift(makeBoundVariable(0), 5, 1);
        auto* bv = std::get_if<BoundVariable>(&result->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 0);
    }
    {
        auto result = shift(makeBoundVariable(2), 5, 1);
        auto* bv = std::get_if<BoundVariable>(&result->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 7);
    }

    // shift leaves FreeVariable, Sort, Constant unchanged.
    {
        auto fv = makeFreeVariable("x");
        EXPECT_TRUE(shift(fv, 3).get() == fv.get());
        auto sort = makeType(0);
        EXPECT_TRUE(shift(sort, 3).get() == sort.get());
        auto c = makeConstant("Foo");
        EXPECT_TRUE(shift(c, 3).get() == c.get());
    }

    // shift under a Pi increments the cutoff in the codomain.
    //   shift(Π(_ : Natural). Bound(1), 1, 0)
    //   The Bound(1) refers OUTSIDE the Pi. Inside the codomain, cutoff is 1.
    //   Bound(1) >= 1, so it shifts to Bound(2).
    {
        auto term = makePi("_", makeConstant("Natural"), makeBoundVariable(1));
        auto shifted = shift(term, 1, 0);
        auto* pi = std::get_if<Pi>(&shifted->node);
        EXPECT_TRUE(pi);
        auto* inner = std::get_if<BoundVariable>(&pi->codomain->node);
        EXPECT_TRUE(inner && inner->deBruijnIndex == 2);
    }

    // shift under a Pi: Bound(0) inside the codomain references the binder
    // itself (inside cutoff after descent), so it stays Bound(0).
    {
        auto term = makePi("_", makeConstant("Natural"), makeBoundVariable(0));
        auto shifted = shift(term, 1, 0);
        auto* pi = std::get_if<Pi>(&shifted->node);
        EXPECT_TRUE(pi);
        auto* inner = std::get_if<BoundVariable>(&pi->codomain->node);
        EXPECT_TRUE(inner && inner->deBruijnIndex == 0);
    }

    // substitute: Bound(0) gets replaced.
    {
        auto result = substitute(makeBoundVariable(0), 0,
                                 makeConstant("zero"));
        auto* c = std::get_if<Constant>(&result->node);
        EXPECT_TRUE(c && c->name == "zero");
    }

    // substitute: higher indices are decremented (binder going away).
    {
        auto result = substitute(makeBoundVariable(3), 0,
                                 makeConstant("zero"));
        auto* bv = std::get_if<BoundVariable>(&result->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 2);
    }

    // substitute: indices below the target are unchanged.
    {
        auto result = substitute(makeBoundVariable(0), 2,
                                 makeConstant("zero"));
        auto* bv = std::get_if<BoundVariable>(&result->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 0);
    }

    // substitute shifts the replacement when crossing a binder. Substitute
    // FreeVariable("v") for index 0 inside Π(_:T). Bound(0). The codomain's
    // Bound(0) refers to its own Pi binder (not target 0 at depth 0); after
    // descent, target becomes 1 and replacement is shift(FreeVar("v"), 1)
    // which is still FreeVar("v"). Inside, Bound(0) != 1, so it's not
    // substituted; it stays Bound(0).
    {
        auto term = makePi("_", makeConstant("T"), makeBoundVariable(0));
        auto result = substitute(term, 0, makeFreeVariable("v"));
        auto* pi = std::get_if<Pi>(&result->node);
        EXPECT_TRUE(pi);
        auto* inner = std::get_if<BoundVariable>(&pi->codomain->node);
        EXPECT_TRUE(inner && inner->deBruijnIndex == 0);
    }

    // substitute does shift the replacement properly. Substitute Bound(0)
    // (an outer reference) into Π(_:T). Bound(1) (which references that
    // outer thing): at depth 1, target=1; Bound(1) matches; replacement is
    // shift(Bound(0), 1) = Bound(1). So we should get Π(_:T). Bound(1).
    {
        auto term = makePi("_", makeConstant("T"), makeBoundVariable(1));
        auto result = substitute(term, 0, makeBoundVariable(0));
        auto* pi = std::get_if<Pi>(&result->node);
        EXPECT_TRUE(pi);
        auto* inner = std::get_if<BoundVariable>(&pi->codomain->node);
        EXPECT_TRUE(inner && inner->deBruijnIndex == 1);
    }

    // openBinder: substitutes BoundVariable(0) with a free variable, leaves
    // higher indices decremented (the binder is conceptually opened).
    {
        auto term = makeBoundVariable(0);
        auto opened = openBinder(term, "x");
        auto* fv = std::get_if<FreeVariable>(&opened->node);
        EXPECT_TRUE(fv && fv->name == "x");
    }

    // closeBinder is the (left) inverse of openBinder for the simple case.
    {
        auto original = makeBoundVariable(0);
        auto opened   = openBinder(original, "x");
        auto closed   = closeBinder(opened,  "x");
        auto* bv = std::get_if<BoundVariable>(&closed->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 0);
    }

    // closeBinder also shifts existing bound vars up by 1 (room for the new
    // outer binder).
    {
        auto original = makeBoundVariable(2);
        auto closed   = closeBinder(original, "nonexistent");
        auto* bv = std::get_if<BoundVariable>(&closed->node);
        EXPECT_TRUE(bv && bv->deBruijnIndex == 3);
    }

    // Origin-tag isolation. The kernel internally uses names like "v0",
    // "v1", "motive", "target" when opening binders or building recursors.
    // A user is free to introduce free variables with those same names; the
    // FreeVariableOrigin tag keeps them distinct from anything the kernel
    // generates internally, so no collision can occur.
    //
    // Here we put a user free variable named "v0" in scope and compare two
    // equivalent terms whose codomain references it. The kernel's first
    // internal opening name (with an empty context) is also "v0" — but
    // Internal-origin — so structurally the two populations coexist.
    {
        Environment empty;
        Context context = {{"v0", makeConstant("PlaceholderType")}};
        // We need PlaceholderType to exist as a type so context entries
        // type-check
        // when the kernel infers types for proof irrelevance.
        Environment localEnvironment;
        addAxiom(localEnvironment, "PlaceholderType", makeType(0));
        auto leftTerm = makePi("y", makeConstant("PlaceholderType"),
                                makeFreeVariable("v0"));
        auto rightTerm = makePi("y", makeConstant("PlaceholderType"),
                                 makeFreeVariable("v0"));
        EXPECT_TRUE(isDefinitionallyEqual(localEnvironment, context,
                                          leftTerm, rightTerm));
        // And two distinct user names "v0" and "motive" don't get confused.
        Context context2 = {{"v0", makeConstant("PlaceholderType")},
                            {"motive", makeConstant("PlaceholderType")}};
        auto leftDifferent = makePi("y", makeConstant("PlaceholderType"),
                                     makeFreeVariable("v0"));
        auto rightDifferent = makePi("y", makeConstant("PlaceholderType"),
                                      makeFreeVariable("motive"));
        EXPECT_FALSE(isDefinitionallyEqual(localEnvironment, context2,
                                           leftDifferent, rightDifferent));
        (void)empty;
    }
}

// ----------------------------------------------------------------------------
// Direct tests of each reduction rule that weakHeadNormalForm implements.
// ----------------------------------------------------------------------------

void runReductionTests(const Environment& arithmetic) {
    std::cout << "--- reduction (β / δ / ζ / ι / idempotence) tests ---\n";

    // β-reduction: (λ(x : T). x) y ↦ y.
    {
        auto applied = makeApplication(
            makeLambda("x", makeConstant("T"), makeBoundVariable(0)),
            makeFreeVariable("y"));
        auto reduced = weakHeadNormalForm({}, applied);
        auto* fv = std::get_if<FreeVariable>(&reduced->node);
        EXPECT_TRUE(fv && fv->name == "y");
    }

    // β-reduction respects substitution under nested binders.
    //   (λ(x : T). λ(y : T). x) a  ↦  λ(y : T). a
    {
        auto applied = makeApplication(
            makeLambda("x", makeConstant("T"),
              makeLambda("y", makeConstant("T"), makeBoundVariable(1))),
            makeFreeVariable("a"));
        auto reduced = weakHeadNormalForm({}, applied);
        auto* lambda = std::get_if<Lambda>(&reduced->node);
        EXPECT_TRUE(lambda);
        if (lambda) {
            auto* body = std::get_if<FreeVariable>(&lambda->body->node);
            EXPECT_TRUE(body && body->name == "a");
        }
    }

    // δ-reduction: a Definition unfolds to its body.
    {
        auto reduced = weakHeadNormalForm(arithmetic, makeConstant("one"));
        // one unfolds to (successor zero). After whnf, head is "successor"
        // (a Constructor, stuck), with one argument "zero".
        auto* app = std::get_if<Application>(&reduced->node);
        EXPECT_TRUE(app);
        if (app) {
            auto* head = std::get_if<Constant>(&app->function->node);
            EXPECT_TRUE(head && head->name == "successor");
        }
    }

    // δ-reduction chains: two Definitions unfold transitively.
    //   oneAlias  ↦  one  ↦  successor zero.
    {
        auto reduced = weakHeadNormalForm(
            arithmetic, makeConstant("oneAlias"));
        auto* app = std::get_if<Application>(&reduced->node);
        EXPECT_TRUE(app);
        if (app) {
            auto* head = std::get_if<Constant>(&app->function->node);
            EXPECT_TRUE(head && head->name == "successor");
            auto* arg = std::get_if<Constant>(&app->argument->node);
            EXPECT_TRUE(arg && arg->name == "zero");
        }
    }

    // ζ-reduction: let x : T := v in body  ↦  body[x := v].
    {
        auto term = makeLet("x", makeConstant("Natural"),
                            makeConstant("zero"),
                            makeBoundVariable(0));
        auto reduced = weakHeadNormalForm(arithmetic, term);
        auto* c = std::get_if<Constant>(&reduced->node);
        EXPECT_TRUE(c && c->name == "zero");
    }

    // ι-reduction: Natural_recursor on zero collapses to case_zero.
    {
        // Natural_recursor (λ_. Natural) case_zero case_successor zero ↦ case_zero
        auto motive = makeLambda("_", makeConstant("Natural"),
                                  makeConstant("Natural"));
        auto caseZero    = makeConstant("zero");
        auto caseSuccessor = makeLambda("k", makeConstant("Natural"),
            makeLambda("_recK", makeConstant("Natural"),
                makeConstant("zero")));
        auto applied = makeApplication(
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Natural_recursor", {makeLevelConst(1)}), motive),
                    caseZero),
                caseSuccessor),
            makeConstant("zero"));
        auto reduced = weakHeadNormalForm(arithmetic, applied);
        auto* c = std::get_if<Constant>(&reduced->node);
        EXPECT_TRUE(c && c->name == "zero");
    }

    // ι-reduction: Natural_recursor on (successor v) inserts a recursive call.
    //   The fully reduced result has head = case_successor applied to v and to
    //   a recursive Natural_recursor call.
    {
        auto motive = makeLambda("_", makeConstant("Natural"),
                                  makeConstant("Natural"));
        auto caseZero    = makeConstant("zero");
        // case_successor k recK = k  (just returns k, ignoring the recursive call).
        auto caseSuccessor = makeLambda("k", makeConstant("Natural"),
            makeLambda("_recK", makeConstant("Natural"),
                makeBoundVariable(1) /* k */));
        auto target = makeApplication(makeConstant("successor"),
                                       makeConstant("zero"));
        auto applied = makeApplication(
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Natural_recursor", {makeLevelConst(1)}), motive),
                    caseZero),
                caseSuccessor),
            target);
        auto reduced = weakHeadNormalForm(arithmetic, applied);
        // case_successor k _ = k, applied to zero, gives zero.
        auto* c = std::get_if<Constant>(&reduced->node);
        EXPECT_TRUE(c && c->name == "zero");
    }

    // ι doesn't fire if the target isn't a constructor application.
    // Here the target is a free variable.
    {
        Context context = {{"n", makeConstant("Natural")}};
        auto motive = makeLambda("_", makeConstant("Natural"),
                                  makeConstant("Natural"));
        auto caseZero = makeConstant("zero");
        auto caseSuccessor = makeLambda("k", makeConstant("Natural"),
            makeLambda("_recK", makeConstant("Natural"),
                makeBoundVariable(1)));
        auto stuck = makeApplication(
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Natural_recursor", {makeLevelConst(1)}), motive),
                    caseZero),
                caseSuccessor),
            makeFreeVariable("n"));
        auto reduced = weakHeadNormalForm(arithmetic, stuck);
        // No reduction: head is still Natural_recursor (a Constant).
        auto spineHead = reduced;
        while (auto* app = std::get_if<Application>(&spineHead->node)) {
            spineHead = app->function;
        }
        auto* c = std::get_if<Constant>(&spineHead->node);
        EXPECT_TRUE(c && c->name == "Natural_recursor");
    }

    // Idempotence: whnf'ing twice gives a definitionally-equal result.
    {
        auto term = makeApplication(
            makeApplication(makeConstant("add"), makeConstant("zero")),
            makeConstant("zero"));
        auto once  = weakHeadNormalForm(arithmetic, term);
        auto twice = weakHeadNormalForm(arithmetic, once);
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, {}, once, twice));
    }

    // whnf doesn't reduce inside binders.
    //   λ(x : Natural). ((λy. y) x)  has a β-redex inside its body, but whnf
    //   should leave the lambda intact.
    {
        auto term = makeLambda("x", makeConstant("Natural"),
            makeApplication(
                makeLambda("y", makeConstant("Natural"), makeBoundVariable(0)),
                makeBoundVariable(0)));
        auto reduced = weakHeadNormalForm(arithmetic, term);
        EXPECT_TRUE(std::holds_alternative<Lambda>(reduced->node));
    }
}

// ----------------------------------------------------------------------------
// Comprehensive negative-path coverage for inferType. Each test produces a
// specific failure mode of the type checker.
// ----------------------------------------------------------------------------

void runInferTypeErrorTests(const Environment& arithmetic) {
    std::cout << "--- inferType error tests ---\n";

    // Unbound free variable.
    EXPECT_THROW(inferType(arithmetic, {}, makeFreeVariable("ghost")));

    // Undefined constant.
    EXPECT_THROW(inferType(arithmetic, {}, makeConstant("ghost")));

    // Constant with wrong universe-argument arity.
    EXPECT_THROW(inferType(arithmetic, {},
        makeConstant("Equality", {makeLevelConst(0), makeLevelConst(1)})));
    EXPECT_THROW(inferType(arithmetic, {},
        makeConstant("Natural", {makeLevelConst(0)})));  // Natural has no params.

    // Pi: domain isn't a type. Pass a Natural value (`zero`) as a domain.
    EXPECT_THROW(inferType(arithmetic, {},
        makePi("_", makeConstant("zero"), makeType(0))));

    // Pi: codomain isn't a type. In a context where `n : Natural` is in
    // scope, `Π(_ : Natural). n` has codomain `n`, which is a value, not
    // a type.
    {
        Context context = {{"n", makeConstant("Natural")}};
        EXPECT_THROW(inferType(arithmetic, context,
            makePi("_", makeConstant("Natural"), makeFreeVariable("n"))));
    }

    // Lambda: domain isn't a type.
    EXPECT_THROW(inferType(arithmetic, {},
        makeLambda("_", makeConstant("zero"), makeConstant("zero"))));

    // Application: function isn't a Pi.
    EXPECT_THROW(inferType(arithmetic, {},
        makeApplication(makeConstant("zero"), makeConstant("zero"))));

    // Application: argument type doesn't match Pi domain. successor expects
    // Natural; passing it a Type 0 is wrong.
    EXPECT_THROW(inferType(arithmetic, {},
        makeApplication(makeConstant("successor"), makeType(0))));

    // Let: declared type isn't a type.
    EXPECT_THROW(inferType(arithmetic, {},
        makeLet("x", makeConstant("zero"),
                makeConstant("zero"),
                makeConstant("zero"))));

    // Let: value's type doesn't match declared.
    EXPECT_THROW(inferType(arithmetic, {},
        makeLet("x", makeConstant("Natural"),
                makeType(0),  // value has type Type 1, doesn't match Natural.
                makeConstant("zero"))));

    // A bare BoundVariable at the top level is a kernel-internal error
    // (binders should be opened before recursing into inferType).
    EXPECT_THROW(inferType(arithmetic, {}, makeBoundVariable(0)));
}

// ----------------------------------------------------------------------------
// Negative-path coverage for declarations: addAxiom / addDefinition /
// addInductive should reject malformed inputs without corrupting the env.
// ----------------------------------------------------------------------------

void runDeclarationErrorTests(const Environment& arithmetic) {
    std::cout << "--- declaration error tests ---\n";

    // addAxiom: duplicate name.
    {
        Environment local = arithmetic;
        EXPECT_THROW(addAxiom(local, "Natural", makeType(0)));
    }

    // addAxiom: declared "type" isn't a type.
    {
        Environment local;
        EXPECT_THROW(addAxiom(local, "bad", makeConstant("nope")));
    }

    // addDefinition: duplicate name.
    {
        Environment local = arithmetic;
        EXPECT_THROW(addDefinition(local, "one",
                                   makeConstant("Natural"),
                                   makeConstant("zero")));
    }

    // addDefinition: body's type does not match declared type.
    {
        Environment local = arithmetic;
        EXPECT_THROW(addDefinition(
            local, "bogus",
            makeConstant("Natural"), makeType(0)));
    }

    // addDefinition leaves the environment unchanged after a failed
    // declaration (size stays the same).
    {
        Environment local = arithmetic;
        std::size_t sizeBefore = local.declarations.size();
        try {
            addDefinition(local, "bogus",
                          makeConstant("Natural"), makeType(0));
        } catch (const TypeError&) {}
        EXPECT_TRUE(local.declarations.size() == sizeBefore);
    }

    // addInductive: duplicate name.
    {
        Environment local = arithmetic;
        EXPECT_THROW(addInductive(local, "Natural", makeType(0),
                                  {{"someCtor", makeConstant("Natural")}}));
    }

    // addInductive: constructor name conflicts with an existing declaration.
    {
        Environment local = arithmetic;
        // "zero" is already declared (as the Constructor of Natural).
        EXPECT_THROW(addInductive(local, "AnotherNatural", makeType(0),
                                  {{"zero", makeConstant("AnotherNatural")}}));
    }

    // addInductive: kind is not itself a type (passing a value).
    {
        Environment local = arithmetic;
        EXPECT_THROW(addInductive(local, "Bad", makeConstant("zero"),
                                  {{"someCtor", makeConstant("Bad")}}));
    }

    // addInductive: a Pi-kind is now accepted (it describes parameters or
    // indices). But numParameters out of range relative to the Pi-chain
    // length is still rejected.
    {
        Environment local;
        // Kind has one Pi; numParameters = 5 is out of range.
        EXPECT_THROW(addInductive(
            local, "Bogus",
            makePi("_", makeType(0), makeType(0)),
            /*numParameters=*/ 5,
            {}));
    }

    // addInductive on failure leaves the env unchanged (rollback).
    {
        Environment local = arithmetic;
        std::size_t sizeBefore = local.declarations.size();
        try {
            // Constructor type with a Constant that doesn't exist.
            addInductive(local, "Stranger", makeType(0),
                         {{"strangerCtor",
                           makeApplication(makeConstant("Stranger"),
                                           makeConstant("not_a_thing"))}});
        } catch (const TypeError&) {}
        EXPECT_TRUE(local.declarations.size() == sizeBefore);
        // The inductive's name and constructor name shouldn't be in the env
        // after the failed addInductive.
        EXPECT_TRUE(local.lookup("Stranger") == nullptr);
        EXPECT_TRUE(local.lookup("strangerCtor") == nullptr);
        EXPECT_TRUE(local.lookup("Stranger_recursor") == nullptr);
    }
}

// ----------------------------------------------------------------------------
// Universe polymorphism tests: polymorphic definitions, level substitution
// across reductions, and end-to-end uses with different universe args.
// ----------------------------------------------------------------------------

void runUniversePolymorphismTests(const Environment& arithmetic) {
    std::cout << "--- universe polymorphism tests ---\n";

    // The polymorphic identity at the kernel level. We define
    //   identity.{u} : Π(A : Type u). Π(x : A). A := λA. λx. x
    // and check that it instantiates at multiple universes.
    Environment env = arithmetic;
    addDefinition(env, "identity", {"u"},
        makePi("A", makeType(makeLevelParam("u")),
          makePi("x", makeBoundVariable(0), makeBoundVariable(1))),
        makeLambda("A", makeType(makeLevelParam("u")),
          makeLambda("x", makeBoundVariable(0), makeBoundVariable(0))));

    // identity.{0} Natural zero  ≡  zero  (after β reductions).
    {
        auto applied = makeApplication(
            makeApplication(makeConstant("identity", {makeLevelConst(0)}),
                            makeConstant("Natural")),
            makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, applied,
                                          makeConstant("zero")));
    }

    // identity.{1} (Type 0) Natural  has type Type 0 and reduces to Natural.
    {
        auto applied = makeApplication(
            makeApplication(makeConstant("identity", {makeLevelConst(1)}),
                            makeType(0)),
            makeConstant("Natural"));
        auto inferredType = inferType(env, {}, applied);
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, inferredType,
                                          makeType(0)));
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, applied,
                                          makeConstant("Natural")));
    }

    // The recorded universe arguments survive printing.
    EXPECT_PRINTS(makeConstant("Equality", {makeLevelConst(0)}),
                  "Equality.{0}");
    EXPECT_PRINTS(makeConstant("Equality", {makeLevelParam("u")}),
                  "Equality.{u}");

    // The same polymorphic constant at different levels has the same NAME
    // when compared as Constants — but the kernel doesn't consider them
    // definitionally equal unless universe args also agree.
    EXPECT_FALSE(isDefinitionallyEqual(env, {},
        makeConstant("Equality", {makeLevelConst(0)}),
        makeConstant("Equality", {makeLevelConst(1)})));

    // Polymorphic δ-reduction: when a polymorphic definition is unfolded,
    // universe arguments get substituted into the body. typeIdAt.{u} is a
    // function that returns the type it is given.
    //   typeIdAt.{u} : Π(A : Type u). Type u
    //   typeIdAt.{u} := λA. A
    addDefinition(env, "typeIdAt", {"u"},
        makePi("A", makeType(makeLevelParam("u")),
               makeType(makeLevelParam("u"))),
        makeLambda("A", makeType(makeLevelParam("u")), makeBoundVariable(0)));
    // typeIdAt.{0} Natural reduces under δ + β to Natural.
    {
        auto applied = makeApplication(
            makeConstant("typeIdAt", {makeLevelConst(0)}),
            makeConstant("Natural"));
        auto reduced = weakHeadNormalForm(env, applied);
        auto* c = std::get_if<Constant>(&reduced->node);
        EXPECT_TRUE(c && c->name == "Natural");
    }
}

// ----------------------------------------------------------------------------
// Pretty-printer output tests. These pin down the exact rendering so any
// future change is detected.
// ----------------------------------------------------------------------------

void runPrintingTests(const Environment& arithmetic) {
    std::cout << "--- pretty-printer tests ---\n";

    EXPECT_PRINTS(makeProposition(), "Proposition");
    EXPECT_PRINTS(makeType(0), "Type 0");
    EXPECT_PRINTS(makeType(1), "Type 1");
    EXPECT_PRINTS(makeType(makeLevelParam("u")), "Type u");
    EXPECT_PRINTS(makeSort(makeLevelMax(makeLevelParam("u"),
                                        makeLevelParam("v"))),
                  "Sort max(u, v)");

    EXPECT_PRINTS(makeConstant("zero"), "zero");
    EXPECT_PRINTS(makeConstant("Equality", {makeLevelConst(0)}),
                  "Equality.{0}");
    EXPECT_PRINTS(makeConstant("foo",
                               {makeLevelParam("u"), makeLevelParam("v")}),
                  "foo.{u, v}");

    EXPECT_PRINTS(makeFreeVariable("x"), "x");

    // Application is left-associative: f g h prints flat.
    EXPECT_PRINTS(makeApplication(
                      makeApplication(makeConstant("f"), makeConstant("g")),
                      makeConstant("h")),
                  "f g h");

    // Application: argument that is itself an Application gets parens.
    EXPECT_PRINTS(makeApplication(
                      makeConstant("f"),
                      makeApplication(makeConstant("g"), makeConstant("h"))),
                  "f (g h)");

    // Pi prints with Π and a colon-typed binder.
    EXPECT_PRINTS(
        makePi("x", makeConstant("Natural"), makeConstant("Natural")),
        "Π(x : Natural). Natural");

    // Lambda prints with λ.
    EXPECT_PRINTS(
        makeLambda("x", makeConstant("Natural"), makeBoundVariable(0)),
        "λ(x : Natural). x");

    // Binder hint collision: inner binder is freshened.
    EXPECT_PRINTS(
        makeLambda("x", makeConstant("T"),
          makeLambda("x", makeConstant("T"), makeBoundVariable(1))),
        "λ(x : T). λ(x_1 : T). x");

    // Let prints with "let ... := ... in ...".
    EXPECT_PRINTS(
        makeLet("n", makeConstant("Natural"), makeConstant("zero"),
                makeBoundVariable(0)),
        "let n : Natural := zero in n");

    // Suppress the arithmetic-environment warning by referencing it.
    (void)arithmetic;
}

// ----------------------------------------------------------------------------
// Strict-positivity tests: addInductive must reject constructor types in
// which the inductive being declared appears in a non-strictly-positive
// position. Without this check, a malicious user can derive False.
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// Universe-polymorphic recursor tests. With a polymorphic motive, the same
// Natural_recursor can be instantiated at any motive universe — Type 0 for
// the typical case (computing Naturals from Naturals), or Proposition to prove
// propositions by induction.
// ----------------------------------------------------------------------------

void runPolymorphicRecursorTests(const Environment& arithmetic) {
    std::cout << "--- polymorphic recursor tests ---\n";

    // The recursor takes a motive-level universe argument.
    {
        auto type = inferType(arithmetic, {},
            makeConstant("Natural_recursor", {makeLevelConst(1)}));
        // Motive is Π(_ : Natural). Type 0 in this case. Type of the
        // recursor lives in Sort imax(of motive type, ...) = Type 1.
        EXPECT_TRUE(std::holds_alternative<Pi>(type->node));
    }

    // Instantiate at motive level 0 (Proposition motive). The recursor's motive
    // type becomes Π(_ : Natural). Proposition. Calls to it eliminate Natural
    // into propositions — i.e. proofs by induction.
    {
        auto recursorPropositionMotive =
            makeConstant("Natural_recursor", {makeLevelConst(0)});
        auto inferredType = inferType(arithmetic, {}, recursorPropositionMotive);
        // Pretty-print to confirm motive is Π(_ : Natural). Proposition.
        // (Concretely: the type starts with Π(motive : Π(_ : Natural). Proposition).)
        auto whnfType = weakHeadNormalForm(arithmetic, inferredType);
        auto* pi = std::get_if<Pi>(&whnfType->node);
        EXPECT_TRUE(pi);
        if (pi) {
            // pi->domain is the motive's TYPE, which should be
            // Π(_ : Natural). Proposition.
            auto* motivePi = std::get_if<Pi>(&pi->domain->node);
            EXPECT_TRUE(motivePi);
            if (motivePi) {
                auto* codomainSort =
                    std::get_if<Sort>(&motivePi->codomain->node);
                EXPECT_TRUE(
                    codomainSort &&
                    levelAsConstant(codomainSort->level) &&
                    *levelAsConstant(codomainSort->level) == 0);  // Proposition
            }
        }
    }

    // Prove a proposition by induction: ∀(n : Natural). Equality.{0}
    //                                      Natural n n.
    // The proof is reflexivity applied to each constructor case, and
    // Natural_recursor at motive level 0 (Proposition) ties them together.
    //
    //   inductionProof : Π(n : Natural). Equality Natural n n
    //   inductionProof =
    //     Natural_recursor.{0}
    //       (λn. Equality Natural n n)              -- motive : Natural → Proposition
    //       (reflexivity Natural zero)              -- case_zero
    //       (λk recK. reflexivity Natural (successor k))  -- case_successor
    {
        Environment env = arithmetic;
        auto motive = makeLambda("n", makeConstant("Natural"),
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeConstant("Equality", {makeLevelConst(0)}),
                        makeConstant("Natural")),
                    makeBoundVariable(0) /* n */),
                makeBoundVariable(0) /* n */));
        auto caseZero = makeApplication(
            makeApplication(makeConstant("reflexivity",
                                          {makeLevelConst(0)}),
                            makeConstant("Natural")),
            makeConstant("zero"));
        auto caseSuccessor = makeLambda("k", makeConstant("Natural"),
            // recK is the IH; we ignore it because reflexivity gives us
            // what we want directly. Bound 0 = recK, bound 1 = k.
            makeLambda("recK",
                makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Equality", {makeLevelConst(0)}),
                            makeConstant("Natural")),
                        makeBoundVariable(0) /* k */),
                    makeBoundVariable(0) /* k */),
                makeApplication(
                    makeApplication(makeConstant("reflexivity",
                                                  {makeLevelConst(0)}),
                                    makeConstant("Natural")),
                    makeApplication(makeConstant("successor"),
                                    makeBoundVariable(1) /* k */))));
        auto inductionProof = makeLambda("n", makeConstant("Natural"),
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Natural_recursor",
                                          {makeLevelConst(0)}),
                            motive),
                        caseZero),
                    caseSuccessor),
                makeBoundVariable(0) /* n */));
        auto proofType = makePi("n", makeConstant("Natural"),
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeConstant("Equality", {makeLevelConst(0)}),
                        makeConstant("Natural")),
                    makeBoundVariable(0)),
                makeBoundVariable(0)));
        addDefinition(env, "inductionProof", proofType, inductionProof);
        // The definition typechecks: kernel-verified proof by induction.
        EXPECT_TRUE(env.lookup("inductionProof") != nullptr);
    }
}

// ----------------------------------------------------------------------------
// Restricted-elimination tests for Proposition inductives. A non-empty Proposition
// inductive must not allow its proofs to be eliminated into Type — that
// would let users extract data from a proof and break proof irrelevance.
// The kernel forces the motive's universe to Proposition for such recursors.
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// Proof irrelevance × impredicativity audit. These tests pin down what the
// kernel's proof-irrelevance branch does and doesn't equate, especially
// around the impredicative Pi rule. The principle: two terms are
// definitionally equal by proof irrelevance iff their type lives in Proposition.
// ----------------------------------------------------------------------------

void runProofIrrelevanceAuditTests(const Environment& arithmetic) {
    std::cout << "--- proof-irrelevance audit tests ---\n";

    // Baseline: two proofs of the same proposition are equal.
    {
        auto propositionType = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        Context ctx = {{"p", propositionType}, {"q", propositionType}};
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, ctx,
                                          makeFreeVariable("p"),
                                          makeFreeVariable("q")));
    }

    // Proofs of *distinct* propositions are NOT equal.
    {
        auto leftProposition = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        auto rightProposition = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeApplication(makeConstant("successor"), makeConstant("zero")));
        Context ctx = {{"p", leftProposition}, {"q", rightProposition}};
        EXPECT_FALSE(isDefinitionallyEqual(arithmetic, ctx,
                                           makeFreeVariable("p"),
                                           makeFreeVariable("q")));
    }

    // A term whose type lives in Type (not Proposition) is NOT equated by proof
    // irrelevance, even if both sides are "predicates".
    // Two distinct predicates  λ(n : Natural). Equality Natural n n  and
    // λ(n : Natural). Equality Natural zero zero  have type
    // Π(_ : Natural). Proposition, whose universe is imax(1, 1) = Type 0. Not in
    // Proposition. So they aren't equated.
    {
        auto predicateA = makeLambda("n", makeConstant("Natural"),
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                    makeConstant("Natural")),
                    makeBoundVariable(0)),
                makeBoundVariable(0)));
        auto predicateB = makeLambda("n", makeConstant("Natural"),
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                    makeConstant("Natural")),
                    makeConstant("zero")),
                makeConstant("zero")));
        EXPECT_FALSE(isDefinitionallyEqual(arithmetic, {},
                                           predicateA, predicateB));
    }

    // A function whose codomain is a proof type IS in Proposition (impredicativity
    // collapses the Pi to Proposition), so two such functions are equal by proof
    // irrelevance. The functions are "extensionally equal" because they
    // return interchangeable proofs.
    //
    //   Π(x : Natural). Equality Natural zero zero  has universe
    //     imax(1, 0) = 0 = Proposition.
    {
        auto propositionType = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        auto functionType =
            makePi("_", makeConstant("Natural"), propositionType);
        Context ctx = {{"f", functionType}, {"g", functionType}};
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, ctx,
                                          makeFreeVariable("f"),
                                          makeFreeVariable("g")));
    }

    // Proof irrelevance never equates terms of disjoint types.
    {
        Context ctx = {{"n", makeConstant("Natural")},
                       {"b", makeConstant("Natural")}};
        // n and b are Naturals (Type 0). Not in Proposition. Distinct free vars.
        EXPECT_FALSE(isDefinitionallyEqual(arithmetic, ctx,
                                           makeFreeVariable("n"),
                                           makeFreeVariable("b")));
    }

    // η + proof irrelevance: a Lambda that wraps a proof-returning function
    // is equal to the bare function. Both have type in Proposition (codomain is
    // Equality, which is in Proposition).
    //   λ(x : Natural). reflexivity Natural zero  vs  the partially-
    //   applied reflexivity at zero — but reflexivity needs a type AND a
    //   value; the partially-applied form ends differently. Skip; the
    //   eta-equality of these forms is a separate test.

    // Proof irrelevance + applications: comparing  Equality Natural zero
    // zero  and  Equality Natural zero zero  (same Application chain)
    // succeeds structurally — proof irrelevance isn't needed but also
    // doesn't break things.
    {
        auto term = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, {}, term, term));
    }
}

void runRestrictedEliminationTests() {
    std::cout << "--- restricted elimination tests ---\n";

    // A Proposition inductive with two constructors: a disjunction over a fixed
    // pair of propositions. Its recursor must NOT take a motive-universe
    // parameter (motive is forced to Proposition).
    {
        Environment env;
        addAxiom(env, "P", makeProposition());
        addAxiom(env, "Q", makeProposition());
        addInductive(env, "Or_PQ", makeProposition(), {
            {"inl", makePi("_", makeConstant("P"), makeConstant("Or_PQ"))},
            {"inr", makePi("_", makeConstant("Q"), makeConstant("Or_PQ"))},
        });
        // The recursor takes no universe arguments.
        auto recursor = makeConstant("Or_PQ_recursor");
        auto type = inferType(env, {}, recursor);
        EXPECT_TRUE(std::holds_alternative<Pi>(type->node));
        // Supplying a universe argument is rejected as wrong arity.
        EXPECT_THROW(inferType(env, {},
            makeConstant("Or_PQ_recursor", {makeLevelConst(1)})));
        // The motive's codomain in the recursor type is Proposition, not a
        // universe parameter. We inspect by walking into the Pi:
        auto* pi = std::get_if<Pi>(&type->node);
        EXPECT_TRUE(pi);
        if (pi) {
            auto* motivePi = std::get_if<Pi>(&pi->domain->node);
            EXPECT_TRUE(motivePi);
            if (motivePi) {
                auto* codomainSort =
                    std::get_if<Sort>(&motivePi->codomain->node);
                EXPECT_TRUE(codomainSort &&
                            levelAsConstant(codomainSort->level) &&
                            *levelAsConstant(codomainSort->level) == 0);
            }
        }
    }

    // An empty Proposition inductive (zero constructors, like False) DOES allow
    // large elimination — there's no proof to extract from, so any motive
    // universe is sound. The recursor takes a motive-level universe arg.
    {
        Environment env;
        addInductive(env, "False", makeProposition(), {});
        auto recursor =
            makeConstant("False_recursor", {makeLevelConst(1)});
        auto type = inferType(env, {}, recursor);
        EXPECT_TRUE(std::holds_alternative<Pi>(type->node));
        // Without a universe arg it's wrong arity.
        EXPECT_THROW(inferType(env, {}, makeConstant("False_recursor")));
    }

    // For a Type-valued inductive, large elimination is allowed normally
    // — the recursor takes a motive-level universe arg as before.
    {
        Environment env;
        addInductive(env, "Boolean", makeType(0), {
            {"true",  makeConstant("Boolean")},
            {"false", makeConstant("Boolean")},
        });
        auto type = inferType(env, {},
            makeConstant("Boolean_recursor", {makeLevelConst(1)}));
        EXPECT_TRUE(std::holds_alternative<Pi>(type->node));
    }
}

void runStrictPositivityTests() {
    std::cout << "--- strict positivity tests ---\n";

    // The canonical bad inductive:
    //   Bad : Type 0 := mkBad : (Bad → Bool) → Bad
    // The constructor mkBad has an argument of type (Bad → Bool), which
    // places Bad in the domain of a Pi inside an argument — a non-strictly-
    // positive occurrence. This is rejected.
    {
        Environment local;
        addInductive(local, "Boolean", makeType(0), {
            {"true",  makeConstant("Boolean")},
            {"false", makeConstant("Boolean")},
        });
        EXPECT_THROW(addInductive(local, "Bad", makeType(0), {
            {"mkBad",
                makePi("_",
                    makePi("_",
                        makeConstant("Bad"),
                        makeConstant("Boolean")),
                    makeConstant("Bad"))},
        }));
        // The whole declaration was rolled back.
        EXPECT_TRUE(local.lookup("Bad") == nullptr);
        EXPECT_TRUE(local.lookup("mkBad") == nullptr);
        EXPECT_TRUE(local.lookup("Bad_recursor") == nullptr);
    }

    // A worse case: Bad appears under multiple Pis on the way down.
    //   Worse : Type 0 := mkWorse : ((Worse → Worse) → Bool) → Worse
    {
        Environment local;
        addInductive(local, "Boolean", makeType(0), {
            {"true",  makeConstant("Boolean")},
            {"false", makeConstant("Boolean")},
        });
        EXPECT_THROW(addInductive(local, "Worse", makeType(0), {
            {"mkWorse",
                makePi("_",
                    makePi("_",
                        makePi("_",
                            makeConstant("Worse"),
                            makeConstant("Worse")),
                        makeConstant("Boolean")),
                    makeConstant("Worse"))},
        }));
    }

    // A constructor whose conclusion isn't the inductive must be rejected.
    {
        Environment local;
        addInductive(local, "Boolean", makeType(0), {
            {"true",  makeConstant("Boolean")},
            {"false", makeConstant("Boolean")},
        });
        EXPECT_THROW(addInductive(local, "Nope", makeType(0), {
            // Conclusion is Boolean, not Nope.
            {"mkNope", makeConstant("Boolean")},
        }));
    }

    // Good inductives are still accepted.
    {
        Environment local;
        // Natural: zero, successor.
        EXPECT_TRUE([&]() {
            try {
                addInductive(local, "Natural", makeType(0), {
                    {"zero", makeConstant("Natural")},
                    {"successor", makePi("_", makeConstant("Natural"),
                                          makeConstant("Natural"))},
                });
                return true;
            } catch (...) { return false; }
        }());

        // Higher-order recursive arguments are allowed when the inductive
        // appears only as the codomain of the parameter type.
        //   InfTree : Type 0 := mkLeaf : InfTree
        //                     | mkBranch : (Natural → InfTree) → InfTree
        EXPECT_TRUE([&]() {
            try {
                addInductive(local, "InfTree", makeType(0), {
                    {"mkLeaf", makeConstant("InfTree")},
                    {"mkBranch",
                        makePi("_",
                            makePi("_", makeConstant("Natural"),
                                   makeConstant("InfTree")),
                            makeConstant("InfTree"))},
                });
                return true;
            } catch (...) { return false; }
        }());
    }
}

// ----------------------------------------------------------------------------
// Defensive-hardening tests: explicit universe-arity checks in the kernel's
// internal reductions, and the fuel-limit safety net.
// ----------------------------------------------------------------------------

void runHardeningTests(const Environment& arithmetic) {
    std::cout << "--- defensive hardening tests ---\n";

    // The internal universe-arity check catches a malformed Definition
    // reference reaching weakHeadNormalForm directly. We construct a
    // Constant referring to a definition but with the wrong universe-arg
    // count, then hand it straight to weakHeadNormalForm (bypassing the
    // arity check in inferType).
    {
        Environment local = arithmetic;
        // polyDef.{u} : Type (u+1) := Type u
        addDefinition(local, "polyDef", {"u"},
                      makeType(makeLevelSuccessor(makeLevelParam("u"))),
                      makeType(makeLevelParam("u")));
        // Construct polyDef with zero universe args (instead of one).
        EXPECT_THROW(weakHeadNormalForm(local, makeConstant("polyDef")));
        // Two universe args is also wrong.
        EXPECT_THROW(weakHeadNormalForm(
            local, makeConstant("polyDef",
                                {makeLevelConst(0), makeLevelConst(1)})));
        // The correct arity reduces fine — body Type 0 unfolds.
        auto reduced = weakHeadNormalForm(
            local, makeConstant("polyDef", {makeLevelConst(0)}));
        EXPECT_TRUE(std::holds_alternative<Sort>(reduced->node));
    }

    // The recursor has one universe parameter — the motive's universe.
    // Zero args is wrong arity.
    {
        EXPECT_THROW(inferType(arithmetic, {},
            makeConstant("Natural_recursor")));
        // Two args is also wrong.
        EXPECT_THROW(inferType(arithmetic, {},
            makeConstant("Natural_recursor",
                         {makeLevelConst(0), makeLevelConst(1)})));
    }

    // Fuel limit: an explicit fuel budget of 0 causes weakHeadNormalForm
    // to throw on any non-atomic term.
    {
        auto applied = makeApplication(
            makeLambda("x", makeConstant("Natural"), makeBoundVariable(0)),
            makeConstant("zero"));
        // With ample fuel, this reduces to "zero".
        auto reduced = weakHeadNormalForm(arithmetic, applied, 1000);
        EXPECT_TRUE(isDefinitionallyEqual(
            arithmetic, {}, reduced, makeConstant("zero")));
        // With no fuel, throws.
        EXPECT_THROW(weakHeadNormalForm(arithmetic, applied, 1));
    }

    // Fuel limit: isDefinitionallyEqual conservatively returns false on
    // exhaustion rather than throwing — equality is undecidable in this
    // window, but we must not falsely claim equality.
    {
        auto applied = makeApplication(
            makeLambda("x", makeConstant("Natural"), makeBoundVariable(0)),
            makeConstant("zero"));
        // With fuel 1, the function reduces the LHS to "zero" but can't
        // also reduce the RHS. The result is conservatively false.
        EXPECT_FALSE(isDefinitionallyEqual(
            arithmetic, {}, applied, makeConstant("zero"), 1));
        // With ample fuel they're equal.
        EXPECT_TRUE(isDefinitionallyEqual(
            arithmetic, {}, applied, makeConstant("zero"), 1000));
    }
}

// ----------------------------------------------------------------------------
// Public-API input validation. Names supplied through addAxiom /
// addDefinition / addInductive must be non-empty, must not begin with '@'
// (reserved by the printer for internal free variables), and must not
// contain control characters. The validation runs unconditionally — these
// are cheap checks that catch obvious abuse at the boundary.
// ----------------------------------------------------------------------------

void runInputValidationTests() {
    std::cout << "--- input validation tests ---\n";

    {
        Environment env;
        // Empty name.
        EXPECT_THROW(addAxiom(env, "", makeType(0)));
        // Names beginning with '@' are reserved.
        EXPECT_THROW(addAxiom(env, "@bad", makeType(0)));
        // Control characters.
        EXPECT_THROW(addAxiom(env, std::string("bad\x01here"), makeType(0)));
        // Bad universe-parameter name.
        EXPECT_THROW(addAxiom(env, "good", {""}, makeType(0)));
        EXPECT_THROW(addAxiom(env, "good", {"@u"}, makeType(0)));
        // A clean axiom name works.
        addAxiom(env, "Good", makeType(0));
        EXPECT_TRUE(env.lookup("Good") != nullptr);
    }
    {
        Environment env;
        EXPECT_THROW(addDefinition(env, "@bad",
                                   makeType(0), makeType(0)));
    }
    {
        Environment env;
        EXPECT_THROW(addInductive(env, "@bad", makeType(0), {}));
        EXPECT_THROW(addInductive(env, "good", makeType(0),
                                   {{"@badCtor", makeConstant("good")}}));
    }
}

// ----------------------------------------------------------------------------
// Optional invariant checking: flip on kernelCheckInvariants and re-run a
// representative subset of the existing tests. Every successful inferType
// runs a kind-soundness postcondition; the cost roughly doubles but every
// internal inconsistency would surface here.
// ----------------------------------------------------------------------------

void runInvariantCheckedTests(const Environment& arithmetic) {
    std::cout << "--- invariant-checked tests (postcondition enabled) ---\n";
    kernelCheckInvariants = true;
    try {
        // Re-run a sample of representative kernel work with the
        // postcondition enabled. If the kernel ever produced an internally
        // ill-formed type, the postcondition would throw — these calls
        // would not succeed.
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, {},
            makeApplication(
                makeApplication(makeConstant("add"), makeConstant("zero")),
                makeConstant("zero")),
            makeConstant("zero")));

        auto twoTimesOne = makeApplication(
            makeApplication(makeConstant("add"),
                            makeApplication(makeConstant("successor"),
                                            makeConstant("zero"))),
            makeApplication(makeConstant("successor"),
                            makeConstant("zero")));
        auto two = makeApplication(makeConstant("successor"),
            makeApplication(makeConstant("successor"), makeConstant("zero")));
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, {},
                                          twoTimesOne, two));

        // Inference round-trips through the postcondition.
        auto recursorType = inferType(arithmetic, {},
            makeConstant("Natural_recursor", {makeLevelConst(1)}));
        EXPECT_TRUE(std::holds_alternative<Pi>(recursorType->node));

        // Polymorphic reflexivity at multiple universes.
        auto proofZero = inferType(arithmetic, {},
            makeApplication(
                makeApplication(makeConstant("reflexivity",
                                              {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")));
        auto expectedZero = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        EXPECT_TRUE(isDefinitionallyEqual(arithmetic, {},
                                          proofZero, expectedZero));
    } catch (...) {
        kernelCheckInvariants = false;
        throw;
    }
    kernelCheckInvariants = false;
}

// ----------------------------------------------------------------------------
// Property-based testing. Generates random closed expressions over the
// arithmetic environment, filters those that successfully type-check, and
// runs four invariants over each:
//   - whnf is idempotent  (whnf (whnf e)  is def-equal to  whnf e).
//   - isDefEq is reflexive  (every term is def-equal to itself).
//   - isDefEq is symmetric  (a ≡ b implies b ≡ a, on a sampled pair).
//   - Type preservation  (inferType (whnf e)  is def-equal to  inferType e).
// Failures are catalogued and reported; the test count includes the number
// of typechecking cases, not the number generated.
// ----------------------------------------------------------------------------

namespace {

ExpressionPointer randomExpression(std::mt19937& rng, int depth) {
    static const std::vector<std::string> constantPool = {
        "zero", "one", "two", "successor", "add", "Natural"
    };
    auto pickFrom = [&](const std::vector<std::string>& xs) {
        std::uniform_int_distribution<int> d(0, (int)xs.size() - 1);
        return xs[d(rng)];
    };
    auto pickConstant = [&]() { return makeConstant(pickFrom(constantPool)); };

    if (depth <= 0) {
        return pickConstant();
    }
    // Pick a shape weighted toward leaves so the term doesn't blow up.
    std::uniform_int_distribution<int> shape(0, 9);
    int choice = shape(rng);
    if (choice < 4) {
        return pickConstant();
    } else if (choice < 7) {
        auto function = randomExpression(rng, depth - 1);
        auto argument = randomExpression(rng, depth - 1);
        return makeApplication(function, argument);
    } else if (choice < 8) {
        auto body = randomExpression(rng, depth - 1);
        return makeLambda("x", makeConstant("Natural"), body);
    } else if (choice < 9) {
        // Let
        auto value = randomExpression(rng, depth - 1);
        auto body  = randomExpression(rng, depth - 1);
        return makeLet("x", makeConstant("Natural"), value, body);
    } else {
        return makeType(0);
    }
}

} // namespace

void runPropertyTests(const Environment& arithmetic) {
    std::cout << "--- property tests ---\n";

    const int trialCount = 400;
    const int maxDepth   = 5;
    std::mt19937 rng(0xCAFE);  // deterministic seed for reproducibility.

    int wellTyped = 0;
    int idempotentFailures = 0;
    int reflexiveFailures = 0;
    int symmetricFailures = 0;
    int typePreservationFailures = 0;
    int kindSoundnessFailures = 0;

    auto sample = [&]() {
        std::uniform_int_distribution<int> d(1, maxDepth);
        return randomExpression(rng, d(rng));
    };

    for (int trial = 0; trial < trialCount; ++trial) {
        auto expression = sample();
        ExpressionPointer type;
        try {
            type = inferType(arithmetic, {}, expression);
        } catch (const TypeError&) {
            continue;  // Untypable — skip.
        }
        ++wellTyped;

        // Idempotence of whnf.
        try {
            auto once  = weakHeadNormalForm(arithmetic, expression);
            auto twice = weakHeadNormalForm(arithmetic, once);
            if (!isDefinitionallyEqual(arithmetic, {}, once, twice)) {
                ++idempotentFailures;
            }
        } catch (const TypeError&) {
            ++idempotentFailures;
        }

        // Reflexivity of isDefinitionallyEqual.
        try {
            if (!isDefinitionallyEqual(arithmetic, {}, expression, expression)) {
                ++reflexiveFailures;
            }
        } catch (const TypeError&) {
            ++reflexiveFailures;
        }

        // Symmetry: pair against a second random well-typed term.
        try {
            auto other = sample();
            try {
                (void)inferType(arithmetic, {}, other);  // require well-typed.
                bool ab = isDefinitionallyEqual(arithmetic, {}, expression, other);
                bool ba = isDefinitionallyEqual(arithmetic, {}, other, expression);
                if (ab != ba) ++symmetricFailures;
            } catch (const TypeError&) {
                // Other side untypable — skip the symmetry check for this trial.
            }
        } catch (const TypeError&) {
            ++symmetricFailures;
        }

        // Type preservation under reduction.
        try {
            auto reduced = weakHeadNormalForm(arithmetic, expression);
            auto reducedType = inferType(arithmetic, {}, reduced);
            if (!isDefinitionallyEqual(arithmetic, {}, type, reducedType)) {
                ++typePreservationFailures;
            }
        } catch (const TypeError&) {
            ++typePreservationFailures;
        }

        // Kind soundness: the inferred type must itself be a well-formed
        // type — i.e. inferType(type) must succeed and reduce to a Sort.
        // This catches cases where inferType returns something internally
        // ill-formed (for instance, a term with dangling bound indices).
        try {
            auto kindOfType = weakHeadNormalForm(
                arithmetic, inferType(arithmetic, {}, type));
            if (!std::holds_alternative<Sort>(kindOfType->node)) {
                ++kindSoundnessFailures;
            }
        } catch (const TypeError&) {
            ++kindSoundnessFailures;
        }
    }

    std::cout << "  " << wellTyped << " well-typed expressions sampled (of "
              << trialCount << " trials)\n";
    EXPECT_TRUE(wellTyped >= trialCount / 4);  // expect a reasonable hit rate.
    EXPECT_TRUE(idempotentFailures       == 0);
    EXPECT_TRUE(reflexiveFailures        == 0);
    EXPECT_TRUE(symmetricFailures        == 0);
    EXPECT_TRUE(typePreservationFailures == 0);
    EXPECT_TRUE(kindSoundnessFailures    == 0);
}

// ----------------------------------------------------------------------------
// Natural-Number-Game-style proofs. Demonstrates kernel-verified theorems
// about Natural and addition. Some go through by pure β/δ/ι/ζ reduction;
// others need induction via Natural_recursor.{0} (a Proposition-valued motive).
// Equality (the inductive type provided by buildArithmeticEnvironment)
// supplies the J principle through its auto-generated recursor; that's
// what derived lemmas like Equality.symmetry, Equality.transitivity,
// and Natural.successorCongruence use to reason about proofs of equality.
// ----------------------------------------------------------------------------

void runNaturalNumberGameProofs() {
    std::cout << "--- natural number game proofs ---\n";

    Environment env = buildArithmeticEnvironment();

    // Equality (inductive, with its recursor — the J principle) is
    // declared in buildArithmeticEnvironment, so the proofs below can
    // just refer to it by name. Convenience helpers follow.
    auto Natural = []() { return makeConstant("Natural"); };
    auto zero = []() { return makeConstant("zero"); };
    auto successor = [](ExpressionPointer n) {
        return makeApplication(makeConstant("successor"), n);
    };
    auto plus = [](ExpressionPointer n, ExpressionPointer m) {
        return makeApplication(makeApplication(makeConstant("add"), n), m);
    };
    auto equality = [](ExpressionPointer a, ExpressionPointer x,
                       ExpressionPointer y) {
        return makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality", {makeLevelConst(0)}),
                    a),
                x),
            y);
    };
    auto reflexivity = [](ExpressionPointer a, ExpressionPointer x) {
        return makeApplication(
            makeApplication(
                makeConstant("reflexivity", {makeLevelConst(0)}),
                a),
            x);
    };

    // ------------------------------------------------------------------
    // Equality.symmetry — universe-polymorphic.
    //   Π(A : Type u). Π(x y : A). Equality A x y → Equality A y x.
    // Derived from the recursor. Recurses on the input equality with
    // motive  λ y' _. Equality A y' x.  Base case y'=x needs x = x,
    // i.e. reflexivity A x.
    // ------------------------------------------------------------------
    {
        // Proof body lives inside  λ A. λ x. λ y. λ eq. [body].
        // From body's perspective: eq=0, y=1, x=2, A=3.
        // Motive is  λ y'. λ _eq'. Equality.{u} A y' x.
        //   At motive's _eq' body level: _eq'=0, y'=1, eq=2, y=3, x=4, A=5.
        //   At _eq' TYPE position (inside y' but outside _eq'):
        //                          y'=0, eq=1, y=2, x=3, A=4.
        auto motive = makeLambda("y'", makeBoundVariable(3) /* A */,
            makeLambda("_eq'",
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality", {makeLevelParam("u")}),
                    makeBoundVariable(4) /* A */),
                    makeBoundVariable(3) /* x */),
                    makeBoundVariable(0) /* y' */),
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality", {makeLevelParam("u")}),
                    makeBoundVariable(5) /* A */),
                    makeBoundVariable(1) /* y' */),
                    makeBoundVariable(4) /* x */)));

        auto caseReflexivity = makeApplication(
            makeApplication(
                makeConstant("reflexivity", {makeLevelParam("u")}),
                makeBoundVariable(3) /* A */),
            makeBoundVariable(2) /* x */);

        auto proof = makeLambda("A", makeType(makeLevelParam("u")),
            makeLambda("x", makeBoundVariable(0) /* A */,
                makeLambda("y", makeBoundVariable(1) /* A */,
                    makeLambda("_eq",
                        makeApplication(makeApplication(makeApplication(
                            makeConstant("Equality", {makeLevelParam("u")}),
                            makeBoundVariable(2)),
                            makeBoundVariable(1)),
                            makeBoundVariable(0)),
                        makeApplication(
                            makeApplication(
                                makeApplication(
                                    makeApplication(
                                        makeApplication(
                                            makeApplication(
                                                makeConstant(
                                                    "Equality_recursor",
                                                    {makeLevelParam("u"),
                                                     makeLevelConst(0)}),
                                                makeBoundVariable(3) /* A */),
                                            makeBoundVariable(2) /* x */),
                                        motive),
                                    caseReflexivity),
                                makeBoundVariable(1) /* y */),
                            makeBoundVariable(0) /* eq */)))));

        auto theoremType =
            makePi("A", makeType(makeLevelParam("u")),
                makePi("x", makeBoundVariable(0),
                    makePi("y", makeBoundVariable(1),
                        makePi("_eq",
                            makeApplication(makeApplication(makeApplication(
                                makeConstant("Equality",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(2)),
                                makeBoundVariable(1)),
                                makeBoundVariable(0)),
                            makeApplication(makeApplication(makeApplication(
                                makeConstant("Equality",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(3)),
                                makeBoundVariable(1)),
                                makeBoundVariable(2))))));

        addDefinition(env, "Equality.symmetry", {"u"}, theoremType, proof);
        std::cout << "  Equality.symmetry    ⊨  Π(A : Type u). Π(x y : A). x = y → "
                     "y = x   (J, universe-polymorphic)\n";
    }

    // ------------------------------------------------------------------
    // Equality.transitivity — universe-polymorphic.
    //   Π(A : Type u). Π(x y z : A). x = y → y = z → x = z.
    // Recurse on the SECOND equality with motive  λ z' _. Equality A x z'.
    // Base case z'=y needs x = y, supplied directly by the first equality.
    // ------------------------------------------------------------------
    {
        // Proof body lives inside  λ A x y z eq_xy eq_yz. From body:
        //   eq_yz=0, eq_xy=1, z=2, y=3, x=4, A=5.
        // Motive  λ z'. λ _eq'. Equality.{u} A x z'.
        //   _eq' body: _eq'=0, z'=1, eq_yz=2, eq_xy=3, z=4, y=5, x=6, A=7.
        //   _eq' TYPE (inside z' but outside _eq'): z'=0, eq_yz=1, eq_xy=2,
        //     z=3, y=4, x=5, A=6.
        auto motive = makeLambda("z'", makeBoundVariable(5) /* A */,
            makeLambda("_eq'",
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality", {makeLevelParam("u")}),
                    makeBoundVariable(6) /* A */),
                    makeBoundVariable(4) /* y */),
                    makeBoundVariable(0) /* z' */),
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality", {makeLevelParam("u")}),
                    makeBoundVariable(7) /* A */),
                    makeBoundVariable(6) /* x */),
                    makeBoundVariable(1) /* z' */)));

        // caseReflexivity at body level (eq_yz=0, eq_xy=1, z=2, y=3, x=4, A=5):
        // we need Equality.{u} A x y, which is eq_xy = Bound 1.
        auto caseReflexivity = makeBoundVariable(1) /* eq_xy */;

        auto proof = makeLambda("A", makeType(makeLevelParam("u")),
            makeLambda("x", makeBoundVariable(0),
                makeLambda("y", makeBoundVariable(1),
                    makeLambda("z", makeBoundVariable(2),
                        makeLambda("eq_xy",
                            makeApplication(makeApplication(makeApplication(
                                makeConstant("Equality",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(3) /* A */),
                                makeBoundVariable(2) /* x */),
                                makeBoundVariable(1) /* y */),
                            makeLambda("eq_yz",
                                // At this position (inside A,x,y,z,eq_xy
                                // outside eq_yz): eq_xy=0, z=1, y=2, x=3,
                                // A=4. So y is Bound(2), not Bound(3).
                                makeApplication(makeApplication(makeApplication(
                                    makeConstant("Equality",
                                                  {makeLevelParam("u")}),
                                    makeBoundVariable(4) /* A */),
                                    makeBoundVariable(2) /* y */),
                                    makeBoundVariable(1) /* z */),
                                makeApplication(
                                    makeApplication(
                                        makeApplication(
                                            makeApplication(
                                                makeApplication(
                                                    makeApplication(
                                                        makeConstant(
                                                            "Equality_recursor",
                                                            {makeLevelParam("u"),
                                                             makeLevelConst(0)}),
                                                        makeBoundVariable(5) /* A */),
                                                    makeBoundVariable(3) /* y */),
                                                motive),
                                            caseReflexivity),
                                        makeBoundVariable(2) /* z */),
                                    makeBoundVariable(0) /* eq_yz */)))))));

        auto theoremType =
            makePi("A", makeType(makeLevelParam("u")),
                makePi("x", makeBoundVariable(0),
                    makePi("y", makeBoundVariable(1),
                        makePi("z", makeBoundVariable(2),
                            makePi("eq_xy",
                                makeApplication(makeApplication(makeApplication(
                                    makeConstant("Equality",
                                                  {makeLevelParam("u")}),
                                    makeBoundVariable(3)),
                                    makeBoundVariable(2)),
                                    makeBoundVariable(1)),
                                makePi("eq_yz",
                                    makeApplication(makeApplication(makeApplication(
                                        makeConstant("Equality",
                                                      {makeLevelParam("u")}),
                                        makeBoundVariable(4) /* A */),
                                        makeBoundVariable(2) /* y */),
                                        makeBoundVariable(1) /* z */),
                                    makeApplication(makeApplication(makeApplication(
                                        makeConstant("Equality",
                                                      {makeLevelParam("u")}),
                                        makeBoundVariable(5) /* A */),
                                        makeBoundVariable(4) /* x */),
                                        makeBoundVariable(2) /* z */)))))));

        addDefinition(env, "Equality.transitivity", {"u"}, theoremType, proof);
        std::cout << "  Equality.transitivity   ⊨  Π(A : Type u). Π(x y z : A). "
                     "x = y → y = z → x = z   (J, universe-polymorphic)\n";
    }

    // ------------------------------------------------------------------
    // Polymorphic demo: Equality instantiated at universe 1 (Type 0 as
    // the value-level type). naturalEqualsItself : Equality.{1} (Type 0)
    // Natural Natural. Proof: reflexivity.{1} (Type 0) Natural. The same
    // declarations work at higher universes.
    // ------------------------------------------------------------------
    addDefinition(env, "naturalEqualsItself",
        makeApplication(makeApplication(makeApplication(
            makeConstant("Equality", {makeLevelConst(1)}),
            makeType(0)),
            makeConstant("Natural")),
            makeConstant("Natural")),
        makeApplication(
            makeApplication(makeConstant("reflexivity", {makeLevelConst(1)}),
                            makeType(0)),
            makeConstant("Natural")));
    std::cout << "  naturalEqualsItself  ⊨  Equality.{1} (Type 0) "
                 "Natural Natural\n";

    // ------------------------------------------------------------------
    // Derived: Natural.successorCongruence :
    //   Π(x y : Natural). x = y → successor x = successor y.
    //
    // Eliminate the equality using Equality's recursor. The motive
    //   λ y' _eq'. Equality Natural (successor x) (successor y')
    // turns the goal "successor x = successor y" into the special case
    // where y' = x (so we need successor x = successor x, immediate from
    // reflexivity).
    // ------------------------------------------------------------------
    {
        // Proof body lives inside  λ x. λ y. λ eq. [body]. From body:
        //   eq=0, y=1, x=2.
        // Motive constructed inside body — inside its inner _eq' body the
        // binders are _eq'=0, y'=1, eq=2, y=3, x=4. The _eq's TYPE is
        // built inside y' but outside _eq', so binders are y'=0, eq=1,
        // y=2, x=3.
        auto motive = makeLambda("y'", Natural(),
            makeLambda("_eq'",
                equality(Natural(),
                   makeBoundVariable(3) /* x */,
                   makeBoundVariable(0) /* y' */),
                equality(Natural(),
                   successor(makeBoundVariable(4) /* x */),
                   successor(makeBoundVariable(1) /* y' */))));
        auto caseReflexivity = reflexivity(Natural(), successor(makeBoundVariable(2) /* x */));
        auto proof = makeLambda("x", Natural(),
            makeLambda("y", Natural(),
                makeLambda("eq",
                    equality(Natural(),
                       makeBoundVariable(1) /* x */,
                       makeBoundVariable(0) /* y */),
                    makeApplication(
                        makeApplication(
                            makeApplication(
                                makeApplication(
                                    makeApplication(
                                        makeApplication(
                                            makeConstant("Equality_recursor",
                                                          {makeLevelConst(0),
                                                           makeLevelConst(0)}),
                                            Natural()),
                                        makeBoundVariable(2) /* x */),
                                    motive),
                                caseReflexivity),
                            makeBoundVariable(1) /* y */),
                        makeBoundVariable(0) /* eq */))));
        auto theoremType = makePi("x", Natural(),
            makePi("y", Natural(),
                makePi("_eq",
                    equality(Natural(), makeBoundVariable(1), makeBoundVariable(0)),
                    equality(Natural(),
                       successor(makeBoundVariable(2)),
                       successor(makeBoundVariable(1))))));
        addDefinition(env, "Natural.successorCongruence", theoremType, proof);
        std::cout << "  Natural.successorCongruence   ⊨  Π(x y : Natural). x = y → "
                     "successor x = successor y   (J)\n";
    }

    // ------------------------------------------------------------------
    // Theorem 1: zero_add :  Π(a : Natural). 0 + a = a.
    //
    // Definitional: add zero a ι-reduces to a, so the proof is just
    // reflexivity Natural a.
    // ------------------------------------------------------------------
    {
        auto theoremType =
            makePi("a", Natural(),
                equality(Natural(), plus(zero(), makeBoundVariable(0)),
                   makeBoundVariable(0)));
        auto proof = makeLambda("a", Natural(),
            reflexivity(Natural(), makeBoundVariable(0)));
        addDefinition(env, "zero_add", theoremType, proof);
        std::cout << "  zero_add   ⊨  Π(a : Natural). 0 + a = a   "
                     "(definitional)\n";
    }

    // ------------------------------------------------------------------
    // Theorem 2: add_zero :  Π(a : Natural). a + 0 = a.
    //
    // Not definitional. Proof by induction on a using Natural_recursor
    // with a Proposition-valued motive, and Natural.successorCongruence (derived above, not an
    // axiom) for the successor case.
    // ------------------------------------------------------------------
    {
        auto motive = makeLambda("a", Natural(),
            equality(Natural(),
               plus(makeBoundVariable(0), zero()),
               makeBoundVariable(0)));
        auto caseZero = reflexivity(Natural(), zero());
        auto caseSucc = makeLambda("k", Natural(),
            makeLambda("inductionHypothesis",
                equality(Natural(),
                   plus(makeBoundVariable(0), zero()),
                   makeBoundVariable(0)),
                makeApplication(
                    makeApplication(
                        makeApplication(makeConstant("Natural.successorCongruence"),
                                        plus(makeBoundVariable(1) /* k */,
                                              zero())),
                        makeBoundVariable(1) /* k */),
                    makeBoundVariable(0) /* inductionHypothesis */)));

        auto theoremType =
            makePi("a", Natural(),
                equality(Natural(), plus(makeBoundVariable(0), zero()),
                   makeBoundVariable(0)));
        auto proof = makeLambda("a", Natural(),
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Natural_recursor", {makeLevelConst(0)}),
                            motive),
                        caseZero),
                    caseSucc),
                makeBoundVariable(0)));

        addDefinition(env, "add_zero", theoremType, proof);
        std::cout << "  add_zero   ⊨  Π(a : Natural). a + 0 = a   "
                     "(induction + Natural.successorCongruence)\n";
    }

    // ------------------------------------------------------------------
    // Theorem 3: one_add :  Π(a : Natural). 1 + a = successor a.
    //
    // Definitional once you observe that add (successor zero) a
    // ι-reduces to successor a directly.
    // ------------------------------------------------------------------
    {
        auto theoremType =
            makePi("a", Natural(),
                equality(Natural(), plus(successor(zero()), makeBoundVariable(0)),
                   successor(makeBoundVariable(0))));
        auto proof = makeLambda("a", Natural(),
            reflexivity(Natural(), successor(makeBoundVariable(0))));
        addDefinition(env, "one_add", theoremType, proof);
        std::cout << "  one_add    ⊨  Π(a : Natural). 1 + a = successor a   "
                     "(definitional)\n";
    }
}

// ----------------------------------------------------------------------------
// A small library of inductive types and derived functions. Demonstrates
// that the kernel now handles a variety of inductive shapes:
//   And      — Proposition, 1 ctor with 2 non-param Proposition args (restricted elim)
//   Or       — Proposition, 2 ctors                            (restricted elim)
//   Sum      — Type, 2 ctors                            (large elim)
//   Prod     — Type, 1 ctor with 2 non-param Type args  (large elim)
//   Option   — Type, 2 ctors                            (large elim)
//   List     — Type, 2 ctors, one recursive             (large elim)
// Each comes with at least one derived function or theorem.
// ----------------------------------------------------------------------------

void runInductiveLibraryProofs() {
    std::cout << "--- inductive library proofs ---\n";

    Environment env = buildArithmeticEnvironment();

    auto Natural = []() { return makeConstant("Natural"); };
    auto zero = []() { return makeConstant("zero"); };
    auto successor = [](ExpressionPointer n) {
        return makeApplication(makeConstant("successor"), n);
    };

    // ---------------- And (Proposition) -----------------
    // And.swap : Π(A B : Proposition). And A B → And B A.
    {
        addInductive(env, "And",
            makePi("A", makeProposition(),
                makePi("B", makeProposition(), makeProposition())),
            /*numParameters=*/ 2,
            {{
                "And.introduction",
                makePi("A", makeProposition(),
                    makePi("B", makeProposition(),
                        makePi("_a", makeBoundVariable(1) /* A */,
                            makePi("_b", makeBoundVariable(1) /* B */,
                                makeApplication(makeApplication(
                                    makeConstant("And"),
                                    makeBoundVariable(3) /* A */),
                                    makeBoundVariable(2) /* B */)))))
            }});

        // And.swap : Π(A B : Proposition). And A B → And B A.
        // Proof: λ A B p. And_recursor A B (λ _. And B A) (λ a b. And.introduction B A b a) p.
        // And is multi-arg Proposition ctor → restricted elim. Recursor has 0
        // motive-universe args (motive forced to Proposition).
        //
        // Inside the 3 outer lambdas (A, B, p): p=0, B=1, A=2.
        // Inside motive's `_` body (one more binder): _=0, p=1, B=2, A=3.
        // Inside the And.introduction case body's `b` lambda (3 lambdas in: a, b inside, p, B, A outside):
        //   b=0, a=1, p=2, B=3, A=4.
        auto motiveAndSwap = makeLambda("_",
            makeApplication(makeApplication(
                makeConstant("And"),
                makeBoundVariable(2) /* A */),
                makeBoundVariable(1) /* B */),
            // body: And B A.  At this position B=2, A=3.
            makeApplication(makeApplication(
                makeConstant("And"),
                makeBoundVariable(2) /* B */),
                makeBoundVariable(3) /* A */));
        auto caseAndIntroduction = makeLambda("a", makeBoundVariable(2) /* A */,
            makeLambda("b", makeBoundVariable(2) /* B */,
                // body: And.introduction B A b a.  At this position b=0, a=1, p=2, B=3, A=4.
                makeApplication(makeApplication(makeApplication(makeApplication(
                    makeConstant("And.introduction"),
                    makeBoundVariable(3) /* B */),
                    makeBoundVariable(4) /* A */),
                    makeBoundVariable(0) /* b */),
                    makeBoundVariable(1) /* a */)));
        auto swapBody = makeLambda("A", makeProposition(),
            makeLambda("B", makeProposition(),
                makeLambda("p",
                    makeApplication(makeApplication(
                        makeConstant("And"),
                        makeBoundVariable(1) /* A */),
                        makeBoundVariable(0) /* B */),
                    // body: And_recursor A B motive case p.
                    // At this position: p=0, B=1, A=2.
                    makeApplication(makeApplication(makeApplication(
                            makeApplication(makeApplication(
                                makeConstant("And_recursor"),
                                makeBoundVariable(2) /* A */),
                                makeBoundVariable(1) /* B */),
                            motiveAndSwap),
                        caseAndIntroduction),
                        makeBoundVariable(0) /* p */))));
        auto swapType = makePi("A", makeProposition(),
            makePi("B", makeProposition(),
                makePi("_",
                    makeApplication(makeApplication(
                        makeConstant("And"),
                        makeBoundVariable(1)),
                        makeBoundVariable(0)),
                    // body: And B A.  At position _=0, B=1, A=2.
                    makeApplication(makeApplication(
                        makeConstant("And"),
                        makeBoundVariable(1) /* B */),
                        makeBoundVariable(2) /* A */))));
        addDefinition(env, "And.swap", swapType, swapBody);
        std::cout << "  And.swap   ⊨  Π(A B : Proposition). And A B → And B A\n";
    }

    // ---------------- Or (Proposition) -----------------
    {
        addInductive(env, "Or",
            makePi("A", makeProposition(),
                makePi("B", makeProposition(), makeProposition())),
            /*numParameters=*/ 2,
            {
                {"Or.introduceLeft",
                    makePi("A", makeProposition(),
                        makePi("B", makeProposition(),
                            makePi("_a", makeBoundVariable(1) /* A */,
                                makeApplication(makeApplication(
                                    makeConstant("Or"),
                                    makeBoundVariable(2)),
                                    makeBoundVariable(1)))))},
                {"Or.introduceRight",
                    makePi("A", makeProposition(),
                        makePi("B", makeProposition(),
                            makePi("_b", makeBoundVariable(0) /* B */,
                                makeApplication(makeApplication(
                                    makeConstant("Or"),
                                    makeBoundVariable(2)),
                                    makeBoundVariable(1)))))},
            });

        // Or.swap : Π(A B : Proposition). Or A B → Or B A.
        // Or has multiple constructors → restricted elim.
        //
        // motive at body level (p=0, B=1, A=2): λ _ : Or A B. Or B A.
        //   In _ body (one more binder): _=0, p=1, B=2, A=3. Or B A means
        //   B=2, A=3.
        // Case for Or.introduceLeft: λ (a : A). Or.introduceRight B A a. At a body: a=0, p=1, B=2, A=3.
        //   Or.introduceRight B A a = Or.introduceRight (Bound 2) (Bound 3) (Bound 0).
        // Case for Or.introduceRight: λ (b : B). Or.introduceLeft B A b. At b body: same indices.
        auto motiveOrSwap = makeLambda("_",
            makeApplication(makeApplication(
                makeConstant("Or"),
                makeBoundVariable(2) /* A */),
                makeBoundVariable(1) /* B */),
            makeApplication(makeApplication(
                makeConstant("Or"),
                makeBoundVariable(2) /* B */),
                makeBoundVariable(3) /* A */));
        auto caseOrIntroduceLeft = makeLambda("a", makeBoundVariable(2) /* A */,
            makeApplication(makeApplication(makeApplication(
                makeConstant("Or.introduceRight"),
                makeBoundVariable(2) /* B */),
                makeBoundVariable(3) /* A */),
                makeBoundVariable(0) /* a */));
        auto caseOrIntroduceRight = makeLambda("b", makeBoundVariable(1) /* B */,
            makeApplication(makeApplication(makeApplication(
                makeConstant("Or.introduceLeft"),
                makeBoundVariable(2) /* B */),
                makeBoundVariable(3) /* A */),
                makeBoundVariable(0) /* b */));
        auto swapBody = makeLambda("A", makeProposition(),
            makeLambda("B", makeProposition(),
                makeLambda("p",
                    makeApplication(makeApplication(
                        makeConstant("Or"),
                        makeBoundVariable(1)),
                        makeBoundVariable(0)),
                    makeApplication(makeApplication(makeApplication(makeApplication(
                            makeApplication(makeApplication(
                                makeConstant("Or_recursor"),
                                makeBoundVariable(2) /* A */),
                                makeBoundVariable(1) /* B */),
                            motiveOrSwap),
                        caseOrIntroduceLeft),
                        caseOrIntroduceRight),
                        makeBoundVariable(0) /* p */))));
        auto swapType = makePi("A", makeProposition(),
            makePi("B", makeProposition(),
                makePi("_",
                    makeApplication(makeApplication(
                        makeConstant("Or"),
                        makeBoundVariable(1)),
                        makeBoundVariable(0)),
                    makeApplication(makeApplication(
                        makeConstant("Or"),
                        makeBoundVariable(1) /* B */),
                        makeBoundVariable(2) /* A */))));
        addDefinition(env, "Or.swap", swapType, swapBody);
        std::cout << "  Or.swap    ⊨  Π(A B : Proposition). Or A B → Or B A\n";
    }

    // ---------------- Prod (Type) -----------------
    {
        addInductive(env, "Prod",
            makePi("A", makeType(0),
                makePi("B", makeType(0), makeType(0))),
            /*numParameters=*/ 2,
            {{
                "Prod.pair",
                makePi("A", makeType(0),
                    makePi("B", makeType(0),
                        makePi("_a", makeBoundVariable(1),
                            makePi("_b", makeBoundVariable(1),
                                makeApplication(makeApplication(
                                    makeConstant("Prod"),
                                    makeBoundVariable(3) /* A */),
                                    makeBoundVariable(2) /* B */)))))
            }});

        // Prod.swap : Π(A B : Type 0). Prod A B → Prod B A.
        // Prod is in Type, so large elim is allowed; recursor takes a
        // motive-level universe arg. We use {1} so the motive returns
        // Type 0 (a Type-valued recursor).
        auto motiveProdSwap = makeLambda("_",
            makeApplication(makeApplication(
                makeConstant("Prod"),
                makeBoundVariable(2)),
                makeBoundVariable(1)),
            makeApplication(makeApplication(
                makeConstant("Prod"),
                makeBoundVariable(2) /* B */),
                makeBoundVariable(3) /* A */));
        auto caseProdPair = makeLambda("a", makeBoundVariable(2),
            makeLambda("b", makeBoundVariable(2),
                makeApplication(makeApplication(makeApplication(makeApplication(
                    makeConstant("Prod.pair"),
                    makeBoundVariable(3) /* B */),
                    makeBoundVariable(4) /* A */),
                    makeBoundVariable(0) /* b */),
                    makeBoundVariable(1) /* a */)));
        auto swapBody = makeLambda("A", makeType(0),
            makeLambda("B", makeType(0),
                makeLambda("p",
                    makeApplication(makeApplication(
                        makeConstant("Prod"),
                        makeBoundVariable(1)),
                        makeBoundVariable(0)),
                    makeApplication(makeApplication(makeApplication(
                            makeApplication(makeApplication(
                                makeConstant("Prod_recursor", {makeLevelConst(1)}),
                                makeBoundVariable(2)),
                                makeBoundVariable(1)),
                            motiveProdSwap),
                        caseProdPair),
                        makeBoundVariable(0)))));
        auto swapType = makePi("A", makeType(0),
            makePi("B", makeType(0),
                makePi("_",
                    makeApplication(makeApplication(
                        makeConstant("Prod"),
                        makeBoundVariable(1)),
                        makeBoundVariable(0)),
                    makeApplication(makeApplication(
                        makeConstant("Prod"),
                        makeBoundVariable(1) /* B */),
                        makeBoundVariable(2) /* A */))));
        addDefinition(env, "Prod.swap", swapType, swapBody);
        std::cout << "  Prod.swap  ⊨  Π(A B : Type 0). Prod A B → Prod B A\n";
    }

    // ---------------- Option (Type) -----------------
    {
        addInductive(env, "Option",
            makePi("A", makeType(0), makeType(0)),
            /*numParameters=*/ 1,
            {
                {"Option.none",
                    makePi("A", makeType(0),
                        makeApplication(makeConstant("Option"),
                                          makeBoundVariable(0)))},
                {"Option.some",
                    makePi("A", makeType(0),
                        makePi("_a", makeBoundVariable(0),
                            makeApplication(makeConstant("Option"),
                                              makeBoundVariable(1))))},
            });

        // Option.defaultTo : Π(A : Type 0). A → Option A → A.
        // At body level (3 outer lambdas A, dflt, opt): opt=0, dflt=1, A=2.
        // motive : λ _ : Option A. A.  Inside _: _=0, opt=1, dflt=2, A=3.
        //   The motive's body is A = Bound 3.
        // Case for Option.none : motive (Option.none A) = A. At body level
        //   we need the default value, which is dflt = Bound 1.
        // Case for Option.some : λ a : A. motive (Option.some A a) = A.
        //   Just return a. Inside a: a=0, opt=1, dflt=2, A=3. So a = Bound 0.
        auto motiveDefaultTo = makeLambda("_",
            makeApplication(makeConstant("Option"),
                              makeBoundVariable(2) /* A */),
            makeBoundVariable(3) /* A */);
        auto caseOptionNone = makeBoundVariable(1) /* dflt */;
        auto caseOptionSome = makeLambda("a", makeBoundVariable(2) /* A */,
            makeBoundVariable(0) /* a */);
        // Option.defaultTo : Π(A : Type 0). A → Option A → A.
        // Body: Option_recursor.{1} A (λ _. A) dflt (λ a. a) opt.
        auto defaultToBody = makeLambda("A", makeType(0),
            makeLambda("dflt", makeBoundVariable(0) /* A */,
                makeLambda("opt",
                    makeApplication(makeConstant("Option"),
                                      makeBoundVariable(1) /* A */),
                    makeApplication(
                        makeApplication(
                            makeApplication(
                                makeApplication(
                                    makeApplication(
                                        makeConstant("Option_recursor",
                                                      {makeLevelConst(1)}),
                                        makeBoundVariable(2) /* A */),
                                    motiveDefaultTo),
                                caseOptionNone),
                            caseOptionSome),
                        makeBoundVariable(0) /* opt */))));
        auto defaultToType = makePi("A", makeType(0),
            makePi("_dflt", makeBoundVariable(0) /* A */,
                makePi("_opt",
                    makeApplication(makeConstant("Option"),
                                      makeBoundVariable(1)),
                    makeBoundVariable(2) /* A */)));
        addDefinition(env, "Option.defaultTo", defaultToType, defaultToBody);
        std::cout << "  Option.defaultTo  ⊨  "
                     "Π(A : Type 0). A → Option A → A\n";

        // Test: Option.defaultTo Natural zero (Option.some Natural (successor zero))
        //       ≡ successor zero.
        // And:  Option.defaultTo Natural zero (Option.none Natural) ≡ zero.
        auto someOne = makeApplication(
            makeApplication(makeConstant("Option.some"), Natural()),
            successor(zero()));
        auto noneOfNaturals = makeApplication(makeConstant("Option.none"), Natural());
        auto callSome =
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Option.defaultTo"), Natural()),
                    zero()),
                someOne);
        auto callNone =
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("Option.defaultTo"), Natural()),
                    zero()),
                noneOfNaturals);
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, callSome, successor(zero())));
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, callNone, zero()));
    }

    // ---------------- List (Type) -----------------
    {
        addInductive(env, "List",
            makePi("A", makeType(0), makeType(0)),
            /*numParameters=*/ 1,
            {
                {"List.nil",
                    makePi("A", makeType(0),
                        makeApplication(makeConstant("List"),
                                          makeBoundVariable(0)))},
                {"List.prepend",
                    makePi("A", makeType(0),
                        makePi("_head", makeBoundVariable(0),
                            makePi("_tail",
                                makeApplication(makeConstant("List"),
                                                  makeBoundVariable(1)),
                                makeApplication(makeConstant("List"),
                                                  makeBoundVariable(2)))))},
            });

        // length : Π(A : Type 0). List A → Natural.
        // Recurses on the list. The case for List.nil returns zero; the
        // case for List.prepend takes head, tail, and IH (the length of the
        // tail), and returns successor IH.
        //
        // motive = λ _ : List A. Natural.  (No A dependence in the
        // codomain, so no Bound refs to A needed.)
        //
        // At the body level (2 outer lambdas A, list): list=0, A=1.
        // Case for List.prepend:  λ head tail IH. successor IH.
        //   Inside inductionHypothesis body (5 binders deep: inductionHypothesis=0, tail=1, head=2, list=3, A=4):
        //   inductionHypothesis = Bound 0.
        auto motiveLength = makeLambda("_",
            makeApplication(makeConstant("List"),
                              makeBoundVariable(1) /* A */),
            Natural());
        auto caseListNil = zero();
        auto caseListPrepend =
            makeLambda("head", makeBoundVariable(1) /* A */,
                makeLambda("tail",
                    makeApplication(makeConstant("List"),
                                      makeBoundVariable(2) /* A */),
                    makeLambda("inductionHypothesis", Natural(),
                        successor(makeBoundVariable(0) /* inductionHypothesis */))));
        auto lengthBody = makeLambda("A", makeType(0),
            makeLambda("list",
                makeApplication(makeConstant("List"),
                                  makeBoundVariable(0) /* A */),
                makeApplication(  // apply to list
                    makeApplication(  // apply to caseListPrepend
                        makeApplication(  // apply to caseListNil
                            makeApplication(  // apply to motive
                                makeApplication(  // apply to A
                                    makeConstant("List_recursor", {makeLevelConst(1)}),
                                    makeBoundVariable(1) /* A */),
                                motiveLength),
                            caseListNil),
                        caseListPrepend),
                    makeBoundVariable(0) /* list */)));
        auto lengthType = makePi("A", makeType(0),
            makePi("_list",
                makeApplication(makeConstant("List"),
                                  makeBoundVariable(0)),
                Natural()));
        addDefinition(env, "List.length", lengthType, lengthBody);
        std::cout << "  List.length       ⊨  "
                     "Π(A : Type 0). List A → Natural\n";

        // Test: List.length Natural (List.prepend zero List.nil)
        //       ≡ successor zero.
        // And:  List.length Natural List.nil ≡ zero.
        auto nilOfNaturals =
            makeApplication(makeConstant("List.nil"), Natural());
        auto singletonZero =
            makeApplication(
                makeApplication(
                    makeApplication(makeConstant("List.prepend"), Natural()),
                    zero()),
                nilOfNaturals);
        auto lengthEmpty =
            makeApplication(
                makeApplication(makeConstant("List.length"), Natural()),
                nilOfNaturals);
        auto lengthOne =
            makeApplication(
                makeApplication(makeConstant("List.length"), Natural()),
                singletonZero);
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, lengthEmpty, zero()));
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, lengthOne,   successor(zero())));
    }
}

// ----------------------------------------------------------------------------
// Surface-AST pretty-printer used by parser tests. Not a public API of
// the parser; lives here as a test convenience. Produces a deterministic
// fully-parenthesised string so test assertions can compare for equality.
// ----------------------------------------------------------------------------

std::string surfaceLevelToDebugString(const SurfaceLevel& level);
std::string surfaceToDebugString(const SurfaceExpression& expression);

std::string surfaceLevelToDebugString(const SurfaceLevel& level) {
    if (auto* numeric = std::get_if<SurfaceLevelNumeric>(&level.node)) {
        return std::to_string(numeric->value);
    }
    if (auto* name = std::get_if<SurfaceLevelName>(&level.node)) {
        return name->name;
    }
    if (auto* maxLevel = std::get_if<SurfaceLevelMax>(&level.node)) {
        return "max(" + surfaceLevelToDebugString(*maxLevel->left) + ", "
             + surfaceLevelToDebugString(*maxLevel->right) + ")";
    }
    if (auto* imaxLevel = std::get_if<SurfaceLevelImax>(&level.node)) {
        return "imax(" + surfaceLevelToDebugString(*imaxLevel->left) + ", "
             + surfaceLevelToDebugString(*imaxLevel->right) + ")";
    }
    if (auto* addLevel = std::get_if<SurfaceLevelAdd>(&level.node)) {
        return "(" + surfaceLevelToDebugString(*addLevel->base) + " + "
             + std::to_string(addLevel->amount) + ")";
    }
    return "?";
}

std::string surfaceToDebugString(const SurfaceExpression& expression) {
    if (auto* identifier = std::get_if<SurfaceIdentifier>(&expression.node)) {
        std::string result = identifier->qualifiedName;
        if (!identifier->universeArgs.empty()) {
            result += ".{";
            for (size_t i = 0; i < identifier->universeArgs.size(); ++i) {
                if (i) result += ", ";
                result += surfaceLevelToDebugString(
                    *identifier->universeArgs[i]);
            }
            result += "}";
        }
        return result;
    }
    if (auto* numeric = std::get_if<SurfaceNumericLiteral>(&expression.node)) {
        return numeric->digits;
    }
    if (auto* application = std::get_if<SurfaceApplication>(&expression.node)) {
        std::string result = surfaceToDebugString(*application->function);
        result += "(";
        for (size_t i = 0; i < application->arguments.size(); ++i) {
            if (i) result += ", ";
            result += surfaceToDebugString(*application->arguments[i]);
        }
        result += ")";
        return result;
    }
    if (auto* pi = std::get_if<SurfacePiType>(&expression.node)) {
        std::string result = "Pi(";
        if (pi->binder.names.empty()) {
            result += "_";
        } else {
            for (size_t i = 0; i < pi->binder.names.size(); ++i) {
                if (i) result += " ";
                result += pi->binder.names[i];
            }
        }
        result += " : " + surfaceToDebugString(*pi->binder.type);
        result += ", " + surfaceToDebugString(*pi->codomain) + ")";
        return result;
    }
    if (auto* lambda = std::get_if<SurfaceLambda>(&expression.node)) {
        std::string result = "Lambda(";
        for (size_t i = 0; i < lambda->binder.names.size(); ++i) {
            if (i) result += " ";
            result += lambda->binder.names[i];
        }
        result += " : " + surfaceToDebugString(*lambda->binder.type);
        result += ", " + surfaceToDebugString(*lambda->body) + ")";
        return result;
    }
    if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
        return "Let(" + let->name
             + " : " + surfaceToDebugString(*let->type)
             + " := " + surfaceToDebugString(*let->value)
             + ", " + surfaceToDebugString(*let->body) + ")";
    }
    if (auto* ascription = std::get_if<SurfaceAscription>(&expression.node)) {
        return "Ascribe(" + surfaceToDebugString(*ascription->expression)
             + " : " + surfaceToDebugString(*ascription->type) + ")";
    }
    if (auto* typeExpr = std::get_if<SurfaceType>(&expression.node)) {
        return "Type(" + surfaceLevelToDebugString(*typeExpr->level) + ")";
    }
    if (std::get_if<SurfaceProposition>(&expression.node)) {
        return "Proposition";
    }
    if (auto* binary = std::get_if<SurfaceBinaryOperation>(&expression.node)) {
        return "(" + surfaceToDebugString(*binary->left)
             + " " + binary->opSymbol + " "
             + surfaceToDebugString(*binary->right) + ")";
    }
    if (auto* unary = std::get_if<SurfaceUnaryOperation>(&expression.node)) {
        return unary->opSymbol + surfaceToDebugString(*unary->operand);
    }
    return "?";
}

// ----------------------------------------------------------------------------
// Lexer tests. The lexer is part of the .math surface-language frontend
// and is independent of the kernel — these tests exercise only token
// production, not parsing or elaboration.
// ----------------------------------------------------------------------------

void runLexerTests() {
    std::cout << "--- lexer tests ---\n";

    auto kindsOf = [](const std::string& source) {
        std::vector<TokenKind> kinds;
        for (const auto& token : lex(source)) kinds.push_back(token.kind);
        return kinds;
    };

    auto expectLexError = [](const std::string& source,
                             const char* description, int testLine) {
        bool threw = false;
        try { lex(source); } catch (const LexError&) { threw = true; }
        if (threw) { ++passed; }
        else { ++failed; std::cerr << "FAIL (line " << testLine
                                    << "): expected LexError from "
                                    << description << "\n"; }
    };

    // Plain identifier.
    {
        auto tokens = lex("foo");
        EXPECT_TRUE(tokens.size() == 2);
        EXPECT_TRUE(tokens[0].kind == TokenKind::Identifier
                    && tokens[0].lexeme == "foo");
        EXPECT_TRUE(tokens[1].kind == TokenKind::EndOfFile);
    }

    // A keyword is recognised over a generic identifier.
    {
        auto tokens = lex("theorem");
        EXPECT_TRUE(tokens[0].kind == TokenKind::KeywordTheorem);
        EXPECT_TRUE(tokens[0].lexeme == "theorem");
    }

    // Identifier prefixed by underscore is allowed.
    {
        auto tokens = lex("_private");
        EXPECT_TRUE(tokens[0].kind == TokenKind::Identifier
                    && tokens[0].lexeme == "_private");
    }

    // Qualified name is lexed as three tokens: ident, dot, ident.
    {
        auto tokens = lex("Natural.add");
        EXPECT_TRUE(tokens.size() == 4);
        EXPECT_TRUE(tokens[0].kind == TokenKind::Identifier
                    && tokens[0].lexeme == "Natural");
        EXPECT_TRUE(tokens[1].kind == TokenKind::Dot);
        EXPECT_TRUE(tokens[2].kind == TokenKind::Identifier
                    && tokens[2].lexeme == "add");
    }

    // Universe-args opener .{ is a single token, distinguishing namespace
    // qualification from universe instantiation.
    {
        auto tokens = lex("Equality.{u}");
        EXPECT_TRUE(tokens.size() == 5);
        EXPECT_TRUE(tokens[0].kind == TokenKind::Identifier);
        EXPECT_TRUE(tokens[1].kind == TokenKind::DotLeftBrace);
        EXPECT_TRUE(tokens[2].kind == TokenKind::Identifier
                    && tokens[2].lexeme == "u");
        EXPECT_TRUE(tokens[3].kind == TokenKind::RightBrace);
    }

    // Numeric literal.
    {
        auto tokens = lex("25");
        EXPECT_TRUE(tokens[0].kind == TokenKind::NumericLiteral
                    && tokens[0].lexeme == "25");
    }

    // Multiple numeric literals interleaved with operators.
    {
        auto kinds = kindsOf("25 + 100");
        std::vector<TokenKind> expected = {
            TokenKind::NumericLiteral, TokenKind::Plus,
            TokenKind::NumericLiteral, TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }

    // ASCII multi-char operators win over their first character.
    {
        auto kinds = kindsOf("x := y");
        std::vector<TokenKind> expected = {
            TokenKind::Identifier, TokenKind::Assign,
            TokenKind::Identifier, TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }
    {
        auto kinds = kindsOf("a <= b");
        std::vector<TokenKind> expected = {
            TokenKind::Identifier, TokenKind::LessOrEqual,
            TokenKind::Identifier, TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }
    {
        auto kinds = kindsOf("function (x : T) => x");
        std::vector<TokenKind> expected = {
            TokenKind::KeywordFunction, TokenKind::LeftParen,
            TokenKind::Identifier, TokenKind::Colon, TokenKind::Identifier,
            TokenKind::RightParen, TokenKind::FatArrow,
            TokenKind::Identifier, TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }

    // ASCII and Unicode arrows both tokenise as Arrow.
    {
        auto tokens = lex("Natural -> Natural");
        EXPECT_TRUE(tokens[1].kind == TokenKind::Arrow
                    && tokens[1].lexeme == "->");
    }
    {
        auto tokens = lex("Natural → Natural");
        EXPECT_TRUE(tokens[1].kind == TokenKind::Arrow
                    && tokens[1].lexeme == "→");
    }

    // Logical operators.
    {
        auto kinds = kindsOf("p /\\ q \\/ r");
        std::vector<TokenKind> expected = {
            TokenKind::Identifier, TokenKind::LogicalAnd,
            TokenKind::Identifier, TokenKind::LogicalOr,
            TokenKind::Identifier, TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }
    {
        auto kinds = kindsOf("p ∧ q ∨ r");
        std::vector<TokenKind> expected = {
            TokenKind::Identifier, TokenKind::LogicalAnd,
            TokenKind::Identifier, TokenKind::LogicalOr,
            TokenKind::Identifier, TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }

    // Line comments are skipped entirely.
    {
        auto tokens = lex("-- skip me\nfoo");
        EXPECT_TRUE(tokens.size() == 2);
        EXPECT_TRUE(tokens[0].lexeme == "foo");
    }

    // Block comments are skipped; nesting works.
    {
        auto tokens = lex("/- outer /- inner -/ still outer -/ foo");
        EXPECT_TRUE(tokens.size() == 2);
        EXPECT_TRUE(tokens[0].lexeme == "foo");
    }

    // Multi-line block comments adjust the line counter.
    {
        auto tokens = lex("/- multi\n  line\n  comment -/\nfoo");
        EXPECT_TRUE(tokens[0].kind == TokenKind::Identifier);
        EXPECT_TRUE(tokens[0].line == 4);
    }

    // Errors: unterminated block comment.
    expectLexError("/- never closed", "unterminated block comment",
                   __LINE__);

    // Errors: unknown character.
    expectLexError("foo @ bar", "unexpected '@'", __LINE__);

    // Position tracking: column on a single line.
    {
        auto tokens = lex("a + b");
        EXPECT_TRUE(tokens[0].line == 1 && tokens[0].column == 1);
        EXPECT_TRUE(tokens[1].line == 1 && tokens[1].column == 3);
        EXPECT_TRUE(tokens[2].line == 1 && tokens[2].column == 5);
    }

    // Position tracking: line on multi-line input.
    {
        auto tokens = lex("a\nb\nc");
        EXPECT_TRUE(tokens[0].line == 1);
        EXPECT_TRUE(tokens[1].line == 2);
        EXPECT_TRUE(tokens[2].line == 3);
    }

    // Pipe (constructor separator) tokenises distinctly from logical-or.
    {
        auto kinds = kindsOf("| zero : Natural");
        EXPECT_TRUE(kinds[0] == TokenKind::Pipe);
    }

    // A realistic small fragment.
    {
        auto kinds = kindsOf(
            "theorem Natural.add_zero(a : Natural) : a + zero = a");
        std::vector<TokenKind> expected = {
            TokenKind::KeywordTheorem,
            TokenKind::Identifier, TokenKind::Dot, TokenKind::Identifier,
            TokenKind::LeftParen,
            TokenKind::Identifier, TokenKind::Colon, TokenKind::Identifier,
            TokenKind::RightParen,
            TokenKind::Colon,
            TokenKind::Identifier, TokenKind::Plus, TokenKind::Identifier,
            TokenKind::Equal, TokenKind::Identifier,
            TokenKind::EndOfFile};
        EXPECT_TRUE(kinds == expected);
    }
}

// ----------------------------------------------------------------------------
// Parser tests. Exercises the expression sub-grammar via the
// surface-AST pretty-printer above. Each test parses a source string
// and checks that its debug-print matches the expected fully-
// parenthesised form. Errors are tested by expecting ParseError.
// ----------------------------------------------------------------------------

void runParserTests() {
    std::cout << "--- parser tests ---\n";

    auto parseString = [](const std::string& source) {
        return parseExpression(lex(source));
    };

    auto expectParse = [&](const std::string& source,
                           const std::string& expected,
                           int testLine) {
        try {
            auto result = parseString(source);
            std::string actual = surfaceToDebugString(*result);
            if (actual != expected) {
                ++failed;
                std::cerr << "FAIL (line " << testLine << "): "
                          << "parse(\"" << source << "\")\n"
                          << "  expected: " << expected << "\n"
                          << "  actual:   " << actual << "\n";
            } else {
                ++passed;
            }
        } catch (const ParseError& error) {
            ++failed;
            std::cerr << "FAIL (line " << testLine << "): "
                      << "parse(\"" << source << "\") threw: "
                      << error.what() << "\n";
        }
    };

    auto expectParseError = [&](const std::string& source,
                                const char* description, int testLine) {
        bool threw = false;
        try { parseString(source); }
        catch (const ParseError&) { threw = true; }
        catch (const LexError&) { threw = true; }
        if (threw) ++passed;
        else {
            ++failed;
            std::cerr << "FAIL (line " << testLine
                      << "): expected ParseError from " << description << "\n";
        }
    };

    // Atoms.
    expectParse("foo",                "foo",                                __LINE__);
    expectParse("Natural.add",        "Natural.add",                        __LINE__);
    expectParse("Equality.symmetry",  "Equality.symmetry",                  __LINE__);
    expectParse("25",                 "25",                                 __LINE__);
    expectParse("Proposition",        "Proposition",                        __LINE__);
    expectParse("Type(0)",            "Type(0)",                            __LINE__);
    expectParse("Type(u)",            "Type(u)",                            __LINE__);
    expectParse("Type(u + 1)",        "Type((u + 1))",                      __LINE__);
    expectParse("Type(max(u, v))",    "Type(max(u, v))",                    __LINE__);
    expectParse("Type(max(u, v + 1))","Type(max(u, (v + 1)))",              __LINE__);
    expectParse("Type(imax(u, v))",   "Type(imax(u, v))",                   __LINE__);

    // Universe arguments on identifiers.
    expectParse("Equality.{u}",       "Equality.{u}",                       __LINE__);
    expectParse("Equality.{0}",       "Equality.{0}",                       __LINE__);
    expectParse("Equality.recursor.{u, 0}",
                "Equality.recursor.{u, 0}",                                 __LINE__);

    // Application.
    expectParse("f(x)",               "f(x)",                               __LINE__);
    expectParse("f(x, y)",            "f(x, y)",                            __LINE__);
    expectParse("f(g(x))",            "f(g(x))",                            __LINE__);
    expectParse("f(x)(y)",            "f(x)(y)",                            __LINE__);

    // Binary operator precedence — multiplicative binds tighter than additive.
    expectParse("a + b",              "(a + b)",                            __LINE__);
    expectParse("a + b * c",          "(a + (b * c))",                      __LINE__);
    expectParse("a * b + c",          "((a * b) + c)",                      __LINE__);

    // Left associativity for + and *.
    expectParse("a + b + c",          "((a + b) + c)",                      __LINE__);
    expectParse("a * b * c",          "((a * b) * c)",                      __LINE__);

    // Right associativity for ^.
    expectParse("a ^ b ^ c",          "(a ^ (b ^ c))",                      __LINE__);

    // Right associativity for →.
    expectParse("A -> B -> C",        "Pi(_ : A, Pi(_ : B, C))",            __LINE__);
    expectParse("A → B → C",          "Pi(_ : A, Pi(_ : B, C))",            __LINE__);

    // Equality is non-associative.
    expectParseError("a = b = c", "a = b = c (chained)", __LINE__);
    expectParseError("a < b < c", "a < b < c (chained)", __LINE__);

    // Unary minus.
    expectParse("-x",                 "-x",                                 __LINE__);
    expectParse("-x + y",             "(-x + y)",                           __LINE__);

    // Logical operators.
    expectParse("p ∧ q ∨ r",          "((p ∧ q) ∨ r)",                      __LINE__);
    expectParse("p /\\ q \\/ r",      "((p ∧ q) ∨ r)",                      __LINE__);

    // Parenthesised grouping and ascription.
    expectParse("(a + b)",            "(a + b)",                            __LINE__);
    expectParse("(25 : Integer)",     "Ascribe(25 : Integer)",              __LINE__);

    // Pi types with named binders.
    expectParse("(x : T) -> U",       "Pi(x : T, U)",                       __LINE__);
    expectParse("(x y : T) -> U",     "Pi(x y : T, U)",                     __LINE__);
    expectParse("(x : T) -> (y : U) -> V",
                "Pi(x : T, Pi(y : U, V))",                                  __LINE__);
    // Curried Pi where the codomain references the binder.
    expectParse("(A : Type(0)) -> A -> A",
                "Pi(A : Type(0), Pi(_ : A, A))",                            __LINE__);

    // Lambdas.
    expectParse("function (x : T) => x",   "Lambda(x : T, x)",                   __LINE__);
    expectParse("function (x : T) (y : U) => x",
                "Lambda(x : T, Lambda(y : U, x))",                          __LINE__);

    // Let.
    expectParse("let x : T := y in x",
                "Let(x : T := y, x)",                                       __LINE__);

    // Mixed precedence with operators around application.
    expectParse("f(x) + g(y) * h(z)",
                "(f(x) + (g(y) * h(z)))",                                   __LINE__);

    // A realistic theorem statement.
    expectParse("(a : Natural) -> a + zero = a",
                "Pi(a : Natural, ((a + zero) = a))",                        __LINE__);

    // Empty argument list error.
    expectParseError("f()", "empty argument list", __LINE__);
}

// ----------------------------------------------------------------------------
// End-to-end pipeline tests. Drive a .math source string through the
// full lexer + parser + elaborator + kernel and check the resulting
// environment.
// ----------------------------------------------------------------------------

Environment verifyMathSource(const std::string& source) {
    Environment environment;
    auto tokens = lex(source);
    auto module = parseModule(tokens);
    std::vector<std::string> importedModules;
    // The elaborator writes axiom-admission warnings straight to
    // std::cerr; redirect to a sink during ordinary unit tests so they
    // don't clutter the suite output. Tests that want to assert on the
    // warning text can call elaborateModule directly with cerr restored.
    std::ostringstream warningSink;
    std::streambuf* originalCerrBuffer = std::cerr.rdbuf(warningSink.rdbuf());
    try {
        elaborateModule(module, environment, importedModules);
    } catch (...) {
        std::cerr.rdbuf(originalCerrBuffer);
        throw;
    }
    std::cerr.rdbuf(originalCerrBuffer);
    return environment;
}

// Like verifyMathSource, but returns the captured stderr alongside the
// environment so tests can inspect axiom-admission warnings.
struct VerifyResult {
    Environment environment;
    std::string capturedStderr;
};

VerifyResult verifyMathSourceCapturingStderr(const std::string& source) {
    VerifyResult result;
    auto tokens = lex(source);
    auto module = parseModule(tokens);
    std::vector<std::string> importedModules;
    std::ostringstream warningSink;
    std::streambuf* originalCerrBuffer = std::cerr.rdbuf(warningSink.rdbuf());
    try {
        elaborateModule(module, result.environment, importedModules);
    } catch (...) {
        std::cerr.rdbuf(originalCerrBuffer);
        throw;
    }
    std::cerr.rdbuf(originalCerrBuffer);
    result.capturedStderr = warningSink.str();
    return result;
}

// Exercises the elaborator's diagnostic output — checks that intended
// error categories produce messages containing the expected substrings
// (frame phrases, type names, hints). We don't pin the FULL message
// because the formatting may evolve; we just lock in the cues that a
// user would scan for when fixing the bug.
void runErrorMessageTests() {
    std::cout << "--- error message tests ---\n";

    auto expectErrorContains =
        [](const std::string& source,
           const std::vector<std::string>& mustContain,
           const char* description, int testLine) {
        std::string message;
        bool threw = false;
        try { verifyMathSource(source); }
        catch (const LexError& e)       { threw = true; message = e.what(); }
        catch (const ParseError& e)     { threw = true; message = e.what(); }
        catch (const ElaborateError& e) { threw = true; message = e.what(); }
        catch (const TypeError& e)      { threw = true; message = e.what(); }
        if (!threw) {
            ++failed;
            std::cerr << "FAIL (line " << testLine
                      << "): expected error from " << description
                      << " but none was thrown\n";
            return;
        }
        std::vector<std::string> missing;
        for (const auto& needle : mustContain) {
            if (message.find(needle) == std::string::npos) {
                missing.push_back(needle);
            }
        }
        if (missing.empty()) ++passed;
        else {
            ++failed;
            std::cerr << "FAIL (line " << testLine
                      << "): error for " << description
                      << " missing substring(s):\n";
            for (const auto& needle : missing) {
                std::cerr << "    expected: " << needle << "\n";
            }
            std::cerr << "    actual message:\n      " << message << "\n";
        }
    };

    // Hammer failure: should name the theorem, the goal type, and
    // list at least one candidate.
    expectErrorContains(R"(
module Test.errors_hammer

theorem cant_find (A B : Proposition) (h : A) : B := ?
)",
        {"hammer placeholder '?'",
         "theorem 'cant_find'",
         "could not find a proof",
         "Candidates in scope:",
         "h : A"},
        "hammer-failure error",
        __LINE__);

    // Cases body type mismatch: the case-for-Constructor frame should
    // appear, along with expected vs actual types.
    expectErrorContains(R"(
module Test.errors_cases

inductive And (A B : Proposition) : Proposition where
  | And.introduction : A → B → And(A, B)

theorem wrong_branch (A B : Proposition) (h : And(A, B)) : A :=
  cases h {
    | And.introduction(a, b) => b
  }
)",
        {"case for 'And.introduction'",
         "cases expression at line",
         "theorem 'wrong_branch'",
         "expected type: A",
         "actual type:   B"},
        "cases-branch type mismatch",
        __LINE__);

    // Under-applied inference with explicit `{x : T}` binders: when
    // the declaration uses implicit markers, the user has committed
    // to inference, so a failure surfaces directly. `pick_b` has
    // two propositional parameters but the second's return type only
    // mentions B — A cannot be determined from the trailing proof.
    expectErrorContains(R"(
module Test.errors_under_applied

theorem pick_b {A B : Proposition} (b : B) : B := b

-- Call with only the proof of B; inference cannot pin down A.
theorem caller (P Q : Proposition) (h : Q) : Q := pick_b(h)
)",
        {"could not infer all leading arguments",
         "pick_b",
         "Provide the missing argument(s)"},
        "under-applied implicit inference",
        __LINE__);

    // Constructor argument type mismatch: kernel error attribution to
    // the theorem, with expected and actual types pretty-printed.
    expectErrorContains(R"(
module Test.errors_constructor

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive And (A B : Proposition) : Proposition where
  | And.introduction : A → B → And(A, B)

theorem bad_call (A : Proposition) (n : Natural) : And(A, A) :=
  And.introduction(A, A, n, n)
)",
        {"theorem 'bad_call'",
         "kernel:",
         "expected type: A",
         "actual type:   Natural"},
        "constructor argument type mismatch",
        __LINE__);

    // Successful hammer: '?' resolves to a hypothesis, no error.
    {
        try {
            verifyMathSource(R"(
module Test.errors_hammer_ok

inductive Dummy : Proposition where
  | unit : Dummy

theorem hammer_ok (A : Proposition) (h : A) : A := ?
)");
            ++passed;
        } catch (const std::exception& e) {
            ++failed;
            std::cerr << "FAIL (line " << __LINE__
                      << "): hammer should have resolved hypothesis-match: "
                      << e.what() << "\n";
        }
    }

    // Phase 3.1: depth-1 hypothesis application — `h : A → B`, `a : A`
    // in scope and goal `B`, the hammer should apply `h(a)`.
    auto expectVerifies = [](const std::string& source,
                              const char* description,
                              int testLine) {
        try {
            verifyMathSource(source);
            ++passed;
        } catch (const std::exception& e) {
            ++failed;
            std::cerr << "FAIL (line " << testLine
                      << "): " << description << ": "
                      << e.what() << "\n";
        }
    };

    expectVerifies(R"(
module Test.hammer_app_one_step

theorem one_step (A B : Proposition) (h : A → B) (a : A) : B := ?
)",
        "depth-1 hypothesis application (single arg)",
        __LINE__);

    expectVerifies(R"(
module Test.hammer_app_two_step

theorem two_step (A B C : Proposition)
                 (h : A → B → C)
                 (a : A) (b : B) : C := ?
)",
        "depth-1 hypothesis application (two args)",
        __LINE__);

    // Application strategy must not shadow hypothesis-match: when the
    // goal is directly in scope, prefer the cheaper direct match.
    expectVerifies(R"(
module Test.hammer_app_prefers_direct

theorem prefers_direct (A : Proposition) (h : A → A) (a : A) : A := ?
)",
        "direct match still wins over application",
        __LINE__);

    // When the application's argument is itself missing from scope,
    // the hammer reports failure (we don't yet recurse into multi-
    // level application).
    expectErrorContains(R"(
module Test.hammer_app_unfillable

theorem unfillable (A B : Proposition) (h : A → B) : B := ?
)",
        {"hammer placeholder '?'",
         "theorem 'unfillable'",
         "could not find a proof",
         "depth-1 hypothesis-application"},
        "hammer fails when an application arg is unfillable",
        __LINE__);

    // Axiom-admission warning: every `axiom` declaration must surface
    // on stderr so a verified file is never silent about its unproved
    // assumptions. Two axioms in one module → two warning lines.
    {
        auto result = verifyMathSourceCapturingStderr(R"(
module Test.axiom_warnings
axiom AssumedFact : Type(0)
axiom AnotherFact : Type(0)
)");
        const std::string& captured = result.capturedStderr;
        std::vector<std::string> mustContain = {
            "warning: axiom 'AssumedFact' admitted without proof",
            "warning: axiom 'AnotherFact' admitted without proof",
        };
        std::vector<std::string> missing;
        for (const auto& needle : mustContain) {
            if (captured.find(needle) == std::string::npos)
                missing.push_back(needle);
        }
        if (missing.empty()) ++passed;
        else {
            ++failed;
            std::cerr << "FAIL (line " << __LINE__
                      << "): axiom-admission warning missing substring(s):\n";
            for (const auto& needle : missing)
                std::cerr << "    expected: " << needle << "\n";
            std::cerr << "    actual captured stderr:\n" << captured << "\n";
        }
    }

    // Definitions and theorems must NOT trigger the axiom warning.
    {
        auto result = verifyMathSourceCapturingStderr(R"(
module Test.no_warning_on_definition
inductive Bool : Type(0) where
  | true : Bool
  | false : Bool
definition Bool.identity : Bool → Bool := function (b : Bool) => b
)");
        if (result.capturedStderr.empty()) ++passed;
        else {
            ++failed;
            std::cerr << "FAIL (line " << __LINE__
                      << "): non-axiom declarations should not emit warnings."
                      << " stderr captured: " << result.capturedStderr << "\n";
        }
    }

    // calc block, single step: just returns the proof.
    expectVerifies(R"(
module Test.calc_single_step

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

theorem trivial (A : Type(0)) (x : A) : Equality.{0}(A, x, x) :=
  calc x = x by reflexivity.{0}(A, x)
)",
        "calc with a single step elaborates to the step proof",
        __LINE__);

    // calc block, two-step transitivity chain.
    expectVerifies(R"(
module Test.calc_two_step

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

axiom Equality.transitivity.{u}
  : (A : Type(u)) → (x y z : A)
    → Equality.{u}(A, x, y) → Equality.{u}(A, y, z)
    → Equality.{u}(A, x, z)

axiom step_ab : Equality.{0}(Natural, zero, successor(zero))
axiom step_bc : Equality.{0}(Natural, successor(zero),
                              successor(successor(zero)))

theorem chained
        : Equality.{0}(Natural, zero, successor(successor(zero))) :=
  calc zero
     = successor(zero)             by step_ab
     = successor(successor(zero))  by step_bc
)",
        "calc with two steps folds into Equality.transitivity",
        __LINE__);

    // Pattern-match definition with a recursive call inside a cases
    // clause's body. Exercises rewriteRecursiveCalls's descent into
    // SurfaceCases — without it the recursive call wouldn't be
    // rewritten to the recursion hypothesis and elaboration fails.
    expectVerifies(R"(
module Test.recursive_call_inside_cases

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

definition recursive_through_cases : Natural → Natural
  | zero                   => zero
  | successor(predecessor) =>
      cases predecessor {
        | zero               => successor(zero)
        | successor(_inner)  => recursive_through_cases(predecessor)
      }
)",
        "recursive call inside cases body is rewritten",
        __LINE__);

    // Numeric literal: `2` desugars to `successor(successor(zero))`.
    expectVerifies(R"(
module Test.numeric_literal_desugar

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

theorem two_equals_two : Equality.{0}(Natural, 2, successor(successor(zero)))
  := reflexivity.{0}(Natural, 2)
)",
        "numeric literal desugars to successor chain",
        __LINE__);

    // `≤` on Naturals desugars to `LessOrEqual`.
    expectVerifies(R"(
module Test.le_operator

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive LessOrEqual : Natural → Natural → Proposition where
  | LessOrEqual.reflexivity
      : (n : Natural) → LessOrEqual(n, n)
  | LessOrEqual.step
      : (smaller larger : Natural)
        → LessOrEqual(smaller, larger)
        → LessOrEqual(smaller, successor(larger))

theorem two_le_three : 2 ≤ 3 :=
  LessOrEqual.step(2, 2, LessOrEqual.reflexivity(2))
)",
        "≤ operator desugars to LessOrEqual",
        __LINE__);

    // `∧` on propositions desugars to `And(P, Q)`.
    expectVerifies(R"(
module Test.and_operator

inductive And (A B : Proposition) : Proposition where
  | And.introduction : A → B → And(A, B)

theorem both_intro (A B : Proposition) (a : A) (b : B) : A ∧ B :=
  And.introduction(A, B, a, b)
)",
        "∧ operator desugars to And",
        __LINE__);

    // `∨` on propositions desugars to `Or(P, Q)`.
    expectVerifies(R"(
module Test.or_operator

inductive Or (A B : Proposition) : Proposition where
  | Or.introduceLeft  : A → Or(A, B)
  | Or.introduceRight : B → Or(A, B)

theorem left_in (A B : Proposition) (a : A) : A ∨ B :=
  Or.introduceLeft(A, B, a)
)",
        "∨ operator desugars to Or",
        __LINE__);

    // `¬` desugars to `Not(P)`.
    expectVerifies(R"(
module Test.not_operator

inductive False : Proposition where

definition Not (A : Proposition) : Proposition := A → False

inductive True : Proposition where
  | True.trivial : True

theorem trivial_does_not_imply_false (h : True) : ¬False :=
  function (f : False) => f
)",
        "¬ operator desugars to Not",
        __LINE__);

    // `∣` on Naturals desugars to `Natural.divides(a, b)`.
    expectVerifies(R"(
module Test.divides_operator

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

inductive Exists.{u} (A : Type(u)) (P : A → Proposition) : Proposition where
  | Exists.introduce : (witness : A) → P(witness) → Exists(A, P)

definition Natural.multiply : Natural → Natural → Natural
  | zero,         _ => zero
  | successor(k), m => m

definition Natural.divides (divisor dividend : Natural) : Proposition :=
  Exists(Natural,
          function (quotient : Natural)
              => Equality.{0}(Natural, dividend, Natural.multiply(divisor, quotient)))

theorem one_divides_one : 1 ∣ 1 :=
  Exists.introduce.{0}(Natural,
      function (quotient : Natural)
          => Equality.{0}(Natural, 1, Natural.multiply(1, quotient)),
      1,
      reflexivity.{0}(Natural, 1))
)",
        "∣ operator desugars to Natural.divides",
        __LINE__);

    // `<` on Naturals desugars to `LessOrEqual(successor(_), _)`.
    expectVerifies(R"(
module Test.lt_operator

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive LessOrEqual : Natural → Natural → Proposition where
  | LessOrEqual.reflexivity
      : (n : Natural) → LessOrEqual(n, n)
  | LessOrEqual.step
      : (smaller larger : Natural)
        → LessOrEqual(smaller, larger)
        → LessOrEqual(smaller, successor(larger))

theorem one_lt_two : 1 < 2 := LessOrEqual.reflexivity(2)
)",
        "< operator desugars to LessOrEqual on successor of left",
        __LINE__);

    // `∀ (x : T). body` desugars to `(x : T) → body` (Pi type).
    expectVerifies(R"(
module Test.forall_quantifier

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

theorem reflexive_for_all : ∀ (n : Natural). Equality.{0}(Natural, n, n) :=
  function (n : Natural) => reflexivity.{0}(Natural, n)
)",
        "∀ desugars to a Pi type",
        __LINE__);

    // `∃ (x : T). body` desugars to `Exists(T, function (x : T) => body)`.
    expectVerifies(R"(
module Test.exists_quantifier

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

inductive Exists.{u} (A : Type(u)) (P : A → Proposition) : Proposition where
  | Exists.introduce : (witness : A) → P(witness) → Exists(A, P)

theorem some_natural_equals_zero
        : ∃ (n : Natural). Equality.{0}(Natural, n, zero) :=
  Exists.introduce.{0}(Natural,
      function (n : Natural) => Equality.{0}(Natural, n, zero),
      zero,
      reflexivity.{0}(Natural, zero))
)",
        "∃ desugars to Exists",
        __LINE__);

    // Multi-name binder: `∀ (x y : T). body` chains Pi.
    expectVerifies(R"(
module Test.forall_multi_binder

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

theorem swap_or_keep
        : ∀ (a b : Natural). Equality.{0}(Natural, a, b)
                              → Equality.{0}(Natural, a, b) :=
  function (a b : Natural)
           (h : Equality.{0}(Natural, a, b)) => h
)",
        "∀ with multiple names in one binder chains Pi",
        __LINE__);

    // Hammer constructor disjointness: `Not(C(...) = D(...))` for
    // distinct constructors of the same inductive elaborates to a
    // synthesized discriminator + Equality_recursor proof.
    expectVerifies(R"(
module Test.hammer_disjointness_successor_zero

inductive True : Proposition where
  | True.trivial : True

inductive False : Proposition where

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

theorem successor_disjoint_from_zero (n : Natural)
        : (Equality.{0}(Natural, successor(n), zero)) → False := ?
)",
        "hammer disjointness: successor(n) ≠ zero",
        __LINE__);

    // Symmetric direction: zero ≠ successor(n).
    expectVerifies(R"(
module Test.hammer_disjointness_zero_successor

inductive True : Proposition where
  | True.trivial : True

inductive False : Proposition where

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

theorem zero_disjoint_from_successor (n : Natural)
        : (Equality.{0}(Natural, zero, successor(n))) → False := ?
)",
        "hammer disjointness: zero ≠ successor(n)",
        __LINE__);

    // Two-constructor enum: distinct constructors are unequal.
    expectVerifies(R"(
module Test.hammer_disjointness_enum

inductive True : Proposition where
  | True.trivial : True

inductive False : Proposition where

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

inductive Color : Type(0) where
  | red    : Color
  | green  : Color
  | blue   : Color

theorem red_is_not_blue
        : (Equality.{0}(Color, red, blue)) → False := ?
)",
        "hammer disjointness: distinct nullary constructors",
        __LINE__);

    // Negative: same constructor on both sides should fall through.
    expectErrorContains(R"(
module Test.hammer_disjointness_same_constructor

inductive True : Proposition where
  | True.trivial : True

inductive False : Proposition where

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

theorem succ_eq_succ_not_disjoint
        : (Equality.{0}(Natural, successor(zero), successor(zero))) → False := ?
)",
        {"could not find a proof",
         "succ_eq_succ_not_disjoint"},
        "hammer rejects same-constructor disjointness",
        __LINE__);

    // calc in a pattern-match body verifies. (A recursive call inside
    // a calc step PROOF is exercised end-to-end by the rewrite of
    // Natural.add_commutative in library/Natural/arithmetic.math —
    // without the rewriter descending into SurfaceCalc that proof
    // wouldn't elaborate.)
    expectVerifies(R"(
module Test.calc_inside_pattern_match

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

theorem identity_reflexive
        : (n : Natural) → Equality.{0}(Natural, n, n)
  | zero => reflexivity.{0}(Natural, zero)
  | successor(predecessor) =>
      calc successor(predecessor)
         = successor(predecessor)
              by reflexivity.{0}(Natural, successor(predecessor))
)",
        "calc inside pattern-match body verifies",
        __LINE__);

    // calc block: ill-typed step proof reports the failing step.
    expectErrorContains(R"(
module Test.calc_bad_step

inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural → Natural

inductive Equality.{u} (A : Type(u)) (x : A) : A → Proposition where
  | reflexivity : Equality(A, x, x)

axiom step_ab : Equality.{0}(Natural, zero, successor(zero))

theorem mismatched
        : Equality.{0}(Natural, zero, successor(successor(zero))) :=
  calc zero
     = successor(zero)             by step_ab
     = successor(successor(zero))  by step_ab
)",
        {"calc step 2", "theorem 'mismatched'"},
        "calc surfaces step-level error attribution",
        __LINE__);
}

void runEndToEndPipelineTests() {
    std::cout << "--- end-to-end pipeline tests ---\n";

    auto expectFails = [](const std::string& source,
                          const char* description, int testLine) {
        bool threw = false;
        try { verifyMathSource(source); }
        catch (const LexError&)       { threw = true; }
        catch (const ParseError&)     { threw = true; }
        catch (const ElaborateError&) { threw = true; }
        catch (const TypeError&)      { threw = true; }
        if (threw) ++passed;
        else {
            ++failed;
            std::cerr << "FAIL (line " << testLine
                      << "): expected failure from " << description << "\n";
        }
    };

    // Smallest viable module: an axiom whose type is Type(0).
    {
        auto environment = verifyMathSource(R"(
module Test.basic
axiom Foo : Type(0)
)");
        EXPECT_TRUE(environment.lookup("Foo") != nullptr);
    }

    // An axiom referring to another axiom, plus a definition.
    {
        auto environment = verifyMathSource(R"(
module Test.references
axiom Foo : Type(0)
axiom bar : Foo
definition baz : Foo := bar
)");
        EXPECT_TRUE(environment.lookup("Foo") != nullptr);
        EXPECT_TRUE(environment.lookup("bar") != nullptr);
        EXPECT_TRUE(environment.lookup("baz") != nullptr);
    }

    // Reference to an undeclared identifier fails elaboration.
    expectFails(R"(
module Test.bad
axiom bar : Foo
)", "axiom referencing undeclared Foo", __LINE__);

    // A definition whose body's type doesn't match the declared type fails.
    expectFails(R"(
module Test.bad
axiom Foo : Type(0)
axiom Bar : Type(0)
axiom foo : Foo
definition broken : Bar := foo
)", "definition body type mismatch", __LINE__);

    // Inductive declaration with two nullary constructors.
    {
        auto environment = verifyMathSource(R"(
module Test.enums
inductive Color : Type(0) where
  | red : Color
  | green : Color
  | blue : Color
)");
        EXPECT_TRUE(environment.lookup("Color") != nullptr);
        EXPECT_TRUE(environment.lookup("red") != nullptr);
        EXPECT_TRUE(environment.lookup("blue") != nullptr);
        EXPECT_TRUE(environment.lookup("Color_recursor") != nullptr);
    }

    // Inductive Natural with one recursive constructor.
    {
        auto environment = verifyMathSource(R"(
module Test.naturals
inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural -> Natural

definition one : Natural := successor(zero)
definition two : Natural := successor(successor(zero))
)");
        EXPECT_TRUE(environment.lookup("Natural") != nullptr);
        EXPECT_TRUE(environment.lookup("zero") != nullptr);
        EXPECT_TRUE(environment.lookup("successor") != nullptr);
        EXPECT_TRUE(environment.lookup("Natural_recursor") != nullptr);
        EXPECT_TRUE(environment.lookup("one") != nullptr);
        EXPECT_TRUE(environment.lookup("two") != nullptr);
    }

    // Numeric literals desugar to successor(...(zero)) once Natural is in
    // scope.
    {
        auto environment = verifyMathSource(R"(
module Test.numerics
inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural -> Natural

definition three : Natural := 3
)");
        EXPECT_TRUE(environment.lookup("three") != nullptr);
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeConstant("three"),
            makeApplication(makeConstant("successor"),
                makeApplication(makeConstant("successor"),
                    makeApplication(makeConstant("successor"),
                        makeConstant("zero"))))));
    }

    // Pi types in declarations.
    {
        auto environment = verifyMathSource(R"(
module Test.functions
axiom Foo : Type(0)
axiom Bar : Type(0)
axiom kludge : Foo -> Bar
axiom kludgeBack : (foo : Foo) -> Bar
)");
        EXPECT_TRUE(environment.lookup("kludge") != nullptr);
        EXPECT_TRUE(environment.lookup("kludgeBack") != nullptr);
    }

    // Universe-polymorphic declarations.
    {
        auto environment = verifyMathSource(R"(
module Test.polymorphism
definition identity.{u} (A : Type(u)) (x : A) : A := x
)");
        EXPECT_TRUE(environment.lookup("identity") != nullptr);
    }

    // Universe-polymorphic inductive with parameters and indices.
    {
        auto environment = verifyMathSource(R"(
module Test.equality
inductive Equality.{u} (A : Type(u)) (x : A) : A -> Proposition where
  | reflexivity : Equality(A, x, x)
)");
        EXPECT_TRUE(environment.lookup("Equality") != nullptr);
        EXPECT_TRUE(environment.lookup("reflexivity") != nullptr);
        EXPECT_TRUE(environment.lookup("Equality_recursor") != nullptr);
    }

    // Lambda + application: identity function applied at Natural.
    {
        auto environment = verifyMathSource(R"(
module Test.lambda
inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural -> Natural

definition apply_zero (f : Natural -> Natural) : Natural := f(zero)
definition succ_zero : Natural := apply_zero(function (n : Natural) => successor(n))
)");
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeConstant("succ_zero"),
            makeApplication(makeConstant("successor"),
                            makeConstant("zero"))));
    }

    // Let expressions.
    {
        auto environment = verifyMathSource(R"(
module Test.lets
inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural -> Natural

definition double_successor (n : Natural) : Natural :=
  let once : Natural := successor(n) in
  successor(once)
)");
        EXPECT_TRUE(environment.lookup("double_successor") != nullptr);
    }

    // Pattern-matching definition: Natural.add.
    {
        auto environment = verifyMathSource(R"(
module Test.pattern_add
inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural -> Natural

definition Natural.add : Natural -> Natural -> Natural
  | zero,         m => m
  | successor(k), m => successor(Natural.add(k, m))
)");
        EXPECT_TRUE(environment.lookup("Natural.add") != nullptr);
        // Check definitional behaviour: add(zero, m) reduces to m, and
        // add(successor(zero), zero) reduces to successor(zero).
        auto zero = makeConstant("zero");
        auto successorOfZero = makeApplication(makeConstant("successor"),
                                                zero);
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeApplication(
                makeApplication(makeConstant("Natural.add"), zero),
                successorOfZero),
            successorOfZero));
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeApplication(
                makeApplication(makeConstant("Natural.add"), successorOfZero),
                zero),
            successorOfZero));
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeApplication(
                makeApplication(makeConstant("Natural.add"), successorOfZero),
                successorOfZero),
            makeApplication(makeConstant("successor"), successorOfZero)));
    }

    // Pattern-matching with a non-recursive function (Boolean.not).
    {
        auto environment = verifyMathSource(R"(
module Test.pattern_not
inductive Boolean : Type(0) where
  | true : Boolean
  | false : Boolean

definition Boolean.not : Boolean -> Boolean
  | true  => false
  | false => true
)");
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeApplication(makeConstant("Boolean.not"),
                            makeConstant("true")),
            makeConstant("false")));
        EXPECT_TRUE(isDefinitionallyEqual(
            environment, {},
            makeApplication(makeConstant("Boolean.not"),
                            makeApplication(makeConstant("Boolean.not"),
                                            makeConstant("true"))),
            makeConstant("true")));
    }

    // Pattern-matching with recursive proof: Natural.add_zero.
    {
        auto environment = verifyMathSource(R"(
module Test.add_zero_proof
inductive Natural : Type(0) where
  | zero : Natural
  | successor : Natural -> Natural

definition Natural.add : Natural -> Natural -> Natural
  | zero,         m => m
  | successor(k), m => successor(Natural.add(k, m))

inductive Equality.{u} (A : Type(u)) (x : A) : A -> Proposition where
  | reflexivity : Equality(A, x, x)

axiom Equality.congruence.{u, v}
  : (A : Type(u)) -> (B : Type(v)) -> (f : A -> B)
    -> (x y : A) -> Equality.{u}(A, x, y) -> Equality.{v}(B, f(x), f(y))

theorem Natural.add_zero : (a : Natural) -> Equality.{0}(Natural, Natural.add(a, zero), a)
  | zero         => reflexivity.{0}(Natural, zero)
  | successor(k) => Equality.congruence.{0, 0}(
                       Natural, Natural, successor,
                       Natural.add(k, zero), k,
                       Natural.add_zero(k))
)");
        EXPECT_TRUE(environment.lookup("Natural.add_zero") != nullptr);
    }
}

// ----------------------------------------------------------------------------
// Integration test: a second inductive (Boolean) and a function defined via
// its recursor, exercised alongside the existing Natural / add.
// ----------------------------------------------------------------------------

void runIntegrationTests() {
    std::cout << "--- integration tests ---\n";

    Environment env = buildArithmeticEnvironment();

    // Boolean as a second inductive type.
    addInductive(env, "Boolean", makeType(0), {
        {"true",  makeConstant("Boolean")},
        {"false", makeConstant("Boolean")},
    });

    // Negation defined via the Boolean recursor.
    //   not b = Boolean_recursor (λ_. Boolean) false true b
    addDefinition(env, "not",
        makePi("_", makeConstant("Boolean"), makeConstant("Boolean")),
        makeLambda("b", makeConstant("Boolean"),
            makeApplication(
                makeApplication(
                    makeApplication(
                        makeApplication(
                            makeConstant("Boolean_recursor", {makeLevelConst(1)}),
                            makeLambda("_", makeConstant("Boolean"),
                                        makeConstant("Boolean"))),
                        makeConstant("false")),
                    makeConstant("true")),
                makeBoundVariable(0))));

    // not true ≡ false; not false ≡ true; not (not b) is η-equal to b after
    // we further substitute, but it doesn't reduce without knowing b — so we
    // only check the concrete cases.
    EXPECT_TRUE(isDefinitionallyEqual(env, {},
        makeApplication(makeConstant("not"), makeConstant("true")),
        makeConstant("false")));
    EXPECT_TRUE(isDefinitionallyEqual(env, {},
        makeApplication(makeConstant("not"), makeConstant("false")),
        makeConstant("true")));
    EXPECT_TRUE(isDefinitionallyEqual(env, {},
        makeApplication(makeConstant("not"),
                        makeApplication(makeConstant("not"),
                                        makeConstant("true"))),
        makeConstant("true")));

    // Multiplication on Natural, defined via the recursor and add. The
    // motive is a constant function — we use a Natural → Natural to keep
    // things in Type 0.
    //   multiply n m = Natural_recursor (λ_. Natural → Natural)
    //                                    (λ_. zero)
    //                                    (λk recK m. add m (recK m))
    //                                    n m
    {
        auto naturalToNatural = makePi(
            "_", makeConstant("Natural"), makeConstant("Natural"));
        auto motive = makeLambda("_", makeConstant("Natural"),
                                  naturalToNatural);
        // case_zero: multiply zero m = zero — a constant zero function.
        auto caseZero = makeLambda("_m", makeConstant("Natural"),
                                    makeConstant("zero"));
        // case_successor k recK m = add m (recK m)
        auto caseSuccessor = makeLambda("k", makeConstant("Natural"),
            makeLambda("recK", naturalToNatural,
              makeLambda("m", makeConstant("Natural"),
                makeApplication(
                    makeApplication(makeConstant("add"),
                                    makeBoundVariable(0) /* m */),
                    makeApplication(makeBoundVariable(1) /* recK */,
                                    makeBoundVariable(0) /* m */)))));

        auto multiplyBody = makeLambda("n", makeConstant("Natural"),
            makeLambda("m", makeConstant("Natural"),
              makeApplication(
                makeApplication(
                  makeApplication(
                    makeApplication(
                      makeApplication(makeConstant("Natural_recursor", {makeLevelConst(1)}),
                                      motive),
                      caseZero),
                    caseSuccessor),
                  makeBoundVariable(1) /* n */),
                makeBoundVariable(0) /* m */)));

        auto multiplyType = makePi("n", makeConstant("Natural"),
                                makePi("m", makeConstant("Natural"),
                                  makeConstant("Natural")));
        addDefinition(env, "multiply", multiplyType, multiplyBody);

        // multiply two three  ≡  six.
        auto buildN = [](int n) {
            ExpressionPointer result = makeConstant("zero");
            for (int i = 0; i < n; ++i) {
                result = makeApplication(makeConstant("successor"), result);
            }
            return result;
        };
        auto two   = buildN(2);
        auto three = buildN(3);
        auto six   = buildN(6);
        auto product = makeApplication(
            makeApplication(makeConstant("multiply"), two),
            three);
        EXPECT_TRUE(isDefinitionallyEqual(env, {}, product, six));

        // multiply zero n ≡ zero for any concrete n. Whatever n is, the
        // motive's zero case takes over.
        auto fiveTimesZero = makeApplication(
            makeApplication(makeConstant("multiply"),
                            makeConstant("zero")),
            buildN(5));
        EXPECT_TRUE(isDefinitionallyEqual(env, {},
            fiveTimesZero, makeConstant("zero")));
    }
}

int verifyFiles(const std::vector<std::string>& filenames) {
    Environment environment;
    std::vector<std::string> importedModules;
    for (const auto& filename : filenames) {
        std::ifstream input(filename);
        if (!input.is_open()) {
            std::cerr << "cannot open file: " << filename << "\n";
            return 1;
        }
        std::stringstream buffer;
        buffer << input.rdbuf();
        std::string source = buffer.str();
        std::string moduleName;
        size_t declarationCountBefore = environment.declarations.size();
        try {
            auto tokens = lex(source);
            auto module = parseModule(tokens);
            moduleName = module.moduleName;
            elaborateModule(module, environment, importedModules);
        } catch (const LexError& error) {
            std::cerr << "lex error in " << filename << ": "
                      << error.what() << "\n";
            return 1;
        } catch (const ParseError& error) {
            std::cerr << "parse error in " << filename << ": "
                      << error.what() << "\n";
            return 1;
        } catch (const ElaborateError& error) {
            std::cerr << "elaborate error in " << filename << ": "
                      << error.what() << "\n";
            return 1;
        } catch (const TypeError& error) {
            std::cerr << "type error in " << filename << ": "
                      << error.what() << "\n";
            return 1;
        } catch (const std::exception& error) {
            std::cerr << "error in " << filename << ": "
                      << error.what() << "\n";
            return 1;
        }
        size_t added =
            environment.declarations.size() - declarationCountBefore;
        std::cout << "verified " << filename << " (module " << moduleName
                  << ", " << added << " new declarations)\n";
    }
    return 0;
}

} // namespace

int main(int argc, char* argv[]) {
    if (argc >= 3 && std::string(argv[1]) == "verify") {
        std::vector<std::string> filenames;
        for (int i = 2; i < argc; ++i) filenames.push_back(argv[i]);
        return verifyFiles(filenames);
    }
    if (argc >= 2 && (std::string(argv[1]) == "-h"
                      || std::string(argv[1]) == "--help")) {
        std::cout << "Usage:\n"
                  << "  kernel              run the test suite\n"
                  << "  kernel verify FILE [FILE ...]\n"
                  << "                      verify one or more .math files\n"
                  << "                      (provide dependencies first)\n";
        return 0;
    }
    std::cout << "=== worked examples (empty environment) ===\n\n";

    Environment empty;

    runExample(empty, "Type 0", makeType(0));

    runExample(empty, "identity on Type 0:  λ(x : Type 0). x",
               makeLambda("x", makeType(0), makeBoundVariable(0)));

    runExample(empty, "polymorphic identity:  λ(A : Type 0). λ(x : A). x",
               makeLambda("A", makeType(0),
                 makeLambda("x", makeBoundVariable(0), makeBoundVariable(0))));

    runExample(empty, "K combinator:  λA. λB. λ(x:A). λ(y:B). x",
               makeLambda("A", makeType(0),
                 makeLambda("B", makeType(0),
                   makeLambda("x", makeBoundVariable(1),
                     makeLambda("y", makeBoundVariable(1),
                       makeBoundVariable(1))))));

    runExample(empty,
               "(λ(A:Type 1). λ(x:A). x) applied to (Type 0)",
               makeApplication(
                   makeLambda("A", makeType(1),
                     makeLambda("x", makeBoundVariable(0),
                                makeBoundVariable(0))),
                   makeType(0)));

    std::cout << "=== worked examples (with Natural, Equality, reflexivity "
                 "axioms and definitions one := successor zero, "
                 "two := successor one) ===\n\n";

    Environment arithmetic = buildArithmeticEnvironment();

    runExample(arithmetic, "zero", makeConstant("zero"));
    runExample(arithmetic, "successor", makeConstant("successor"));
    runExample(arithmetic, "successor zero",
               makeApplication(makeConstant("successor"), makeConstant("zero")));
    runExample(arithmetic, "one (a definition)", makeConstant("one"));
    runExample(arithmetic, "two (a definition)", makeConstant("two"));

    runExample(arithmetic,
               "reflexivity Natural zero  -- a proof that zero = zero",
               makeApplication(
                   makeApplication(makeConstant("reflexivity", {makeLevelConst(0)}),
                                   makeConstant("Natural")),
                   makeConstant("zero")));

    runExample(arithmetic,
               "reflexivity Natural  -- partially applied; codomain depends on A",
               makeApplication(makeConstant("reflexivity", {makeLevelConst(0)}),
                               makeConstant("Natural")));

    runExample(arithmetic,
               "let n : Natural := zero in successor n",
               makeLet("n", makeConstant("Natural"), makeConstant("zero"),
                       makeApplication(makeConstant("successor"),
                                       makeBoundVariable(0))));

    runExample(arithmetic,
               "λ(n : Natural). successor n   (η-equal to successor itself)",
               makeLambda("n", makeConstant("Natural"),
                          makeApplication(makeConstant("successor"),
                                          makeBoundVariable(0))));

    runExample(arithmetic, "Proposition", makeProposition());
    runExample(arithmetic, "Equality (now lands in Proposition)",
               makeConstant("Equality", {makeLevelConst(0)}));
    runExample(arithmetic,
               "Π(P : Proposition). P "
               "  (impredicative quantifier; lives in Proposition)",
               makePi("P", makeProposition(), makeBoundVariable(0)));

    runExample(arithmetic, "Natural_recursor  (auto-generated)",
               makeConstant("Natural_recursor", {makeLevelConst(1)}));

    runExample(arithmetic, "add  (defined via Natural_recursor)",
               makeConstant("add"));

    runExample(arithmetic,
               "add (successor zero) (successor zero)  -- exercises ι",
               makeApplication(
                   makeApplication(
                       makeConstant("add"),
                       makeApplication(makeConstant("successor"),
                                       makeConstant("zero"))),
                   makeApplication(makeConstant("successor"),
                                   makeConstant("zero"))));

    runExample(arithmetic,
               "Equality (universe-polymorphic)",
               makeConstant("Equality", {makeLevelParam("u")}));

    runExample(arithmetic,
               "reflexivity.{1} (Type 0) Natural  -- proof at a higher universe",
               makeApplication(
                   makeApplication(
                       makeConstant("reflexivity", {makeLevelConst(1)}),
                       makeType(0)),
                   makeConstant("Natural")));

    runCoreTests();
    runEnvironmentTests(arithmetic);
    runLevelArithmeticTests();
    runDeBruijnOperationTests();
    runReductionTests(arithmetic);
    runInferTypeErrorTests(arithmetic);
    runDeclarationErrorTests(arithmetic);
    runUniversePolymorphismTests(arithmetic);
    runPrintingTests(arithmetic);
    runHardeningTests(arithmetic);
    runStrictPositivityTests();
    runPolymorphicRecursorTests(arithmetic);
    runRestrictedEliminationTests();
    runProofIrrelevanceAuditTests(arithmetic);
    runInputValidationTests();
    runInvariantCheckedTests(arithmetic);
    runPropertyTests(arithmetic);
    runNaturalNumberGameProofs();
    runInductiveLibraryProofs();
    runLexerTests();
    runParserTests();
    runEndToEndPipelineTests();
    runErrorMessageTests();
    runIntegrationTests();

    std::cout << "\n" << passed << " passed, " << failed << " failed\n";
    return failed == 0 ? 0 : 1;
}
