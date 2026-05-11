#include "expression.hpp"
#include "kernel.hpp"
#include "printer.hpp"

#include <iostream>
#include <random>
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

    // Equality.{u} : Π(A : Type u). Π(x : A). Π(y : A). Prop
    // Universe-polymorphic in u, so the same Equality works at any
    // universe level.
    addAxiom(environment, "Equality", {"u"},
        makePi("A", makeType(makeLevelParam("u")),
          makePi("x", makeBoundVariable(0),
            makePi("y", makeBoundVariable(1),
              makeProp()))));

    // reflexivity.{u} : Π(A : Type u). Π(x : A). Equality.{u} A x x
    addAxiom(environment, "reflexivity", {"u"},
        makePi("A", makeType(makeLevelParam("u")),
          makePi("x", makeBoundVariable(0),
            makeApplication(
              makeApplication(
                makeApplication(
                    makeConstant("Equality", {makeLevelParam("u")}),
                    makeBoundVariable(1)),
                makeBoundVariable(0)),
              makeBoundVariable(0)))));

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
    //               (λk recK m. successor (recK m))          -- case_succ
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

    // Prop and impredicativity: Equality lives in Prop. Reflexivity's full
    // type therefore also lives in Prop:
    //   reflexivity : ∀(A : Type 0). ∀(x : A). Equality A x x   : Prop
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

    // Π(P : Prop). P — quantifying over all propositions, itself a Prop.
    // This is the impredicative encoding of False (and of any quantifier
    // that ranges over Prop). Impredicativity fires here because the
    // codomain P has type Prop (universe 0), so imax(_, 0) = 0.
    {
        auto term = makePi("P", makeProp(), makeBoundVariable(0));
        auto kind = weakHeadNormalForm(environment,
                                       inferType(environment, {}, term));
        auto* sort = std::get_if<Sort>(&kind->node);
        EXPECT_TRUE(sort != nullptr &&
                    levelAsConstant(sort->level) &&
                    *levelAsConstant(sort->level) == 0);  // Prop
    }

    // Π(_ : Prop). Prop is NOT in Prop — its codomain is the *type* Prop
    // (which lives in Type 0), not a proposition. Result is Type 0.
    {
        auto term = makePi("_", makeProp(), makeProp());
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
    // in Prop. Two distinct free Naturals are not definitionally equal.
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
        // Equality.{0} Natural zero zero  : Prop
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

        // Equality.{1} (Type 0) Natural Natural  : Prop
        // (Natural : Type 0, so we're stating that the type Natural equals
        // itself.) Lives in Prop just like Equality.{0} — propositions are
        // always in Prop regardless of u.
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

    // makeLevelSucc folds over concrete levels.
    EXPECT_TRUE(*levelAsConstant(makeLevelSucc(makeLevelConst(0))) == 1);
    EXPECT_TRUE(*levelAsConstant(makeLevelSucc(makeLevelConst(7))) == 8);

    // makeLevelSucc stays symbolic for parameters.
    {
        auto succU = makeLevelSucc(makeLevelParam("u"));
        EXPECT_FALSE(levelAsConstant(succU).has_value());
        EXPECT_LEVEL_PRINTS(succU, "u+1");
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

    // makeLevelIMax: codomain succ(_) is never 0, so becomes max.
    {
        auto u = makeLevelParam("u");
        auto imaxResult = makeLevelIMax(u, makeLevelSucc(makeLevelParam("v")));
        // Should be max(u, succ(v)) — folded.
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

    // levelLessOrEqual: succ(a) <= succ(b) iff a <= b.
    EXPECT_TRUE(levelLessOrEqual(
        makeLevelSucc(makeLevelConst(2)), makeLevelSucc(makeLevelConst(3))));
    EXPECT_FALSE(levelLessOrEqual(
        makeLevelSucc(makeLevelConst(3)), makeLevelSucc(makeLevelConst(2))));

    // Substitution: replacing the param appears throughout, others are
    // untouched.
    {
        auto level = makeLevelMax(
            makeLevelParam("u"),
            makeLevelSucc(makeLevelParam("v")));
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
    //   shift(Π(_ : Nat). Bound(1), 1, 0)
    //   The Bound(1) refers OUTSIDE the Pi. Inside the codomain, cutoff is 1.
    //   Bound(1) >= 1, so it shifts to Bound(2).
    {
        auto term = makePi("_", makeConstant("Nat"), makeBoundVariable(1));
        auto shifted = shift(term, 1, 0);
        auto* pi = std::get_if<Pi>(&shifted->node);
        EXPECT_TRUE(pi);
        auto* inner = std::get_if<BoundVariable>(&pi->codomain->node);
        EXPECT_TRUE(inner && inner->deBruijnIndex == 2);
    }

    // shift under a Pi: Bound(0) inside the codomain references the binder
    // itself (inside cutoff after descent), so it stays Bound(0).
    {
        auto term = makePi("_", makeConstant("Nat"), makeBoundVariable(0));
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
        Context context = {{"v0", makeConstant("Nat0")}};
        // We need Nat0 to exist as a type so context entries type-check
        // when the kernel infers types for proof irrelevance.
        Environment localEnvironment;
        addAxiom(localEnvironment, "Nat0", makeType(0));
        auto leftTerm = makePi("y", makeConstant("Nat0"),
                                makeFreeVariable("v0"));
        auto rightTerm = makePi("y", makeConstant("Nat0"),
                                 makeFreeVariable("v0"));
        EXPECT_TRUE(isDefinitionallyEqual(localEnvironment, context,
                                          leftTerm, rightTerm));
        // And two distinct user names "v0" and "motive" don't get confused.
        Context context2 = {{"v0", makeConstant("Nat0")},
                            {"motive", makeConstant("Nat0")}};
        auto leftDifferent = makePi("y", makeConstant("Nat0"),
                                     makeFreeVariable("v0"));
        auto rightDifferent = makePi("y", makeConstant("Nat0"),
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
        // Natural_recursor (λ_. Nat) case_zero case_succ zero ↦ case_zero
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
    //   The fully reduced result has head = case_succ applied to v and to
    //   a recursive Natural_recursor call.
    {
        auto motive = makeLambda("_", makeConstant("Natural"),
                                  makeConstant("Natural"));
        auto caseZero    = makeConstant("zero");
        // case_succ k recK = k  (just returns k, ignoring the recursive call).
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
        // case_succ k _ = k, applied to zero, gives zero.
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
    //   λ(x : Nat). ((λy. y) x)  has a β-redex inside its body, but whnf
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
        EXPECT_THROW(addInductive(local, "AnotherNat", makeType(0),
                                  {{"zero", makeConstant("AnotherNat")}}));
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

    EXPECT_PRINTS(makeProp(), "Prop");
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
// the typical case (computing Naturals from Naturals), or Prop to prove
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

    // Instantiate at motive level 0 (Prop motive). The recursor's motive
    // type becomes Π(_ : Natural). Prop. Calls to it eliminate Natural
    // into propositions — i.e. proofs by induction.
    {
        auto recursorPropMotive =
            makeConstant("Natural_recursor", {makeLevelConst(0)});
        auto inferredType = inferType(arithmetic, {}, recursorPropMotive);
        // Pretty-print to confirm motive is Π(_ : Natural). Prop.
        // (Concretely: the type starts with Π(motive : Π(_ : Natural). Prop).)
        auto whnfType = weakHeadNormalForm(arithmetic, inferredType);
        auto* pi = std::get_if<Pi>(&whnfType->node);
        EXPECT_TRUE(pi);
        if (pi) {
            // pi->domain is the motive's TYPE, which should be
            // Π(_ : Natural). Prop.
            auto* motivePi = std::get_if<Pi>(&pi->domain->node);
            EXPECT_TRUE(motivePi);
            if (motivePi) {
                auto* codomainSort =
                    std::get_if<Sort>(&motivePi->codomain->node);
                EXPECT_TRUE(
                    codomainSort &&
                    levelAsConstant(codomainSort->level) &&
                    *levelAsConstant(codomainSort->level) == 0);  // Prop
            }
        }
    }

    // Prove a proposition by induction: ∀(n : Natural). Equality.{0}
    //                                      Natural n n.
    // The proof is reflexivity applied to each constructor case, and
    // Natural_recursor at motive level 0 (Prop) ties them together.
    //
    //   inductionProof : Π(n : Natural). Equality Natural n n
    //   inductionProof =
    //     Natural_recursor.{0}
    //       (λn. Equality Natural n n)              -- motive : Natural → Prop
    //       (reflexivity Natural zero)              -- case_zero
    //       (λk recK. reflexivity Natural (successor k))  -- case_succ
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
// Restricted-elimination tests for Prop inductives. A non-empty Prop
// inductive must not allow its proofs to be eliminated into Type — that
// would let users extract data from a proof and break proof irrelevance.
// The kernel forces the motive's universe to Prop for such recursors.
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
// Proof irrelevance × impredicativity audit. These tests pin down what the
// kernel's proof-irrelevance branch does and doesn't equate, especially
// around the impredicative Pi rule. The principle: two terms are
// definitionally equal by proof irrelevance iff their type lives in Prop.
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
        auto leftProp = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeConstant("zero"));
        auto rightProp = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality", {makeLevelConst(0)}),
                                makeConstant("Natural")),
                makeConstant("zero")),
            makeApplication(makeConstant("successor"), makeConstant("zero")));
        Context ctx = {{"p", leftProp}, {"q", rightProp}};
        EXPECT_FALSE(isDefinitionallyEqual(arithmetic, ctx,
                                           makeFreeVariable("p"),
                                           makeFreeVariable("q")));
    }

    // A term whose type lives in Type (not Prop) is NOT equated by proof
    // irrelevance, even if both sides are "predicates".
    // Two distinct predicates  λ(n : Natural). Equality Natural n n  and
    // λ(n : Natural). Equality Natural zero zero  have type
    // Π(_ : Natural). Prop, whose universe is imax(1, 1) = Type 0. Not in
    // Prop. So they aren't equated.
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

    // A function whose codomain is a proof type IS in Prop (impredicativity
    // collapses the Pi to Prop), so two such functions are equal by proof
    // irrelevance. The functions are "extensionally equal" because they
    // return interchangeable proofs.
    //
    //   Π(x : Natural). Equality Natural zero zero  has universe
    //     imax(1, 0) = 0 = Prop.
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
        // n and b are Naturals (Type 0). Not in Prop. Distinct free vars.
        EXPECT_FALSE(isDefinitionallyEqual(arithmetic, ctx,
                                           makeFreeVariable("n"),
                                           makeFreeVariable("b")));
    }

    // η + proof irrelevance: a Lambda that wraps a proof-returning function
    // is equal to the bare function. Both have type in Prop (codomain is
    // Equality, which is in Prop).
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

    // A Prop inductive with two constructors: a disjunction over a fixed
    // pair of propositions. Its recursor must NOT take a motive-universe
    // parameter (motive is forced to Prop).
    {
        Environment env;
        addAxiom(env, "P", makeProp());
        addAxiom(env, "Q", makeProp());
        addInductive(env, "Or_PQ", makeProp(), {
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
        // The motive's codomain in the recursor type is Prop, not a
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

    // An empty Prop inductive (zero constructors, like False) DOES allow
    // large elimination — there's no proof to extract from, so any motive
    // universe is sound. The recursor takes a motive-level universe arg.
    {
        Environment env;
        addInductive(env, "False", makeProp(), {});
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
                      makeType(makeLevelSucc(makeLevelParam("u"))),
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
// others need induction via Natural_recursor.{0} (a Prop-valued motive).
// Where our axiomatic Equality lacks an elimination principle, we add a
// congruence-of-successor axiom — what an inductive Equality with refl as
// its constructor would give us for free if we had parameters/indices on
// inductives.
// ----------------------------------------------------------------------------

void runNaturalNumberGameProofs() {
    std::cout << "--- natural number game proofs ---\n";

    Environment env = buildArithmeticEnvironment();

    // ------------------------------------------------------------------
    // The equality we'll use throughout these proofs is an INDUCTIVE
    // equality — no longer an axiom. Its recursor (the J principle)
    // gives us substitution / Leibniz reasoning for free, so we won't
    // need a separate successorCongruence axiom.
    //
    //   inductive Equality₁.{u} (A : Type u) (x : A) : A → Prop
    //     | refl₁ : Equality₁ A x x
    //
    // We use the name Equality₁ (and refl₁) inside this function to
    // avoid clashing with the axiomatic Equality / reflexivity in
    // buildArithmeticEnvironment(), which other tests depend on.
    // ------------------------------------------------------------------
    addInductive(env, "Equality1", {"u"},
        makePi("A", makeType(makeLevelParam("u")),
            makePi("x", makeBoundVariable(0),
                makePi("y", makeBoundVariable(1), makeProp()))),
        /*numParameters=*/ 2,
        {{
            "refl1",
            makePi("A", makeType(makeLevelParam("u")),
                makePi("x", makeBoundVariable(0),
                    makeApplication(
                        makeApplication(
                            makeApplication(
                                makeConstant("Equality1",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(1)),
                            makeBoundVariable(0)),
                        makeBoundVariable(0))))
        }});

    // Convenience helpers. All proofs below use the inductive equality.
    auto Nat = []() { return makeConstant("Natural"); };
    auto zero = []() { return makeConstant("zero"); };
    auto succ = [](ExpressionPointer n) {
        return makeApplication(makeConstant("successor"), n);
    };
    auto plus = [](ExpressionPointer n, ExpressionPointer m) {
        return makeApplication(makeApplication(makeConstant("add"), n), m);
    };
    auto eq = [](ExpressionPointer a, ExpressionPointer x,
                 ExpressionPointer y) {
        return makeApplication(
            makeApplication(
                makeApplication(
                    makeConstant("Equality1", {makeLevelConst(0)}),
                    a),
                x),
            y);
    };
    auto refl = [](ExpressionPointer a, ExpressionPointer x) {
        return makeApplication(
            makeApplication(
                makeConstant("refl1", {makeLevelConst(0)}),
                a),
            x);
    };

    // ------------------------------------------------------------------
    // Eq.symm — universe-polymorphic.
    //   Π(A : Type u). Π(x y : A). Equality1 A x y → Equality1 A y x.
    // Derived from the recursor. Recurses on the input equality with
    // motive  λ y' _. Equality1 A y' x.  Base case y'=x needs x = x,
    // i.e. refl1 A x.
    // ------------------------------------------------------------------
    {
        // Proof body lives inside  λ A. λ x. λ y. λ eq. [body].
        // From body's perspective: eq=0, y=1, x=2, A=3.
        // Motive is  λ y'. λ _eq'. Equality1.{u} A y' x.
        //   At motive's _eq' body level: _eq'=0, y'=1, eq=2, y=3, x=4, A=5.
        //   At _eq' TYPE position (inside y' but outside _eq'):
        //                          y'=0, eq=1, y=2, x=3, A=4.
        auto motive = makeLambda("y'", makeBoundVariable(3) /* A */,
            makeLambda("_eq'",
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality1", {makeLevelParam("u")}),
                    makeBoundVariable(4) /* A */),
                    makeBoundVariable(3) /* x */),
                    makeBoundVariable(0) /* y' */),
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality1", {makeLevelParam("u")}),
                    makeBoundVariable(5) /* A */),
                    makeBoundVariable(1) /* y' */),
                    makeBoundVariable(4) /* x */)));

        auto caseRefl = makeApplication(
            makeApplication(
                makeConstant("refl1", {makeLevelParam("u")}),
                makeBoundVariable(3) /* A */),
            makeBoundVariable(2) /* x */);

        auto proof = makeLambda("A", makeType(makeLevelParam("u")),
            makeLambda("x", makeBoundVariable(0) /* A */,
                makeLambda("y", makeBoundVariable(1) /* A */,
                    makeLambda("_eq",
                        makeApplication(makeApplication(makeApplication(
                            makeConstant("Equality1", {makeLevelParam("u")}),
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
                                                    "Equality1_recursor",
                                                    {makeLevelParam("u"),
                                                     makeLevelConst(0)}),
                                                makeBoundVariable(3) /* A */),
                                            makeBoundVariable(2) /* x */),
                                        motive),
                                    caseRefl),
                                makeBoundVariable(1) /* y */),
                            makeBoundVariable(0) /* eq */)))));

        auto theoremType =
            makePi("A", makeType(makeLevelParam("u")),
                makePi("x", makeBoundVariable(0),
                    makePi("y", makeBoundVariable(1),
                        makePi("_eq",
                            makeApplication(makeApplication(makeApplication(
                                makeConstant("Equality1",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(2)),
                                makeBoundVariable(1)),
                                makeBoundVariable(0)),
                            makeApplication(makeApplication(makeApplication(
                                makeConstant("Equality1",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(3)),
                                makeBoundVariable(1)),
                                makeBoundVariable(2))))));

        addDefinition(env, "Eq.symm", {"u"}, theoremType, proof);
        std::cout << "  Eq.symm    ⊨  Π(A : Type u). Π(x y : A). x = y → "
                     "y = x   (J, universe-polymorphic)\n";
    }

    // ------------------------------------------------------------------
    // Eq.trans — universe-polymorphic.
    //   Π(A : Type u). Π(x y z : A). x = y → y = z → x = z.
    // Recurse on the SECOND equality with motive  λ z' _. Equality1 A x z'.
    // Base case z'=y needs x = y, supplied directly by the first equality.
    // ------------------------------------------------------------------
    {
        // Proof body lives inside  λ A x y z eq_xy eq_yz. From body:
        //   eq_yz=0, eq_xy=1, z=2, y=3, x=4, A=5.
        // Motive  λ z'. λ _eq'. Equality1.{u} A x z'.
        //   _eq' body: _eq'=0, z'=1, eq_yz=2, eq_xy=3, z=4, y=5, x=6, A=7.
        //   _eq' TYPE (inside z' but outside _eq'): z'=0, eq_yz=1, eq_xy=2,
        //     z=3, y=4, x=5, A=6.
        auto motive = makeLambda("z'", makeBoundVariable(5) /* A */,
            makeLambda("_eq'",
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality1", {makeLevelParam("u")}),
                    makeBoundVariable(6) /* A */),
                    makeBoundVariable(4) /* y */),
                    makeBoundVariable(0) /* z' */),
                makeApplication(makeApplication(makeApplication(
                    makeConstant("Equality1", {makeLevelParam("u")}),
                    makeBoundVariable(7) /* A */),
                    makeBoundVariable(6) /* x */),
                    makeBoundVariable(1) /* z' */)));

        // caseRefl at body level (eq_yz=0, eq_xy=1, z=2, y=3, x=4, A=5):
        // we need Equality1.{u} A x y, which is eq_xy = Bound 1.
        auto caseRefl = makeBoundVariable(1) /* eq_xy */;

        auto proof = makeLambda("A", makeType(makeLevelParam("u")),
            makeLambda("x", makeBoundVariable(0),
                makeLambda("y", makeBoundVariable(1),
                    makeLambda("z", makeBoundVariable(2),
                        makeLambda("eq_xy",
                            makeApplication(makeApplication(makeApplication(
                                makeConstant("Equality1",
                                              {makeLevelParam("u")}),
                                makeBoundVariable(3) /* A */),
                                makeBoundVariable(2) /* x */),
                                makeBoundVariable(1) /* y */),
                            makeLambda("eq_yz",
                                // At this position (inside A,x,y,z,eq_xy
                                // outside eq_yz): eq_xy=0, z=1, y=2, x=3,
                                // A=4. So y is Bound(2), not Bound(3).
                                makeApplication(makeApplication(makeApplication(
                                    makeConstant("Equality1",
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
                                                            "Equality1_recursor",
                                                            {makeLevelParam("u"),
                                                             makeLevelConst(0)}),
                                                        makeBoundVariable(5) /* A */),
                                                    makeBoundVariable(3) /* y */),
                                                motive),
                                            caseRefl),
                                        makeBoundVariable(2) /* z */),
                                    makeBoundVariable(0) /* eq_yz */)))))));

        auto theoremType =
            makePi("A", makeType(makeLevelParam("u")),
                makePi("x", makeBoundVariable(0),
                    makePi("y", makeBoundVariable(1),
                        makePi("z", makeBoundVariable(2),
                            makePi("eq_xy",
                                makeApplication(makeApplication(makeApplication(
                                    makeConstant("Equality1",
                                                  {makeLevelParam("u")}),
                                    makeBoundVariable(3)),
                                    makeBoundVariable(2)),
                                    makeBoundVariable(1)),
                                makePi("eq_yz",
                                    makeApplication(makeApplication(makeApplication(
                                        makeConstant("Equality1",
                                                      {makeLevelParam("u")}),
                                        makeBoundVariable(4) /* A */),
                                        makeBoundVariable(2) /* y */),
                                        makeBoundVariable(1) /* z */),
                                    makeApplication(makeApplication(makeApplication(
                                        makeConstant("Equality1",
                                                      {makeLevelParam("u")}),
                                        makeBoundVariable(5) /* A */),
                                        makeBoundVariable(4) /* x */),
                                        makeBoundVariable(2) /* z */)))))));

        addDefinition(env, "Eq.trans", {"u"}, theoremType, proof);
        std::cout << "  Eq.trans   ⊨  Π(A : Type u). Π(x y z : A). "
                     "x = y → y = z → x = z   (J, universe-polymorphic)\n";
    }

    // ------------------------------------------------------------------
    // Polymorphic demo: Equality1 instantiated at universe 1 (Type 0 as
    // the value-level type). naturalEqualsItself : Equality1.{1} (Type 0)
    // Natural Natural. Proof: refl1.{1} (Type 0) Natural. The same
    // declarations work at higher universes.
    // ------------------------------------------------------------------
    addDefinition(env, "naturalEqualsItself",
        makeApplication(makeApplication(makeApplication(
            makeConstant("Equality1", {makeLevelConst(1)}),
            makeType(0)),
            makeConstant("Natural")),
            makeConstant("Natural")),
        makeApplication(
            makeApplication(makeConstant("refl1", {makeLevelConst(1)}),
                            makeType(0)),
            makeConstant("Natural")));
    std::cout << "  naturalEqualsItself  ⊨  Equality1.{1} (Type 0) "
                 "Natural Natural\n";

    // ------------------------------------------------------------------
    // Derived: succCong : Π(x y : Natural). x = y → succ x = succ y.
    //
    // Eliminate the equality using Equality1's recursor. The motive
    //   λ y' _eq'. Equality1 Natural (succ x) (succ y')
    // turns the goal "succ x = succ y" into the special case where
    // y' = x (so we need succ x = succ x, immediate from refl).
    // ------------------------------------------------------------------
    {
        // Proof body lives inside  λ x. λ y. λ eq. [body]. From body:
        //   eq=0, y=1, x=2.
        // Motive constructed inside body — inside its inner _eq' body the
        // binders are _eq'=0, y'=1, eq=2, y=3, x=4. The _eq's TYPE is
        // built inside y' but outside _eq', so binders are y'=0, eq=1,
        // y=2, x=3.
        auto motive = makeLambda("y'", Nat(),
            makeLambda("_eq'",
                eq(Nat(),
                   makeBoundVariable(3) /* x */,
                   makeBoundVariable(0) /* y' */),
                eq(Nat(),
                   succ(makeBoundVariable(4) /* x */),
                   succ(makeBoundVariable(1) /* y' */))));
        auto caseRefl = refl(Nat(), succ(makeBoundVariable(2) /* x */));
        auto proof = makeLambda("x", Nat(),
            makeLambda("y", Nat(),
                makeLambda("eq",
                    eq(Nat(),
                       makeBoundVariable(1) /* x */,
                       makeBoundVariable(0) /* y */),
                    makeApplication(
                        makeApplication(
                            makeApplication(
                                makeApplication(
                                    makeApplication(
                                        makeApplication(
                                            makeConstant("Equality1_recursor",
                                                          {makeLevelConst(0),
                                                           makeLevelConst(0)}),
                                            Nat()),
                                        makeBoundVariable(2) /* x */),
                                    motive),
                                caseRefl),
                            makeBoundVariable(1) /* y */),
                        makeBoundVariable(0) /* eq */))));
        auto theoremType = makePi("x", Nat(),
            makePi("y", Nat(),
                makePi("_eq",
                    eq(Nat(), makeBoundVariable(1), makeBoundVariable(0)),
                    eq(Nat(),
                       succ(makeBoundVariable(2)),
                       succ(makeBoundVariable(1))))));
        addDefinition(env, "succCong", theoremType, proof);
        std::cout << "  succCong   ⊨  Π(x y : Natural). x = y → "
                     "succ x = succ y   (J)\n";
    }

    // ------------------------------------------------------------------
    // Theorem 1: zero_add :  Π(a : Natural). 0 + a = a.
    //
    // Definitional: add zero a ι-reduces to a, so the proof is just
    // refl Natural a.
    // ------------------------------------------------------------------
    {
        auto theoremType =
            makePi("a", Nat(),
                eq(Nat(), plus(zero(), makeBoundVariable(0)),
                   makeBoundVariable(0)));
        auto proof = makeLambda("a", Nat(),
            refl(Nat(), makeBoundVariable(0)));
        addDefinition(env, "zero_add", theoremType, proof);
        std::cout << "  zero_add   ⊨  Π(a : Natural). 0 + a = a   "
                     "(definitional)\n";
    }

    // ------------------------------------------------------------------
    // Theorem 2: add_zero :  Π(a : Natural). a + 0 = a.
    //
    // Not definitional. Proof by induction on a using Natural_recursor
    // with a Prop-valued motive, and succCong (derived above, not an
    // axiom) for the successor case.
    // ------------------------------------------------------------------
    {
        auto motive = makeLambda("a", Nat(),
            eq(Nat(),
               plus(makeBoundVariable(0), zero()),
               makeBoundVariable(0)));
        auto caseZero = refl(Nat(), zero());
        auto caseSucc = makeLambda("k", Nat(),
            makeLambda("IH",
                eq(Nat(),
                   plus(makeBoundVariable(0), zero()),
                   makeBoundVariable(0)),
                makeApplication(
                    makeApplication(
                        makeApplication(makeConstant("succCong"),
                                        plus(makeBoundVariable(1) /* k */,
                                              zero())),
                        makeBoundVariable(1) /* k */),
                    makeBoundVariable(0) /* IH */)));

        auto theoremType =
            makePi("a", Nat(),
                eq(Nat(), plus(makeBoundVariable(0), zero()),
                   makeBoundVariable(0)));
        auto proof = makeLambda("a", Nat(),
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
                     "(induction + succCong)\n";
    }

    // ------------------------------------------------------------------
    // Theorem 3: one_add :  Π(a : Natural). 1 + a = succ a.
    //
    // Definitional once you observe that add (succ zero) a ι-reduces
    // to succ a directly.
    // ------------------------------------------------------------------
    {
        auto theoremType =
            makePi("a", Nat(),
                eq(Nat(), plus(succ(zero()), makeBoundVariable(0)),
                   succ(makeBoundVariable(0))));
        auto proof = makeLambda("a", Nat(),
            refl(Nat(), succ(makeBoundVariable(0))));
        addDefinition(env, "one_add", theoremType, proof);
        std::cout << "  one_add    ⊨  Π(a : Natural). 1 + a = succ a   "
                     "(definitional)\n";
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
        // case_succ k recK m = add m (recK m)
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

} // namespace

int main() {
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

    runExample(arithmetic, "Prop", makeProp());
    runExample(arithmetic, "Equality (now lands in Prop)",
               makeConstant("Equality", {makeLevelConst(0)}));
    runExample(arithmetic,
               "Π(P : Prop). P   (impredicative quantifier; lives in Prop)",
               makePi("P", makeProp(), makeBoundVariable(0)));

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
    runIntegrationTests();

    std::cout << "\n" << passed << " passed, " << failed << " failed\n";
    return failed == 0 ? 0 : 1;
}
