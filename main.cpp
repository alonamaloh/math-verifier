#include "expression.hpp"
#include "kernel.hpp"
#include "printer.hpp"

#include <iostream>
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

#define EXPECT_TRUE(condition)   expectTrue((condition), #condition, __LINE__)
#define EXPECT_THROW(expression) expectThrow([&]{ (void)(expression); }, \
                                             #expression, __LINE__)

void runCoreTests() {
    std::cout << "--- core tests ---\n";

    Environment environment;

    // Type level : Type (level+1) for several levels.
    for (int level = 0; level < 3; ++level) {
        auto inferredType = inferType(environment, {}, makeSort(level));
        auto* sort = std::get_if<Sort>(&inferredType->node);
        EXPECT_TRUE(sort != nullptr && sort->universeLevel == level + 1);
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

    // Equality : Π(A : Type 0). Π(x : A). Π(y : A). Prop
    // de Bruijn:  Π(Type 0). Π(@0). Π(@1). Prop
    addAxiom(environment, "Equality",
        makePi("A", makeType(0),
          makePi("x", makeBoundVariable(0),
            makePi("y", makeBoundVariable(1),
              makeProp()))));

    // reflexivity : Π(A : Type 0). Π(x : A). Equality A x x
    // de Bruijn:    Π(Type 0). Π(@0). Equality @1 @0 @0
    addAxiom(environment, "reflexivity",
        makePi("A", makeType(0),
          makePi("x", makeBoundVariable(0),
            makeApplication(
              makeApplication(
                makeApplication(makeConstant("Equality"), makeBoundVariable(1)),
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
                      makeApplication(makeConstant("Natural_recursor"),
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
            makeApplication(makeConstant("reflexivity"), makeConstant("Natural")),
            makeConstant("zero"));
        auto inferredType = inferType(environment, {}, proof);
        auto expected = makeApplication(
            makeApplication(
                makeApplication(makeConstant("Equality"), makeConstant("Natural")),
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
                makeApplication(makeConstant("reflexivity"), makeConstant("Natural")),
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
                makeApplication(makeConstant("reflexivity"),
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
                makeApplication(makeConstant("reflexivity"),
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
            inferType(environment, {}, makeConstant("reflexivity"));
        auto reflexivityKind =
            weakHeadNormalForm(environment,
                               inferType(environment, {}, reflexivityType));
        auto* sort = std::get_if<Sort>(&reflexivityKind->node);
        EXPECT_TRUE(sort != nullptr && sort->universeLevel == 0);
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
        EXPECT_TRUE(sort != nullptr && sort->universeLevel == 0);  // Prop
    }

    // Π(_ : Prop). Prop is NOT in Prop — its codomain is the *type* Prop
    // (which lives in Type 0), not a proposition. Result is Type 0.
    {
        auto term = makePi("_", makeProp(), makeProp());
        auto kind = weakHeadNormalForm(environment,
                                       inferType(environment, {}, term));
        auto* sort = std::get_if<Sort>(&kind->node);
        EXPECT_TRUE(sort != nullptr && sort->universeLevel == 1);  // Type 0
    }

    // Π(_ : Type 0). Type 0 lives in Type 1.
    {
        auto term = makePi("_", makeType(0), makeType(0));
        auto kind = weakHeadNormalForm(environment,
                                       inferType(environment, {}, term));
        auto* sort = std::get_if<Sort>(&kind->node);
        EXPECT_TRUE(sort != nullptr && sort->universeLevel == 2);  // Type 1
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
                makeApplication(makeConstant("Equality"),
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
            inferType(environment, {}, makeConstant("Natural_recursor"));
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
                   makeApplication(makeConstant("reflexivity"),
                                   makeConstant("Natural")),
                   makeConstant("zero")));

    runExample(arithmetic,
               "reflexivity Natural  -- partially applied; codomain depends on A",
               makeApplication(makeConstant("reflexivity"),
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
               makeConstant("Equality"));
    runExample(arithmetic,
               "Π(P : Prop). P   (impredicative quantifier; lives in Prop)",
               makePi("P", makeProp(), makeBoundVariable(0)));

    runExample(arithmetic, "Natural_recursor  (auto-generated)",
               makeConstant("Natural_recursor"));

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

    runCoreTests();
    runEnvironmentTests(arithmetic);

    std::cout << "\n" << passed << " passed, " << failed << " failed\n";
    return failed == 0 ? 0 : 1;
}
