#pragma once

#include "kernel/expression.hpp"

#include <cstdint>
#include <map>
#include <stdexcept>
#include <string>
#include <tuple>
#include <variant>
#include <vector>

struct TypeError : std::runtime_error {
    using std::runtime_error::runtime_error;

    // Optional structured info. The kernel populates these for the
    // type-mismatch case (Application argument vs Pi domain, Let value
    // vs declared type, etc.) so callers can paraphrase the error
    // with pretty-printed types rather than the bare message. They
    // are `nullptr` when the error has no meaningful "expected/actual"
    // pair (e.g. "internal" errors, name-collision errors).
    ExpressionPointer expectedType;
    ExpressionPointer actualType;
};

// `opaque` is HARD by default: the demand-point force-unfold retries (kernel
// defeq/inferType bridge, elaborator deep-WHNF / cases-on-expression / tuple-
// lambda-Pi intro) refuse to expand an opaque head, so the only way to see
// through one is an explicit `unfold X in …`. Returns true for every opaque
// constant; kept as the single decision point for a possible future
// `reducible` opt-in. (Formerly gated by the MATH_HARD_OPAQUE env var.)
bool isHardOpaqueConstant(const std::string& name);

// A reduction ran out of its resource budget — the recursion-depth bound
// or the WHNF fuel limit — before reaching a normal form. Distinct from a
// genuine type error so `isDefinitionallyEqual` can downgrade it to a
// conservative `false` ("can't decide, assume not equal" — never an unsound
// acceptance, which would require `true`), while direct WHNF / type-checking
// callers still see it as the TypeError it derives from.
struct KernelResourceExhausted : TypeError {
    using TypeError::TypeError;
};

struct ContextEntry {
    std::string name;
    ExpressionPointer type;
    FreeVariableOrigin origin = FreeVariableOrigin::User;
    // Non-null for let-style binders (surface `let X := V`). When set,
    // isDefinitionallyEqual ζ-reduces references to the FreeVariable
    // {name, origin} to this value during equality comparison. The
    // elaborator's auto-prover separately ζ-unfolds at the closed-term
    // level so structural matchers (lemma index, hypothesis match)
    // can see through let-bound names.
    ExpressionPointer value = nullptr;
};
using Context = std::vector<ContextEntry>;

// A global declaration is one of:
//   Axiom       — a name and its type, no body ("assume this exists").
//   Definition  — name, declared type, and body whose inferred type matches.
//                 Delta-reduces to body in weakHeadNormalForm.
//   Inductive   — an inductively-defined type, with its kind (a Pi-chain
//                 of parameters and indices ending in a Sort) and the names
//                 of its constructors. Stuck under reduction.
//   Constructor — a single constructor of an inductive type, with the name
//                 of that inductive, the constructor's index within it,
//                 and the constructor's declared type. Stuck.
//   Recursor    — the auto-generated eliminator for an inductive. Stuck on
//                 its own, but iota-reduces when fully applied with the
//                 final argument being a constructor application.
// Each declaration carries the universe parameter names it abstracts over.
// At a Constant use site, the caller supplies a matching list of Level
// arguments; inferType substitutes those into the declaration's type.
// Most declarations in everyday use have no parameters (empty vector).
// `automatic` is elaborator-facing metadata (the kernel never reads it):
// it whitelists the declaration for the auto-prover's unprompted
// cross-module use. Persisted in the cache so importers see it.
struct Axiom       { std::vector<std::string> universeParameters;
                     ExpressionPointer type; bool automatic = false; };
// `opacity` controls whether the kernel may δ-unfold this definition
// during reduction. Transparent (default): treated as today — the body
// is unfolded freely, enabling β/ι to fire on definitions that compute
// by pattern-match. Opaque: the kernel refuses to δ-unfold; the
// Application stays as `<name>(args...)` and is only equal to itself.
// Proofs that need the body must invoke an explicit `unfold` step at
// the surface or rely on named lemmas about the definition's
// extensional behaviour. Cache format v4 adds the byte.
enum class Opacity : uint8_t { Transparent = 0, Opaque = 1 };
struct Definition  { std::vector<std::string> universeParameters;
                     ExpressionPointer type; ExpressionPointer body;
                     Opacity opacity = Opacity::Transparent;
                     // See Axiom::automatic.
                     bool automatic = false; };
// An Inductive's `kind` is a Pi-chain ending in a Sort. The first
// `numParameters` Pis bind parameters (uniform across constructors); the
// remaining Pis bind indices (allowed to vary per constructor). For
// non-parameterised, non-indexed inductives like Natural, the kind is a
// plain Sort and numParameters is 0.
struct Inductive   { std::vector<std::string> universeParameters;
                     ExpressionPointer kind;
                     std::vector<std::string> constructorNames;
                     int numParameters; };
struct Constructor { std::vector<std::string> universeParameters;
                     std::string inductiveName;
                     int constructorIndex;
                     ExpressionPointer type; };
struct Recursor    { std::vector<std::string> universeParameters;
                     std::string inductiveName;
                     ExpressionPointer type;
                     int numConstructors;
                     int numParameters;
                     int numIndices; };

using Declaration = std::variant<Axiom, Definition,
                                 Inductive, Constructor, Recursor>;

struct Environment {
    std::map<std::string, Declaration> declarations;
    // Elaborator-side metadata: number of leading implicit binders for
    // each declaration. The kernel itself ignores this — it's used by
    // the surface elaborator to decide which leading arguments at a
    // call site to fill in via unification. A declaration not present
    // in this map has zero implicit binders. Phase 2.1 restricts
    // implicit binders to leading consecutive positions.
    std::map<std::string, int> implicitArgumentCounts;

    // Operator-dispatch registry. Key: (operator symbol, left operand
    // type head name, right operand type head name). Value: the fully-
    // qualified function name to dispatch to. Populated by `operator
    // (<sym>) on (<T1>, <T2>) := <F>;` declarations. The kernel itself
    // never reads this — it's a surface-elaborator concern.
    std::map<std::tuple<std::string, std::string, std::string>,
              std::string> operatorRegistry;

    // Function-name overload aliases. Key: the surface alias name (e.g.
    // "add"). Value: a list of fully-qualified function names that the
    // alias resolves to. The elaborator picks one by matching argument
    // types at each call site. Populated by `overload <alias> := <F>;`.
    std::map<std::string, std::vector<std::string>> overloadAliases;

    // Congruence-under-binder lemmas. Key: a function head name (e.g.
    // "Polynomial.Sum"). Value: the congruence lemmas registered for it
    // (e.g. Sum.extensional, Sum.extensional_range), tried in order. A
    // calc `=` step `F(…, λx.f, …) = F(…, λx.g, …)` is discharged from the
    // author's pointwise `(x) => f(x) = g(x)` via one of these. Populated
    // by `congruence_under_binder <F> := <L>;`. Surface-elaborator concern.
    std::map<std::string, std::vector<std::string>>
        congruenceUnderBinderRegistry;

    // Coercion registry. Key: (sourceTypeName, targetTypeName). Value:
    // the chain of fully-qualified function names to compose, in order
    // (apply functionNames[0] first, then functionNames[1], etc.). A
    // direct registration is a one-element chain; transitive entries
    // computed at registration time have more. Used by the ascription
    // path to insert coercion calls when `(expr : T)` has expr of a
    // different source type with a registered embedding.
    std::map<std::tuple<std::string, std::string>,
              std::vector<std::string>> coercionRegistry;

    // Canonical-instance registry (instance inference). Key: (structure
    // class head name, carrier head name) — e.g. ("IsGroup", "Integer").
    // Value: the instance theorem's name, its (structure-application)
    // type, the count of leading carrier-parameter Pis (0 for a concrete
    // carrier, 1 for `IntegerMod(m)`, …), and its universe parameters.
    // The elaborator fills an implicit structure-typed argument by
    // looking up the carrier head here. Surface-elaborator concern; the
    // kernel never reads it. Persisted across modules like the others.
    struct CanonicalInstance {
        std::string termName;
        ExpressionPointer type;
        int parameterCount = 0;
        std::vector<std::string> universeParameters;
    };
    std::map<std::tuple<std::string, std::string>, CanonicalInstance>
        canonicalInstanceRegistry;

    // Canonical structure BUNDLE for a carrier type: `(structure, carrier
    // head) → bundle term name`, e.g. `(Ring, Integer) → Integer.ring_bundle`.
    // Lets an implicit `{r : Ring}` be solved from a concrete carrier when
    // unification is stuck on `Ring.carrier(?r) ≡ Integer` — the bundled-ring
    // analogue of resolving a typeclass instance from the type. Populated by
    // `instance <bundle>` (a bare-bundle-typed instance, vs. the predicate
    // form). Surface-elaborator concern; the kernel never reads it.
    std::map<std::tuple<std::string, std::string>, std::string>
        canonicalBundleRegistry;

    // Forgetful (derived) instances: a carrier-POLYMORPHIC lemma that
    // produces one structure class from another on the SAME carrier, e.g.
    // `IsRing.additive_group : … → IsGroup(carrier, +, zero, -)` with premise
    // `ringProof : IsRing(carrier, +, zero, -, ·, one)`. Because the carrier
    // is abstract there is no concrete `(structure, carrier)` key; instead we
    // key by the CONCLUSION structure and, when a needed structure-class
    // proof has no direct instance/hypothesis, apply the lemma to a unique
    // in-scope premise-structure hypothesis (`tryForgetfulDerivation`).
    // Registered by `instance <lemma>` whose conclusion carrier is abstract
    // and which has a structure-class premise. Surface-elaborator concern.
    struct ForgetfulInstance {
        std::string termName;
        ExpressionPointer type;
        int leadingImplicitCount = 0;
        int premiseIndex = -1;          // which leading binder is the premise
        std::string premiseStructureName;
        std::vector<std::string> universeParameters;
    };
    std::map<std::string, std::vector<ForgetfulInstance>>
        forgetfulInstanceRegistry;

    // Fold-capable operations: `(operator symbol, carrier head) →
    // {operation, identity, IsMonoid witness}`, populated by
    // `fold_operation (+) on T := W;`. The certificate is a proof of
    // `IsMonoid(T, operation, identity)`; the registry feeds the fold
    // binder form and the ellipsis recognizer (A8). Canonical per key —
    // a second registration for the same (symbol, carrier) is rejected
    // at declaration time. Surface-elaborator concern; the kernel never
    // reads it. Persisted across modules like the other registries.
    struct FoldOperation {
        std::string operationName;
        std::string identityName;
        std::string witnessName;
    };
    std::map<std::tuple<std::string, std::string>, FoldOperation>
        foldOperationRegistry;

    const Declaration* lookup(const std::string& name) const {
        auto iterator = declarations.find(name);
        return iterator == declarations.end() ? nullptr : &iterator->second;
    }

    int implicitArgumentCount(const std::string& name) const {
        auto iterator = implicitArgumentCounts.find(name);
        return iterator == implicitArgumentCounts.end()
            ? 0 : iterator->second;
    }

    // Look up a registered operator-dispatch target. Returns the
    // function name on success, empty string if no registration exists.
    // Tries the exact (leftType, rightType) match first; falls back to
    // wildcard `_` registrations in priority order: (left, _), (_,
    // right), (_, _). This lets polymorphic operators like `∈` (where
    // the carrier on the LHS is arbitrary) register once with `_` and
    // dispatch on any concrete LHS type.
    std::string lookupOperator(
        const std::string& operatorSymbol,
        const std::string& leftTypeName,
        const std::string& rightTypeName) const {
        auto tryKey =
            [&](const std::string& l, const std::string& r) -> std::string {
                auto iterator = operatorRegistry.find(
                    std::make_tuple(operatorSymbol, l, r));
                return iterator == operatorRegistry.end()
                    ? std::string{} : iterator->second;
            };
        std::string result = tryKey(leftTypeName, rightTypeName);
        if (!result.empty()) return result;
        result = tryKey(leftTypeName, "_");
        if (!result.empty()) return result;
        result = tryKey("_", rightTypeName);
        if (!result.empty()) return result;
        return tryKey("_", "_");
    }

    // Look up the list of fully-qualified function names registered
    // under `aliasName`. Returns an empty vector if the alias is
    // unknown. Callers do overload resolution by matching argument
    // types against each candidate's signature.
    const std::vector<std::string>* lookupOverloads(
        const std::string& aliasName) const {
        auto iterator = overloadAliases.find(aliasName);
        return iterator == overloadAliases.end()
            ? nullptr : &iterator->second;
    }
};

// Type-checks `declaredType` (it must itself be a type) and adds an axiom
// to `environment`. Throws TypeError on name collision or ill-formed type.
// `universeParameters` are the names of the level parameters this axiom
// abstracts over; pass {} for a non-polymorphic axiom.
void addAxiom(Environment& environment, std::string name,
              std::vector<std::string> universeParameters,
              ExpressionPointer declaredType, bool automatic = false);

inline void addAxiom(Environment& environment, std::string name,
                     ExpressionPointer declaredType) {
    addAxiom(environment, std::move(name), {}, std::move(declaredType));
}

// Type-checks both `declaredType` and `body`, requires they agree
// definitionally, and adds the definition to `environment`.
void addDefinition(Environment& environment, std::string name,
                   std::vector<std::string> universeParameters,
                   ExpressionPointer declaredType, ExpressionPointer body,
                   Opacity opacity = Opacity::Transparent,
                   bool automatic = false);

inline void addDefinition(Environment& environment, std::string name,
                          ExpressionPointer declaredType,
                          ExpressionPointer body) {
    addDefinition(environment, std::move(name), {},
                  std::move(declaredType), std::move(body),
                  Opacity::Transparent);
}

// A constructor specification supplied to addInductive: the constructor's
// name and its declared type (a Pi-prefix ending in the inductive being
// declared).
struct ConstructorSpec {
    std::string name;
    ExpressionPointer type;
};

// Declares an inductive type and atomically adds: the inductive itself,
// each of its constructors, and an automatically-generated recursor under
// the name "<inductiveName>_recursor". Constructor types must be a Pi-
// prefix whose recursive arguments are direct references to the inductive
// (no nested or higher-order recursion). Strict positivity is the user's
// responsibility; the kernel does not check it.
// Canonical signature: inductive with explicit numParameters. The kind is
// a Pi-chain Π(p_1) ... Π(p_n). Π(i_1) ... Π(i_m). Sort u, where the first
// `numParameters` Pis bind parameters and the remaining Pis bind indices.
// Each constructor's type must begin with those same parameter Pis and
// end in `inductiveName` applied to the parameters and to some specific
// indices.
void addInductive(Environment& environment, std::string inductiveName,
                  std::vector<std::string> universeParameters,
                  ExpressionPointer kind,
                  int numParameters,
                  std::vector<ConstructorSpec> constructors);

// Convenience overloads for the most common cases. Without numParameters,
// the inductive has zero parameters and the kind must be a plain Sort.
inline void addInductive(Environment& environment, std::string inductiveName,
                         std::vector<std::string> universeParameters,
                         ExpressionPointer kind,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName),
                 std::move(universeParameters),
                 std::move(kind), 0, std::move(constructors));
}
inline void addInductive(Environment& environment, std::string inductiveName,
                         ExpressionPointer kind,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName), {},
                 std::move(kind), 0, std::move(constructors));
}
inline void addInductive(Environment& environment, std::string inductiveName,
                         ExpressionPointer kind,
                         int numParameters,
                         std::vector<ConstructorSpec> constructors) {
    addInductive(environment, std::move(inductiveName), {},
                 std::move(kind), numParameters, std::move(constructors));
}

// Adds `amount` to every BoundVariable whose index is at least `cutoff`.
// Used to keep indices coherent when a term crosses additional binders.
ExpressionPointer shift(ExpressionPointer expression, int amount, int cutoff = 0);

// Cheap allocation-free structural equality (alpha-equivalent via
// de Bruijn). Returns true only on truly identical terms — does not
// perform any reductions. Pointer-identity short-circuits at every
// level. Used by `isDefinitionallyEqual` as a fast path and by the
// elaborator's `rewrite` tactic to locate the unique occurrence of
// the lemma's left endpoint inside the goal's left side.
bool structurallyEqual(ExpressionPointer left, ExpressionPointer right);

// Walks `expression` and replaces every LevelParam appearing in any Sort
// or Constant universe-argument list, mapping each name in `parameterNames`
// to the corresponding entry in `replacements`. Used to instantiate a
// polymorphic constant when its universe arguments are known.
ExpressionPointer substituteUniverseLevels(
    ExpressionPointer expression,
    const std::vector<std::string>& parameterNames,
    const std::vector<LevelPointer>& replacements);

// Replaces BoundVariable{targetIndex} with `replacement` and decrements
// higher indices (the binder being removed). Recurses under binders with
// targetIndex+1 and a shifted replacement. Used by beta reduction.
ExpressionPointer substitute(ExpressionPointer expression,
                         int targetIndex,
                         ExpressionPointer replacement);

// Replaces BoundVariable{0} with the supplied free variable and decrements
// higher indices. Used to descend under a binder while exposing the bound
// variable as a free variable for type-checking and equality. The `origin`
// argument distinguishes user-supplied fresh names (the default) from
// kernel-internal ones used by isDefinitionallyEqual and the recursor
// builders.
ExpressionPointer openBinder(ExpressionPointer expression,
                             const std::string& freshName,
                             FreeVariableOrigin origin
                                 = FreeVariableOrigin::User);

// Replaces every FreeVariable matching (name, origin) with a BoundVariable
// referring to a binder added one level above `expression`, and shifts
// other bound variables up by one. The inverse of openBinder.
ExpressionPointer closeBinder(ExpressionPointer expression,
                              const std::string& name,
                              FreeVariableOrigin origin
                                  = FreeVariableOrigin::User);

// Default fuel for kernel functions that recursively reduce. The fuel is
// decremented at every reduction step and recursive call; functions throw
// (or return false conservatively) when it runs out. This guards against
// non-termination for malformed input — a well-typed expression in our
// fragment never approaches this bound for any realistic input.
constexpr int defaultFuel = 10000;

// Optional runtime invariant checks. When true, inferType performs a
// kind-soundness postcondition on every successful inference (it re-infers
// the result type and requires it to be a Sort). This roughly doubles the
// cost of type-checking but catches the entire class of "kernel produced
// internally-inconsistent output" bugs. Off by default; tests enable it.
extern bool kernelCheckInvariants;

// ---- Optional kernel instrumentation -------------------------------------
//
// Three independently-controlled knobs, all opt-in (off = zero cost beyond
// one branch per kernel-step). Set from env vars in main.cpp before any
// type-checking runs.
//
//   kernelStepLimit:    abort with TypeError when the per-top-level step
//                       counter exceeds this. 0 = no limit. Useful for
//                       turning a hang into a localised, debuggable error.
//
//   kernelTraceInterval: when > 0, emit one diagnostic line to stderr every
//                       N steps. Each line names the current operation
//                       (whnf / isDefEq / inferType) and the head of the
//                       expression(s) being processed.
//
//   kernelProfileEnabled: tally δ-reductions by definition name; on top-
//                       level call completion, emit a one-line summary if
//                       any single definition was unfolded more than a
//                       small threshold. Off by default.
//
// The counters are thread_local; the kernel itself is single-threaded but
// this lets a host embed multiple kernel sessions in different threads.
// The reset point is each public entry (addAxiom/addDefinition/addInductive)
// and the diagnostic printing/limit-checking only fires inside those.
extern uint64_t kernelStepLimit;
extern uint64_t kernelTraceInterval;
extern bool kernelProfileEnabled;

// Current value of the per-thread kernel reduction-step counter. It is
// reset to 0 at every public addAxiom/addDefinition/addInductive entry and
// incremented once per WHNF/isDefEq/inferType reduction step. The
// elaborator's auto-prover snapshots this around a top-level claim and
// bounds the *increase* it causes, so an effort budget can be expressed in
// the kernel's own unit of work (reduction steps) rather than a coarse
// per-candidate count — this is what makes the budget trip on a goal whose
// per-conversion cost (not iteration count) is what blows up. Monotonic
// within one top-level kernel call.
uint64_t kernelStepsSoFar();

// Truncate diagnostic expression dumps to this many characters. Bumped from
// the default of 240 when investigating an issue where the truncated form
// hides the diverging subterm.
extern std::size_t kernelDumpWidth;

// When true, weakHeadNormalForm consults and populates a thread-local
// structural-hash cache. The cache is automatically cleared at every
// public addAxiom / addDefinition / addInductive boundary (since those
// mutate the environment that WHNF reads). Default: false — leaves the
// kernel stateless, important for the test suite which intentionally
// runs short scenarios that depend on uncached fuel/throw behaviour.
//
// Embedders (the `kernel verify` command) should set this to true at
// startup so the cache covers all kernel calls — both the elaborator's
// own WHNF/inferType walks and the final addDefinition's body check.
// On heavy quotient proofs that mention the same subexpression in many
// positions, this turns O(N^k) work into O(N).
extern bool kernelCacheEnabled;

// Diagnostic counters for the per-decl typecheck cost. Updated from
// addAxiom / addDefinition's inferType pair. Read by main.cpp's
// verifyWithCache to report what fraction of file time is spent in
// the kernel's final typecheck (the part the trust cache would skip).
extern uint64_t kernelAddDeclMicros;
extern uint64_t kernelAddDeclCount;

// Drop every cached WHNF / isDefEq result. Must be called whenever the
// environment mutates in a way that could change reduction (e.g. an
// opacity flip via `unfold`, or the matching restore): a cached TRUE
// `isDefEq` computed under transparent opacity is unsound to reuse
// once opacity is restored to opaque. `addDefinition` already wipes
// the cache via KernelInstrumentationScope; this entry point is for
// the cases where the environment changes WITHOUT going through
// `addDefinition`.
void invalidateKernelCaches();

// Reduces only the head: enough to see whether the outermost form is a
// Sort, Pi, Lambda, etc. Unfolds definitions in head position
// (delta-reduction). Throws TypeError on fuel exhaustion.
ExpressionPointer weakHeadNormalForm(const Environment& environment,
                                 ExpressionPointer expression,
                                 int fuel = defaultFuel);

// Definitional equality: same up to reduction, alpha-renaming, η, and
// proof irrelevance. The `context` is consulted when proof irrelevance
// needs to infer the types of the two sides. Returns false conservatively
// when fuel runs out.
bool isDefinitionallyEqual(const Environment& environment,
                           const Context& context,
                           ExpressionPointer left,
                           ExpressionPointer right,
                           int fuel = defaultFuel);

// (`isSubtype` was removed: the kernel adopted Lean 4's non-cumulative
// universe convention, which makes it identical to `isDefinitionallyEqual`.
// Application argument checks, Let value checks, and the addDefinition body
// check call `isDefinitionallyEqual` directly.)

// Returns the type of `expression` in `environment` and `context`,
// or throws TypeError.
ExpressionPointer inferType(const Environment& environment,
                        const Context& context,
                        ExpressionPointer expression);

// Returns a name not present in `context`. Tries `displayHint` first,
// then "displayHint_1", "displayHint_2", ...
std::string freshName(const std::string& displayHint, const Context& context);
