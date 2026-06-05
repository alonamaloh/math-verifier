#pragma once

#include "kernel/level.hpp"
#include "kernel/subtree_hash.hpp"

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <memory>
#include <type_traits>
#include <variant>
#include <vector>

struct Expression;

// Forward-declared refcount manipulation. Implementations live below the
// Expression definition (need to access `refcount`).
inline void intrusiveAddRef(Expression* expression) noexcept;
inline void intrusiveSubRef(Expression* expression) noexcept;

// Intrusive reference-counted pointer to Expression. Replaces
// std::shared_ptr<Expression> — 8 bytes per pointer (vs 16 for shared_ptr),
// no control-block allocation (vs shared_ptr's two-allocation pattern
// when not using make_shared), no atomic refcount op cost. Matches Lean 4's
// `lean_object*` model.
//
// API surface is the subset of shared_ptr<Expression> we actually use:
// default/copy/move construct + assign, ->, *, get(), bool, reset(),
// nullptr-comparison. Single-threaded — the kernel runs on the verify
// command's main thread, so refcount ops are plain ++/-- (not atomic).
class IntrusiveExpressionPointer {
public:
    constexpr IntrusiveExpressionPointer() noexcept : ptr_(nullptr) {}
    constexpr IntrusiveExpressionPointer(std::nullptr_t) noexcept
        : ptr_(nullptr) {}
    explicit IntrusiveExpressionPointer(Expression* p) noexcept
        : ptr_(p) {
        if (ptr_) intrusiveAddRef(ptr_);
    }
    IntrusiveExpressionPointer(const IntrusiveExpressionPointer& other) noexcept
        : ptr_(other.ptr_) {
        if (ptr_) intrusiveAddRef(ptr_);
    }
    IntrusiveExpressionPointer(IntrusiveExpressionPointer&& other) noexcept
        : ptr_(other.ptr_) {
        other.ptr_ = nullptr;
    }
    ~IntrusiveExpressionPointer() noexcept {
        if (ptr_) intrusiveSubRef(ptr_);
    }
    IntrusiveExpressionPointer&
    operator=(const IntrusiveExpressionPointer& other) noexcept {
        // Cache `other.ptr_` up front. `other` itself may live inside an
        // Expression that `*this` transitively owns (e.g. peel loops of
        // the form `cursor = application->function`, where `application`
        // points into `cursor`'s storage). Dropping our refcount can
        // then free the storage backing `other`, so any later read of
        // `other.ptr_` would be UB. Handles self-assignment correctly
        // because the AddRef bumps before the SubRef drops.
        Expression* source = other.ptr_;
        if (source) intrusiveAddRef(source);
        if (ptr_) intrusiveSubRef(ptr_);
        ptr_ = source;
        return *this;
    }
    IntrusiveExpressionPointer&
    operator=(IntrusiveExpressionPointer&& other) noexcept {
        if (this != &other) {
            // Same self-ownership hazard as the copy assignment: read
            // and clear `other` BEFORE the SubRef of our old pointer,
            // since that SubRef can free storage that `other` lives in.
            Expression* source = other.ptr_;
            other.ptr_ = nullptr;
            if (ptr_) intrusiveSubRef(ptr_);
            ptr_ = source;
        }
        return *this;
    }
    IntrusiveExpressionPointer& operator=(std::nullptr_t) noexcept {
        if (ptr_) intrusiveSubRef(ptr_);
        ptr_ = nullptr;
        return *this;
    }

    Expression* get() const noexcept { return ptr_; }
    Expression& operator*() const noexcept { return *ptr_; }
    Expression* operator->() const noexcept { return ptr_; }
    explicit operator bool() const noexcept { return ptr_ != nullptr; }

    void reset() noexcept {
        if (ptr_) intrusiveSubRef(ptr_);
        ptr_ = nullptr;
    }

    bool operator==(const IntrusiveExpressionPointer& o) const noexcept {
        return ptr_ == o.ptr_;
    }
    bool operator!=(const IntrusiveExpressionPointer& o) const noexcept {
        return ptr_ != o.ptr_;
    }
    bool operator==(std::nullptr_t) const noexcept { return ptr_ == nullptr; }
    bool operator!=(std::nullptr_t) const noexcept { return ptr_ != nullptr; }

private:
    Expression* ptr_;
};

// IntrusiveExpressionPointer replaces std::shared_ptr<Expression>:
// 8-byte pointer (vs 16), no separate control-block allocation, no
// atomic refcount ops. See operator= bodies for the self-ownership
// hazard the assignment paths have to guard against — that hazard
// was the historical blocker; peel loops of the form
// `cursor = application->function` (where `application` points into
// `cursor`'s storage) trip it whenever dropping `cursor`'s last ref
// frees the storage backing the rhs.
using ExpressionPointer = IntrusiveExpressionPointer;

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
    // Highest free-BoundVariable index in this subtree, accounting for
    // binders along the way (binders decrement the visible BV indices
    // of references inside their body). -1 means closed (no free BV
    // refs). Populated by the make* helpers. Lets shift/substitute
    // short-circuit on closed subtrees: most of any given proof is
    // closed library terms, so a single int compare at the top of each
    // recursion replaces an O(size) walk.
    int maxFreeBoundVariable = -1;
    // Intrusive refcount, managed by IntrusiveExpressionPointer's
    // ctor/dtor/assignment. Starts at 0; the first IntrusiveExpressionPointer
    // bumps it to 1; last release deletes the Expression.
    mutable uint32_t refcount = 0;

    Expression() = default;

    template <typename Alternative,
              typename = std::enable_if_t<
                  !std::is_same_v<std::decay_t<Alternative>, Expression>>>
    Expression(Alternative&& alternative)
        : node(std::forward<Alternative>(alternative)) {}
};

// Refcount manipulators — defined inline after Expression so they can
// touch the `refcount` field. Single-threaded; non-atomic. Diagnostic
// abort guards remain in place since the intrusive path isn't on the
// production code path yet — they're cheap (one compare) and catch
// the obvious classes of bug if/when this gets re-enabled.
inline void intrusiveAddRef(Expression* expression) noexcept {
    ++expression->refcount;
}
inline void intrusiveSubRef(Expression* expression) noexcept {
    if (--expression->refcount == 0) delete expression;
}

// Factory: allocate an Expression on the heap initialised with `alternative`,
// wrap in an ExpressionPointer (refcount → 1). Replaces the
// `std::make_shared<Expression>(...)` calls used previously.
template <typename Alternative>
inline ExpressionPointer makeRawExpression(Alternative&& alternative) {
    return ExpressionPointer(new Expression(std::forward<Alternative>(alternative)));
}

// Hash-cons table for Expression nodes. Each make* helper calls
// internExpression with the freshly-allocated candidate; if a
// structurally-equal Expression already exists in the table, that
// pre-existing pointer is returned and the candidate is discarded.
// Otherwise the candidate is inserted and returned.
//
// Consequences:
//   * structurallyEqual(a, b) ≡ (a.get() == b.get()) becomes the
//     common case — the structural recursion only triggers on hash
//     collisions.
//   * Repeated substitution of the same subterm into many positions
//     shares storage instead of duplicating, so motive trees built by
//     WHNF-unfolded Quotient.lift bodies (the main supremum
//     bottleneck) collapse from O(N positions × tree size) to
//     O(unique subterm count).
//   * Memory grows monotonically over a verify run, but is bounded by
//     the number of distinct subterms — orders of magnitude smaller
//     than the worst-case substitution blowup.
//
// Defined in kernel.cpp because the table's equaler needs
// `structurallyEqual` (also defined there).
ExpressionPointer internExpression(ExpressionPointer candidate);
// Toggle for hash-consing. Default off until perf-tested across the
// library. main.cpp sets this to true for the `verify` command (when
// the env var `MATH_HASH_CONS` is set or unconditionally if we land
// it as default-on).
extern bool g_hashConsEnabled;

inline ExpressionPointer makeBoundVariable(int index) {
    auto expression = makeRawExpression(BoundVariable{index});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(subtree_hash::kSeed,
                           subtree_hash::kTagBoundVariable),
        static_cast<uint64_t>(index));
    expression->maxFreeBoundVariable = index;
    return expression;  // Leaf — don't intern (per-alloc cost > sharing benefit)
}
inline ExpressionPointer makeFreeVariable(std::string name) {
    uint64_t nameHash = subtree_hash::hashString(name);
    auto expression = makeRawExpression(
        FreeVariable{std::move(name)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagFreeVariable),
            nameHash),
        static_cast<uint64_t>(FreeVariableOrigin::User));
    return expression;  // Leaf — don't intern
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
    auto expression = makeRawExpression(
        Sort{std::move(level)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(subtree_hash::kSeed,
                           subtree_hash::kTagSort),
        levelHash);
    return expression;  // Leaf — don't intern
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
    // Binder shifts BVs in codomain by 1 (BV(0) refers to this Pi's
    // binder, BV(1) refers to enclosing scope's BV(0), etc).
    int domainMax = domain->maxFreeBoundVariable;
    int codomainAdj = codomain->maxFreeBoundVariable - 1;
    int maxFree = domainMax > codomainAdj ? domainMax : codomainAdj;
    if (maxFree < -1) maxFree = -1;
    auto expression = makeRawExpression(
        Pi{std::move(displayHint), std::move(domain),
           std::move(codomain)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagPi),
            domainHash),
        codomainHash);
    expression->maxFreeBoundVariable = maxFree;
    return internExpression(std::move(expression));
}
inline ExpressionPointer makeLambda(std::string displayHint,
                                ExpressionPointer domain,
                                ExpressionPointer body) {
    uint64_t domainHash = domain->hash;
    uint64_t bodyHash = body->hash;
    int domainMax = domain->maxFreeBoundVariable;
    int bodyAdj = body->maxFreeBoundVariable - 1;
    int maxFree = domainMax > bodyAdj ? domainMax : bodyAdj;
    if (maxFree < -1) maxFree = -1;
    auto expression = makeRawExpression(
        Lambda{std::move(displayHint), std::move(domain),
               std::move(body)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagLambda),
            domainHash),
        bodyHash);
    expression->maxFreeBoundVariable = maxFree;
    return internExpression(std::move(expression));
}
inline ExpressionPointer makeApplication(ExpressionPointer function,
                                     ExpressionPointer argument) {
    uint64_t functionHash = function->hash;
    uint64_t argumentHash = argument->hash;
    int fnMax = function->maxFreeBoundVariable;
    int argMax = argument->maxFreeBoundVariable;
    int maxFree = fnMax > argMax ? fnMax : argMax;
    auto expression = makeRawExpression(
        Application{std::move(function), std::move(argument)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagApplication),
            functionHash),
        argumentHash);
    expression->maxFreeBoundVariable = maxFree;
    return internExpression(std::move(expression));
}
inline ExpressionPointer makeConstant(std::string name,
                                      std::vector<LevelPointer> universeArguments) {
    uint64_t nameHash = subtree_hash::hashString(name);
    uint64_t universeHash = subtree_hash::kSeed;
    for (const auto& universeArgument : universeArguments) {
        universeHash = subtree_hash::mix(universeHash,
                                            universeArgument->hash);
    }
    auto expression = makeRawExpression(
        Constant{std::move(name), std::move(universeArguments)});
    expression->hash = subtree_hash::mix(
        subtree_hash::mix(
            subtree_hash::mix(subtree_hash::kSeed,
                               subtree_hash::kTagConstant),
            nameHash),
        universeHash);
    return expression;  // Constant — don't intern (cheap leaves)
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
    int typeMax = type->maxFreeBoundVariable;
    int valueMax = value->maxFreeBoundVariable;
    int bodyAdj = body->maxFreeBoundVariable - 1;
    int maxFree = typeMax;
    if (valueMax > maxFree) maxFree = valueMax;
    if (bodyAdj > maxFree) maxFree = bodyAdj;
    if (maxFree < -1) maxFree = -1;
    auto expression = makeRawExpression(
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
    expression->maxFreeBoundVariable = maxFree;
    return internExpression(std::move(expression));
}
