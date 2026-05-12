#pragma once

#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>
#include <vector>

// Universe levels are recursive expressions. Following Lean's design:
//   LevelConst n  — a concrete integer level. 0 is Proposition, 1 is Type 0, ...
//   LevelParam n  — a named universe parameter; substituted when a
//                   polymorphic constant is applied.
//   LevelSuccessor l   — l + 1.
//   LevelMax a b  — max(a, b).
//   LevelIMax a b — Lean's imax: 0 if b normalises to 0 (impredicative
//                   Proposition behaviour), otherwise max(a, b).
struct Level;
using LevelPointer = std::shared_ptr<Level>;

struct LevelConst { int value; };
struct LevelParam { std::string name; };
struct LevelSuccessor  { LevelPointer base; };
struct LevelMax   { LevelPointer left; LevelPointer right; };
struct LevelIMax  { LevelPointer left; LevelPointer right; };

struct Level {
    std::variant<LevelConst, LevelParam, LevelSuccessor, LevelMax, LevelIMax> node;

    Level() = default;

    template <typename Alternative,
              typename = std::enable_if_t<
                  !std::is_same_v<std::decay_t<Alternative>, Level>>>
    Level(Alternative&& alternative)
        : node(std::forward<Alternative>(alternative)) {}
};

// Construction helpers. These perform a small amount of normalisation at
// construction time (e.g. max(0, l) = l, successor(LevelConst n) =
// LevelConst (n+1)) so that simple structural equality is enough at
// most call sites.
LevelPointer makeLevelConst(int value);
LevelPointer makeLevelParam(std::string name);
LevelPointer makeLevelSuccessor(LevelPointer base);
LevelPointer makeLevelMax(LevelPointer left, LevelPointer right);
LevelPointer makeLevelIMax(LevelPointer left, LevelPointer right);

// If the (normalised) level is LevelConst{value}, returns the value;
// otherwise returns std::nullopt. Used by callers that only care about
// concrete levels (e.g. detecting Proposition and the impredicative Pi rule).
std::optional<int> levelAsConstant(LevelPointer level);

// Replaces every LevelParam{name} with the supplied `replacement`. Used by
// inferType when instantiating a polymorphic constant with explicit level
// arguments.
LevelPointer substituteLevelParameter(LevelPointer level,
                                      const std::string& parameterName,
                                      LevelPointer replacement);

// True if the two levels are definitionally equal. Handles a small amount
// of structural reasoning beyond literal pointer equality (e.g. levels
// reduced by the normalising constructors).
bool levelsDefinitionallyEqual(LevelPointer left, LevelPointer right);

// True if subLevel can be used wherever superLevel is expected (universe
// cumulativity). For concrete LevelConst this is integer ordering; for
// other forms we conservatively fall back to definitional equality.
bool levelLessOrEqual(LevelPointer subLevel, LevelPointer superLevel);

// Pretty-prints a level. Used by the expression printer for Sort and the
// universe arguments of Constants.
std::string prettyPrintLevel(LevelPointer level);
