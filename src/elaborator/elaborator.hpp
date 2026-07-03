#pragma once

#include "kernel/expression.hpp"
#include "kernel/kernel.hpp"
#include "elaborator/lemma_search.hpp"
#include "kernel/level.hpp"
#include "syntax/surface.hpp"

#include <functional>
#include <stdexcept>
#include <string>

struct ElaborateError : std::runtime_error {
    // Position of the innermost frame at the time the error was thrown,
    // when available. 0 means "unknown" — most call sites do know the
    // position, but a few internal frames don't. Used by the driver to
    // emit the canonical `FILE:LINE:COL:` prefix editors recognise.
    int line = 0;
    int column = 0;
    using std::runtime_error::runtime_error;
    ElaborateError(const std::string& message, int line_, int column_)
        : std::runtime_error(message), line(line_), column(column_) {}
};

// Thrown when the auto-prover exhausts its effort budget (kernel_quirks
// #19). Deliberately NOT derived from ElaborateError / TypeError so that
// the many speculative `catch (ElaborateError&)/(TypeError&) -> nullptr`
// sites inside the prover and its callers do NOT swallow it: a budget
// trip must abort the whole search and surface the actionable "add `by`"
// message, never be silently turned into "this tactic missed". It is
// caught at exactly one place — the by-less proof-step dispatch — and
// re-issued as a positioned ElaborateError with the surrounding context.
struct AutoProverBudgetError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

// Elaborates a single surface expression to a kernel expression in the
// given environment, with no local binders and no universe parameters in
// scope. Used by tests; modules call elaborateModule instead.
ExpressionPointer elaborateExpression(const SurfaceExpression& expression,
                                       const Environment& environment);

// Processes a parsed module top-to-bottom, registering each declaration
// in the environment. Throws ElaborateError on lookup failures, malformed
// declarations, etc. Throws TypeError (from the kernel) on type errors.
//
// `import` directives are recorded into `importedModules` but no module
// loading happens here — the driver is responsible for resolving and
// pre-loading dependencies into `environment` before calling this.
//
// `using` directives are currently a no-op (notation resolution is
// deferred for v0; modules must use explicit function calls and the
// fully-qualified `Equality(A, x, y)` form rather than `a = b`).
// `librarySearchProvider`, when set, returns (lazily, the first time it is
// called) a snapshot of the whole built library — used only to enrich a
// failing-proof error with candidate lemmas that aren't imported yet. It
// is consulted at most once and only on a failure path, so a build that
// succeeds never calls it. Pass nullptr (the default) to disable; then
// suggestions come from the in-scope environment alone.
//
// `goalAtLine` >= 1 (the `--goal-at` query) records the goal and local
// context at the statement at (or nearest before) that source line and
// writes the prettied report into `*goalAtReport` — including when
// elaboration throws downstream of the queried line, so a file whose
// proof fails after the query point still reports its goal.

// D Phase-1: one obligation checked while elaborating an `interface
// module` — the name, its role, and the type AS STATED in the interface
// source. The cache writer seals the STATED spelling (the public
// contract), not the implementation's defeq-equal spelling, so a
// construction-side reduced form can never re-enter through the seal.
struct CheckedInterfaceObligation {
    std::string name;
    SurfaceAxiomDeclaration::InterfaceRole role;
    ExpressionPointer statedType;
};

void elaborateModule(const SurfaceModule& module,
                     Environment& environment,
                     std::vector<std::string>& importedModules,
                     bool reportRedundantBy = false,
                     bool reportRedundantCalcSteps = false,
                     bool reportRedundantByNonEq = false,
                     bool reportUnusedNames = false,
                     std::function<const LibrarySearchIndex*()>
                         librarySearchProvider = nullptr,
                     int goalAtLine = -1,
                     std::string* goalAtReport = nullptr,
                     std::vector<CheckedInterfaceObligation>*
                         interfaceObligations = nullptr);
