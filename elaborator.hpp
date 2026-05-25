#pragma once

#include "expression.hpp"
#include "kernel.hpp"
#include "level.hpp"
#include "surface.hpp"

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
void elaborateModule(const SurfaceModule& module,
                     Environment& environment,
                     std::vector<std::string>& importedModules,
                     bool reportRedundantBy = false,
                     bool reportRedundantCalcSteps = false);
