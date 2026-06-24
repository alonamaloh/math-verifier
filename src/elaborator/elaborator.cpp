#include "elaborator/internal.hpp"

ExpressionPointer elaborateExpression(const SurfaceExpression& expression,
                                       const Environment& environment) {
    Environment local = environment;  // can't pass const Environment&
    std::vector<std::string> imports;
    Elaborator elaborator(local, imports);
    return elaborator.runExpression(expression);
}

void elaborateModule(const SurfaceModule& module,
                     Environment& environment,
                     std::vector<std::string>& importedModules,
                     bool reportRedundantBy,
                     bool reportRedundantCalcSteps,
                     bool reportRedundantByNonEq,
                     bool reportUnusedNames,
                     std::function<const LibrarySearchIndex*()>
                         librarySearchProvider,
                     int goalAtLine,
                     std::string* goalAtReport) {
    Elaborator elaborator(environment, importedModules);
    elaborator.setReportRedundantBy(reportRedundantBy);
    elaborator.setReportRedundantCalcSteps(reportRedundantCalcSteps);
    elaborator.setReportRedundantByNonEq(reportRedundantByNonEq);
    elaborator.setReportUnusedNames(reportUnusedNames);
    // Opt-in cast-redundancy polishing pass (expensive: each cast operand
    // triggers a speculative re-elaboration). Env-var gated like the other
    // MATH_* diagnostics: `MATH_CHECK_REDUNDANT_CASTS=1`.
    elaborator.setReportRedundantCasts(
        std::getenv("MATH_CHECK_REDUNDANT_CASTS") != nullptr);
    elaborator.setLibrarySearchProvider(std::move(librarySearchProvider));
    elaborator.setGoalAtLine(goalAtLine);
    if (!goalAtReport) {
        elaborator.runModule(module);
        return;
    }
    // The queried goal is wanted even when elaboration fails past the
    // query point — "what was I proving where I'm stuck" is the use case.
    try {
        elaborator.runModule(module);
    } catch (...) {
        *goalAtReport = elaborator.formatGoalAtReport();
        throw;
    }
    *goalAtReport = elaborator.formatGoalAtReport();
}
