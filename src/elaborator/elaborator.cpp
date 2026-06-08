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
                         librarySearchProvider) {
    Elaborator elaborator(environment, importedModules);
    elaborator.setReportRedundantBy(reportRedundantBy);
    elaborator.setReportRedundantCalcSteps(reportRedundantCalcSteps);
    elaborator.setReportRedundantByNonEq(reportRedundantByNonEq);
    elaborator.setReportUnusedNames(reportUnusedNames);
    elaborator.setLibrarySearchProvider(std::move(librarySearchProvider));
    elaborator.runModule(module);
}
