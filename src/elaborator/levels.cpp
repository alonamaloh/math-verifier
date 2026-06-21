// Out-of-line Elaborator method definitions: universe-level elaboration.
//
// Part of the elaborator split (see elaborator_internal.hpp): the class is
// declared in the header; each elaborator_*.cpp defines a topical slice of
// its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

LevelPointer Elaborator::elaborateLevel(const SurfaceLevel& level) {
    if (auto* numeric = std::get_if<SurfaceLevelNumeric>(&level.node)) {
        return makeLevelConst(numeric->value);
    }
    if (auto* name = std::get_if<SurfaceLevelName>(&level.node)) {
        if (currentUniverseParameters_.count(name->name) == 0) {
            throw ElaborateError(
                "universe parameter '" + name->name
                + "' is not declared (use .{...} on the declaration "
                "to introduce it)");
        }
        return makeLevelParam(name->name);
    }
    if (auto* maxLevel = std::get_if<SurfaceLevelMax>(&level.node)) {
        return makeLevelMax(elaborateLevel(*maxLevel->left),
                             elaborateLevel(*maxLevel->right));
    }
    if (auto* imaxLevel = std::get_if<SurfaceLevelImax>(&level.node)) {
        return makeLevelIMax(elaborateLevel(*imaxLevel->left),
                              elaborateLevel(*imaxLevel->right));
    }
    if (auto* addLevel = std::get_if<SurfaceLevelAdd>(&level.node)) {
        LevelPointer base = elaborateLevel(*addLevel->base);
        for (int i = 0; i < addLevel->amount; ++i) {
            base = makeLevelSuccessor(std::move(base));
        }
        return base;
    }
    if (std::get_if<SurfaceLevelMeta>(&level.node)) {
        // Bare `Type` in source: generate a fresh universe parameter
        // name and let it be auto-bound to the enclosing declaration.
        return makeLevelParam(freshAutoBoundUniverseName());
    }
    throw ElaborateError("unhandled level variant");
}

std::string Elaborator::freshAutoBoundUniverseName() {
    std::string name =
        "_auto_u_" + std::to_string(metavarCounter_++);
    autoBoundUniverseParameters_.push_back(name);
    currentUniverseParametersOrdered_.push_back(name);
    currentUniverseParameters_.insert(name);
    return name;
}

void Elaborator::resetAutoBoundState() {
    autoBoundUniverseParameters_.clear();
    metavarCounter_ = 0;
}

bool Elaborator::citationLevelIsPlaceholder(
    const LevelPointer& level) const {
    if (citationLevelPlaceholders_.empty()) return false;
    if (auto* parameter = std::get_if<LevelParam>(&level->node)) {
        return citationLevelPlaceholders_.count(parameter->name) > 0;
    }
    return false;
}

std::vector<std::string> Elaborator::finalUniverseParameters(
    const std::vector<std::string>& userDeclared) {
    std::vector<std::string> result = userDeclared;
    for (const auto& name : autoBoundUniverseParameters_) {
        result.push_back(name);
    }
    return result;
}
