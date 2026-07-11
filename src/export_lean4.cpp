// export_lean4.cpp — PLAN_KERNEL_EXPORT Stage 3: the untrusted exporter.
//
// `kernel export-lean4 --output OUT.ndjson ROOT.mathv [ROOT.mathv ...]`
// walks the verified library's FULL caches (.mathv — never the sealed
// .iface views, whose theorem bodies are placeholders) in dependency
// order and emits the lean4export NDJSON format 3.1.0 that external
// Lean-kernel checkers (nanoda) replay. The mapping decisions live in
// docs/kernel-export-quotient-mapping.md and
// docs/kernel-export-axiom-inventory.md; the format facts in
// docs/kernel-export-poc.md §f.
//
// Everything here is OUTSIDE the trusted computing base: a bug in this
// file produces a trail that fails to check (or fails the Stage-4 axiom
// assertion), never a false "verified".

#include "kernel/kernel.hpp"
#include "kernel/serialize.hpp"
#include "elaborator/lemma_search.hpp"  // collectConstantNames

#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <string>
#include <vector>

namespace {

struct ExportError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

// ----------------------------------------------------------------------
// Name mapping (docs/kernel-export-quotient-mapping.md §maps). The
// kernel-coupled names become their Lean equivalents so the checker's
// name-keyed Nat acceleration and recursor re-derivation line up;
// everything else exports under its own name.

std::string mapDeclarationName(const std::string& name) {
    static const std::map<std::string, std::string> fixed = {
        {"Natural", "Nat"},
        {"zero", "Nat.zero"},
        {"successor", "Nat.succ"},
        {"Natural.add", "Nat.add"},
        {"Natural.multiply", "Nat.mul"},
        {"Natural.monus", "Nat.sub"},
        {"Natural.power", "Nat.pow"},
        {"Natural.floor_divide", "Nat.div"},
        {"Natural.modulo", "Nat.mod"},
    };
    auto found = fixed.find(name);
    if (found != fixed.end()) return found->second;
    constexpr const char* recursorSuffix = "_recursor";
    constexpr std::size_t suffixLength = 9;
    if (name.size() > suffixLength
        && name.compare(name.size() - suffixLength, suffixLength,
                        recursorSuffix) == 0) {
        return mapDeclarationName(name.substr(0, name.size() - suffixLength))
               + ".rec";
    }
    return name;
}

// JSON string escaping (RFC 8259 minimal set; UTF-8 passes through).
std::string jsonEscape(const std::string& text) {
    std::string out;
    out.reserve(text.size() + 2);
    for (unsigned char c : text) {
        switch (c) {
            case '"':  out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\b': out += "\\b";  break;
            case '\f': out += "\\f";  break;
            case '\n': out += "\\n";  break;
            case '\r': out += "\\r";  break;
            case '\t': out += "\\t";  break;
            default:
                if (c < 0x20) {
                    char buffer[8];
                    std::snprintf(buffer, sizeof buffer, "\\u%04x", c);
                    out += buffer;
                } else {
                    out += (char)c;
                }
        }
    }
    return out;
}

int countLeadingPis(ExpressionPointer type) {
    int count = 0;
    while (auto* pi = std::get_if<Pi>(&type->node)) {
        type = pi->codomain;
        count++;
    }
    return count;
}

ExpressionPointer piTerminal(ExpressionPointer type) {
    while (auto* pi = std::get_if<Pi>(&type->node)) type = pi->codomain;
    return type;
}

// Peel an application spine: returns head, fills args outermost-first.
ExpressionPointer peelApplications(ExpressionPointer expression,
                                   std::vector<ExpressionPointer>& args) {
    while (auto* application = std::get_if<Application>(&expression->node)) {
        args.push_back(application->argument);
        expression = application->function;
    }
    std::reverse(args.begin(), args.end());
    return expression;
}

// ----------------------------------------------------------------------
// The exporter.

class Lean4Exporter {
public:
    explicit Lean4Exporter(std::ostream& out) : out_(out) {}

    int run(const std::vector<std::string>& rootCachePaths) {
        for (const auto& path : rootCachePaths) loadOrdered(path);
        declareEqInductive();
        emitMetaLine();
        emitInductiveGroup("Eq");
        emitQuotPackage();
        std::set<std::string> inFlight;
        for (const auto& name : orderedNames_) {
            emitWithDependencies(name, inFlight);
        }
        return 0;
    }

private:
    std::ostream& out_;
    Environment environment_;
    // First-seen order across all caches (dependency post-order); the
    // emission pass walks this with a reference-driven DFS, so the
    // order only has to be a reasonable seed, not exact.
    std::vector<std::string> orderedNames_;
    // Names whose ONLY loaded body is a sealed-interface placeholder —
    // reaching one at emission means the implementation cache is
    // missing from the trail.
    std::set<std::string> sealedPlaceholderNames_;
    std::set<std::string> loadedCachePaths_;

    // --- interning state (indices must be continuous; name 0 =
    // anonymous and level 0 = Level.zero are reserved and never
    // written).
    std::map<std::pair<int, std::string>, int> nameComponentIndex_;
    int nextNameIndex_ = 1;
    std::map<std::string, int> levelKeyIndex_;
    int nextLevelIndex_ = 1;
    std::map<std::string, int> exprKeyIndex_;
    int nextExprIndex_ = 0;

    std::set<std::string> emitted_;   // by OUR declaration name
    std::map<std::string, int> definitionHeight_;
    bool bridgesEmitted_ = false;

    // ------------------------------------------------------------------
    // Cache loading: full caches only, dependency post-order, first
    // declaration of a name wins (the implementation module precedes any
    // sealed-interface re-emission in post-order).

    void loadOrdered(std::string cachePath) {
        constexpr const char* ifaceSuffix = ".iface";
        constexpr std::size_t ifaceLength = 6;
        if (cachePath.size() > ifaceLength
            && cachePath.compare(cachePath.size() - ifaceLength, ifaceLength,
                                 ifaceSuffix) == 0) {
            cachePath.resize(cachePath.size() - ifaceLength);
        }
        if (loadedCachePaths_.count(cachePath)) return;
        loadedCachePaths_.insert(cachePath);
        if (!std::filesystem::exists(cachePath)) {
            throw ExportError("full cache not found: " + cachePath
                              + " (run `make -j 16 library` first)");
        }
        CacheContents contents = readCacheFile(cachePath);
        for (const auto& dependency : contents.dependencies) {
            loadOrdered(dependency.cachePath);
        }
        for (const auto& [name, declaration] : contents.declarations) {
            bool placeholder = isSealedPlaceholder(declaration);
            auto existing = environment_.declarations.find(name);
            if (existing != environment_.declarations.end()) {
                // Keep the first REAL declaration; upgrade a sealed
                // stand-in when the implementation shows up later. A
                // sealed interface re-emits obligation theorems as
                // Opaque placeholder-body Definitions and abstract
                // types as bodyless Axioms — a genuine axiom is never
                // shadowed by a same-named non-axiom, so the axiom →
                // non-axiom upgrade only ever fires on that pattern.
                bool existingIsAxiomStandIn =
                    std::holds_alternative<Axiom>(existing->second)
                    && !std::holds_alternative<Axiom>(declaration);
                if ((sealedPlaceholderNames_.count(name) && !placeholder)
                    || existingIsAxiomStandIn) {
                    environment_.declarations[name] =
                        stripOpacity(declaration);
                    if (!placeholder) sealedPlaceholderNames_.erase(name);
                    else sealedPlaceholderNames_.insert(name);
                }
                continue;
            }
            // The trail is fully transparent (opacity is proof-hygiene,
            // not kernel semantics for the export) — and the exporter's
            // own sort inference needs to see through `opaque`
            // definitions exactly like the implementation modules that
            // declared them did.
            environment_.declarations.emplace(name,
                                              stripOpacity(declaration));
            if (placeholder) sealedPlaceholderNames_.insert(name);
            orderedNames_.push_back(name);
        }
    }

    // A D-part sealed interface re-emits obligation theorems with the
    // fixed placeholder body `Sort 0` under `Opacity::Opaque` — the real
    // proof lives in the implementation module's cache.
    static bool isSealedPlaceholder(const Declaration& declaration) {
        auto* definition = std::get_if<Definition>(&declaration);
        return definition && definition->opacity == Opacity::Opaque
            && std::holds_alternative<Sort>(definition->body->node)
            && !std::holds_alternative<Sort>(
                   piTerminal(definition->type)->node);
    }

    static Declaration stripOpacity(const Declaration& declaration) {
        if (auto* definition = std::get_if<Definition>(&declaration)) {
            Definition transparent = *definition;
            transparent.opacity = Opacity::Transparent;
            return transparent;
        }
        return declaration;
    }

    // ------------------------------------------------------------------
    // Interning + line emission.

    int internNameComponents(const std::string& dotted) {
        int prefix = 0;
        std::size_t start = 0;
        while (start <= dotted.size()) {
            std::size_t dot = dotted.find('.', start);
            std::string component = dotted.substr(
                start, dot == std::string::npos ? std::string::npos
                                                : dot - start);
            auto key = std::make_pair(prefix, component);
            auto found = nameComponentIndex_.find(key);
            if (found != nameComponentIndex_.end()) {
                prefix = found->second;
            } else {
                int index = nextNameIndex_++;
                out_ << "{\"in\":" << index << ",\"str\":{\"pre\":" << prefix
                     << ",\"str\":\"" << jsonEscape(component) << "\"}}\n";
                nameComponentIndex_.emplace(key, index);
                prefix = index;
            }
            if (dot == std::string::npos) break;
            start = dot + 1;
        }
        return prefix;
    }

    int nameIndexForDeclaration(const std::string& ourName) {
        return internNameComponents(mapDeclarationName(ourName));
    }

    int nameIndexForBinder(const std::string& hint) {
        if (hint.empty()) return 0;  // anonymous
        return internNameComponents(hint);
    }

    int levelIndex(const LevelPointer& level) {
        if (auto* constant = std::get_if<LevelConst>(&level->node)) {
            if (constant->value == 0) return 0;
            std::string key = "c" + std::to_string(constant->value);
            auto found = levelKeyIndex_.find(key);
            if (found != levelKeyIndex_.end()) return found->second;
            int below = levelIndex(makeLevelConst(constant->value - 1));
            int index = nextLevelIndex_++;
            out_ << "{\"il\":" << index << ",\"succ\":" << below << "}\n";
            levelKeyIndex_.emplace(key, index);
            return index;
        }
        std::string key;
        std::string payload;
        if (auto* parameter = std::get_if<LevelParam>(&level->node)) {
            int nameIdx = internNameComponents(parameter->name);
            key = "p" + std::to_string(nameIdx);
            payload = "\"param\":" + std::to_string(nameIdx);
        } else if (auto* successor =
                       std::get_if<LevelSuccessor>(&level->node)) {
            int base = levelIndex(successor->base);
            key = "s" + std::to_string(base);
            payload = "\"succ\":" + std::to_string(base);
        } else if (auto* maximum = std::get_if<LevelMax>(&level->node)) {
            int left = levelIndex(maximum->left);
            int right = levelIndex(maximum->right);
            key = "m" + std::to_string(left) + "," + std::to_string(right);
            payload = "\"max\":[" + std::to_string(left) + ","
                      + std::to_string(right) + "]";
        } else if (auto* imax = std::get_if<LevelIMax>(&level->node)) {
            int left = levelIndex(imax->left);
            int right = levelIndex(imax->right);
            key = "i" + std::to_string(left) + "," + std::to_string(right);
            payload = "\"imax\":[" + std::to_string(left) + ","
                      + std::to_string(right) + "]";
        } else {
            throw ExportError("unhandled Level variant");
        }
        auto found = levelKeyIndex_.find(key);
        if (found != levelKeyIndex_.end()) return found->second;
        int index = nextLevelIndex_++;
        out_ << "{\"il\":" << index << "," << payload << "}\n";
        levelKeyIndex_.emplace(key, index);
        return index;
    }

    int emitExprLine(const std::string& key, const std::string& payload) {
        auto found = exprKeyIndex_.find(key);
        if (found != exprKeyIndex_.end()) return found->second;
        int index = nextExprIndex_++;
        out_ << "{\"ie\":" << index << "," << payload << "}\n";
        exprKeyIndex_.emplace(key, index);
        return index;
    }

    int exprIndex(const ExpressionPointer& expression) {
        if (auto* bound = std::get_if<BoundVariable>(&expression->node)) {
            return emitExprLine(
                "b" + std::to_string(bound->deBruijnIndex),
                "\"bvar\":" + std::to_string(bound->deBruijnIndex));
        }
        if (auto* freeVariable =
                std::get_if<FreeVariable>(&expression->node)) {
            throw ExportError(
                "closed-declaration check failed: stored expression "
                "contains FreeVariable '" + freeVariable->name + "'");
        }
        if (auto* sort = std::get_if<Sort>(&expression->node)) {
            int level = levelIndex(sort->level);
            return emitExprLine("s" + std::to_string(level),
                                "\"sort\":" + std::to_string(level));
        }
        if (auto* constant = std::get_if<Constant>(&expression->node)) {
            int name = nameIndexForDeclaration(constant->name);
            std::string levels;
            for (const auto& level : constant->universeArguments) {
                if (!levels.empty()) levels += ",";
                levels += std::to_string(levelIndex(level));
            }
            return emitExprLine(
                "c" + std::to_string(name) + "[" + levels + "]",
                "\"const\":{\"name\":" + std::to_string(name)
                    + ",\"us\":[" + levels + "]}");
        }
        if (auto* application = std::get_if<Application>(&expression->node)) {
            int function = exprIndex(application->function);
            int argument = exprIndex(application->argument);
            return emitExprLine(
                "a" + std::to_string(function) + "," + std::to_string(argument),
                "\"app\":{\"fn\":" + std::to_string(function) + ",\"arg\":"
                    + std::to_string(argument) + "}");
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return emitBinderExpr("forallE", "f", pi->displayHint, pi->domain,
                                  pi->codomain);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return emitBinderExpr("lam", "l", lambda->displayHint,
                                  lambda->domain, lambda->body);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            int name = nameIndexForBinder(let->displayHint);
            int type = exprIndex(let->type);
            int value = exprIndex(let->value);
            int body = exprIndex(let->body);
            return emitExprLine(
                "t" + std::to_string(name) + "," + std::to_string(type) + ","
                    + std::to_string(value) + "," + std::to_string(body),
                "\"letE\":{\"name\":" + std::to_string(name) + ",\"type\":"
                    + std::to_string(type) + ",\"value\":"
                    + std::to_string(value) + ",\"body\":"
                    + std::to_string(body) + ",\"nondep\":false}");
        }
        if (auto* literal = std::get_if<NaturalLiteral>(&expression->node)) {
            std::string decimal = naturalValueToString(literal->value);
            return emitExprLine("n" + decimal,
                                "\"natVal\":\"" + decimal + "\"");
        }
        throw ExportError("unhandled Expression variant in exporter");
    }

    int emitBinderExpr(const std::string& tag, const std::string& keyTag,
                       const std::string& hint,
                       const ExpressionPointer& domain,
                       const ExpressionPointer& body) {
        int name = nameIndexForBinder(hint);
        int domainIndex = exprIndex(domain);
        int bodyIndex = exprIndex(body);
        return emitExprLine(
            keyTag + std::to_string(name) + "," + std::to_string(domainIndex)
                + "," + std::to_string(bodyIndex),
            "\"" + tag + "\":{\"name\":" + std::to_string(name)
                + ",\"type\":" + std::to_string(domainIndex) + ",\"body\":"
                + std::to_string(bodyIndex)
                + ",\"binderInfo\":\"default\"}");
    }

    std::string levelParamsJson(const std::vector<std::string>& parameters) {
        std::string out = "[";
        for (const auto& parameter : parameters) {
            if (out.size() > 1) out += ",";
            out += std::to_string(internNameComponents(parameter));
        }
        return out + "]";
    }

    void emitMetaLine() {
        out_ << "{\"meta\":{\"exporter\":{\"name\":\"mathkernel\","
                "\"version\":\"0.1.0\"},"
                "\"lean\":{\"githash\":\"\",\"version\":\"4.31.0\"},"
                "\"format\":{\"version\":\"3.1.0\"}}}\n";
    }

    // ------------------------------------------------------------------
    // Emission driver: intra-module dependency DFS (cache declarations
    // are name-sorted, not insertion-ordered).

    void emitWithDependencies(const std::string& name,
                              std::set<std::string>& inFlight) {
        if (emitted_.count(name)) return;
        auto found = environment_.declarations.find(name);
        if (found == environment_.declarations.end()) {
            throw ExportError("declaration '" + name
                              + "' is referenced but not in any loaded "
                                "cache");
        }
        const Declaration& declaration = found->second;
        // Constructors and recursors are emitted with their inductive's
        // group.
        if (auto* constructor = std::get_if<Constructor>(&declaration)) {
            emitWithDependencies(constructor->inductiveName, inFlight);
            return;
        }
        if (auto* recursor = std::get_if<Recursor>(&declaration)) {
            emitWithDependencies(recursor->inductiveName, inFlight);
            return;
        }
        if (inFlight.count(name)) {
            throw ExportError("declaration dependency cycle at '" + name
                              + "'");
        }
        inFlight.insert(name);
        std::set<std::string> referenced;
        std::set<std::string> groupNames = {name};
        if (auto* axiom = std::get_if<Axiom>(&declaration)) {
            collectConstantNames(axiom->type, referenced);
        } else if (auto* definition = std::get_if<Definition>(&declaration)) {
            collectConstantNames(definition->type, referenced);
            collectConstantNames(definition->body, referenced);
        } else if (auto* inductive = std::get_if<Inductive>(&declaration)) {
            collectConstantNames(inductive->kind, referenced);
            for (const auto& constructorName : inductive->constructorNames) {
                groupNames.insert(constructorName);
                const auto* ctorDeclaration =
                    environment_.lookup(constructorName);
                const auto* ctor = ctorDeclaration
                    ? std::get_if<Constructor>(ctorDeclaration) : nullptr;
                if (!ctor) {
                    throw ExportError("constructor '" + constructorName
                                      + "' missing for inductive '" + name
                                      + "'");
                }
                collectConstantNames(ctor->type, referenced);
            }
            groupNames.insert(name + "_recursor");
        }
        for (const auto& reference : referenced) {
            if (groupNames.count(reference)) continue;
            emitWithDependencies(reference, inFlight);
        }
        emitDeclaration(name, declaration);
        inFlight.erase(name);
    }

    void emitDeclaration(const std::string& name,
                         const Declaration& declaration) {
        if (auto* axiom = std::get_if<Axiom>(&declaration)) {
            if (name.rfind("Internal.sorry", 0) == 0) {
                // Omitted from the trail so any surviving use is a loud
                // dangling-name failure (the axiom-inventory doc).
                emitted_.insert(name);
                return;
            }
            if (name.rfind("Quotient", 0) == 0 && isQuotientPrimitive(name)) {
                emitQuotientWrapper(name, *axiom);
                emitted_.insert(name);
                return;
            }
            int nameIdx = nameIndexForDeclaration(name);
            std::string parameters =
                levelParamsJson(axiom->universeParameters);
            int typeIdx = exprIndex(axiom->type);
            out_ << "{\"axiom\":{\"name\":" << nameIdx
                 << ",\"levelParams\":" << parameters
                 << ",\"type\":" << typeIdx << ",\"isUnsafe\":false}}\n";
            emitted_.insert(name);
            return;
        }
        if (auto* definition = std::get_if<Definition>(&declaration)) {
            // Every sealed-placeholder body must have been upgraded to
            // its implementation's real body during loading.
            if (sealedPlaceholderNames_.count(name)) {
                throw ExportError(
                    "only a sealed placeholder body was loaded for '"
                    + name + "' — implementation cache missing from the "
                    "trail's roots?");
            }
            emitDefinitionOrTheorem(name, definition->universeParameters,
                                    definition->type, definition->body);
            emitted_.insert(name);
            return;
        }
        if (std::holds_alternative<Inductive>(declaration)) {
            emitInductiveGroup(name);
            if (name == "Equality") emitEqualityBridges();
            return;
        }
        throw ExportError("unexpected declaration kind for '" + name + "'");
    }

    bool typeIsProposition(const ExpressionPointer& type) {
        auto sortOfType = weakHeadNormalForm(
            environment_, inferType(environment_, {}, type));
        auto* sort = std::get_if<Sort>(&sortOfType->node);
        if (!sort) return false;
        auto level = levelAsConstant(sort->level);
        return level && *level == 0;
    }

    int definitionHeight(const ExpressionPointer& body) {
        std::set<std::string> referenced;
        collectConstantNames(body, referenced);
        int height = 0;
        for (const auto& reference : referenced) {
            auto found = definitionHeight_.find(reference);
            if (found != definitionHeight_.end()) {
                height = std::max(height, found->second);
            }
        }
        return height + 1;
    }

    void emitDefinitionOrTheorem(const std::string& name,
                                 const std::vector<std::string>& parameters,
                                 const ExpressionPointer& type,
                                 const ExpressionPointer& body,
                                 std::optional<bool> forceTheorem
                                     = std::nullopt) {
        bool isTheorem;
        try {
            isTheorem = forceTheorem ? *forceTheorem
                                     : typeIsProposition(type);
        } catch (const TypeError& error) {
            throw ExportError("cannot classify '" + name
                              + "' as def/thm (sort inference failed: "
                              + error.what() + ")");
        }
        int nameIdx = nameIndexForDeclaration(name);
        std::string parametersJson = levelParamsJson(parameters);
        int typeIdx = exprIndex(type);
        int valueIdx = exprIndex(body);
        if (isTheorem) {
            out_ << "{\"thm\":{\"name\":" << nameIdx << ",\"levelParams\":"
                 << parametersJson << ",\"type\":" << typeIdx
                 << ",\"value\":" << valueIdx << ",\"all\":[" << nameIdx
                 << "]}}\n";
            return;
        }
        int height = definitionHeight(body);
        definitionHeight_[name] = height;
        out_ << "{\"def\":{\"name\":" << nameIdx << ",\"levelParams\":"
             << parametersJson << ",\"type\":" << typeIdx << ",\"value\":"
             << valueIdx << ",\"hints\":{\"regular\":" << height
             << "},\"safety\":\"safe\",\"all\":[" << nameIdx << "]}}\n";
    }

    // ------------------------------------------------------------------
    // Inductive groups (type + constructors + re-derivable recursor with
    // its ι-rules, one NDJSON line — the shape lean4export emits).

    struct ConstructorAnalysis {
        std::string name;
        const Constructor* declaration;
        int numFields = 0;
        // Per field: the field's domain (in the scope of params +
        // earlier fields) and, when recursive, the index arguments of
        // the recursive occurrence (same scope).
        std::vector<ExpressionPointer> fieldDomains;
        std::vector<bool> fieldIsRecursive;
        std::vector<std::vector<ExpressionPointer>> fieldRecursiveIndices;
        std::vector<std::string> fieldHints;
    };

    ConstructorAnalysis analyzeConstructor(const std::string& inductiveName,
                                           const std::string& constructorName,
                                           int numParameters) {
        const auto* lookup = environment_.lookup(constructorName);
        const auto* constructor =
            lookup ? std::get_if<Constructor>(lookup) : nullptr;
        if (!constructor) {
            throw ExportError("missing constructor '" + constructorName
                              + "'");
        }
        ConstructorAnalysis analysis;
        analysis.name = constructorName;
        analysis.declaration = constructor;
        ExpressionPointer walker = constructor->type;
        for (int p = 0; p < numParameters; ++p) {
            auto* pi = std::get_if<Pi>(&walker->node);
            if (!pi) {
                throw ExportError("constructor '" + constructorName
                                  + "' has fewer Pis than parameters");
            }
            walker = pi->codomain;
        }
        while (auto* pi = std::get_if<Pi>(&walker->node)) {
            analysis.fieldDomains.push_back(pi->domain);
            analysis.fieldHints.push_back(pi->displayHint);
            std::vector<ExpressionPointer> args;
            auto head = peelApplications(pi->domain, args);
            bool recursive = false;
            std::vector<ExpressionPointer> recursiveIndices;
            if (auto* constant = std::get_if<Constant>(&head->node);
                constant && constant->name == inductiveName) {
                recursive = true;
                for (std::size_t i = (std::size_t)numParameters;
                     i < args.size(); ++i) {
                    recursiveIndices.push_back(args[i]);
                }
            } else {
                // A nested/reflexive occurrence (the inductive under a
                // Pi or deeper in the field type) would need recursor
                // machinery we do not generate — fail loudly rather
                // than emit a mismatching group.
                std::set<std::string> mentioned;
                collectConstantNames(pi->domain, mentioned);
                if (mentioned.count(inductiveName)) {
                    throw ExportError(
                        "constructor '" + constructorName
                        + "' mentions '" + inductiveName
                        + "' in a non-direct position (reflexive/nested "
                          "inductives are unsupported)");
                }
            }
            analysis.fieldIsRecursive.push_back(recursive);
            analysis.fieldRecursiveIndices.push_back(
                std::move(recursiveIndices));
            walker = pi->codomain;
        }
        analysis.numFields = (int)analysis.fieldDomains.size();
        return analysis;
    }

    // The ι-rule right-hand side for one constructor, in Lean's shape:
    //   λ params. λ motive. λ minors. λ fields.
    //     minor_j fields (recursive calls in field order)
    // Binder types for params/motive/minors are the recursor type's own
    // Pi domains, verbatim; field domains are the constructor's, with
    // external references moved past the motive+minor binders.
    ExpressionPointer buildRecursorRuleRhs(
        const std::string& recursorName, const Recursor& recursor,
        int constructorIndex, const ConstructorAnalysis& analysis) {
        int P = recursor.numParameters;
        int C = recursor.numConstructors;
        int F = analysis.numFields;

        std::vector<ExpressionPointer> outerDomains;   // params, motive, minors
        std::vector<std::string> outerHints;
        {
            ExpressionPointer walker = recursor.type;
            for (int i = 0; i < P + 1 + C; ++i) {
                auto* pi = std::get_if<Pi>(&walker->node);
                if (!pi) {
                    throw ExportError("recursor '" + recursorName
                                      + "' has fewer Pis than expected");
                }
                outerDomains.push_back(pi->domain);
                outerHints.push_back(pi->displayHint);
                walker = pi->codomain;
            }
        }

        std::vector<LevelPointer> recursorLevels;
        for (const auto& parameter : recursor.universeParameters) {
            recursorLevels.push_back(makeLevelParam(parameter));
        }

        // Body: minor_j applied to the fields, then the recursive calls.
        ExpressionPointer body =
            makeBoundVariable(F + (C - 1 - constructorIndex));
        for (int i = 0; i < F; ++i) {
            body = makeApplication(body, makeBoundVariable(F - 1 - i));
        }
        for (int i = 0; i < F; ++i) {
            if (!analysis.fieldIsRecursive[i]) continue;
            ExpressionPointer call =
                makeConstant(recursorName, recursorLevels);
            for (int p = 0; p < P; ++p) {
                call = makeApplication(
                    call, makeBoundVariable(F + C + 1 + (P - 1 - p)));
            }
            call = makeApplication(call, makeBoundVariable(F + C));
            for (int j = 0; j < C; ++j) {
                call = makeApplication(call,
                                       makeBoundVariable(F + (C - 1 - j)));
            }
            for (const auto& indexArgument :
                 analysis.fieldRecursiveIndices[i]) {
                // The argument lives in scope [params, fields<i]; in the
                // body's scope the params sit past the motive+minors and
                // the earlier fields past the later ones.
                ExpressionPointer rebased =
                    shift(indexArgument, C + 1, /*cutoff=*/i);
                rebased = shift(rebased, F - i, /*cutoff=*/0);
                call = makeApplication(call, rebased);
            }
            call = makeApplication(call, makeBoundVariable(F - 1 - i));
            body = makeApplication(body, call);
        }

        // Field lambdas (innermost), then minors, motive, params.
        for (int i = F - 1; i >= 0; --i) {
            ExpressionPointer domain =
                shift(analysis.fieldDomains[i], C + 1, /*cutoff=*/i);
            body = makeLambda(analysis.fieldHints[i], domain, body);
        }
        for (int i = P + 1 + C - 1; i >= 0; --i) {
            body = makeLambda(outerHints[i], outerDomains[i], body);
        }
        return body;
    }

    void emitInductiveGroup(const std::string& name) {
        const auto* lookup = environment_.lookup(name);
        const auto* inductive =
            lookup ? std::get_if<Inductive>(lookup) : nullptr;
        if (!inductive) {
            throw ExportError("missing inductive '" + name + "'");
        }
        std::string recursorName = name + "_recursor";
        const auto* recursorLookup = environment_.lookup(recursorName);
        const auto* recursor = recursorLookup
            ? std::get_if<Recursor>(recursorLookup) : nullptr;
        if (!recursor) {
            throw ExportError("missing recursor '" + recursorName + "'");
        }
        int numParameters = inductive->numParameters;
        int numIndices = countLeadingPis(inductive->kind) - numParameters;
        bool livesInProposition = false;
        {
            auto* sort = std::get_if<Sort>(&piTerminal(inductive->kind)->node);
            auto level = sort ? levelAsConstant(sort->level) : std::nullopt;
            livesInProposition = level && *level == 0;
        }

        std::vector<ConstructorAnalysis> constructors;
        bool isRec = false;
        for (const auto& constructorName : inductive->constructorNames) {
            constructors.push_back(
                analyzeConstructor(name, constructorName, numParameters));
            for (bool recursive : constructors.back().fieldIsRecursive) {
                if (recursive) isRec = true;
            }
        }
        bool kLikeReduction = livesInProposition && constructors.size() == 1
            && constructors[0].numFields == 0;

        int inductiveNameIdx = nameIndexForDeclaration(name);
        std::string uparams = levelParamsJson(inductive->universeParameters);

        std::string ctorNameIndices;
        for (const auto& analysis : constructors) {
            if (!ctorNameIndices.empty()) ctorNameIndices += ",";
            ctorNameIndices +=
                std::to_string(nameIndexForDeclaration(analysis.name));
        }

        std::ostringstream line;
        line << "{\"inductive\":{\"types\":[{\"name\":" << inductiveNameIdx
             << ",\"levelParams\":" << uparams << ",\"type\":"
             << exprIndex(inductive->kind) << ",\"numParams\":"
             << numParameters << ",\"numIndices\":" << numIndices
             << ",\"all\":[" << inductiveNameIdx << "],\"ctors\":["
             << ctorNameIndices << "],\"numNested\":0,\"isRec\":"
             << (isRec ? "true" : "false")
             << ",\"isUnsafe\":false,\"isReflexive\":false}],\"ctors\":[";
        for (std::size_t i = 0; i < constructors.size(); ++i) {
            const auto& analysis = constructors[i];
            if (i) line << ",";
            line << "{\"name\":" << nameIndexForDeclaration(analysis.name)
                 << ",\"levelParams\":"
                 << levelParamsJson(
                        analysis.declaration->universeParameters)
                 << ",\"type\":" << exprIndex(analysis.declaration->type)
                 << ",\"induct\":" << inductiveNameIdx << ",\"cidx\":" << i
                 << ",\"numParams\":" << numParameters << ",\"numFields\":"
                 << analysis.numFields << ",\"isUnsafe\":false}";
        }
        int recursorNameIdx = nameIndexForDeclaration(recursorName);
        line << "],\"recs\":[{\"name\":" << recursorNameIdx
             << ",\"levelParams\":"
             << levelParamsJson(recursor->universeParameters) << ",\"type\":"
             << exprIndex(recursor->type) << ",\"all\":[" << inductiveNameIdx
             << "],\"numParams\":" << numParameters << ",\"numIndices\":"
             << numIndices << ",\"numMotives\":1,\"numMinors\":"
             << recursor->numConstructors << ",\"rules\":[";
        for (std::size_t i = 0; i < constructors.size(); ++i) {
            const auto& analysis = constructors[i];
            if (i) line << ",";
            ExpressionPointer rhs = buildRecursorRuleRhs(
                recursorName, *recursor, (int)i, analysis);
            line << "{\"ctor\":" << nameIndexForDeclaration(analysis.name)
                 << ",\"nfields\":" << analysis.numFields << ",\"rhs\":"
                 << exprIndex(rhs) << "}";
        }
        line << "],\"k\":" << (kLikeReduction ? "true" : "false")
             << ",\"isUnsafe\":false}]}}";
        out_ << line.str() << "\n";

        emitted_.insert(name);
        emitted_.insert(recursorName);
        for (const auto& constructorName : inductive->constructorNames) {
            emitted_.insert(constructorName);
        }
    }

    // ------------------------------------------------------------------
    // The quotient prelude (docs/kernel-export-quotient-mapping.md).

    // A Lean-shaped, Sort-polymorphic `Eq`, declared through our own
    // addInductive so the recursor (and its Lean-layout minor premise +
    // leading motive level) is generated by the same code the library
    // uses — the exporter only renames `Eq_recursor` → `Eq.rec`.
    void declareEqInductive() {
        if (environment_.lookup("Eq")) {
            throw ExportError("the environment already declares 'Eq'");
        }
        auto u = makeLevelParam("u");
        auto kind = makePi("\xce\xb1", makeSort(u),
                           makePi("a", makeBoundVariable(0),
                                  makePi("b", makeBoundVariable(1),
                                         makeSort(0))));
        auto reflType = makePi(
            "\xce\xb1", makeSort(u),
            makePi("a", makeBoundVariable(0),
                   makeApplication(
                       makeApplication(
                           makeApplication(makeConstant("Eq", {u}),
                                           makeBoundVariable(1)),
                           makeBoundVariable(0)),
                       makeBoundVariable(0))));
        addInductive(environment_, "Eq", {"u"}, kind, 2,
                     {{"Eq.refl", reflType}});
    }

    // Emit the four `quot` declarations and the `Quot.sound` axiom with
    // Lean's exact shapes (validated defeq by the checker, so binder
    // styles don't matter — only structure).
    void emitQuotPackage() {
        auto u = makeLevelParam("u");
        auto v = makeLevelParam("v");
        auto B = [](int i) { return makeBoundVariable(i); };
        auto arrow = [](ExpressionPointer domain, ExpressionPointer codomain) {
            return makePi("", std::move(domain), std::move(codomain));
        };
        auto app = [](ExpressionPointer function,
                      std::initializer_list<ExpressionPointer> args) {
            for (const auto& argument : args) {
                function = makeApplication(function, argument);
            }
            return function;
        };

        // Quot : Π (A : Sort u). (A → A → Prop) → Sort u
        auto relationOn = [&](ExpressionPointer carrier0,
                              ExpressionPointer carrier1) {
            return arrow(carrier0, arrow(carrier1, makeSort(0)));
        };
        auto quotType = makePi("A", makeSort(u),
                               arrow(relationOn(B(0), B(1)), makeSort(u)));
        emitQuotLine("Quot", {"u"}, quotType, "type");

        // Quot.mk : Π (A : Sort u) (R : A → A → Prop). A → Quot A R
        auto quotMkType = makePi(
            "A", makeSort(u),
            makePi("R", relationOn(B(0), B(1)),
                   arrow(B(1), app(makeConstant("Quot", {u}),
                                   {B(2), B(1)}))));
        emitQuotLine("Quot.mk", {"u"}, quotMkType, "ctor");

        // Quot.lift : Π (A : Sort u) (R : A → A → Prop) (U : Sort v)
        //               (f : A → U).
        //               (Π (a b : A). R a b → Eq U (f a) (f b))
        //               → Quot A R → U
        auto quotLiftType = makePi(
            "A", makeSort(u),
            makePi(
                "R", relationOn(B(0), B(1)),
                makePi(
                    "U", makeSort(v),
                    makePi(
                        "f", arrow(B(2), B(1)),
                        arrow(
                            makePi(
                                "a", B(3),
                                makePi(
                                    "b", B(4),
                                    arrow(app(B(4), {B(1), B(0)}),
                                          app(makeConstant("Eq", {v}),
                                              {B(4), app(B(3), {B(2)}),
                                               app(B(3), {B(1)})})))),
                            arrow(app(makeConstant("Quot", {u}),
                                      {B(4), B(3)}),
                                  B(3)))))));
        emitQuotLine("Quot.lift", {"u", "v"}, quotLiftType, "lift");

        // Quot.ind : Π (A : Sort u) (R : A → A → Prop)
        //              (motive : Quot A R → Prop).
        //              (Π (a : A). motive (Quot.mk A R a))
        //              → Π (q : Quot A R). motive q
        auto quotIndType = makePi(
            "A", makeSort(u),
            makePi(
                "R", relationOn(B(0), B(1)),
                makePi(
                    "motive",
                    arrow(app(makeConstant("Quot", {u}), {B(1), B(0)}),
                          makeSort(0)),
                    arrow(
                        makePi("a", B(2),
                               app(B(1),
                                   {app(makeConstant("Quot.mk", {u}),
                                        {B(3), B(2), B(0)})})),
                        makePi("q",
                               app(makeConstant("Quot", {u}), {B(3), B(2)}),
                               app(B(2), {B(0)}))))));
        emitQuotLine("Quot.ind", {"u"}, quotIndType, "ind");

        // Quot.sound : Π (A : Sort u) (R : A → A → Prop) (a b : A).
        //                R a b → Eq (Quot A R) (Quot.mk A R a)
        //                           (Quot.mk A R b)
        auto quotSoundType = makePi(
            "A", makeSort(u),
            makePi(
                "R", relationOn(B(0), B(1)),
                makePi(
                    "a", B(1),
                    makePi(
                        "b", B(2),
                        arrow(app(B(2), {B(1), B(0)}),
                              app(makeConstant("Eq", {u}),
                                  {app(makeConstant("Quot", {u}),
                                       {B(4), B(3)}),
                                   app(makeConstant("Quot.mk", {u}),
                                       {B(4), B(3), B(2)}),
                                   app(makeConstant("Quot.mk", {u}),
                                       {B(4), B(3), B(1)})}))))));
        int soundNameIdx = internNameComponents("Quot.sound");
        std::string soundParameters = levelParamsJson({"u"});
        int soundTypeIdx = exprIndex(quotSoundType);
        out_ << "{\"axiom\":{\"name\":" << soundNameIdx
             << ",\"levelParams\":" << soundParameters << ",\"type\":"
             << soundTypeIdx << ",\"isUnsafe\":false}}\n";
    }

    void emitQuotLine(const std::string& name,
                      const std::vector<std::string>& parameters,
                      const ExpressionPointer& type,
                      const std::string& kind) {
        int nameIdx = internNameComponents(name);
        std::string parametersJson = levelParamsJson(parameters);
        int typeIdx = exprIndex(type);
        out_ << "{\"quot\":{\"name\":" << nameIdx << ",\"levelParams\":"
             << parametersJson << ",\"type\":" << typeIdx << ",\"kind\":\""
             << kind << "\"}}\n";
    }

    // ------------------------------------------------------------------
    // The Equality ↔ Eq bridges (emitted right after `Equality`'s group;
    // referenced by the Quotient.* wrappers).

    void emitEqualityBridges() {
        if (bridgesEmitted_) return;
        bridgesEmitted_ = true;
        auto u = makeLevelParam("u");
        auto successorOfU = makeLevelSuccessor(u);
        auto B = [](int i) { return makeBoundVariable(i); };
        auto app = [](ExpressionPointer function,
                      std::initializer_list<ExpressionPointer> args) {
            for (const auto& argument : args) {
                function = makeApplication(function, argument);
            }
            return function;
        };
        auto equalityApp = [&](ExpressionPointer carrier,
                               ExpressionPointer left,
                               ExpressionPointer right) {
            return app(makeConstant("Equality", {u}),
                       {std::move(carrier), std::move(left),
                        std::move(right)});
        };
        auto eqApp = [&](ExpressionPointer carrier, ExpressionPointer left,
                         ExpressionPointer right) {
            return app(makeConstant("Eq", {successorOfU}),
                       {std::move(carrier), std::move(left),
                        std::move(right)});
        };

        // eq_of_equality : Π (A : Type u) (a b : A).
        //                    Equality A a b → Eq A a b
        {
            auto type = makePi(
                "A", makeType(u),
                makePi("a", B(0),
                       makePi("b", B(1),
                              makePi("h", equalityApp(B(2), B(1), B(0)),
                                     eqApp(B(3), B(2), B(1))))));
            // λ A a b h. Equality_recursor.{0, u}
            //     A a (λ b' _. Eq A a b') (Eq.refl A a) b h
            auto motive = makeLambda(
                "b2", B(3),
                makeLambda("h2", equalityApp(B(4), B(3), B(0)),
                           eqApp(B(5), B(4), B(1))));
            auto body = makeLambda(
                "A", makeType(u),
                makeLambda(
                    "a", B(0),
                    makeLambda(
                        "b", B(1),
                        makeLambda(
                            "h", equalityApp(B(2), B(1), B(0)),
                            app(makeConstant("Equality_recursor",
                                             {makeLevelConst(0), u}),
                                {B(3), B(2), motive,
                                 app(makeConstant("Eq.refl", {successorOfU}),
                                     {B(3), B(2)}),
                                 B(1), B(0)})))));
            emitDefinitionOrTheorem("eq_of_equality", {"u"}, type, body,
                                    /*forceTheorem=*/true);
            emitted_.insert("eq_of_equality");
        }

        // equality_of_eq : Π (A : Type u) (a b : A).
        //                    Eq A a b → Equality A a b
        {
            auto type = makePi(
                "A", makeType(u),
                makePi("a", B(0),
                       makePi("b", B(1),
                              makePi("h", eqApp(B(2), B(1), B(0)),
                                     equalityApp(B(3), B(2), B(1))))));
            // λ A a b h. Eq_recursor.{0, u+1}
            //     A a (λ b' _. Equality A a b')
            //     (Equality.reflexivity A a) b h
            auto motive = makeLambda(
                "b2", B(3),
                makeLambda("h2", eqApp(B(4), B(3), B(0)),
                           equalityApp(B(5), B(4), B(1))));
            auto body = makeLambda(
                "A", makeType(u),
                makeLambda(
                    "a", B(0),
                    makeLambda(
                        "b", B(1),
                        makeLambda(
                            "h", eqApp(B(2), B(1), B(0)),
                            app(makeConstant("Eq_recursor",
                                             {makeLevelConst(0),
                                              successorOfU}),
                                {B(3), B(2), motive,
                                 app(makeConstant("reflexivity", {u}),
                                     {B(3), B(2)}),
                                 B(1), B(0)})))));
            emitDefinitionOrTheorem("equality_of_eq", {"u"}, type, body,
                                    /*forceTheorem=*/true);
            emitted_.insert("equality_of_eq");
        }
    }

    // ------------------------------------------------------------------
    // The Quotient.* wrappers: our five axioms become transparent
    // definitions over the quot package, preserving the lift computation
    // rule through δ + the checker's quot reduction.

    bool isQuotientPrimitive(const std::string& name) {
        return name == "Quotient" || name == "Quotient.class_of"
            || name == "Quotient.equivalent_implies_equal"
            || name == "Quotient.lift" || name == "Quotient.induct";
    }

    void emitQuotientWrapper(const std::string& name, const Axiom& axiom) {
        if (!bridgesEmitted_) {
            throw ExportError(
                "Quotient.* reached before Equality's bridges were "
                "emitted");
        }
        auto u = makeLevelParam("u");
        auto v = makeLevelParam("v");
        auto successorOfU = makeLevelSuccessor(u);
        auto successorOfV = makeLevelSuccessor(v);
        auto B = [](int i) { return makeBoundVariable(i); };
        auto app = [](ExpressionPointer function,
                      std::initializer_list<ExpressionPointer> args) {
            for (const auto& argument : args) {
                function = makeApplication(function, argument);
            }
            return function;
        };
        auto arrow = [](ExpressionPointer domain, ExpressionPointer codomain) {
            return makePi("", std::move(domain), std::move(codomain));
        };
        auto relationOn = [&](ExpressionPointer carrier0,
                              ExpressionPointer carrier1) {
            return arrow(std::move(carrier0),
                         arrow(std::move(carrier1), makeSort(0)));
        };

        ExpressionPointer body;
        if (name == "Quotient") {
            // λ (T : Type u) (R). Quot.{u+1} T R
            body = makeLambda(
                "T", makeType(u),
                makeLambda("R", relationOn(B(0), B(1)),
                           app(makeConstant("Quot", {successorOfU}),
                               {B(1), B(0)})));
        } else if (name == "Quotient.class_of") {
            body = makeLambda(
                "T", makeType(u),
                makeLambda(
                    "R", relationOn(B(0), B(1)),
                    makeLambda("x", B(1),
                               app(makeConstant("Quot.mk", {successorOfU}),
                                   {B(2), B(1), B(0)}))));
        } else if (name == "Quotient.equivalent_implies_equal") {
            // λ T R x y proof. equality_of_eq (Quot T R) (mk x) (mk y)
            //                    (Quot.sound proof)
            auto quotTR = app(makeConstant("Quot", {successorOfU}),
                              {B(4), B(3)});
            auto mkOf = [&](int variable) {
                return app(makeConstant("Quot.mk", {successorOfU}),
                           {B(4), B(3), B(variable)});
            };
            body = makeLambda(
                "T", makeType(u),
                makeLambda(
                    "R", relationOn(B(0), B(1)),
                    makeLambda(
                        "x", B(1),
                        makeLambda(
                            "y", B(2),
                            makeLambda(
                                "proof", app(B(2), {B(1), B(0)}),
                                app(makeConstant("equality_of_eq", {u}),
                                    {quotTR, mkOf(2), mkOf(1),
                                     app(makeConstant("Quot.sound",
                                                      {successorOfU}),
                                         {B(4), B(3), B(2), B(1),
                                          B(0)})}))))));
        } else if (name == "Quotient.lift") {
            // λ T R U f respect q. Quot.lift.{u+1, v+1} T R U f
            //     (λ x y r. eq_of_equality U (f x) (f y) (respect x y r)) q
            // Placed at depth 6 (inside T R U f respect q): T=B(5),
            // R=B(4), f=B(2), U=B(3), respect=B(1) shift as x/y/r bind.
            auto convertedRespect = makeLambda(
                "x", B(5),
                makeLambda(
                    "y", B(6),
                    makeLambda(
                        "r", app(B(6), {B(1), B(0)}),
                        app(makeConstant("eq_of_equality", {v}),
                            {B(6), app(B(5), {B(2)}), app(B(5), {B(1)}),
                             app(B(4), {B(2), B(1), B(0)})}))));
            body = makeLambda(
                "T", makeType(u),
                makeLambda(
                    "R", relationOn(B(0), B(1)),
                    makeLambda(
                        "U", makeType(v),
                        makeLambda(
                            "f", arrow(B(2), B(1)),
                            makeLambda(
                                "respect",
                                makePi(
                                    "x", B(3),
                                    makePi(
                                        "y", B(4),
                                        arrow(app(B(4), {B(1), B(0)}),
                                              app(makeConstant("Equality",
                                                               {v}),
                                                  {B(4),
                                                   app(B(3), {B(2)}),
                                                   app(B(3), {B(1)})})))),
                                makeLambda(
                                    "q",
                                    app(makeConstant("Quotient", {u}),
                                        {B(4), B(3)}),
                                    app(makeConstant(
                                            "Quot.lift",
                                            {successorOfU, successorOfV}),
                                        {B(5), B(4), B(3), B(2),
                                         convertedRespect, B(0)})))))));
        } else if (name == "Quotient.induct") {
            // λ T R motive base q. Quot.ind.{u+1} T R motive base q
            body = makeLambda(
                "T", makeType(u),
                makeLambda(
                    "R", relationOn(B(0), B(1)),
                    makeLambda(
                        "motive",
                        arrow(app(makeConstant("Quotient", {u}),
                                  {B(1), B(0)}),
                              makeSort(0)),
                        makeLambda(
                            "base",
                            makePi(
                                "x", B(2),
                                app(B(1),
                                    {app(makeConstant("Quotient.class_of",
                                                      {u}),
                                         {B(3), B(2), B(0)})})),
                            makeLambda(
                                "q",
                                app(makeConstant("Quotient", {u}),
                                    {B(3), B(2)}),
                                app(makeConstant("Quot.ind", {successorOfU}),
                                    {B(4), B(3), B(2), B(1), B(0)}))))));
        } else {
            throw ExportError("unknown quotient primitive '" + name + "'");
        }
        // `Quotient` itself yields a Type; the rest are value-level but
        // only `class_of`/`lift` land outside Prop.
        bool isTheorem = (name == "Quotient.equivalent_implies_equal"
                          || name == "Quotient.induct");
        emitDefinitionOrTheorem(name, axiom.universeParameters, axiom.type,
                                body, isTheorem);
    }
};

}  // namespace

int runExportLean4(int argc, char* argv[]) {
    std::string outputPath;
    std::vector<std::string> rootCachePaths;
    for (int i = 2; i < argc; ++i) {
        std::string argument = argv[i];
        if (argument == "--output") {
            if (i + 1 >= argc) {
                std::cerr << "export-lean4: --output needs a path\n";
                return 1;
            }
            outputPath = argv[++i];
            continue;
        }
        rootCachePaths.push_back(argument);
    }
    if (outputPath.empty() || rootCachePaths.empty()) {
        std::cerr << "usage: kernel export-lean4 --output OUT.ndjson "
                     "ROOT.mathv [ROOT.mathv ...]\n";
        return 1;
    }
    std::ofstream out(outputPath, std::ios::binary);
    if (!out) {
        std::cerr << "export-lean4: cannot open " << outputPath << "\n";
        return 1;
    }
    try {
        Lean4Exporter exporter(out);
        int status = exporter.run(rootCachePaths);
        out.flush();
        if (!out) {
            std::cerr << "export-lean4: write failure for " << outputPath
                      << "\n";
            return 1;
        }
        return status;
    } catch (const std::exception& error) {
        std::cerr << "export-lean4: " << error.what() << "\n";
        return 1;
    }
}
