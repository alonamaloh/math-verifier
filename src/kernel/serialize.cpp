#include "kernel/serialize.hpp"

#include "kernel/kernel.hpp"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <unordered_map>
#include <variant>
#include <vector>

namespace {

constexpr uint32_t cacheMagic = 0x5648544DU;   // "MTHV" little-endian.
// Format version 2 adds the operator-registry and overload-alias
// sections at the tail of the file. Files written by version 1 readers
// are not accepted; on cache-version mismatch the kernel rebuilds.
// Version 5 adds the congruence-under-binder registry section.
// Version 7 makes expression serialization DAG-aware: tag 8 is a
// backreference to an already-(de)serialized node, indexed in
// post-order of completion. Before this, the in-memory expression DAG
// was expanded to a TREE on disk — Test/ring_test.mathv was 574 MB of
// which gzip kept 17 (every shared subterm of the ring certificate
// written out in full at every occurrence).
// Version 10 adds the fold-operation registry section at the tail.
constexpr uint32_t cacheVersion = 11;

// ----------------------------------------------------------------------
// Low-level primitives. We assume little-endian (the platforms we
// target — x86_64 and Apple Silicon — are LE).

struct Writer {
    std::ofstream& stream;
    // DAG-aware expression dedup: structural-hash buckets of already
    // emitted nodes -> their post-order indices. Scoped to one file.
    std::unordered_map<uint64_t,
                       std::vector<std::pair<ExpressionPointer, uint32_t>>>
        emittedExpressions;
    uint32_t nextExpressionIndex = 0;
    void writeBytes(const void* data, size_t bytes) {
        stream.write(static_cast<const char*>(data),
                     static_cast<std::streamsize>(bytes));
        if (!stream) {
            throw SerializationError("write failed");
        }
    }
    void writeU8(uint8_t value)   { writeBytes(&value, 1); }
    void writeU32(uint32_t value) { writeBytes(&value, 4); }
    void writeI32(int32_t value)  { writeBytes(&value, 4); }
    void writeU64(uint64_t value) { writeBytes(&value, 8); }
    void writeString(const std::string& text) {
        writeU32(static_cast<uint32_t>(text.size()));
        if (!text.empty()) writeBytes(text.data(), text.size());
    }
};

struct Reader {
    std::ifstream& stream;
    // Post-order table of every decoded expression node; backreference
    // tags index into it. Scoped to one file.
    std::vector<ExpressionPointer> decodedExpressions;
    void readBytes(void* data, size_t bytes) {
        stream.read(static_cast<char*>(data),
                    static_cast<std::streamsize>(bytes));
        if (stream.gcount() != static_cast<std::streamsize>(bytes)) {
            throw SerializationError("short read");
        }
    }
    uint8_t readU8() {
        uint8_t value = 0; readBytes(&value, 1); return value;
    }
    uint32_t readU32() {
        uint32_t value = 0; readBytes(&value, 4); return value;
    }
    int32_t readI32() {
        int32_t value = 0; readBytes(&value, 4); return value;
    }
    uint64_t readU64() {
        uint64_t value = 0; readBytes(&value, 8); return value;
    }
    std::string readString() {
        uint32_t length = readU32();
        std::string result(length, '\0');
        if (length > 0) readBytes(result.data(), length);
        return result;
    }
};

// ----------------------------------------------------------------------
// Level serialization. Five variants, one byte tag each.
//
//   0 = LevelConst{value}
//   1 = LevelParam{name}
//   2 = LevelSuccessor{base}
//   3 = LevelMax{left, right}
//   4 = LevelIMax{left, right}

void writeLevel(Writer& writer, LevelPointer level) {
    if (auto* constant = std::get_if<LevelConst>(&level->node)) {
        writer.writeU8(0);
        writer.writeI32(constant->value);
    } else if (auto* parameter = std::get_if<LevelParam>(&level->node)) {
        writer.writeU8(1);
        writer.writeString(parameter->name);
    } else if (auto* succ = std::get_if<LevelSuccessor>(&level->node)) {
        writer.writeU8(2);
        writeLevel(writer, succ->base);
    } else if (auto* maxNode = std::get_if<LevelMax>(&level->node)) {
        writer.writeU8(3);
        writeLevel(writer, maxNode->left);
        writeLevel(writer, maxNode->right);
    } else if (auto* imaxNode = std::get_if<LevelIMax>(&level->node)) {
        writer.writeU8(4);
        writeLevel(writer, imaxNode->left);
        writeLevel(writer, imaxNode->right);
    } else {
        throw SerializationError("writeLevel: unknown variant");
    }
}

LevelPointer readLevel(Reader& reader) {
    uint8_t tag = reader.readU8();
    switch (tag) {
        case 0: return makeLevelConst(reader.readI32());
        case 1: return makeLevelParam(reader.readString());
        case 2: return makeLevelSuccessor(readLevel(reader));
        case 3: {
            auto left = readLevel(reader);
            auto right = readLevel(reader);
            return makeLevelMax(std::move(left), std::move(right));
        }
        case 4: {
            auto left = readLevel(reader);
            auto right = readLevel(reader);
            return makeLevelIMax(std::move(left), std::move(right));
        }
        default:
            throw SerializationError("readLevel: bad tag");
    }
}

// ----------------------------------------------------------------------
// Expression serialization. Eight variants, one byte tag each.
//
//   0 = BoundVariable{deBruijnIndex}
//   1 = FreeVariable{name, origin}      (origin: 0 User, 1 Internal)
//   2 = Sort{level}
//   3 = Pi{displayHint, domain, codomain}
//   4 = Lambda{displayHint, domain, body}
//   5 = Application{function, argument}
//   6 = Constant{name, universeArguments[]}
//   7 = Let{displayHint, type, value, body}

void writeExpression(Writer& writer, ExpressionPointer expression);

// One top-level expression = one dedup scope. Backreferences never
// cross unit boundaries, so a skipping reader (skipExpression, used by
// the lemma-index loader to avoid materialising proof bodies) stays
// aligned: a skipped unit's internal backreferences are skipped with
// it, and the next unit starts a fresh index space on both sides.
void writeExpressionUnit(Writer& writer, ExpressionPointer expression) {
    writer.emittedExpressions.clear();
    writer.nextExpressionIndex = 0;
    writeExpression(writer, expression);
}

void writeExpression(Writer& writer, ExpressionPointer expression) {
    // DAG-awareness: if a structurally identical node was already
    // written, emit a backreference instead of re-expanding the whole
    // subtree (tag 8 + post-order index). The lookup keys on the
    // precomputed structural hash, confirmed by structurallyEqual.
    {
        auto bucket = writer.emittedExpressions.find(expression->hash);
        if (bucket != writer.emittedExpressions.end()) {
            for (const auto& [seen, index] : bucket->second) {
                if (seen.get() == expression.get()
                    || structurallyEqual(seen, expression)) {
                    writer.writeU8(8);
                    writer.writeU32(index);
                    return;
                }
            }
        }
    }
    if (auto* boundVar = std::get_if<BoundVariable>(&expression->node)) {
        writer.writeU8(0);
        writer.writeI32(boundVar->deBruijnIndex);
    } else if (auto* freeVar = std::get_if<FreeVariable>(&expression->node)) {
        writer.writeU8(1);
        writer.writeString(freeVar->name);
        writer.writeU8(freeVar->origin == FreeVariableOrigin::User ? 0 : 1);
    } else if (auto* sort = std::get_if<Sort>(&expression->node)) {
        writer.writeU8(2);
        writeLevel(writer, sort->level);
    } else if (auto* piNode = std::get_if<Pi>(&expression->node)) {
        writer.writeU8(3);
        writer.writeString(piNode->displayHint);
        writeExpression(writer, piNode->domain);
        writeExpression(writer, piNode->codomain);
    } else if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        writer.writeU8(4);
        writer.writeString(lambda->displayHint);
        writeExpression(writer, lambda->domain);
        writeExpression(writer, lambda->body);
    } else if (auto* application = std::get_if<Application>(&expression->node)) {
        writer.writeU8(5);
        writeExpression(writer, application->function);
        writeExpression(writer, application->argument);
    } else if (auto* constant = std::get_if<Constant>(&expression->node)) {
        writer.writeU8(6);
        writer.writeString(constant->name);
        writer.writeU32(
            static_cast<uint32_t>(constant->universeArguments.size()));
        for (const auto& level : constant->universeArguments) {
            writeLevel(writer, level);
        }
    } else if (auto* letNode = std::get_if<Let>(&expression->node)) {
        writer.writeU8(7);
        writer.writeString(letNode->displayHint);
        writeExpression(writer, letNode->type);
        writeExpression(writer, letNode->value);
        writeExpression(writer, letNode->body);
    } else {
        throw SerializationError("writeExpression: unknown variant");
    }
    // Register AFTER the children (post-order), so writer and reader
    // assign identical indices.
    writer.emittedExpressions[expression->hash].emplace_back(
        expression, writer.nextExpressionIndex++);
}

// Recursion depth bound for the deserializer. A cache file with a very
// deep expression chain (a runaway proof certificate — e.g. the 574 MB
// ring_test.mathv incident, ~83k nested Applications) would otherwise
// recurse the reader to a stack-overflow SIGSEGV. Failing cleanly names
// the real problem: such a file should never have been written.
constexpr int maxReadExpressionDepth = 20000;
thread_local int readExpressionDepth = 0;

ExpressionPointer readExpression(Reader& reader);
ExpressionPointer readExpressionNode(Reader& reader, uint8_t tag);

ExpressionPointer readExpressionUnit(Reader& reader) {
    reader.decodedExpressions.clear();
    return readExpression(reader);
}

ExpressionPointer readExpression(Reader& reader) {
    struct DepthGuard {
        DepthGuard() {
            if (++readExpressionDepth > maxReadExpressionDepth) {
                --readExpressionDepth;
                throw SerializationError(
                    "readExpression: expression nesting exceeds "
                    + std::to_string(maxReadExpressionDepth)
                    + " — the cache file contains a pathologically deep "
                      "term (likely an exploded proof certificate); "
                      "rebuild it, or fix whatever wrote it");
            }
        }
        ~DepthGuard() { --readExpressionDepth; }
    } depthGuard;
    uint8_t tag = reader.readU8();
    if (tag == 8) {
        uint32_t index = reader.readU32();
        if (index >= reader.decodedExpressions.size()) {
            throw SerializationError(
                "readExpression: backreference index out of range");
        }
        return reader.decodedExpressions[index];
    }
    ExpressionPointer decoded = readExpressionNode(reader, tag);
    // Post-order registration mirrors the writer's index assignment.
    reader.decodedExpressions.push_back(decoded);
    return decoded;
}

ExpressionPointer readExpressionNode(Reader& reader, uint8_t tag) {
    switch (tag) {
        case 0: return makeBoundVariable(reader.readI32());
        case 1: {
            std::string name = reader.readString();
            uint8_t originTag = reader.readU8();
            auto result = makeFreeVariable(std::move(name));
            // Override origin if Internal. The makeFreeVariable hash
            // was computed for User origin, so we recompute it here.
            if (originTag == 1) {
                auto& freeVariable =
                    std::get<FreeVariable>(result->node);
                freeVariable.origin = FreeVariableOrigin::Internal;
                uint64_t nameHash =
                    subtree_hash::hashString(freeVariable.name);
                result->hash = subtree_hash::mix(
                    subtree_hash::mix(
                        subtree_hash::mix(subtree_hash::kSeed,
                                           subtree_hash::kTagFreeVariable),
                        nameHash),
                    static_cast<uint64_t>(FreeVariableOrigin::Internal));
            } else if (originTag != 0) {
                throw SerializationError(
                    "readExpression: bad FreeVariable origin tag");
            }
            return result;
        }
        case 2: return makeSort(readLevel(reader));
        case 3: {
            std::string hint = reader.readString();
            auto domain = readExpression(reader);
            auto codomain = readExpression(reader);
            return makePi(std::move(hint),
                          std::move(domain), std::move(codomain));
        }
        case 4: {
            std::string hint = reader.readString();
            auto domain = readExpression(reader);
            auto body = readExpression(reader);
            return makeLambda(std::move(hint),
                              std::move(domain), std::move(body));
        }
        case 5: {
            auto function = readExpression(reader);
            auto argument = readExpression(reader);
            return makeApplication(std::move(function),
                                   std::move(argument));
        }
        case 6: {
            std::string name = reader.readString();
            uint32_t universeCount = reader.readU32();
            std::vector<LevelPointer> universes;
            universes.reserve(universeCount);
            for (uint32_t i = 0; i < universeCount; ++i) {
                universes.push_back(readLevel(reader));
            }
            return makeConstant(std::move(name), std::move(universes));
        }
        case 7: {
            std::string hint = reader.readString();
            auto type = readExpression(reader);
            auto value = readExpression(reader);
            auto body = readExpression(reader);
            return makeLet(std::move(hint), std::move(type),
                           std::move(value), std::move(body));
        }
        default:
            throw SerializationError("readExpression: bad tag");
    }
}

// Consume exactly the bytes readExpression would, but build NOTHING — no
// node tree is allocated. Used to skip proof BODIES when assembling the
// lemma-suggestion index, which needs only declaration types. Proof terms
// are the bulk of the library's bytes; materialising every one at once is
// what made a single failing-claim suggestion exhaust RAM (and, under
// `make -j16`, take the machine down). Small leaf payloads (strings,
// levels) are read-and-discarded — the win is skipping the deep Pi /
// Lambda / Application / Let spines.
void skipExpression(Reader& reader) {
    uint8_t tag = reader.readU8();
    if (tag == 8) {           // backreference: 4-byte index, no children
        (void)reader.readU32();
        return;
    }
    switch (tag) {
        case 0: reader.readI32(); return;                      // BoundVariable
        case 1: reader.readString(); reader.readU8(); return;  // FreeVariable
        case 2: readLevel(reader); return;                     // Sort
        case 3:                                                // Pi
        case 4:                                                // Lambda
            reader.readString();
            skipExpression(reader);
            skipExpression(reader);
            return;
        case 5:                                                // Application
            skipExpression(reader);
            skipExpression(reader);
            return;
        case 6: {                                              // Constant
            reader.readString();
            uint32_t universeCount = reader.readU32();
            for (uint32_t i = 0; i < universeCount; ++i) readLevel(reader);
            return;
        }
        case 7:                                                // Let
            reader.readString();
            skipExpression(reader);
            skipExpression(reader);
            skipExpression(reader);
            return;
        default:
            throw SerializationError("skipExpression: bad tag");
    }
}

// ----------------------------------------------------------------------
// String-vector helper.

void writeStringVector(Writer& writer, const std::vector<std::string>& strings) {
    writer.writeU32(static_cast<uint32_t>(strings.size()));
    for (const auto& text : strings) writer.writeString(text);
}

std::vector<std::string> readStringVector(Reader& reader) {
    uint32_t count = reader.readU32();
    std::vector<std::string> result;
    result.reserve(count);
    for (uint32_t i = 0; i < count; ++i) {
        result.push_back(reader.readString());
    }
    return result;
}

// ----------------------------------------------------------------------
// Declaration serialization. Five variants:
//
//   0 = Axiom{universeParameters, type}
//   1 = Definition{universeParameters, type, body}
//   2 = Inductive{universeParameters, kind, constructorNames, numParameters}
//   3 = Constructor{universeParameters, inductiveName,
//                   constructorIndex, type}
//   4 = Recursor{universeParameters, inductiveName, type,
//                numConstructors, numParameters, numIndices}

void writeDeclaration(Writer& writer, const Declaration& declaration) {
    if (auto* axiom = std::get_if<Axiom>(&declaration)) {
        writer.writeU8(0);
        writeStringVector(writer, axiom->universeParameters);
        writeExpressionUnit(writer, axiom->type);
        // Cache format v9 adds the `automatic` byte (Axiom + Definition).
        writer.writeU8(axiom->automatic ? 1 : 0);
    } else if (auto* definition = std::get_if<Definition>(&declaration)) {
        writer.writeU8(1);
        writeStringVector(writer, definition->universeParameters);
        writeExpressionUnit(writer, definition->type);
        writeExpressionUnit(writer, definition->body);
        // Cache format v4 adds an opacity byte. Readers of v3 don't
        // read this byte; we bumped cacheVersion to 4 to force a
        // rebuild for cleanliness.
        writer.writeU8(static_cast<uint8_t>(definition->opacity));
        writer.writeU8(definition->automatic ? 1 : 0);  // v9
    } else if (auto* inductive = std::get_if<Inductive>(&declaration)) {
        writer.writeU8(2);
        writeStringVector(writer, inductive->universeParameters);
        writeExpressionUnit(writer, inductive->kind);
        writeStringVector(writer, inductive->constructorNames);
        writer.writeI32(inductive->numParameters);
    } else if (auto* constructor = std::get_if<Constructor>(&declaration)) {
        writer.writeU8(3);
        writeStringVector(writer, constructor->universeParameters);
        writer.writeString(constructor->inductiveName);
        writer.writeI32(constructor->constructorIndex);
        writeExpressionUnit(writer, constructor->type);
    } else if (auto* recursor = std::get_if<Recursor>(&declaration)) {
        writer.writeU8(4);
        writeStringVector(writer, recursor->universeParameters);
        writer.writeString(recursor->inductiveName);
        writeExpressionUnit(writer, recursor->type);
        writer.writeI32(recursor->numConstructors);
        writer.writeI32(recursor->numParameters);
        writer.writeI32(recursor->numIndices);
    } else {
        throw SerializationError("writeDeclaration: unknown variant");
    }
}

Declaration readDeclaration(Reader& reader,
                            bool skipDefinitionBodies = false) {
    uint8_t tag = reader.readU8();
    switch (tag) {
        case 0: {
            Axiom axiom;
            axiom.universeParameters = readStringVector(reader);
            axiom.type = readExpressionUnit(reader);
            axiom.automatic = (reader.readU8() != 0);  // v9
            return axiom;
        }
        case 1: {
            Definition definition;
            definition.universeParameters = readStringVector(reader);
            definition.type = readExpressionUnit(reader);
            if (skipDefinitionBodies) {
                // Lemma-index load: parse past the proof body without
                // building it, then drop to a type-only Axiom. The opacity
                // byte follows the body in the format, so it must still be
                // consumed. Nothing downstream δ-unfolds an Axiom, so the
                // missing body can't cause a wrong result — only the type
                // (all the index matches on) is retained.
                skipExpression(reader);
                reader.readU8();  // opacity byte (discarded)
                Axiom axiom;
                axiom.universeParameters =
                    std::move(definition.universeParameters);
                axiom.type = std::move(definition.type);
                axiom.automatic = (reader.readU8() != 0);  // v9
                return axiom;
            }
            definition.body = readExpressionUnit(reader);
            uint8_t opacityByte = reader.readU8();
            definition.opacity = (opacityByte == 0)
                ? Opacity::Transparent : Opacity::Opaque;
            definition.automatic = (reader.readU8() != 0);  // v9
            return definition;
        }
        case 2: {
            Inductive inductive;
            inductive.universeParameters = readStringVector(reader);
            inductive.kind = readExpressionUnit(reader);
            inductive.constructorNames = readStringVector(reader);
            inductive.numParameters = reader.readI32();
            return inductive;
        }
        case 3: {
            Constructor constructor;
            constructor.universeParameters = readStringVector(reader);
            constructor.inductiveName = reader.readString();
            constructor.constructorIndex = reader.readI32();
            constructor.type = readExpressionUnit(reader);
            return constructor;
        }
        case 4: {
            Recursor recursor;
            recursor.universeParameters = readStringVector(reader);
            recursor.inductiveName = reader.readString();
            recursor.type = readExpressionUnit(reader);
            recursor.numConstructors = reader.readI32();
            recursor.numParameters = reader.readI32();
            recursor.numIndices = reader.readI32();
            return recursor;
        }
        default:
            throw SerializationError("readDeclaration: bad tag");
    }
}

} // namespace

// ----------------------------------------------------------------------
// Public API.

void writeCacheFile(const std::string& path, const CacheContents& contents) {
    std::ofstream output(path, std::ios::binary | std::ios::trunc);
    if (!output) {
        throw SerializationError("cannot open for write: " + path);
    }
    Writer writer{output, {}, 0};
    writer.writeU32(cacheMagic);
    writer.writeU32(cacheVersion);
    writer.writeString(contents.sourcePath);
    writer.writeU64(contents.sourceHash);
    writer.writeString(contents.moduleName);
    writer.writeString(contents.implementsName);
    writer.writeU32(static_cast<uint32_t>(contents.dependencies.size()));
    for (const auto& dependency : contents.dependencies) {
        writer.writeString(dependency.moduleName);
        writer.writeString(dependency.cachePath);
        writer.writeU64(dependency.sourceHash);
    }
    writer.writeU32(static_cast<uint32_t>(contents.declarations.size()));
    for (const auto& [name, declaration] : contents.declarations) {
        writer.writeString(name);
        writeDeclaration(writer, declaration);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.implicitArgumentCounts.size()));
    for (const auto& [name, count] : contents.implicitArgumentCounts) {
        writer.writeString(name);
        writer.writeI32(count);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.operatorRegistrations.size()));
    for (const auto& entry : contents.operatorRegistrations) {
        writer.writeString(entry.operatorSymbol);
        writer.writeString(entry.leftTypeName);
        writer.writeString(entry.rightTypeName);
        writer.writeString(entry.functionName);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.overloadRegistrations.size()));
    for (const auto& entry : contents.overloadRegistrations) {
        writer.writeString(entry.aliasName);
        writer.writeString(entry.functionName);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.congruenceRegistrations.size()));
    for (const auto& entry : contents.congruenceRegistrations) {
        writer.writeString(entry.functionName);
        writer.writeString(entry.lemmaName);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.coercionRegistrations.size()));
    for (const auto& entry : contents.coercionRegistrations) {
        writer.writeString(entry.sourceTypeName);
        writer.writeString(entry.targetTypeName);
        writer.writeU32(static_cast<uint32_t>(entry.chain.size()));
        for (const auto& funcName : entry.chain) {
            writer.writeString(funcName);
        }
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.instanceRegistrations.size()));
    for (const auto& entry : contents.instanceRegistrations) {
        writer.writeString(entry.structureName);
        writer.writeString(entry.carrierName);
        writer.writeString(entry.termName);
        writer.writeU32(static_cast<uint32_t>(entry.parameterCount));
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.bundleRegistrations.size()));
    for (const auto& entry : contents.bundleRegistrations) {
        writer.writeString(entry.structureName);
        writer.writeString(entry.carrierName);
        writer.writeString(entry.termName);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.forgetfulRegistrations.size()));
    for (const auto& entry : contents.forgetfulRegistrations) {
        writer.writeString(entry.conclusionStructureName);
        writer.writeString(entry.termName);
        writer.writeU32(static_cast<uint32_t>(entry.leadingImplicitCount));
        writer.writeU32(static_cast<uint32_t>(entry.premiseIndex));
        writer.writeString(entry.premiseStructureName);
    }
    writer.writeU32(
        static_cast<uint32_t>(contents.foldOperationRegistrations.size()));
    for (const auto& entry : contents.foldOperationRegistrations) {
        writer.writeString(entry.operatorSymbol);
        writer.writeString(entry.carrierName);
        writer.writeString(entry.operationName);
        writer.writeString(entry.identityName);
        writer.writeString(entry.witnessName);
    }
    if (!output) {
        throw SerializationError("write failed (final flush): " + path);
    }
}

CacheContents readCacheFile(const std::string& path,
                            bool skipDefinitionBodies) {
    std::ifstream input(path, std::ios::binary);
    if (!input) {
        throw SerializationError("cannot open for read: " + path);
    }
    Reader reader{input, {}};
    uint32_t magic = reader.readU32();
    if (magic != cacheMagic) {
        throw SerializationError("bad magic in " + path);
    }
    uint32_t version = reader.readU32();
    if (version != cacheVersion) {
        throw SerializationError(
            "unsupported cache version in " + path
            + " (got " + std::to_string(version)
            + ", expected " + std::to_string(cacheVersion) + ")");
    }
    CacheContents contents;
    contents.sourcePath = reader.readString();
    contents.sourceHash = reader.readU64();
    contents.moduleName = reader.readString();
    contents.implementsName = reader.readString();
    uint32_t dependencyCount = reader.readU32();
    contents.dependencies.reserve(dependencyCount);
    for (uint32_t i = 0; i < dependencyCount; ++i) {
        CachedDependency dependency;
        dependency.moduleName = reader.readString();
        dependency.cachePath = reader.readString();
        dependency.sourceHash = reader.readU64();
        contents.dependencies.push_back(std::move(dependency));
    }
    uint32_t declarationCount = reader.readU32();
    contents.declarations.reserve(declarationCount);
    for (uint32_t i = 0; i < declarationCount; ++i) {
        std::string name = reader.readString();
        Declaration declaration =
            readDeclaration(reader, skipDefinitionBodies);
        contents.declarations.emplace_back(std::move(name),
                                            std::move(declaration));
    }
    uint32_t implicitCount = reader.readU32();
    contents.implicitArgumentCounts.reserve(implicitCount);
    for (uint32_t i = 0; i < implicitCount; ++i) {
        std::string name = reader.readString();
        int count = reader.readI32();
        contents.implicitArgumentCounts.emplace_back(std::move(name), count);
    }
    uint32_t operatorCount = reader.readU32();
    contents.operatorRegistrations.reserve(operatorCount);
    for (uint32_t i = 0; i < operatorCount; ++i) {
        CachedOperatorRegistration entry;
        entry.operatorSymbol = reader.readString();
        entry.leftTypeName = reader.readString();
        entry.rightTypeName = reader.readString();
        entry.functionName = reader.readString();
        contents.operatorRegistrations.push_back(std::move(entry));
    }
    uint32_t overloadCount = reader.readU32();
    contents.overloadRegistrations.reserve(overloadCount);
    for (uint32_t i = 0; i < overloadCount; ++i) {
        CachedOverloadRegistration entry;
        entry.aliasName = reader.readString();
        entry.functionName = reader.readString();
        contents.overloadRegistrations.push_back(std::move(entry));
    }
    uint32_t congruenceCount = reader.readU32();
    contents.congruenceRegistrations.reserve(congruenceCount);
    for (uint32_t i = 0; i < congruenceCount; ++i) {
        CachedCongruenceRegistration entry;
        entry.functionName = reader.readString();
        entry.lemmaName = reader.readString();
        contents.congruenceRegistrations.push_back(std::move(entry));
    }
    uint32_t coercionCount = reader.readU32();
    contents.coercionRegistrations.reserve(coercionCount);
    for (uint32_t i = 0; i < coercionCount; ++i) {
        CachedCoercionRegistration entry;
        entry.sourceTypeName = reader.readString();
        entry.targetTypeName = reader.readString();
        uint32_t chainLength = reader.readU32();
        entry.chain.reserve(chainLength);
        for (uint32_t j = 0; j < chainLength; ++j) {
            entry.chain.push_back(reader.readString());
        }
        contents.coercionRegistrations.push_back(std::move(entry));
    }
    uint32_t instanceCount = reader.readU32();
    contents.instanceRegistrations.reserve(instanceCount);
    for (uint32_t i = 0; i < instanceCount; ++i) {
        CachedInstanceRegistration entry;
        entry.structureName = reader.readString();
        entry.carrierName = reader.readString();
        entry.termName = reader.readString();
        entry.parameterCount = static_cast<int>(reader.readU32());
        contents.instanceRegistrations.push_back(std::move(entry));
    }
    uint32_t bundleCount = reader.readU32();
    contents.bundleRegistrations.reserve(bundleCount);
    for (uint32_t i = 0; i < bundleCount; ++i) {
        CachedBundleRegistration entry;
        entry.structureName = reader.readString();
        entry.carrierName = reader.readString();
        entry.termName = reader.readString();
        contents.bundleRegistrations.push_back(std::move(entry));
    }
    uint32_t forgetfulCount = reader.readU32();
    contents.forgetfulRegistrations.reserve(forgetfulCount);
    for (uint32_t i = 0; i < forgetfulCount; ++i) {
        CachedForgetfulRegistration entry;
        entry.conclusionStructureName = reader.readString();
        entry.termName = reader.readString();
        entry.leadingImplicitCount = static_cast<int>(reader.readU32());
        entry.premiseIndex = static_cast<int>(reader.readU32());
        entry.premiseStructureName = reader.readString();
        contents.forgetfulRegistrations.push_back(std::move(entry));
    }
    uint32_t foldOperationCount = reader.readU32();
    contents.foldOperationRegistrations.reserve(foldOperationCount);
    for (uint32_t i = 0; i < foldOperationCount; ++i) {
        CachedFoldOperationRegistration entry;
        entry.operatorSymbol = reader.readString();
        entry.carrierName = reader.readString();
        entry.operationName = reader.readString();
        entry.identityName = reader.readString();
        entry.witnessName = reader.readString();
        contents.foldOperationRegistrations.push_back(std::move(entry));
    }
    return contents;
}
