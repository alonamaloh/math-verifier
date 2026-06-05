// Out-of-line Elaborator method definitions: top-level statement/declaration elaboration (conventions, instances, operators, coercions, axioms, definitions, theorem signatures)
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

void Elaborator::elaborateTopStatement(const SurfaceTopStatement& statement) {
        if (auto* import = std::get_if<SurfaceImportDeclaration>(&statement)) {
            importedModules_.push_back(import->moduleName);
            return;
        }
        if (std::get_if<SurfaceUsingDeclaration>(&statement)) {
            // No-op for v0: notation resolution not implemented yet. Modules
            // must use explicit qualified function calls.
            return;
        }
        if (auto* inductive = std::get_if<SurfaceInductiveDeclaration>(&statement)) {
            elaborateInductive(*inductive);
            return;
        }
        if (auto* axiom = std::get_if<SurfaceAxiomDeclaration>(&statement)) {
            elaborateAxiom(*axiom);
            return;
        }
        if (auto* definition = std::get_if<SurfaceDefinitionDeclaration>(&statement)) {
            elaborateDefinition(*definition);
            return;
        }
        if (auto* op = std::get_if<SurfaceOperatorDeclaration>(&statement)) {
            elaborateOperatorDeclaration(*op);
            return;
        }
        if (auto* ov = std::get_if<SurfaceOverloadDeclaration>(&statement)) {
            elaborateOverloadDeclaration(*ov);
            return;
        }
        if (auto* cong =
                std::get_if<SurfaceCongruenceDeclaration>(&statement)) {
            elaborateCongruenceDeclaration(*cong);
            return;
        }
        if (auto* coercion =
                std::get_if<SurfaceCoercionDeclaration>(&statement)) {
            elaborateCoercionDeclaration(*coercion);
            return;
        }
        if (auto* convention =
                std::get_if<SurfaceConventionDeclaration>(&statement)) {
            elaborateConventionDeclaration(*convention);
            return;
        }
        if (auto* instance =
                std::get_if<SurfaceInstanceDeclaration>(&statement)) {
            elaborateInstanceDeclaration(*instance);
            return;
        }
        throw ElaborateError("unhandled top-level statement variant");
    }

void Elaborator::elaborateConventionDeclaration(
        const SurfaceConventionDeclaration& declaration) {
        ConventionEntry entry;
        entry.type = declaration.type;
        entry.propositions = declaration.propositions;
        // Each name shares the same type and propositions. The names
        // CO-DEPEND when a single declaration uses more than one of
        // them: if a theorem mentions both `p` and `q` from
        // `convention p q : Natural with Natural.is_prime(p)`, then the
        // primality binder only fires once (on `p`'s convention entry).
        // We register the same entry under each name; the prepending
        // logic deduplicates side-condition expressions by surface
        // syntax (close enough for v1).
        for (const auto& name : declaration.names) {
            if (conventionRegistry_.count(name) > 0) {
                throw ElaborateError(
                    "convention name '" + name
                    + "' is already registered");
            }
            conventionRegistry_[name] = entry;
        }
    }

void Elaborator::elaborateInstanceDeclaration(
        const SurfaceInstanceDeclaration& declaration) {
        Frame frame(*this, "instance '" + declaration.name + "'");
        const Declaration* decl = environment_.lookup(declaration.name);
        if (!decl) {
            throwElaborate("instance: unknown name '"
                           + declaration.name + "'");
        }
        ExpressionPointer type = declarationType(*decl);
        if (!type) {
            throwElaborate("instance '" + declaration.name
                           + "': could not determine its type");
        }
        // Strip any leading value-parameter Pis (e.g. `(modulus : Natural)`
        // for `IntegerMod`'s instances). What remains is the structure
        // application `Struct(Carrier(params…), ops…)`, whose argument
        // sub-terms reference the stripped parameters as (now dangling)
        // BoundVariables — fine for head extraction, and the resolution
        // site re-instantiates the parameters from the call's carrier.
        ExpressionPointer structureBody = type;
        int parameterCount = 0;
        while (auto* pi = std::get_if<Pi>(&structureBody->node)) {
            structureBody = pi->codomain;
            ++parameterCount;
        }
        std::string structureName = headConstantName(structureBody);
        // Collect the structure application's arguments (reverse order).
        std::vector<ExpressionPointer> reversedArguments;
        ExpressionPointer cursor = structureBody;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            reversedArguments.push_back(application->argument);
            cursor = application->function;
        }
        if (structureName == "<unknown>" || reversedArguments.empty()) {
            throwElaborate(
                "instance '" + declaration.name + "': its type is not a "
                "structure predicate applied to a carrier (expected e.g. "
                "`IsGroup(Carrier, …)`)");
        }
        // The carrier is the FIRST argument (last collected).
        ExpressionPointer carrierArgument = reversedArguments.back();
        std::string carrierName = headConstantName(carrierArgument);
        if (carrierName == "<unknown>") {
            throwElaborate(
                "instance '" + declaration.name + "': could not determine "
                "the carrier head of its structure type");
        }
        auto key = std::make_tuple(structureName, carrierName);
        auto existing = environment_.canonicalInstanceRegistry.find(key);
        if (existing != environment_.canonicalInstanceRegistry.end()
            && existing->second.termName != declaration.name) {
            throwElaborate(
                "instance ambiguity: (" + structureName + ", "
                + carrierName + ") already has canonical instance '"
                + existing->second.termName + "'; refusing to also "
                "register '" + declaration.name + "' (reject-on-"
                "ambiguity, like the coercion registry)");
        }
        Environment::CanonicalInstance entry;
        entry.termName = declaration.name;
        entry.type = type;
        entry.parameterCount = parameterCount;
        entry.universeParameters = declarationUniverseParameters(*decl);
        environment_.canonicalInstanceRegistry[key] = std::move(entry);
    }

void Elaborator::elaborateOperatorDeclaration(
        const SurfaceOperatorDeclaration& declaration) {
        Frame frame(*this,
            "operator (" + declaration.operatorSymbol + ") on ("
            + declaration.leftTypeName + ", "
            + declaration.rightTypeName + ")");
        const Declaration* functionDecl =
            environment_.lookup(declaration.functionName);
        if (!functionDecl) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName + "' is not in scope");
        }
        // Pull the function's type and verify it's T1 → T2 → R. Peel
        // any leading implicit Pi binders first (declared via `{x : T}`)
        // so the validation sees the explicit operand slots. Wildcard
        // sides (`_`) match anything.
        ExpressionPointer functionType = declarationType(*functionDecl);
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, functionType);
        bool leftWildcard = (declaration.leftTypeName == "_");
        bool rightWildcard = (declaration.rightTypeName == "_");
        int declaredImplicitCount =
            environment_.implicitArgumentCount(declaration.functionName);
        for (int i = 0; i < declaredImplicitCount; ++i) {
            auto* implicitPi = std::get_if<Pi>(&cursor->node);
            if (!implicitPi) break;
            cursor = weakHeadNormalForm(
                environment_, implicitPi->codomain);
        }
        // A postfix operator declaration — `operator (sym) on (T)` —
        // leaves rightTypeName empty. It validates and registers a
        // single-operand dispatch function (one explicit arg of type T).
        bool isPostfix = declaration.rightTypeName.empty();
        auto* leftPi = std::get_if<Pi>(&cursor->node);
        if (!leftPi) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + (isPostfix ? "' must take at least one argument"
                             : "' must take at least two arguments"));
        }
        if (!leftWildcard
            && !typeHasHeadName(leftPi->domain, declaration.leftTypeName)) {
            throwElaborate(
                "operator dispatch function '"
                + declaration.functionName
                + (isPostfix ? "' operand parameter type does not have '"
                             : "' first parameter type does not have '")
                + declaration.leftTypeName + "' as its head");
        }
        if (!isPostfix) {
            ExpressionPointer afterLeft = weakHeadNormalForm(
                environment_, leftPi->codomain);
            auto* rightPi = std::get_if<Pi>(&afterLeft->node);
            if (!rightPi) {
                throwElaborate(
                    "operator dispatch function '"
                    + declaration.functionName
                    + "' must take at least two arguments");
            }
            if (!rightWildcard
                && !typeHasHeadName(rightPi->domain, declaration.rightTypeName)) {
                throwElaborate(
                    "operator dispatch function '"
                    + declaration.functionName
                    + "' second parameter type does not have '"
                    + declaration.rightTypeName + "' as its head");
            }
        }
        auto key = std::make_tuple(declaration.operatorSymbol,
                                     declaration.leftTypeName,
                                     declaration.rightTypeName);
        auto& slot = environment_.operatorRegistry[key];
        if (!slot.empty() && slot != declaration.functionName) {
            throwElaborate(
                "operator '" + declaration.operatorSymbol + "' on ("
                + declaration.leftTypeName + ", "
                + declaration.rightTypeName
                + ") is already registered to '" + slot + "'");
        }
        slot = declaration.functionName;
    }

void Elaborator::elaborateCongruenceDeclaration(
        const SurfaceCongruenceDeclaration& declaration) {
        Frame frame(*this,
            "congruence_under_binder '" + declaration.functionName
            + "' := '" + declaration.lemmaName + "'");
        if (!environment_.lookup(declaration.lemmaName)) {
            throwElaborate(
                "congruence_under_binder target '" + declaration.lemmaName
                + "' is not in scope");
        }
        auto& lemmas =
            environment_.congruenceUnderBinderRegistry[
                declaration.functionName];
        for (const auto& existing : lemmas) {
            if (existing == declaration.lemmaName) {
                return;  // idempotent re-registration
            }
        }
        lemmas.push_back(declaration.lemmaName);
    }

void Elaborator::elaborateOverloadDeclaration(
        const SurfaceOverloadDeclaration& declaration) {
        Frame frame(*this,
            "overload '" + declaration.aliasName + "' := '"
            + declaration.functionName + "'");
        const Declaration* functionDecl =
            environment_.lookup(declaration.functionName);
        if (!functionDecl) {
            throwElaborate(
                "overload target '" + declaration.functionName
                + "' is not in scope");
        }
        // Disallow registering an alias whose name collides with an
        // existing declaration — that would be ambiguous at name lookup.
        if (environment_.lookup(declaration.aliasName) != nullptr) {
            throwElaborate(
                "overload alias '" + declaration.aliasName
                + "' collides with an existing declaration of the same "
                "name; pick a different alias");
        }
        auto& candidates =
            environment_.overloadAliases[declaration.aliasName];
        for (const auto& existing : candidates) {
            if (existing == declaration.functionName) {
                return;  // idempotent re-registration
            }
        }
        candidates.push_back(declaration.functionName);
    }

void Elaborator::elaborateCoercionDeclaration(
        const SurfaceCoercionDeclaration& declaration) {
        Frame frame(*this,
            "coercion (" + declaration.sourceTypeName + ", "
            + declaration.targetTypeName + ")");
        if (declaration.sourceTypeName == declaration.targetTypeName) {
            throwElaborate(
                "coercion source and target must differ (got '"
                + declaration.sourceTypeName + "' on both sides)");
        }
        const Declaration* functionDecl =
            environment_.lookup(declaration.functionName);
        if (!functionDecl) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "' is not in scope");
        }
        // Verify F has type S → T (head Constants match).
        ExpressionPointer functionType = declarationType(*functionDecl);
        ExpressionPointer cursor = weakHeadNormalForm(
            environment_, functionType);
        auto* domainPi = std::get_if<Pi>(&cursor->node);
        if (!domainPi) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "' must take exactly one argument of type '"
                + declaration.sourceTypeName + "'");
        }
        if (!typeHasHeadName(domainPi->domain,
                              declaration.sourceTypeName)) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "': parameter type does not have '"
                + declaration.sourceTypeName + "' as its head");
        }
        if (!typeHasHeadName(domainPi->codomain,
                              declaration.targetTypeName)) {
            throwElaborate(
                "coercion function '" + declaration.functionName
                + "': result type does not have '"
                + declaration.targetTypeName + "' as its head");
        }
        // Compute the transitive closure.
        // For each existing (X, S), add (X, T) = chain_XS + [F].
        // For each existing (T, Y), add (S, Y) = [F] + chain_TY.
        // For each combination, add (X, Y) = chain_XS + [F] + chain_TY.
        // Skip same-source-target entries; reject diamonds.
        using Key = std::tuple<std::string, std::string>;
        std::vector<std::pair<Key, std::vector<std::string>>> additions;
        std::vector<std::string> directChain{declaration.functionName};
        additions.push_back({Key{declaration.sourceTypeName,
                                    declaration.targetTypeName},
                              directChain});
        // Snapshot the existing entries so iteration isn't disturbed.
        std::vector<std::pair<Key, std::vector<std::string>>> snapshot(
            environment_.coercionRegistry.begin(),
            environment_.coercionRegistry.end());
        for (const auto& [key, chain] : snapshot) {
            const auto& [src, tgt] = key;
            // Extend the new direct edge with a suffix that starts at T.
            if (src == declaration.targetTypeName
                && tgt != declaration.sourceTypeName) {
                std::vector<std::string> combined = directChain;
                combined.insert(combined.end(),
                                 chain.begin(), chain.end());
                additions.push_back({Key{declaration.sourceTypeName, tgt},
                                      std::move(combined)});
            }
            // Prefix the new direct edge with a chain that ends at S.
            if (tgt == declaration.sourceTypeName
                && src != declaration.targetTypeName) {
                std::vector<std::string> combined = chain;
                combined.push_back(declaration.functionName);
                additions.push_back({Key{src, declaration.targetTypeName},
                                      std::move(combined)});
                // And the cross-combinations: (src → T → Y) for each
                // existing (T, Y).
                for (const auto& [key2, chain2] : snapshot) {
                    const auto& [src2, tgt2] = key2;
                    if (src2 != declaration.targetTypeName) continue;
                    if (src == tgt2) continue;  // skip A → ... → A
                    std::vector<std::string> three = chain;
                    three.push_back(declaration.functionName);
                    three.insert(three.end(),
                                  chain2.begin(), chain2.end());
                    additions.push_back({Key{src, tgt2},
                                          std::move(three)});
                }
            }
        }
        // Diamond check: for each new key, ensure it's not already
        // present (with any chain). If it is, the user has two distinct
        // paths from the same source to the same target — reject.
        for (const auto& [key, chain] : additions) {
            const auto& [src, tgt] = key;
            if (src == tgt) continue;
            auto existing = environment_.coercionRegistry.find(key);
            if (existing != environment_.coercionRegistry.end()) {
                if (existing->second != chain) {
                    throwElaborate(
                        "coercion diamond: registering ("
                        + declaration.sourceTypeName + ", "
                        + declaration.targetTypeName
                        + ") would create a second path from '"
                        + src + "' to '" + tgt + "'; the existing "
                        "chain is already in the registry");
                }
                // Same chain already there — skip.
                continue;
            }
        }
        for (auto& [key, chain] : additions) {
            const auto& [src, tgt] = key;
            if (src == tgt) continue;
            environment_.coercionRegistry[key] = std::move(chain);
        }
    }

bool Elaborator::typeHasHeadName(ExpressionPointer expressionType,
                           const std::string& expectedName) {
        ExpressionPointer cursor = expressionType;
        while (auto* application =
                   std::get_if<Application>(&cursor->node)) {
            cursor = application->function;
        }
        if (auto* constant = std::get_if<Constant>(&cursor->node)) {
            if (constant->name == expectedName) return true;
        }
        // Fall back to WHNF — e.g., when the parameter type is itself a
        // computation that reduces to a Constant head.
        ExpressionPointer reduced = weakHeadNormalForm(
            environment_, expressionType);
        while (auto* application =
                   std::get_if<Application>(&reduced->node)) {
            reduced = weakHeadNormalForm(environment_,
                                          application->function);
        }
        auto* constant = std::get_if<Constant>(&reduced->node);
        return constant && constant->name == expectedName;
    }

void Elaborator::elaborateAxiom(const SurfaceAxiomDeclaration& declaration) {
        Frame frame(*this, "axiom '" + declaration.name + "'");
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();
        ExpressionPointer type =
            elaborateExpression(*declaration.type, {});
        try {
            addAxiom(environment_, declaration.name,
                     finalUniverseParameters(declaration.universeParameters),
                     std::move(type));
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        // Axiom types are written as `(x : T) → U` or
        // `{x : T} → U` arrow chains in the surface syntax. Count the
        // leading implicit `{…}` binders in the SURFACE type and
        // register them so call-site implicit-argument inference can
        // fire — without this the kernel would see a fully-applied Pi
        // chain and there'd be nowhere to record which leading
        // arguments are meant to be inferred.
        int implicitCount =
            countLeadingImplicitArgumentNamesInType(declaration.type);
        if (implicitCount > 0) {
            environment_.implicitArgumentCounts[declaration.name] =
                implicitCount;
        }
        // Axioms are accepted without proof. The foundational ones live
        // in `library/axioms.math` (module name `axioms`) and are
        // silently approved; an axiom declared in any other module is
        // flagged so we never accidentally introduce a new unproved
        // assumption.
        if (moduleName_ != "axioms") {
            std::cerr << "warning: axiom '" << declaration.name
                      << "' admitted without proof\n";
        }
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

int Elaborator::countLeadingImplicitArgumentNamesInType(
        SurfaceExpressionPointer typeExpression) {
        int count = 0;
        SurfaceExpressionPointer cursor = typeExpression;
        while (auto* pi = std::get_if<SurfacePiType>(&cursor->node)) {
            if (!pi->binder.isImplicit) break;
            count += static_cast<int>(pi->binder.names.size());
            cursor = pi->codomain;
        }
        return count;
    }

bool Elaborator::referencesOtherBoundsBelowThreshold(
        ExpressionPointer expression,
        int threshold,
        int abstractIndex,
        int currentDepth) {
        if (auto* boundVariable =
                std::get_if<BoundVariable>(&expression->node)) {
            int effective =
                boundVariable->deBruijnIndex - currentDepth;
            if (effective < 0) return false;
            if (effective == abstractIndex) return false;
            return effective < threshold;
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesOtherBoundsBelowThreshold(
                       pi->domain, threshold, abstractIndex,
                       currentDepth)
                || referencesOtherBoundsBelowThreshold(
                       pi->codomain, threshold, abstractIndex,
                       currentDepth + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return referencesOtherBoundsBelowThreshold(
                       lambda->domain, threshold, abstractIndex,
                       currentDepth)
                || referencesOtherBoundsBelowThreshold(
                       lambda->body, threshold, abstractIndex,
                       currentDepth + 1);
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return referencesOtherBoundsBelowThreshold(
                       application->function, threshold, abstractIndex,
                       currentDepth)
                || referencesOtherBoundsBelowThreshold(
                       application->argument, threshold, abstractIndex,
                       currentDepth);
        }
        return false;
    }

int Elaborator::countLeadingImplicitArgumentNames(
        const SurfaceDefinitionDeclaration& declaration) {
        int count = 0;
        bool seenExplicit = false;
        for (const auto& binder : declaration.arguments) {
            if (binder.isImplicit) {
                if (seenExplicit) {
                    throw ElaborateError(
                        "declaration '" + declaration.name
                        + "': implicit binders '{x : T}' must precede "
                          "all explicit binders");
                }
                count += static_cast<int>(binder.names.size());
            } else {
                seenExplicit = true;
            }
        }
        return count;
    }

SurfaceDefinitionDeclaration Elaborator::augmentDeclarationWithConventions(
        const SurfaceDefinitionDeclaration& declaration) {
        if (conventionRegistry_.empty()) return declaration;
        std::unordered_set<std::string> userBoundNames;
        for (const auto& binder : declaration.arguments) {
            for (const auto& name : binder.names) {
                userBoundNames.insert(name);
            }
        }
        // We preserve insertion order: a convention is added the first
        // time we see it mentioned. We walk binders' types, the
        // declaration type, the body (if any), and each case body.
        std::vector<std::string> orderedMentioned;
        std::unordered_set<std::string> mentionedSet;
        auto record = [&](const std::string& name) {
            if (userBoundNames.count(name) > 0) return;
            if (conventionRegistry_.count(name) == 0) return;
            if (mentionedSet.insert(name).second) {
                orderedMentioned.push_back(name);
            }
        };
        for (const auto& binder : declaration.arguments) {
            if (binder.type) collectMentionsInSurface(*binder.type, record);
        }
        if (declaration.type) {
            collectMentionsInSurface(*declaration.type, record);
        }
        if (declaration.body) {
            collectMentionsInSurface(*declaration.body, record);
        }
        for (const auto& clause : declaration.cases) {
            for (const auto& pattern : clause.patterns) {
                (void)pattern;
            }
            if (clause.body) collectMentionsInSurface(*clause.body, record);
        }
        if (orderedMentioned.empty()) return declaration;
        // Build prepended binders. For each mentioned convention, push
        // an implicit binder for the name itself, then one implicit
        // binder per side-condition proposition (with an auto-generated
        // anonymous name).
        SurfaceDefinitionDeclaration augmented = declaration;
        std::vector<SurfaceBinder> prepended;
        int propCounter = 0;
        for (const auto& name : orderedMentioned) {
            const auto& entry = conventionRegistry_[name];
            SurfaceBinder nameBinder;
            nameBinder.names = {name};
            nameBinder.type = entry.type;
            nameBinder.isImplicit = true;
            prepended.push_back(nameBinder);
            for (const auto& prop : entry.propositions) {
                SurfaceBinder propBinder;
                propBinder.names = {
                    prop.name.empty()
                        ? ("_convention_h"
                           + std::to_string(propCounter++))
                        : prop.name};
                propBinder.type = prop.proposition;
                propBinder.isImplicit = true;
                prepended.push_back(propBinder);
            }
        }
        augmented.arguments.insert(
            augmented.arguments.begin(),
            prepended.begin(), prepended.end());
        return augmented;
    }

void Elaborator::elaborateDefinition(const SurfaceDefinitionDeclaration& origDecl) {
        OpacityRestoreScope opacityScope(*this);
        SurfaceDefinitionDeclaration augmented =
            augmentDeclarationWithConventions(origDecl);
        const SurfaceDefinitionDeclaration& declaration = augmented;
        // Stage-1: a theorem's proof (body or cases) is skipped; only its
        // statement is elaborated. Covers both the direct-body and the
        // pattern (inductive) forms uniformly — the statement is the
        // declared type either way.
        if (statementsOnly_ && declaration.isTheorem) {
            elaborateTheoremStatementOnly(declaration);
            return;
        }
        if (!declaration.cases.empty()) {
            elaboratePatternMatchDefinition(declaration);
            return;
        }
        Frame frame(*this,
            (declaration.isTheorem ? "theorem '" : "definition '")
            + declaration.name + "'",
            declaration.body ? declaration.body->line : 0,
            declaration.body ? declaration.body->column : 0);
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();

        // Surface form has explicit (a : T) binders before the colon, plus
        // a return type after, plus a body. To register with the kernel:
        //   declared type = (a1 : T1) → (a2 : T2) → ... → returnType
        //   body          = fun (a1 : T1) (a2 : T2) ... => bodyExpression
        // We thread a local-binder list as we elaborate the type and body
        // in parallel, then wrap both with the appropriate Pi / Lambda.
        std::vector<LocalBinder> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            argumentBinders;
        for (const auto& binder : declaration.arguments) {
            ExpressionPointer argumentType =
                elaborateExpression(*binder.type, localBinders);
            for (const auto& name : binder.names) {
                argumentBinders.push_back({name, argumentType});
                localBinders.push_back({name, argumentType});
                if (&name != &binder.names.back()) {
                    argumentType = elaborateExpression(*binder.type,
                                                        localBinders);
                }
            }
        }
        ExpressionPointer returnType =
            elaborateExpression(*declaration.type, localBinders);
        ExpressionPointer bodyExpression;
        try {
            bodyExpression = elaborateExpression(*declaration.body,
                                                  localBinders,
                                                  returnType);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }

        // Diff-inference for non-calc equality coercion at theorem body
        // position: covers `theorem foo : succ(a) = succ(b) := eq` (no
        // explicit congruenceOf wrapper) when `eq : a = b`.
        bodyExpression = coerceToExpectedTypeViaDiff(
            localBinders, bodyExpression, returnType);
        checkRedundantCongruenceOfWrapper(
            declaration.body, localBinders, returnType,
            "theorem body");

        // Build the full declared type and body by wrapping in reverse.
        ExpressionPointer fullType = returnType;
        ExpressionPointer fullBody = bodyExpression;
        for (auto iterator = argumentBinders.rbegin();
             iterator != argumentBinders.rend(); ++iterator) {
            fullType = makePi(iterator->first, iterator->second, fullType);
            fullBody = makeLambda(iterator->first, iterator->second,
                                   fullBody);
        }

        // We are about to move fullType/fullBody into addDefinition. Keep
        // a copy of the type for post-registration algebraic-shape
        // detection.
        ExpressionPointer typeForDetection = fullType;
        // WS1: check authoritatively in the elaborator before deferring to
        // the kernel, so a malformed definition fails as mathematics.
        checkDefinitionWellFormedOrThrow(
            declaration.name, fullType, fullBody,
            declaration.isTheorem ? "theorem" : "definition",
            declaration.isTheorem ? "proof" : "body");
        try {
            addDefinition(environment_, declaration.name,
                          finalUniverseParameters(declaration.universeParameters),
                          std::move(fullType), std::move(fullBody),
                          declaration.opaque
                              ? Opacity::Opaque
                              : Opacity::Transparent);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        int implicitCount =
            countLeadingImplicitArgumentNames(declaration);
        if (implicitCount > 0) {
            environment_.implicitArgumentCounts[declaration.name] =
                implicitCount;
        }
        if (declaration.isTheorem) {
            registerAlgebraicShape(declaration.name, typeForDetection);
        }
        if (declaration.isConstruction) {
            // Record as a canonical constructor. The definition itself is
            // an ordinary transparent definition (already added above); the
            // registry lets `by_representatives` and the printer fold a
            // representative term `mk(make(args…))` back to `Name(args…)`.
            canonicalConstructions_.insert(declaration.name);
        }
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

void Elaborator::elaborateTheoremStatementOnly(
            const SurfaceDefinitionDeclaration& declaration) {
        Frame frame(*this, "theorem '" + declaration.name + "' (statement)",
                    declaration.type ? declaration.type->line : 0,
                    declaration.type ? declaration.type->column : 0);
        currentUniverseParametersOrdered_ = declaration.universeParameters;
        currentUniverseParameters_ = std::set<std::string>(
            declaration.universeParameters.begin(),
            declaration.universeParameters.end());
        currentDeclarationName_ = declaration.name;
        resetAutoBoundState();

        std::vector<LocalBinder> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            argumentBinders;
        for (const auto& binder : declaration.arguments) {
            ExpressionPointer argumentType =
                elaborateExpression(*binder.type, localBinders);
            for (const auto& name : binder.names) {
                argumentBinders.push_back({name, argumentType});
                localBinders.push_back({name, argumentType});
                if (&name != &binder.names.back()) {
                    argumentType = elaborateExpression(*binder.type,
                                                        localBinders);
                }
            }
        }
        ExpressionPointer fullType =
            elaborateExpression(*declaration.type, localBinders);
        for (auto iterator = argumentBinders.rbegin();
             iterator != argumentBinders.rend(); ++iterator) {
            fullType = makePi(iterator->first, iterator->second, fullType);
        }

        environment_.declarations[declaration.name] =
            Definition{finalUniverseParameters(declaration.universeParameters),
                       fullType, makeSort(0), Opacity::Opaque};
        invalidateKernelCaches();
        int implicitCount =
            countLeadingImplicitArgumentNames(declaration);
        if (implicitCount > 0) {
            environment_.implicitArgumentCounts[declaration.name] =
                implicitCount;
        }
        registerAlgebraicShape(declaration.name, fullType);
        currentUniverseParametersOrdered_.clear();
        currentUniverseParameters_.clear();
        currentDeclarationName_.clear();
        resetAutoBoundState();
    }

