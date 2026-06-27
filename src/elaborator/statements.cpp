// Out-of-line Elaborator method definitions: top-level statement/declaration elaboration (conventions, instances, operators, coercions, axioms, definitions, theorem signatures)
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

void Elaborator::elaborateTopStatement(const SurfaceTopStatement& statement) {
        try {
            elaborateTopStatementDispatch(statement);
        } catch (const TypeError& kernelError) {
            // A kernel TypeError that reaches this point escaped every
            // wrapping catch below; by now stack unwinding has popped the
            // context frames, so re-throwing it bare would reach the
            // driver, which prints it at 1:1 with no declaration name.
            // Re-anchor it at the declaration being elaborated so that
            // can never happen.
            auto [description, line, column] =
                topStatementErrorAnchor(statement);
            Frame frame(*this, std::move(description), line, column);
            rethrowKernelError(kernelError);
        }
    }

std::tuple<std::string, int, int> Elaborator::topStatementErrorAnchor(
        const SurfaceTopStatement& statement) const {
        if (auto* definition =
                std::get_if<SurfaceDefinitionDeclaration>(&statement)) {
            return {(definition->isTheorem ? "theorem '" : "definition '")
                        + definition->name + "'",
                    definition->type ? definition->type->line : 0,
                    definition->type ? definition->type->column : 0};
        }
        if (auto* axiom = std::get_if<SurfaceAxiomDeclaration>(&statement)) {
            return {"axiom '" + axiom->name + "'",
                    axiom->type ? axiom->type->line : 0,
                    axiom->type ? axiom->type->column : 0};
        }
        if (auto* inductive =
                std::get_if<SurfaceInductiveDeclaration>(&statement)) {
            return {"inductive '" + inductive->name + "'",
                    inductive->kind ? inductive->kind->line : 0,
                    inductive->kind ? inductive->kind->column : 0};
        }
        if (auto* convention =
                std::get_if<SurfaceConventionDeclaration>(&statement)) {
            std::string names;
            for (const auto& name : convention->names) {
                if (!names.empty()) names += " ";
                names += name;
            }
            return {"convention '" + names + "'",
                    convention->type ? convention->type->line : 0,
                    convention->type ? convention->type->column : 0};
        }
        if (auto* instance =
                std::get_if<SurfaceInstanceDeclaration>(&statement)) {
            return {"instance '" + instance->name + "'", 0, 0};
        }
        return {"a top-level declaration", 0, 0};
    }

void Elaborator::elaborateTopStatementDispatch(
        const SurfaceTopStatement& statement) {
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
        // syntax (approximate, but faithful for syntactically equal
        // conditions, which is the case that arises).
        for (const auto& name : declaration.names) {
            if (conventionRegistry_.count(name) > 0) {
                throw ElaborateError(
                    "convention name '" + name
                    + "' is already registered");
            }
            conventionRegistry_[name] = entry;
            conventionOrder_.push_back(name);
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
        // Bundle form: `instance Integer.ring_bundle`, whose type is a bare
        // structure bundle (`Ring`) — not a predicate `IsGroup(Carrier, …)`.
        // Register it as the canonical bundle for its carrier so that an
        // implicit `{r : Ring}` can be solved from a concrete carrier type
        // (the bundled analogue of typeclass resolution). Detected by: no
        // structure-application arguments AND a `<Structure>.carrier`
        // projection in scope. The carrier is read by reducing
        // `<Structure>.carrier(<bundle>)`.
        if (reversedArguments.empty() && structureName != "<unknown>"
            && environment_.lookup(structureName + ".carrier") != nullptr) {
            // Read the carrier as the bundle's `make`-constructor carrier
            // field (via carrierProjectionField) — NOT by WHNF-reducing
            // `<S>.carrier(bundle)`, which would blow past the carrier (e.g.
            // `Integer`) into its own definition body (`Quotient(…)`). We
            // want the carrier's head exactly as it appears in types, so the
            // resolution hooks (which read the raw head) match this key.
            ExpressionPointer carrierField = carrierProjectionField(
                makeApplication(makeConstant(structureName + ".carrier"),
                                makeConstant(declaration.name)));
            std::string carrierName = carrierField
                ? headConstantName(carrierField) : std::string("<unknown>");
            if (carrierName == "<unknown>") {
                throwElaborate(
                    "instance '" + declaration.name + "': could not "
                    "determine the carrier of its bundle type '"
                    + structureName + "'");
            }
            auto key = std::make_tuple(structureName, carrierName);
            auto existing = environment_.canonicalBundleRegistry.find(key);
            if (existing != environment_.canonicalBundleRegistry.end()
                && existing->second != declaration.name) {
                throwElaborate(
                    "instance ambiguity: (" + structureName + ", "
                    + carrierName + ") already has canonical bundle '"
                    + existing->second + "'; refusing to also register '"
                    + declaration.name + "' (reject-on-ambiguity)");
            }
            environment_.canonicalBundleRegistry[key] = declaration.name;
            return;
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
            // Forgetful (derived) instance: the carrier is abstract (a bound
            // variable), but a leading argument is a structure-class premise
            // on that same carrier — e.g. `IsRing.additive_group`, whose
            // `ringProof : IsRing(carrier, …)` premise yields the conclusion
            // `IsGroup(carrier, …)`. Register it under the conclusion
            // structure; resolution applies it to an in-scope premise
            // hypothesis (see `tryForgetfulDerivation`).
            int premiseIndex = -1;
            std::string premiseStructure;
            if (structureHeadIsClass(structureName)) {
                ExpressionPointer walk = type;
                for (int k = 0; k < parameterCount; ++k) {
                    auto* pi = std::get_if<Pi>(&walk->node);
                    if (!pi) break;
                    std::string domainHead = headConstantName(pi->domain);
                    if (domainHead != "<unknown>"
                        && structureHeadIsClass(domainHead)) {
                        premiseIndex = k;
                        premiseStructure = domainHead;
                    }
                    walk = pi->codomain;
                }
            }
            if (premiseIndex >= 0) {
                Environment::ForgetfulInstance forgetful;
                forgetful.termName = declaration.name;
                forgetful.type = type;
                forgetful.leadingImplicitCount = parameterCount;
                forgetful.premiseIndex = premiseIndex;
                forgetful.premiseStructureName = premiseStructure;
                forgetful.universeParameters =
                    declarationUniverseParameters(*decl);
                auto& bucket =
                    environment_.forgetfulInstanceRegistry[structureName];
                bool replaced = false;
                for (auto& existing : bucket) {
                    if (existing.termName == declaration.name) {
                        existing = forgetful;
                        replaced = true;
                        break;
                    }
                }
                if (!replaced) bucket.push_back(std::move(forgetful));
                return;
            }
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

ExpressionPointer Elaborator::applyCoercionChain(
        ExpressionPointer expr, const std::vector<std::string>& chain) {
        for (const auto& functionName : chain) {
            expr = makeApplication(makeConstant(functionName),
                                    std::move(expr));
        }
        return expr;
    }

std::optional<Elaborator::CombineResult> Elaborator::combineOperands(
        const std::string& leftHead, const std::string& rightHead,
        ExpressionPointer leftTypeClosed,
        ExpressionPointer rightTypeClosed) {
        // Homogeneous or untyped-head operands: nothing to reconcile.
        if (leftHead == rightHead) return std::nullopt;
        if (leftHead.empty() || rightHead.empty()) return std::nullopt;
        // `reach(a, b)` — the coercion chain a → b, or nullopt if none.
        // The registry is transitively closed and diamond-free at
        // registration, so a present chain is the unique path.
        auto reach = [&](const std::string& a, const std::string& b)
                -> std::optional<std::vector<std::string>> {
            if (a == b) return std::vector<std::string>{};
            auto it = environment_.coercionRegistry.find(
                std::make_tuple(a, b));
            if (it != environment_.coercionRegistry.end()) {
                return it->second;
            }
            return std::nullopt;
        };
        // Comparable cases — the join is the upper of the two. Covers the
        // entire linear tower (`Rational + Real`, `Natural < Real`, …).
        if (auto chain = reach(leftHead, rightHead)) {
            return CombineResult{rightTypeClosed, std::move(*chain), {}};
        }
        if (auto chain = reach(rightHead, leftHead)) {
            return CombineResult{leftTypeClosed, {}, std::move(*chain)};
        }
        // Incomparable: search for a least common upper bound. Never runs
        // for a chain; present for forward-compat with a branching order
        // (e.g. two completions of the rationals — which correctly yield
        // no common bound, hence nullopt, hence an error at the call).
        std::set<std::string> uppersLeft{leftHead};
        std::set<std::string> uppersRight{rightHead};
        for (const auto& [key, chain] : environment_.coercionRegistry) {
            (void)chain;
            const auto& [src, tgt] = key;
            if (src == leftHead) uppersLeft.insert(tgt);
            if (src == rightHead) uppersRight.insert(tgt);
        }
        std::vector<std::string> commons;
        for (const auto& candidate : uppersLeft) {
            if (uppersRight.count(candidate)) commons.push_back(candidate);
        }
        if (commons.empty()) return std::nullopt;
        std::vector<std::string> least;
        for (const auto& candidate : commons) {
            bool belowAll = true;
            for (const auto& other : commons) {
                if (candidate == other) continue;
                if (!reach(candidate, other)) { belowAll = false; break; }
            }
            if (belowAll) least.push_back(candidate);
        }
        if (least.size() != 1) {
            throwElaborate(
                "ambiguous common type for operands of type '" + leftHead
                + "' and '" + rightHead + "'; cast one explicitly");
        }
        const std::string& target = least.front();
        return CombineResult{makeConstant(target),
                              *reach(leftHead, target),
                              *reach(rightHead, target)};
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
                     std::move(type), declaration.automatic);
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
        // Collect which conventions are needed. A name is needed if the
        // declaration mentions it, OR if an already-needed convention's
        // type / side-conditions mention it (transitive closure): a lemma
        // that names only `multiply` and `ringProof` still needs `carrier`,
        // `add`, `negate`, … because `ringProof`'s `IsRing(carrier, add, …)`
        // type references them. The worklist drives that closure.
        std::unordered_set<std::string> needed;
        std::vector<std::string> worklist;
        auto record = [&](const std::string& name) {
            if (userBoundNames.count(name) > 0) return;
            if (conventionRegistry_.count(name) == 0) return;
            if (needed.insert(name).second) worklist.push_back(name);
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
            if (clause.body) collectMentionsInSurface(*clause.body, record);
        }
        // Transitive closure over convention types and side-conditions.
        auto drainWorklist = [&]() {
            while (!worklist.empty()) {
                std::string name = worklist.back();
                worklist.pop_back();
                const auto& entry = conventionRegistry_[name];
                if (entry.type) collectMentionsInSurface(*entry.type, record);
                for (const auto& prop : entry.propositions) {
                    if (prop.proposition) {
                        collectMentionsInSurface(*prop.proposition, record);
                    }
                }
            }
        };
        drainWorklist();
        // Pervasive bundle-proof conventions. A convention whose type is a
        // structure-class application — `ringProof : IsRing(carrier, add, …)`,
        // head `IsRing` being a `… → Proposition` class — is "in force"
        // throughout the file: writing about its operations means working in
        // that structure. So once the closure has any operation the proof
        // bundles, pull the proof in too (and transitively the rest of the
        // bundle), realising "throughout this file we work in a ring" without
        // the lemma naming `ringProof`. Forward closure pulls a proof's
        // operations but never the proof from an operation (operation types
        // don't mention it); this is the reverse direction, gated to
        // structure-class proofs so ordinary data conventions
        // (`add : carrier → …`) are never auto-included. Fixpoint: a freshly
        // pulled-in proof's operations may license another proof.
        auto surfaceHeadName =
            [](const SurfaceExpression& expr) -> std::string {
            const SurfaceExpression* cursor = &expr;
            while (auto* app =
                       std::get_if<SurfaceApplication>(&cursor->node)) {
                cursor = app->function.get();
            }
            if (auto* identifier =
                    std::get_if<SurfaceIdentifier>(&cursor->node)) {
                return identifier->qualifiedName;
            }
            return "";
        };
        bool addedBundleProof = true;
        while (addedBundleProof) {
            addedBundleProof = false;
            for (const auto& name : conventionOrder_) {
                if (needed.count(name) > 0) continue;
                if (userBoundNames.count(name) > 0) continue;
                const auto& entry = conventionRegistry_[name];
                if (!entry.type) continue;
                std::string head = surfaceHeadName(*entry.type);
                if (head.empty() || !structureHeadIsClass(head)) continue;
                bool referencesNeeded = false;
                collectMentionsInSurface(*entry.type,
                    [&](const std::string& referenced) {
                        if (needed.count(referenced) > 0) {
                            referencesNeeded = true;
                        }
                    });
                if (!referencesNeeded) continue;
                record(name);
                drainWorklist();
                addedBundleProof = true;
            }
        }
        if (needed.empty()) return declaration;
        // Emit in registration order — a valid dependency order, so each
        // prepended binder's type already has its referenced conventions
        // bound ahead of it.
        std::vector<std::string> orderedMentioned;
        for (const auto& name : conventionOrder_) {
            if (needed.count(name) > 0) orderedMentioned.push_back(name);
        }
        // Build prepended binders. For each mentioned convention, push
        // an implicit binder for the name itself, then one implicit
        // binder per side-condition proposition (with an auto-generated
        // anonymous name).
        SurfaceDefinitionDeclaration augmented = declaration;
        std::vector<SurfaceBinder> prepended;
        int propCounter = 0;
        // Side-conditions are shared across the names of one `convention`
        // declaration (`convention p q : … with H(p)` stores the same H on
        // both p and q). Emit each distinct proposition once, keyed by its
        // surface pointer, so a lemma mentioning both names binds H once.
        std::unordered_set<const SurfaceExpression*> emittedProps;
        for (const auto& name : orderedMentioned) {
            const auto& entry = conventionRegistry_[name];
            SurfaceBinder nameBinder;
            nameBinder.names = {name};
            nameBinder.type = entry.type;
            nameBinder.isImplicit = true;
            prepended.push_back(nameBinder);
            for (const auto& prop : entry.propositions) {
                if (prop.proposition
                    && !emittedProps.insert(prop.proposition.get()).second) {
                    continue;
                }
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
        //
        // The statement (binder types + return type) is elaborated under
        // its own frame, anchored at the declared type's source span, and
        // any kernel TypeError is re-thrown here while that frame is still
        // on the stack — otherwise the error unwinds past every frame and
        // prints at 1:1 with no declaration name (the proof body below
        // always had this wrapping; the statement did not).
        std::vector<LocalBinder> localBinders;
        std::vector<std::pair<std::string, ExpressionPointer>>
            argumentBinders;
        ExpressionPointer returnType;
        {
            Frame statementFrame(*this,
                (declaration.isTheorem ? "theorem '" : "definition '")
                + declaration.name + "' (statement)",
                declaration.type ? declaration.type->line : 0,
                declaration.type ? declaration.type->column : 0);
            try {
                for (const auto& binder : declaration.arguments) {
                    ExpressionPointer argumentType =
                        elaborateExpression(*binder.type, localBinders);
                    for (const auto& name : binder.names) {
                        argumentBinders.push_back({name, argumentType});
                        localBinders.push_back({name, argumentType});
                        if (&name != &binder.names.back()) {
                            argumentType = elaborateExpression(
                                *binder.type, localBinders);
                        }
                    }
                }
                returnType =
                    elaborateExpression(*declaration.type, localBinders);
            } catch (const TypeError& kernelError) {
                rethrowKernelError(kernelError);
            }
        }
        Frame frame(*this,
            (declaration.isTheorem ? "theorem '" : "definition '")
            + declaration.name + "'",
            declaration.body ? declaration.body->line : 0,
            declaration.body ? declaration.body->column : 0);
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
                              : Opacity::Transparent,
                          declaration.automatic);
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
        ExpressionPointer fullType;
        // Same statement-error wrapping as elaborateDefinition: a kernel
        // TypeError must be re-thrown while this function's frame is still
        // on the stack, or it reaches the driver bare and prints at 1:1.
        try {
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
            fullType =
                elaborateExpression(*declaration.type, localBinders);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
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

