#include "syntax/parser.hpp"

#include <optional>
#include <string>
#include <utility>

namespace {

// Tactic-block keywords that are contextual: they have meaning only at
// specific positions inside `{ ... }` block bodies, `by_induction`
// constructs, or `obtain ... from ...` statements. Outside those
// contexts they have no syntactic role at all, so the parser accepts
// them as ordinary identifiers — letting mathematicians use `claim`,
// `case`, `with`, etc. as binder or variable names. (The "wide" tactic
// keywords `cases`, `calc`, `witness`, and `by_induction` still
// dispatch to special parsers from `parseAtom`, so they remain
// reserved everywhere; freeing them would require expression-position
// backtracking.)
bool isContextualKeyword(TokenKind kind) {
    switch (kind) {
        case TokenKind::KeywordClaim:
        case TokenKind::KeywordObtain:
        case TokenKind::KeywordSuppose:
        case TokenKind::KeywordChoose:
        case TokenKind::KeywordSet:
        case TokenKind::KeywordSuffices:
        case TokenKind::KeywordFrom:
        case TokenKind::KeywordOn:
        case TokenKind::KeywordWith:
        case TokenKind::KeywordCase:
        case TokenKind::KeywordApply:
        case TokenKind::KeywordContradiction:
        case TokenKind::KeywordSorry:
        case TokenKind::KeywordRing:
        case TokenKind::KeywordGroup:
        case TokenKind::KeywordMonoid:
        case TokenKind::KeywordField:
        case TokenKind::KeywordLinearCombination:
        case TokenKind::KeywordOperator:
        case TokenKind::KeywordOverload:
        case TokenKind::KeywordCoercion:
        // The `decide P { … }` construct is retired, but the bare name
        // is a long-standing module/file name component (Natural.decide,
        // Natural.decide_divides). Mark it contextual so the
        // qualified-name parser accepts it after `.`; parseAtom claims a
        // construct-position `decide` for the migration error.
        case TokenKind::KeywordDecide:
            return true;
        default:
            return false;
    }
}

// True for tokens accepted in identifier-name positions (binder names,
// pattern names, qualified-name parts, variable references). The lexer
// preserves the source text in `lexeme`, so consuming a contextual
// keyword as a name just uses its spelling.
bool isIdentifierLike(TokenKind kind) {
    return kind == TokenKind::Identifier || isContextualKeyword(kind);
}

// Tokens that can appear inside `(<op>)` to denote that operator's symbol
// as an identifier (used in binder positions and in expression position
// to refer to a binder bound under an operator name).
bool isOperatorSymbolToken(TokenKind kind) {
    switch (kind) {
        case TokenKind::Plus:
        case TokenKind::Minus:
        case TokenKind::Star:
        case TokenKind::Slash:
        case TokenKind::Caret:
        case TokenKind::CenterDot:
        case TokenKind::Less:
        case TokenKind::Greater:
        case TokenKind::LessOrEqual:
        case TokenKind::GreaterOrEqual:
        case TokenKind::Equal:
        case TokenKind::NotEqual:
        case TokenKind::LogicalAnd:
        case TokenKind::LogicalOr:
        case TokenKind::LogicalNot:
        case TokenKind::Divides:
        case TokenKind::NotDivides:
        case TokenKind::NotLessOrEqual:
        case TokenKind::ElementOf:
        case TokenKind::NotElementOf:
        case TokenKind::SubsetOf:
        case TokenKind::NotSubsetOf:
        case TokenKind::Approx:
        case TokenKind::InverseSuperscript:
        case TokenKind::Bang:
            return true;
        default:
            return false;
    }
}

// Returns true if `pattern` binds `targetName` somewhere in its tree.
// A bare-name pattern binds `targetName` iff that's its name (except
// for "_", which is a wildcard). Constructor / tuple patterns bind
// whatever their sub-patterns bind.
bool patternBindsName(const SurfacePattern& pattern,
                      const std::string& targetName) {
    if (auto* bare = std::get_if<SurfacePatternBareName>(&pattern.node)) {
        // Bare names that are nullary constructors (resolved by the
        // elaborator) don't bind a variable. We can't distinguish
        // them here, so be conservative: treat any non-"_" bare name
        // matching targetName as a binder. This shadows `set` —
        // unusual in practice, but the safe direction.
        return bare->name != "_" && bare->name == targetName;
    }
    if (auto* constructor =
            std::get_if<SurfacePatternConstructor>(&pattern.node)) {
        for (const auto& argument : constructor->arguments) {
            if (patternBindsName(*argument, targetName)) return true;
        }
        return false;
    }
    if (auto* tuple = std::get_if<SurfacePatternTuple>(&pattern.node)) {
        for (const auto& component : tuple->components) {
            if (patternBindsName(*component, targetName)) return true;
        }
        return false;
    }
    return false;
}

// Substitutes free occurrences of identifier `targetName` (with no
// universe args) in `expression` with `replacement`. Used by `set
// n := E;` in block bodies — every later reference to `n` becomes
// the surface expression `E`, then elaborates afresh at each site.
// Respects shadowing by lambda / Pi / let / cases-pattern /
// by_induction binders.
SurfaceExpressionPointer substituteSurfaceName(
    SurfaceExpressionPointer expression,
    const std::string& targetName,
    SurfaceExpressionPointer replacement) {
    // Optional children (e.g. an untyped `let`'s null type) recurse here;
    // pass them through untouched rather than dereferencing null.
    if (!expression) return expression;
    const SurfaceExpression& node = *expression;
    int line = expression->line;
    int column = expression->column;
    if (auto* identifier = std::get_if<SurfaceIdentifier>(&node.node)) {
        if (identifier->qualifiedName == targetName
            && identifier->universeArgs.empty()) {
            return replacement;
        }
        return expression;
    }
    if (std::get_if<SurfaceNumericLiteral>(&node.node)
        || std::get_if<SurfaceType>(&node.node)
        || std::get_if<SurfaceProposition>(&node.node)) {
        return expression;
    }
    if (auto* application = std::get_if<SurfaceApplication>(&node.node)) {
        auto newFunction = substituteSurfaceName(
            application->function, targetName, replacement);
        std::vector<SurfaceArgument> newArguments;
        for (const auto& argument : application->arguments) {
            SurfaceArgument rewritten;
            rewritten.name = argument.name;
            rewritten.value = substituteSurfaceName(
                argument.value, targetName, replacement);
            newArguments.push_back(std::move(rewritten));
        }
        return makeSurfaceApplication(std::move(newFunction),
                                       std::move(newArguments),
                                       line, column);
    }
    auto substituteBinderType =
        [&](const SurfaceBinder& binder) -> SurfaceBinder {
        return {binder.names,
                substituteSurfaceName(binder.type, targetName, replacement),
                binder.isImplicit};
    };
    auto binderShadows = [&](const SurfaceBinder& binder) {
        for (const auto& name : binder.names) {
            if (name == targetName) return true;
        }
        return false;
    };
    if (auto* piType = std::get_if<SurfacePiType>(&node.node)) {
        SurfaceBinder newBinder = substituteBinderType(piType->binder);
        SurfaceExpressionPointer newCodomain =
            binderShadows(piType->binder)
                ? piType->codomain
                : substituteSurfaceName(piType->codomain,
                                         targetName, replacement);
        return makeSurfacePiType(std::move(newBinder),
                                  std::move(newCodomain), line, column);
    }
    if (auto* lambda = std::get_if<SurfaceLambda>(&node.node)) {
        SurfaceBinder newBinder = substituteBinderType(lambda->binder);
        SurfaceExpressionPointer newBody =
            binderShadows(lambda->binder)
                ? lambda->body
                : substituteSurfaceName(lambda->body,
                                         targetName, replacement);
        return makeSurfaceLambda(std::move(newBinder),
                                  std::move(newBody), line, column);
    }
    if (auto* let = std::get_if<SurfaceLet>(&node.node)) {
        SurfaceExpressionPointer newType = substituteSurfaceName(
            let->type, targetName, replacement);
        SurfaceExpressionPointer newValue = substituteSurfaceName(
            let->value, targetName, replacement);
        SurfaceExpressionPointer newBody =
            let->name == targetName
                ? let->body
                : substituteSurfaceName(let->body,
                                         targetName, replacement);
        return makeSurfaceLet(let->name, std::move(newType),
                               std::move(newValue), std::move(newBody),
                               line, column);
    }
    if (auto* ascription = std::get_if<SurfaceAscription>(&node.node)) {
        return makeSurfaceAscription(
            substituteSurfaceName(ascription->expression,
                                   targetName, replacement),
            substituteSurfaceName(ascription->type,
                                   targetName, replacement),
            line, column);
    }
    if (auto* binary = std::get_if<SurfaceBinaryOperation>(&node.node)) {
        return makeSurfaceBinaryOperation(
            binary->opSymbol,
            substituteSurfaceName(binary->left, targetName, replacement),
            substituteSurfaceName(binary->right, targetName, replacement),
            line, column);
    }
    if (auto* unary = std::get_if<SurfaceUnaryOperation>(&node.node)) {
        return makeSurfaceUnaryOperation(
            unary->opSymbol,
            substituteSurfaceName(unary->operand, targetName, replacement),
            line, column);
    }
    if (auto* foldBinder = std::get_if<SurfaceFoldBinder>(&node.node)) {
        // The index variable shadows `targetName` inside the body only.
        SurfaceExpressionPointer newBody =
            foldBinder->binderName == targetName
                ? foldBinder->body
                : substituteSurfaceName(foldBinder->body,
                                         targetName, replacement);
        return makeSurfaceFoldBinder(
            foldBinder->operatorSymbol, foldBinder->binderName,
            substituteSurfaceName(foldBinder->lowerBound,
                                   targetName, replacement),
            substituteSurfaceName(foldBinder->upperBound,
                                   targetName, replacement),
            std::move(newBody), line, column);
    }
    if (auto* ellipsis = std::get_if<SurfaceEllipsisFold>(&node.node)) {
        std::vector<SurfaceExpressionPointer> newPrefix;
        for (const auto& term : ellipsis->prefixTerms) {
            newPrefix.push_back(
                substituteSurfaceName(term, targetName, replacement));
        }
        return makeSurfaceEllipsisFold(
            ellipsis->operatorSymbol, std::move(newPrefix),
            substituteSurfaceName(ellipsis->generalTerm,
                                   targetName, replacement),
            line, column);
    }
    if (auto* tuple = std::get_if<SurfaceAnonymousTuple>(&node.node)) {
        std::vector<SurfaceExpressionPointer> newComponents;
        for (const auto& component : tuple->components) {
            newComponents.push_back(substituteSurfaceName(
                component, targetName, replacement));
        }
        return makeSurfaceAnonymousTuple(std::move(newComponents),
                                          line, column, tuple->userWritten);
    }
    if (auto* cases = std::get_if<SurfaceCases>(&node.node)) {
        SurfaceExpressionPointer newScrutinee = substituteSurfaceName(
            cases->scrutinee, targetName, replacement);
        std::vector<SurfaceCasesClause> newClauses;
        // The `with <equalityHypothesisName>` binder is in scope inside
        // each arm body, so a substitution targeting that name does not
        // descend into clause bodies.
        bool eqShadows =
            !cases->equalityHypothesisName.empty()
            && cases->equalityHypothesisName == targetName;
        for (const auto& clause : cases->clauses) {
            SurfaceCasesClause newClause;
            newClause.pattern = clause.pattern;
            newClause.body =
                (eqShadows
                 || patternBindsName(*clause.pattern, targetName))
                    ? clause.body
                    : substituteSurfaceName(clause.body,
                                             targetName, replacement);
            newClause.line = clause.line;
            newClause.column = clause.column;
            newClauses.push_back(std::move(newClause));
        }
        if (cases->equalityHypothesisName.empty()
            && cases->refiningNames.empty()) {
            return makeSurfaceCases(std::move(newScrutinee),
                                     std::move(newClauses),
                                     line, column);
        }
        return makeSurfaceCasesWithRefining(
            std::move(newScrutinee), std::move(newClauses),
            cases->equalityHypothesisName,
            cases->refiningNames,
            line, column);
    }
    if (auto* calc = std::get_if<SurfaceCalc>(&node.node)) {
        auto newInitial = substituteSurfaceName(
            calc->initialExpression, targetName, replacement);
        std::vector<SurfaceCalcStep> newSteps;
        for (const auto& step : calc->steps) {
            // Whole-struct copy preserves relation, relationOperator,
            // line, column — and any future field;
            // only the rewritten sub-expressions are overwritten.
            SurfaceCalcStep newStep = step;
            newStep.nextExpression = substituteSurfaceName(
                step.nextExpression, targetName, replacement);
            // step.stepProof is null when the user omits `by …`
            // and lets the auto-prover close the step. Recurse only
            // when present.
            newStep.stepProof = step.stepProof
                ? substituteSurfaceName(
                      step.stepProof, targetName, replacement)
                : nullptr;
            newSteps.push_back(std::move(newStep));
        }
        return makeSurfaceCalc(std::move(newInitial), std::move(newSteps),
                                line, column);
    }
    if (auto* induction =
            std::get_if<SurfaceByInductionUsing>(&node.node)) {
        auto newScrutinee = substituteSurfaceName(
            induction->scrutinee, targetName, replacement);
        auto newLemma = substituteSurfaceName(
            induction->inductionLemma, targetName, replacement);
        bool shadows = induction->subjectName == targetName
                    || induction->ihName == targetName;
        auto newBody = shadows
            ? induction->body
            : substituteSurfaceName(induction->body,
                                     targetName, replacement);
        return makeSurfaceByInductionUsing(
            std::move(newScrutinee), std::move(newLemma),
            induction->subjectName, induction->ihName,
            std::move(newBody), line, column);
    }
    if (auto* structured =
            std::get_if<SurfaceStructuredClaim>(&node.node)) {
        // `claim [P] [by HINT] [{ arms }]` — recurse into the stated
        // proposition, the by-hint, and any `by cases` arm bodies. A
        // named claim desugars to a structured claim wrapped in a `let`,
        // so without this a `set`-bound name used in the claim's
        // proposition would survive unsubstituted.
        SurfaceExpressionPointer newProposition = structured->proposition
            ? substituteSurfaceName(structured->proposition,
                                     targetName, replacement)
            : nullptr;
        SurfaceExpressionPointer newByHint = structured->byHint
            ? substituteSurfaceName(structured->byHint,
                                     targetName, replacement)
            : nullptr;
        std::vector<SurfaceStructuredClaimArm> newArms;
        for (const auto& arm : structured->arms) {
            // Start from a full copy so structural flags (`isOtherwise`,
            // witness binders) survive the substitution — an `otherwise`
            // arm that loses its flag becomes a stated arm with a null
            // proposition and crashes the elaborator downstream.
            SurfaceStructuredClaimArm newArm = arm;
            newArm.disjunctType = arm.disjunctType
                ? substituteSurfaceName(arm.disjunctType,
                                         targetName, replacement)
                : nullptr;
            bool bodyShadowed = arm.binderName == targetName
                || arm.witnessName == targetName;
            newArm.body = (bodyShadowed || !arm.body)
                ? arm.body
                : substituteSurfaceName(arm.body, targetName, replacement);
            newArm.witnessType = arm.witnessType
                ? substituteSurfaceName(arm.witnessType,
                                         targetName, replacement)
                : nullptr;
            newArms.push_back(std::move(newArm));
        }
        return makeSurfaceStructuredClaim(
            std::move(newProposition), structured->label,
            std::move(newByHint), structured->byCases,
            std::move(newArms), line, column,
            structured->byInduction, structured->bySubstitution);
    }
    if (auto* note = std::get_if<SurfaceNote>(&node.node)) {
        // `note goal : T;` / `note P [by V];` / `change T;` — recurse into
        // the goal type / proposition / proof / body so a `set`-bound name
        // used in any of them is substituted (note binds nothing, so the
        // body has no shadowing to guard).
        auto sub = [&](const SurfaceExpressionPointer& e) {
            return e ? substituteSurfaceName(e, targetName, replacement)
                     : SurfaceExpressionPointer{};
        };
        return makeSurfaceNote(
            sub(note->goalType), sub(note->proposition), sub(note->body),
            line, column, note->changesGoal, sub(note->proof));
    }
    if (auto* choose = std::get_if<SurfaceChoose>(&node.node)) {
        // `choose name [such that predicate] [as conditionName] [from
        // source]`. `name` scopes over the predicate and the body;
        // `conditionName` scopes over the body; `source` is in the outer
        // scope. Guard each binder against shadowing the target.
        bool nameShadows = choose->name == targetName;
        bool bodyShadows = nameShadows || choose->conditionName == targetName;
        SurfaceExpressionPointer newPredicate =
            (nameShadows || !choose->predicate)
                ? choose->predicate
                : substituteSurfaceName(choose->predicate,
                                         targetName, replacement);
        SurfaceExpressionPointer newBody =
            bodyShadows
                ? choose->body
                : substituteSurfaceName(choose->body, targetName, replacement);
        SurfaceExpressionPointer newSource = choose->source
            ? substituteSurfaceName(choose->source, targetName, replacement)
            : nullptr;
        return makeSurfaceChoose(choose->name, std::move(newPredicate),
                                  std::move(newBody), line, column,
                                  choose->conditionName, std::move(newSource));
    }
    if (auto* decide = std::get_if<SurfaceDecide>(&node.node)) {
        // `decide proposition { yes h => … | no n => … }`. The proposition
        // is in the outer scope; each arm binds its own hypothesis name.
        SurfaceExpressionPointer newProposition = substituteSurfaceName(
            decide->proposition, targetName, replacement);
        SurfaceExpressionPointer newYesBody =
            decide->yesBinderName == targetName
                ? decide->yesBody
                : substituteSurfaceName(decide->yesBody,
                                         targetName, replacement);
        SurfaceExpressionPointer newNoBody =
            decide->noBinderName == targetName
                ? decide->noBody
                : substituteSurfaceName(decide->noBody,
                                         targetName, replacement);
        return makeSurfaceDecide(std::move(newProposition),
                                  decide->yesBinderName, std::move(newYesBody),
                                  decide->noBinderName, std::move(newNoBody),
                                  line, column);
    }
    // Unhandled node kind: be conservative and return unchanged. If we
    // ever add a new SurfaceExpression variant, the `set` substitution
    // will silently skip it — surfaced by the test suite if it bites.
    return expression;
}

// Recursive-descent parser. One method per precedence level for the
// expression grammar. Lookahead is bounded by one token in most places;
// Pi binders use a bounded backtracking scheme (tryParseExplicitBinder
// saves the position, attempts the match, restores on failure).
class ParserImpl {
public:
    explicit ParserImpl(const std::vector<Token>& tokens) : tokens_(tokens) {}

    SurfaceExpressionPointer parseTopLevelExpression() {
        auto result = parseExpression();
        if (peek().kind != TokenKind::EndOfFile) {
            throwHere("unexpected token after expression");
        }
        return result;
    }

    // -------- module-level entry point --------

    SurfaceModule parseModule() {
        SurfaceModule module;
        // D Phase-1 module kinds — `interface` / `implementation` are
        // CONTEXTUAL words (ordinary identifiers elsewhere).
        if (peek().kind == TokenKind::Identifier
            && peek().lexeme == "interface"
            && peekAt(1).kind == TokenKind::KeywordModule) {
            consumeAny();
            module.kind = ModuleKind::Interface;
        } else if (peek().kind == TokenKind::Identifier
                   && peek().lexeme == "implementation"
                   && peekAt(1).kind == TokenKind::KeywordModule) {
            consumeAny();
            module.kind = ModuleKind::Implementation;
        }
        expect(TokenKind::KeywordModule, "at start of file");
        module.moduleName = consumeQualifiedNameString();
        if (module.kind == ModuleKind::Implementation) {
            if (!(peek().kind == TokenKind::Identifier
                  && peek().lexeme == "implements")) {
                throwHere("an implementation module must declare the "
                          "interface it implements: `implementation "
                          "module Name implements InterfaceName`");
            }
            consumeAny();
            module.implementsName = consumeQualifiedNameString();
        }
        if (module.kind == ModuleKind::Interface
            && peek().kind == TokenKind::Identifier
            && peek().lexeme == "implemented"
            && peekAt(1).kind == TokenKind::KeywordBy) {
            consumeAny();
            consumeAny();
            module.implementedByName = consumeQualifiedNameString();
        }
        interfaceModuleMode_ = module.kind == ModuleKind::Interface;
        while (peek().kind != TokenKind::EndOfFile) {
            // `export theorems of M1, M2, …` (module-granular) and
            // `export definitions D1, D2, …` (name-granular,
            // transparent re-export) — interface-module clauses,
            // recorded on the module (not statements).
            if (interfaceModuleMode_
                && peek().kind == TokenKind::Identifier
                && peek().lexeme == "export"
                && peekAt(1).kind == TokenKind::Identifier
                && peekAt(1).lexeme == "theorems") {
                consumeAny();
                consumeAny();
                if (!(peek().kind == TokenKind::Identifier
                      && peek().lexeme == "of")) {
                    throwHere("expected 'of' after 'export theorems'");
                }
                consumeAny();
                module.exportTheoremsOfModules.push_back(
                    consumeQualifiedNameString());
                while (peek().kind == TokenKind::Comma) {
                    consumeAny();
                    module.exportTheoremsOfModules.push_back(
                        consumeQualifiedNameString());
                }
                continue;
            }
            if (interfaceModuleMode_
                && peek().kind == TokenKind::Identifier
                && peek().lexeme == "export"
                && peekAt(1).kind == TokenKind::Identifier
                && peekAt(1).lexeme == "definitions") {
                consumeAny();
                consumeAny();
                module.exportDefinitionsNames.push_back(
                    consumeQualifiedNameString());
                while (peek().kind == TokenKind::Comma) {
                    consumeAny();
                    module.exportDefinitionsNames.push_back(
                        consumeQualifiedNameString());
                }
                continue;
            }
            module.statements.push_back(parseTopStatement());
        }
        return module;
    }

private:
    SurfaceTopStatement parseTopStatement() {
        // Interface-module body forms: `type N` and `constant N : T`
        // (contextual words), both representing abstract primitives.
        if (interfaceModuleMode_ && peek().kind == TokenKind::Identifier
            && peek().lexeme == "type"
            && peekAt(1).kind == TokenKind::Identifier) {
            consumeAny();
            SurfaceAxiomDeclaration declaration;
            declaration.name = consumeQualifiedNameString();
            declaration.type = makeSurfaceType(
                makeSurfaceLevelNumeric(0, peek().line, peek().column),
                peek().line, peek().column);
            declaration.interfaceRole =
                SurfaceAxiomDeclaration::InterfaceRole::AbstractType;
            return declaration;
        }
        if (interfaceModuleMode_
            && peek().kind == TokenKind::KeywordTheorem) {
            // A theorem SIGNATURE (no `:=`): an obligation the
            // implementation must discharge; consumers see it as a
            // bodyless fact. Binders fold into a Pi type.
            int line = peek().line, column = peek().column;
            consumeAny();
            SurfaceAxiomDeclaration declaration;
            declaration.name = consumeQualifiedNameString();
            std::vector<SurfaceBinder> binders;
            while (peek().kind == TokenKind::LeftParen
                   || peek().kind == TokenKind::LeftBrace) {
                binders.push_back(parseExplicitBinder());
            }
            expect(TokenKind::Colon, "before the theorem signature's "
                                      "statement");
            SurfaceExpressionPointer statement = parseExpression();
            if (peek().kind == TokenKind::Assign) {
                throwHere("an interface theorem is a SIGNATURE — the "
                          "proof belongs in the implementation module");
            }
            for (auto binderIterator = binders.rbegin();
                 binderIterator != binders.rend(); ++binderIterator) {
                statement = makeSurfacePiType(*binderIterator, statement,
                                              line, column);
            }
            declaration.type = statement;
            declaration.interfaceRole =
                SurfaceAxiomDeclaration::InterfaceRole::Obligation;
            return declaration;
        }
        if (interfaceModuleMode_ && peek().kind == TokenKind::Identifier
            && peek().lexeme == "constant"
            && peekAt(1).kind == TokenKind::Identifier) {
            consumeAny();
            SurfaceAxiomDeclaration declaration;
            declaration.name = consumeQualifiedNameString();
            expect(TokenKind::Colon, "after the constant's name");
            declaration.type = parseExpression();
            declaration.interfaceRole =
                SurfaceAxiomDeclaration::InterfaceRole::AbstractConstant;
            return declaration;
        }
        switch (peek().kind) {
            case TokenKind::KeywordImport:     return parseImportDeclaration();
            case TokenKind::KeywordUsing:      return parseUsingDeclaration();
            case TokenKind::KeywordInductive:  return parseInductiveDeclaration();
            case TokenKind::KeywordAxiom:      return parseAxiomDeclaration();
            case TokenKind::KeywordDefinition: return parseDefinitionDeclaration(false);
            case TokenKind::KeywordTheorem:    return parseDefinitionDeclaration(true);
            case TokenKind::KeywordOpaque: {
                // `opaque definition Name … := body` — consume the
                // modifier, require `definition`, set the flag.
                consumeAny();  // 'opaque'
                if (peek().kind != TokenKind::KeywordDefinition) {
                    throwHere("expected 'definition' after 'opaque' "
                              "(theorems can't be opaque — proof "
                              "irrelevance already hides their body)");
                }
                SurfaceDefinitionDeclaration decl =
                    parseDefinitionDeclaration(false);
                decl.opaque = true;
                return decl;
            }
            case TokenKind::KeywordAutomatic: {
                // `automatic theorem/definition/axiom …` — consume the
                // modifier and set the flag on the resulting declaration so
                // the auto-prover may use it unprompted across modules.
                consumeAny();  // 'automatic'
                switch (peek().kind) {
                    case TokenKind::KeywordTheorem: {
                        SurfaceDefinitionDeclaration decl =
                            parseDefinitionDeclaration(true);
                        decl.automatic = true;
                        return decl;
                    }
                    case TokenKind::KeywordDefinition: {
                        SurfaceDefinitionDeclaration decl =
                            parseDefinitionDeclaration(false);
                        decl.automatic = true;
                        return decl;
                    }
                    case TokenKind::KeywordAxiom: {
                        SurfaceAxiomDeclaration decl = parseAxiomDeclaration();
                        decl.automatic = true;
                        return decl;
                    }
                    default:
                        throwHere("expected 'theorem', 'definition', or "
                                  "'axiom' after 'automatic'");
                }
            }
            case TokenKind::KeywordOperator:   return parseOperatorDeclaration();
            case TokenKind::KeywordFoldOperation:
                return parseFoldOperationDeclaration();
            case TokenKind::KeywordOverload:   return parseOverloadDeclaration();
            case TokenKind::KeywordCongruenceUnderBinder:
                return parseCongruenceDeclaration();
            case TokenKind::KeywordCoercion:   return parseCoercionDeclaration();
            case TokenKind::KeywordConvention: return parseConventionDeclaration();
            case TokenKind::KeywordInstance:   return parseInstanceDeclaration();
            case TokenKind::KeywordConstruction: {
                // `construction Name(args) : T := body` — parses exactly
                // like a (non-theorem) definition; the elaborator treats
                // it as a transparent definition and registers Name as a
                // canonical constructor.
                SurfaceDefinitionDeclaration decl =
                    parseDefinitionDeclaration(false);
                decl.isConstruction = true;
                return decl;
            }
            default:
                throwHere("expected top-level statement keyword "
                          "(import / using / inductive / axiom / "
                          "definition / theorem / operator / overload / "
                          "convention / construction / opaque)");
        }
    }

    // `operator (<symbol>) on (<T1>, <T2>) := <Function>`
    //
    // The operator symbol can be any operator-shaped token sequence
    // (`+`, `*`, `-`, `≤`, `<`, `∣`, …). We consume one operator token
    // by its lexeme.
    SurfaceOperatorDeclaration parseOperatorDeclaration() {
        consumeAny();  // 'operator'
        SurfaceOperatorDeclaration declaration;
        expect(TokenKind::LeftParen,
               "expected '(' before operator symbol in operator "
               "declaration");
        if (peek().kind == TokenKind::Identifier
            || peek().kind == TokenKind::EndOfFile) {
            throwHere("expected an operator symbol like '+', '*', "
                      "'-', '≤', '<', '∣' inside the parentheses");
        }
        declaration.operatorSymbol = consumeAny().lexeme;
        expect(TokenKind::RightParen,
               "expected ')' after operator symbol");
        expect(TokenKind::KeywordOn,
               "expected 'on' after operator symbol in operator "
               "declaration");
        expect(TokenKind::LeftParen,
               "expected '(<leftType>, <rightType>)' after 'on'");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a type name (left operand type)");
        }
        declaration.leftTypeName = consumeQualifiedNameString();
        // Two forms: binary `on (LeftType, RightType)` and postfix
        // `on (OperandType)`. A postfix declaration leaves rightTypeName
        // empty, which the elaborator reads as the postfix marker.
        if (peek().kind == TokenKind::Comma) {
            consumeAny();  // ','
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected a type name (right operand type)");
            }
            declaration.rightTypeName = consumeQualifiedNameString();
        } else {
            declaration.rightTypeName = "";
        }
        expect(TokenKind::RightParen,
               "expected ')' after operand-type pair");
        expect(TokenKind::Assign,
               "expected ':=' before the dispatch function name");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a function name as the operator "
                      "dispatch target");
        }
        declaration.functionName = consumeQualifiedNameString();
        return declaration;
    }

    // `fold_operation (<symbol>) on <Carrier> := <witness>`
    //
    // Registers the operation behind `<symbol>` on `<Carrier>` as
    // fold-capable, certified by `<witness> : IsMonoid(Carrier, op, id)`.
    SurfaceFoldOperationDeclaration parseFoldOperationDeclaration() {
        consumeAny();  // 'fold_operation'
        SurfaceFoldOperationDeclaration declaration;
        expect(TokenKind::LeftParen,
               "expected '(' before operator symbol in fold_operation "
               "declaration");
        if (peek().kind == TokenKind::Identifier
            || peek().kind == TokenKind::EndOfFile) {
            throwHere("expected an operator symbol like '+' or '*' "
                      "inside the parentheses");
        }
        declaration.operatorSymbol = consumeAny().lexeme;
        expect(TokenKind::RightParen,
               "expected ')' after operator symbol");
        expect(TokenKind::KeywordOn,
               "expected 'on' after operator symbol in fold_operation "
               "declaration");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a carrier type name after 'on'");
        }
        declaration.carrierName = consumeQualifiedNameString();
        expect(TokenKind::Assign,
               "expected ':=' before the IsMonoid witness name");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected the name of an IsMonoid(Carrier, op, id) "
                      "witness after ':='");
        }
        declaration.witnessName = consumeQualifiedNameString();
        return declaration;
    }

    // `coercion (<sourceTypeName>, <targetTypeName>) := <function>`
    //
    // Registers `function` as the canonical embedding from `source`
    // into `target`. Type names are head Constants (qualified names).
    SurfaceCoercionDeclaration parseCoercionDeclaration() {
        consumeAny();  // 'coercion'
        SurfaceCoercionDeclaration declaration;
        expect(TokenKind::LeftParen,
               "expected '(<sourceType>, <targetType>)' after 'coercion'");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a type name (coercion source)");
        }
        declaration.sourceTypeName = consumeQualifiedNameString();
        expect(TokenKind::Comma,
               "expected ',' between source and target type names");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a type name (coercion target)");
        }
        declaration.targetTypeName = consumeQualifiedNameString();
        expect(TokenKind::RightParen,
               "expected ')' after target type name");
        expect(TokenKind::Assign,
               "expected ':=' before the coercion function name");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a function name as the coercion target");
        }
        declaration.functionName = consumeQualifiedNameString();
        return declaration;
    }

    // `overload <alias> := <Function>`
    // `congruence_under_binder <F> := <L>` — registers congruence lemma
    // `L` for function head `F` (the rewrite-under-binder mechanism).
    SurfaceCongruenceDeclaration parseCongruenceDeclaration() {
        consumeAny();  // 'congruence_under_binder'
        SurfaceCongruenceDeclaration declaration;
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a function head name after "
                      "'congruence_under_binder'");
        }
        declaration.functionName = consumeQualifiedNameString();
        expect(TokenKind::Assign,
               "expected ':=' before the congruence lemma name");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a lemma name as the congruence target");
        }
        declaration.lemmaName = consumeQualifiedNameString();
        return declaration;
    }

    SurfaceOverloadDeclaration parseOverloadDeclaration() {
        consumeAny();  // 'overload'
        SurfaceOverloadDeclaration declaration;
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected an alias name after 'overload'");
        }
        declaration.aliasName = consumeQualifiedNameString();
        expect(TokenKind::Assign,
               "expected ':=' before the function name in overload "
               "declaration");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a function name as the overload target");
        }
        declaration.functionName = consumeQualifiedNameString();
        return declaration;
    }

    SurfaceImportDeclaration parseImportDeclaration() {
        consumeAny();  // 'import'
        SurfaceImportDeclaration declaration;
        declaration.moduleName = consumeQualifiedNameString();
        return declaration;
    }

    SurfaceUsingDeclaration parseUsingDeclaration() {
        consumeAny();  // 'using'
        SurfaceUsingDeclaration declaration;
        declaration.namespacePath = consumeQualifiedNameString();
        expect(TokenKind::Dot, "in using directive");
        if (isIdentifierLike(peek().kind)) {
            // either "operators" or "literals" — we accept them by spelling
            std::string target = consumeAny().lexeme;
            if (target != "operators" && target != "literals") {
                throwHere("expected 'operators', 'literals', or a name "
                          "list in using directive");
            }
            declaration.target = target;
        } else if (peek().kind == TokenKind::LeftBrace) {
            consumeAny();
            declaration.target = "names";
            if (peek().kind != TokenKind::RightBrace) {
                if (!isIdentifierLike(peek().kind)) {
                    throwHere("expected name in using list");
                }
                declaration.names.push_back(consumeAny().lexeme);
                while (peek().kind == TokenKind::Comma) {
                    consumeAny();
                    if (!isIdentifierLike(peek().kind)) {
                        throwHere("expected name in using list");
                    }
                    declaration.names.push_back(consumeAny().lexeme);
                }
            }
            expect(TokenKind::RightBrace, "ending using name list");
        } else {
            throwHere("expected 'operators', 'literals', or '{' after '.'"
                      " in using directive");
        }
        return declaration;
    }

    // `instance <qualifiedName>` — register a canonical structure
    // instance. `<qualifiedName>` names an existing theorem whose type is
    // (possibly under parameters) a structure predicate applied to a
    // concrete carrier, e.g. `Integer.add_is_group`.
    SurfaceInstanceDeclaration parseInstanceDeclaration() {
        consumeAny();  // 'instance'
        SurfaceInstanceDeclaration declaration;
        declaration.name = consumeQualifiedNameString();
        return declaration;
    }

    // `convention p [q ...] : <type> [with <prop1> [, <prop2> ...]];`
    //
    // Registers `p`, `q`, etc. as implicitly-bound names of `<type>` in
    // any subsequent definition/theorem that mentions them. Each `with`
    // proposition becomes an additional implicit binder (anonymous-named).
    //
    // Examples:
    //   convention p : Natural with Natural.is_prime(p);
    //   convention n m k : Natural;
    //   convention x y z : Rational;
    SurfaceConventionDeclaration parseConventionDeclaration() {
        consumeAny();  // 'convention'
        SurfaceConventionDeclaration declaration;
        // A convention name is an identifier OR an operator symbol in
        // parentheses (`(·)`, `(+)`) — the same spelling explicit binders
        // accept. So a ring/group operation can be a pervasive convention
        // and still be written infix (`x · y`, `x + y`) in every lemma.
        auto tryConventionName = [&]() -> bool {
            if (isIdentifierLike(peek().kind)) {
                declaration.names.push_back(consumeAny().lexeme);
                return true;
            }
            if (peek().kind == TokenKind::LeftParen
                && position_ + 2 < tokens_.size()
                && isOperatorSymbolToken(tokens_[position_ + 1].kind)
                && tokens_[position_ + 2].kind == TokenKind::RightParen) {
                consumeAny();  // '('
                declaration.names.push_back(consumeAny().lexeme);
                consumeAny();  // ')'
                return true;
            }
            return false;
        };
        if (!tryConventionName()) {
            throwHere("expected at least one name after 'convention'");
        }
        // Optional additional names share the same type/propositions.
        while (peek().kind != TokenKind::Colon) {
            if (!tryConventionName()) {
                throwHere("expected ':' or another name in convention "
                          "declaration");
            }
        }
        expect(TokenKind::Colon, "before convention type");
        declaration.type = parseExpression();
        if (peek().kind == TokenKind::KeywordWith) {
            consumeAny();  // 'with'
            declaration.propositions.push_back(parseConventionProposition());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();  // ','
                declaration.propositions.push_back(
                    parseConventionProposition());
            }
        }
        return declaration;
    }

    // One `with` entry: either an anonymous proposition `<expr>` or a
    // named one `<name> : <expr>`. We disambiguate by lookahead: an
    // identifier followed by `:` (and not by `.` — qualified names are
    // legal expressions) starts a named entry.
    SurfaceConventionProposition parseConventionProposition() {
        SurfaceConventionProposition entry;
        if (isIdentifierLike(peek().kind)
            && position_ + 1 < tokens_.size()
            && tokens_[position_ + 1].kind == TokenKind::Colon) {
            entry.name = consumeAny().lexeme;
            consumeAny();  // ':'
        }
        entry.proposition = parseExpression();
        return entry;
    }

    SurfaceInductiveDeclaration parseInductiveDeclaration() {
        consumeAny();  // 'inductive'
        SurfaceInductiveDeclaration declaration;
        declaration.name = consumeQualifiedNameString();
        declaration.universeParameters = parseUniverseParameterList();
        while (peek().kind == TokenKind::LeftParen
               || peek().kind == TokenKind::LeftBrace) {
            declaration.parameters.push_back(parseExplicitBinder());
        }
        expect(TokenKind::Colon, "before inductive kind");
        declaration.kind = parseExpression();
        expect(TokenKind::KeywordWhere, "before inductive constructors");
        while (peek().kind == TokenKind::Pipe) {
            consumeAny();  // '|'
            SurfaceConstructorSpec constructorSpec;
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected constructor name after '|'");
            }
            constructorSpec.name = consumeQualifiedNameString();
            expect(TokenKind::Colon, "before constructor type");
            constructorSpec.type = parseExpression();
            declaration.constructors.push_back(std::move(constructorSpec));
        }
        return declaration;
    }

    SurfaceAxiomDeclaration parseAxiomDeclaration() {
        consumeAny();  // 'axiom'
        SurfaceAxiomDeclaration declaration;
        declaration.name = consumeQualifiedNameString();
        declaration.universeParameters = parseUniverseParameterList();
        expect(TokenKind::Colon, "before axiom type");
        declaration.type = parseExpression();
        return declaration;
    }

    SurfaceDefinitionDeclaration parseDefinitionDeclaration(bool isTheorem) {
        consumeAny();  // 'definition' / 'theorem'
        SurfaceDefinitionDeclaration declaration;
        declaration.isTheorem = isTheorem;
        declaration.name = consumeQualifiedNameString();
        declaration.universeParameters = parseUniverseParameterList();
        while (peek().kind == TokenKind::LeftParen
               || peek().kind == TokenKind::LeftBrace) {
            declaration.arguments.push_back(parseExplicitBinder());
        }
        expect(TokenKind::Colon, "before declaration type");
        declaration.type = parseExpression();
        if (peek().kind == TokenKind::Assign) {
            consumeAny();  // ':='
            // `:= by <lemma>` — the whole proof is a citation; the
            // prover does the logical plumbing between the goal and
            // the lemma's form (A7). Reads as the reference target's
            // `sqrt_two_irrational := by no_double_square`; sugar for
            // `:= done by <lemma>`.
            if (peek().kind == TokenKind::KeywordBy) {
                Token byToken = consumeAny();
                declaration.body = makeSurfaceStructuredClaim(
                    makeSurfaceGoal(byToken.line, byToken.column),
                    /*label=*/"", /*byHint=*/parseExpression(),
                    /*byCases=*/false, {}, byToken.line, byToken.column);
            } else {
                declaration.body = parseExpression();
            }
        } else if (peek().kind == TokenKind::Pipe) {
            while (peek().kind == TokenKind::Pipe) {
                declaration.cases.push_back(parsePatternCase());
            }
        } else if (peek().kind == TokenKind::LeftBrace) {
            // Block body form: `theorem foo : T { let pat := v; ...; final_expr }`.
            // Statements are semicolon-terminated; the trailing non-let
            // expression is the block's value. Desugars at parse time to
            // a nested let-in chain.
            declaration.body = parseBlockBody();
        } else if (peek().kind == TokenKind::KeywordBy
                   && position_ + 1 < tokens_.size()
                   && tokens_[position_ + 1].lexeme == "representatives") {
            // Define-by-representatives (WS3):
            //   definition F : Quotient(T, R) → U
            //     by representatives <pat> ↦ <body>
            //     well_defined by <proof>
            // The mathematician's "define F by picking a representative;
            // well-defined because the formula respects the relation".
            declaration.body = parseDefineByRepresentatives();
        } else {
            throwHere("expected ':=', '|', '{', or "
                      "`by representatives` after declaration type");
        }
        return declaration;
    }

    // Parse `by representatives <pat> ↦ <body> well_defined by <proof>` and
    // desugar (unary) to `(x) ↦ Quotient.lift((rep) ↦ <body>, <proof>, x)`.
    // The short-form `Quotient.lift` infers (T, R, U) and coerces the
    // respect proof, so a `well_defined` proof of the bare equivalence
    // closes the obligation — the lift apparatus and `Quotient.equivalent_implies_equal` are
    // never named. The carrier representative may be destructured with a
    // tuple/constructor pattern, in which case `<body>` runs under a
    // `cases` on a synthesised representative binder.
    SurfaceExpressionPointer parseDefineByRepresentatives() {
        Token byToken = consumeAny();   // 'by'
        consumeAny();                   // 'representatives'
        int line = byToken.line;
        int column = byToken.column;
        // Each representative must be a bare name: a destructuring pattern
        // would wrap the body in `cases rep { | <pat> => … }` inside the
        // lift's function argument, where `f(x) = recursor(…x)` is stuck on
        // an abstract x and the respect coercion can't fire. Apply a
        // representative-level function in the body instead.
        std::vector<std::string> representativeNames;
        auto parseBareRepresentative = [&]() {
            SurfacePatternPointer pattern = parsePattern();
            if (auto* bare = std::get_if<SurfacePatternBareName>(
                    &pattern->node)) {
                representativeNames.push_back(bare->name);
            } else {
                throwHere("`definition ... by representatives` requires a bare "
                          "representative name; apply a representative-level "
                          "function in the body (e.g. "
                          "`mk(negate_representatives(rep))`) rather than "
                          "destructuring the representative directly");
            }
        };
        parseBareRepresentative();
        while (peek().kind == TokenKind::Comma) {
            consumeAny();
            parseBareRepresentative();
        }
        expect(TokenKind::MapsTo,
               "after the representative name(s) in `by representatives`");
        SurfaceExpressionPointer body = parseExpression();
        if (!(isIdentifierLike(peek().kind)
              && peek().lexeme == "well_defined")) {
            throwHere("expected `well_defined by <proof>` after the "
                      "`by representatives` body");
        }
        consumeAny();   // 'well_defined'
        expect(TokenKind::KeywordBy, "after `well_defined`");
        std::vector<SurfaceExpressionPointer> wellDefinedProofs;
        wellDefinedProofs.push_back(parseExpression());
        while (peek().kind == TokenKind::Comma) {
            consumeAny();
            wellDefinedProofs.push_back(parseExpression());
        }
        if (representativeNames.size() == 1 && wellDefinedProofs.size() == 1) {
            return buildDefineByRepresentativesUnary(
                representativeNames[0], std::move(body),
                std::move(wellDefinedProofs[0]), line, column);
        }
        if (representativeNames.size() == 2 && wellDefinedProofs.size() == 2) {
            return buildDefineByRepresentativesBinary(
                representativeNames[0], representativeNames[1], std::move(body),
                std::move(wellDefinedProofs[0]), std::move(wellDefinedProofs[1]),
                line, column);
        }
        throwHere("`definition ... by representatives` supports one "
                  "representative + one `well_defined` proof (unary) or two "
                  "representatives + two proofs (the first- and "
                  "second-argument respect proofs, in that order); got "
                  + std::to_string(representativeNames.size())
                  + " representatives and "
                  + std::to_string(wellDefinedProofs.size()) + " proofs");
    }

    // `(name) ↦ body` with a single untyped binder.
    SurfaceExpressionPointer singleBinderLambda(
        const std::string& name, SurfaceExpressionPointer body,
        int line, int column) {
        SurfaceBinder binder;
        binder.names = {name};
        return makeSurfaceLambda(std::move(binder), std::move(body),
                                  line, column);
    }

    // Unary: `(arg) ↦ Quotient.lift((rep) ↦ <body>, <proof>, arg)`.
    SurfaceExpressionPointer buildDefineByRepresentativesUnary(
        const std::string& representativeName,
        SurfaceExpressionPointer body,
        SurfaceExpressionPointer wellDefinedProof,
        int line, int column) {
        const std::string argumentName = "_argumentOfDefinition";
        SurfaceExpressionPointer perRepresentativeFunction =
            singleBinderLambda(representativeName, std::move(body),
                                line, column);
        std::vector<SurfaceExpressionPointer> liftArguments;
        liftArguments.push_back(std::move(perRepresentativeFunction));
        liftArguments.push_back(std::move(wellDefinedProof));
        liftArguments.push_back(
            makeSurfaceIdentifier(argumentName, {}, line, column));
        SurfaceExpressionPointer liftCall = makeSurfaceApplication(
            makeSurfaceIdentifier("Quotient.lift", {}, line, column),
            std::move(liftArguments), line, column);
        return singleBinderLambda(argumentName, std::move(liftCall),
                                   line, column);
    }

    // Binary: nested lifts. With representatives `a`, `c`, body `<body>`,
    // and the first/second respect proofs, build
    //
    //   (argA argB) ↦
    //     Quotient.lift(
    //       (a) ↦ Quotient.lift((c) ↦ <body>, proofSecond(a), argB),
    //       (a a' eA) ↦ cases argB { | c => proofFirst(a, a', c, eA) },
    //       argA)
    //
    // The inner lift varies the second representative with the first held
    // fixed; its respect is `proofSecond(a)` (a partial application that
    // desugarQuotientLift eta-expands + coerces). The outer lift varies the
    // first; its respect destructures the captured second argument so the
    // inner lift collapses on `mk` and the class-equality coercion fires on
    // `proofFirst(a, a', c, eA)`. proofFirst : (repA repA' repB) → R(repA,
    // repA') → R(body(repA,repB), body(repA',repB)); proofSecond : (repA
    // repB repB') → R(repB, repB') → R(body(repA,repB), body(repA,repB')).
    SurfaceExpressionPointer buildDefineByRepresentativesBinary(
        const std::string& firstRepresentativeName,
        const std::string& secondRepresentativeName,
        SurfaceExpressionPointer body,
        SurfaceExpressionPointer proofFirst,
        SurfaceExpressionPointer proofSecond,
        int line, int column) {
        const std::string argumentFirst = "_argumentOfDefinitionFirst";
        const std::string argumentSecond = "_argumentOfDefinitionSecond";
        auto identifier = [&](const std::string& name) {
            return makeSurfaceIdentifier(name, {}, line, column);
        };
        // Inner lift over the second representative; respect = proofSecond
        // partially applied to the (in-scope) first representative.
        std::vector<SurfaceExpressionPointer> proofSecondApplied;
        proofSecondApplied.push_back(identifier(firstRepresentativeName));
        SurfaceExpressionPointer innerRespect = makeSurfaceApplication(
            std::move(proofSecond), std::move(proofSecondApplied),
            line, column);
        std::vector<SurfaceExpressionPointer> innerLiftArguments;
        innerLiftArguments.push_back(singleBinderLambda(
            secondRepresentativeName, std::move(body), line, column));
        innerLiftArguments.push_back(std::move(innerRespect));
        innerLiftArguments.push_back(identifier(argumentSecond));
        SurfaceExpressionPointer innerLift = makeSurfaceApplication(
            identifier("Quotient.lift"), std::move(innerLiftArguments),
            line, column);
        // Outer respect: (a a' eA) ↦ cases argB { | c => proofFirst(a,a',c,eA) }.
        const std::string firstRep = "_firstRepresentative";
        const std::string firstRepPrime = "_firstRepresentativePrime";
        const std::string firstEquiv = "_firstEquivalence";
        const std::string casesRep = "_secondRepresentativeInRespect";
        std::vector<SurfaceExpressionPointer> proofFirstApplied;
        proofFirstApplied.push_back(identifier(firstRep));
        proofFirstApplied.push_back(identifier(firstRepPrime));
        proofFirstApplied.push_back(identifier(casesRep));
        proofFirstApplied.push_back(identifier(firstEquiv));
        SurfaceExpressionPointer casesBody = makeSurfaceApplication(
            std::move(proofFirst), std::move(proofFirstApplied), line, column);
        std::vector<SurfaceCasesClause> casesClauses;
        casesClauses.push_back(SurfaceCasesClause{
            makeSurfacePatternBareName(casesRep, line, column),
            std::move(casesBody), line, column});
        SurfaceExpressionPointer casesExpression = makeSurfaceCases(
            identifier(argumentSecond), std::move(casesClauses), line, column);
        // Nested single-name binders for the outer respect — the equivalence
        // domain `R(a, a')` depends on the earlier binders, which the
        // multi-name untyped-binder path mis-shifts.
        SurfaceExpressionPointer outerRespect = singleBinderLambda(
            firstRep,
            singleBinderLambda(
                firstRepPrime,
                singleBinderLambda(firstEquiv, std::move(casesExpression),
                                    line, column),
                line, column),
            line, column);
        std::vector<SurfaceExpressionPointer> outerLiftArguments;
        outerLiftArguments.push_back(singleBinderLambda(
            firstRepresentativeName, std::move(innerLift), line, column));
        outerLiftArguments.push_back(std::move(outerRespect));
        outerLiftArguments.push_back(identifier(argumentFirst));
        SurfaceExpressionPointer outerLift = makeSurfaceApplication(
            identifier("Quotient.lift"), std::move(outerLiftArguments),
            line, column);
        return singleBinderLambda(
            argumentFirst,
            singleBinderLambda(argumentSecond, std::move(outerLift),
                                line, column),
            line, column);
    }

    // Parses a `{ stmt; stmt; ...; final_expr }` block. Statement
    // forms supported:
    //   - `let pat := value;`            (tuple-pattern destructure)
    //   - `let name : type := value;`    (typed binding)
    //   - `claim name : type [by expr];` (let synonym; auto-prover
    //                                     fills if no `by`)
    //   - `witness expr with proof;`     (terminal; builds ⟨expr, proof⟩
    //                                     for ∃-shaped goals)
    //   - `suffices Q by Reduction;`     (then the rest of the block
    //                                     proves Q; the block's value
    //                                     becomes Reduction(rest))
    // and a trailing expression. The whole block desugars to nested
    // let-in / single-clause cases wrappers around the final
    // expression.
    SurfaceExpressionPointer parseBlockBody() {
        consumeAny();  // '{'
        auto result = parseBlockContents();
        expect(TokenKind::RightBrace, "ending block body");
        return result;
    }

    // Parses the inside of a block (without the surrounding `{ … }`).
    // Used both by parseBlockBody and recursively by the `suffices`
    // continuation.
    SurfaceExpressionPointer parseBlockContents() {
        // A leading block statement always wraps the block's tail. Four
        // forms share the same fold:
        //   `let n : T := V;` / `claim n : T [by V | { proof } | ];`
        //   `let ⟨pat⟩ := V;` / `obtain ⟨pat⟩ from V;`  (destructure)
        //   `suppose P as h;`                            (introduce hypothesis)
        //   `choose n such that P(n);`                   (Exists-elim w/ lookup)
        // Folded back-to-front around the final expression: pattern-let
        // and obtain produce a `cases` clause, plain let / claim a
        // `SurfaceLet`, suppose a `SurfaceLambda`, and choose a
        // `SurfaceChoose` (the elaborator handles the scope lookup).
        struct BlockWrapper {
            enum Kind { TypedLet, PatternLet, Suppose, Choose, Set,
                        NoteGoal, NoteAssertion, ChangeGoal,
                        SupposeForContradiction,
                        SupposeForContradictionForward, SupposeToProve };
            Kind kind = TypedLet;
            SurfacePatternPointer pattern;     // PatternLet, Suppose
                                               // (when set on Suppose,
                                               // wrap body in cases on
                                               // the introduced binder)
            std::string name;                  // TypedLet, Suppose, Choose, Set,
                                               // SupposeForContradiction/ToProve
                                               // (the assumed hypothesis name)
            SurfaceExpressionPointer type;     // TypedLet, Suppose, NoteGoal;
                                               // the assumed P for
                                               // SupposeForContradiction/ToProve
            SurfaceExpressionPointer value;    // TypedLet, PatternLet, Choose, Set,
                                               // NoteAssertion; the goal Q for
                                               // SupposeToProve
            std::string conditionName;         // Choose: optional `as <name>`
            SurfaceExpressionPointer source;   // Choose: optional `from <source>`;
                                               // the `{ block }` for SupposeToProve
                                               // and SupposeForContradictionForward
            // Only set for TypedLet wrappers that came from `calc … as NAME;`
            // with an explicit user-supplied NAME. Propagated onto the
            // resulting SurfaceLet so the elaborator can emit the
            // "explicit `as NAME` is redundant" warning when the body
            // never textually references the name.
            bool fromCalcAsBinding = false;
            int line = 0;
            int column = 0;
        };
        std::vector<BlockWrapper> wrappers;
        // `calc … as NAME;` or bare `calc …;` at statement position
        // gets parsed below and may turn out to NOT be a statement
        // (it's the final expression). In that case we stash the parsed
        // calc here and skip the trailing parseExpression() call.
        SurfaceExpressionPointer parsedFinalCalc;
        // A1: a bare expression at statement position parsed by the
        // fallthrough below and discovered to be the block's FINAL
        // expression (no `;`, or `;` immediately before `}`) is stashed
        // here so the post-loop code doesn't re-parse it.
        SurfaceExpressionPointer parsedFinalExpression;
        // A1 keyword-free chains: the bare-statement fallthrough's
        // speculation detected a relation chain at the cursor; the next
        // iteration routes it through the `calc` statement branch with
        // no anchor keyword.
        bool pendingBareChain = false;
        while (peek().kind == TokenKind::KeywordLet
               || peek().kind == TokenKind::KeywordClaim
               || peek().kind == TokenKind::KeywordObtain
               || peek().kind == TokenKind::KeywordSuppose
               || peek().kind == TokenKind::KeywordChoose
               || peek().kind == TokenKind::KeywordSet
               || peek().kind == TokenKind::KeywordTake
               || peek().kind == TokenKind::KeywordNote
               || peek().kind == TokenKind::KeywordChange
               || peek().kind == TokenKind::KeywordCalc
               || (peek().kind != TokenKind::RightBrace
                   && peek().kind != TokenKind::KeywordFrom
                   && peek().kind != TokenKind::KeywordContradiction
                   && peek().kind != TokenKind::KeywordDone
                   && peek().kind != TokenKind::KeywordOkay
                   && peek().kind != TokenKind::EndOfFile)) {
            // A1 keyword-free claims: a statement that starts with none
            // of the keywords above is a bare stated proposition (or a
            // proof term — the claim machinery's type-directed dispatch
            // covers both): `P;` reads exactly as `claim P;`, and
            // `P as NAME;` as the named form. Backward compatibility:
            // an expression followed by `;}` or `}` keeps its old
            // meaning as the block's final expression (so blocks whose
            // value is data are untouched); only `E; <more>` is a
            // statement.
            if (!pendingBareChain
                && peek().kind != TokenKind::KeywordLet
                && peek().kind != TokenKind::KeywordClaim
                && peek().kind != TokenKind::KeywordObtain
                && peek().kind != TokenKind::KeywordSuppose
                && peek().kind != TokenKind::KeywordChoose
                && peek().kind != TokenKind::KeywordSet
                && peek().kind != TokenKind::KeywordTake
                && peek().kind != TokenKind::KeywordNote
                && peek().kind != TokenKind::KeywordChange
                && peek().kind != TokenKind::KeywordCalc
                && peek().kind != TokenKind::KeywordDone
                && peek().kind != TokenKind::KeywordOkay) {
                Token statementStart = peek();
                // A1 keyword-free chains: a relation chain at statement
                // position is a calc with no anchor keyword. Detect it
                // by a rewound speculative parse of the WHOLE chain: it
                // must have at least two steps (a single relation stays
                // on the claim route) and must end at a statement
                // boundary — otherwise the relation is a subterm of a
                // larger proposition (`k = 0 ∨ …` continues past the
                // first equation) and the plain expression parser owns
                // it. (parseExpression cannot detect chains itself:
                // relations are non-associative there and a second
                // relation token is a parse error.)
                {
                    size_t probePosition = position_;
                    int probeCounter = anonymousClaimCounter_;
                    bool chainAhead = false;
                    try {
                        SurfaceExpressionPointer probeChain =
                            parseCalc(/*consumeCalcKeyword=*/false);
                        auto* calcNode =
                            std::get_if<SurfaceCalc>(&probeChain->node);
                        bool atStatementBoundary =
                            peek().kind == TokenKind::Semicolon
                            || peek().kind == TokenKind::KeywordAs
                            || peek().kind == TokenKind::RightBrace;
                        chainAhead = calcNode
                            && calcNode->steps.size() >= 2
                            && atStatementBoundary;
                    } catch (const ParseError&) {
                        chainAhead = false;
                    }
                    position_ = probePosition;
                    anonymousClaimCounter_ = probeCounter;
                    if (chainAhead) {
                        pendingBareChain = true;
                        continue;
                    }
                }
                SurfaceExpressionPointer expression = parseExpression();
                // Full claim-form parity: a bare statement takes every
                // hint shape the `claim` keyword does — `by <proof>`,
                // `by cases { … }`, `by substituting <eq>`,
                // `by induction on …` — via the same shared tail
                // parser, so the two forms can never drift.
                SurfaceExpressionPointer claimValue;
                bool hasByForm = (peek().kind == TokenKind::KeywordBy);
                if (hasByForm) {
                    claimValue = parseStructuredClaimTail(
                        statementStart, expression);
                } else {
                    claimValue = makeSurfaceStructuredClaim(
                        expression, /*label=*/"", /*byHint=*/nullptr,
                        /*byCases=*/false, {}, statementStart.line,
                        statementStart.column);
                }
                std::string bindingName;
                if (peek().kind == TokenKind::KeywordAs) {
                    consumeAny();  // 'as'
                    if (!isIdentifierLike(peek().kind)) {
                        throwHere("expected name after 'as'");
                    }
                    bindingName = consumeAny().lexeme;
                }
                bool isStatement = false;
                if (peek().kind == TokenKind::Semicolon
                    && peekAt(1).kind != TokenKind::RightBrace) {
                    isStatement = true;
                    consumeAny();  // ';'
                } else if (!bindingName.empty() || hasByForm) {
                    // `E as NAME` / `E by V` only mean anything as a
                    // statement (the old grammar rejected both here).
                    isStatement = true;
                    if (peek().kind == TokenKind::Semicolon) {
                        consumeAny();
                    }
                }
                if (!isStatement) {
                    parsedFinalExpression = std::move(expression);
                    break;
                }
                BlockWrapper wrapper;
                wrapper.kind = BlockWrapper::TypedLet;
                wrapper.name = bindingName.empty()
                    ? "_claim_anon_"
                          + std::to_string(statementStart.line) + "_"
                          + std::to_string(statementStart.column)
                    : bindingName;
                wrapper.type = expression;
                wrapper.value = std::move(claimValue);
                wrapper.line = statementStart.line;
                wrapper.column = statementStart.column;
                wrappers.push_back(std::move(wrapper));
                continue;
            }
            // `calc` at statement position has two shapes:
            //   - `calc … as NAME;`  (named binding for downstream use)
            //   - `calc …;`          (anonymous binding; the auto-prover
            //                         still finds it via type-match)
            // Both desugar to a TypedLet wrapper with type recovered
            // from the calc's endpoints (LHS = final RHS, all-= chain
            // only — mixed `=`/`≤` calcs must use the explicit
            // `claim NAME : TYPE by calc …` form). If the calc is
            // followed by neither `as` nor `;`, treat it as the block's
            // final expression instead.
            if (peek().kind == TokenKind::KeywordCalc || pendingBareChain) {
                bool keyworded = (peek().kind == TokenKind::KeywordCalc);
                pendingBareChain = false;
                Token calcToken = peek();
                SurfaceExpressionPointer calcExpression =
                    parseCalc(/*consumeCalcKeyword=*/keyworded);
                // A calc at statement position is always a binding (named via
                // `as`, else anonymous); the block's `}` then closes the goal
                // through the auto-prover, finding the calc's fact by
                // type-match. (A representative cross-equation is bridged to its
                // class equality by the `by_representatives` eliminator, not by
                // a calc-specific path.) There is no longer a calc-specific
                // "direct path": closing a block is uniformly the auto-prover.
                // The trailing `;` is optional
                // punctuation, so `calc … = c` and `calc … = c;` are identical.
                // The parsedFinalCalc escape only fires when a calc is followed
                // by none of `as`/`;`/`}` — not a block-statement position.
                if (peek().kind != TokenKind::KeywordAs
                    && peek().kind != TokenKind::Semicolon
                    && peek().kind != TokenKind::RightBrace) {
                    parsedFinalCalc = std::move(calcExpression);
                    break;
                }
                std::string statementName;
                bool fromCalcAsBinding = false;
                if (peek().kind == TokenKind::KeywordAs) {
                    consumeAny();  // 'as'
                    if (!isIdentifierLike(peek().kind)) {
                        throwHere("expected identifier after 'as'");
                    }
                    statementName = consumeAny().lexeme;
                    fromCalcAsBinding = true;
                } else {
                    // Anonymous: synthesise a name that won't collide.
                    statementName = "_calc_"
                        + std::to_string(calcToken.line) + "_"
                        + std::to_string(calcToken.column);
                }
                // Trailing `;` optional on the block's last calc (before `}`);
                // required as a separator between statements.
                if (peek().kind == TokenKind::Semicolon) {
                    consumeAny();
                } else if (peek().kind != TokenKind::RightBrace) {
                    expect(TokenKind::Semicolon, "ending calc statement");
                }
                auto* calcNode = std::get_if<SurfaceCalc>(
                    &calcExpression->node);
                if (!calcNode || calcNode->steps.empty()) {
                    throwHere("calc statement needs at least one step");
                }
                // Recover the chain's overall relation and direction.
                //   - any `<`/`>` → strict; sign from first non-= step
                //   - else any `≤`/`≥` → non-strict; sign from first non-=
                //   - else equality
                // Mixing forward (<, ≤) with backward (>, ≥) is rejected by
                // the calc elaborator itself, so we don't re-validate here.
                bool seenStrict = false;
                bool seenNonStrict = false;
                bool seenForward = false;
                bool seenBackward = false;
                // A generic-preorder step (`∣`, `⊆`, `≈`) carries its operator
                // in `relationOperator` and leaves `relation` at the Equality
                // placeholder. Such a chain composes to that operator, absorbing
                // interleaved `=` steps by transport — so the overall relation
                // is the generic operator: `p ∣ 0 = b` ⟹ `p ∣ b`.
                std::string genericRelation;
                for (const auto& step : calcNode->steps) {
                    if (!step.relationOperator.empty()) {
                        genericRelation = step.relationOperator;
                    }
                    switch (step.relation) {
                        case CalcRelation::LessThan:
                            seenStrict = true;
                            seenForward = true;
                            break;
                        case CalcRelation::GreaterThan:
                            seenStrict = true;
                            seenBackward = true;
                            break;
                        case CalcRelation::LessOrEqual:
                            seenNonStrict = true;
                            seenForward = true;
                            break;
                        case CalcRelation::GreaterOrEqual:
                            seenNonStrict = true;
                            seenBackward = true;
                            break;
                        case CalcRelation::Equality:
                            break;
                    }
                }
                std::string relationSymbol;
                if (!genericRelation.empty()) {
                    relationSymbol = genericRelation;
                } else if (seenStrict) {
                    relationSymbol = "<";
                } else if (seenNonStrict) {
                    relationSymbol = "≤";
                } else {
                    relationSymbol = "=";
                }
                SurfaceExpressionPointer firstEndpoint =
                    calcNode->initialExpression;
                SurfaceExpressionPointer lastEndpoint =
                    calcNode->steps.back().nextExpression;
                // Backward direction: `first > last` is rendered as
                // `last < first` (and similarly ≥ → ≤). Equality is
                // bidirectional, so always render as `first = last`.
                if (seenBackward && !seenForward) {
                    std::swap(firstEndpoint, lastEndpoint);
                }
                SurfaceExpressionPointer typeExpression =
                    makeSurfaceBinaryOperation(
                        relationSymbol,
                        std::move(firstEndpoint),
                        std::move(lastEndpoint),
                        calcToken.line, calcToken.column);
                BlockWrapper wrapper;
                wrapper.kind = BlockWrapper::TypedLet;
                wrapper.name = std::move(statementName);
                wrapper.type = std::move(typeExpression);
                wrapper.value = std::move(calcExpression);
                wrapper.fromCalcAsBinding = fromCalcAsBinding;
                wrapper.line = calcToken.line;
                wrapper.column = calcToken.column;
                wrappers.push_back(std::move(wrapper));
                continue;
            }
            // `claim` has two block-statement shapes:
            //   - Legacy:    `claim NAME : TYPE [by V];` (typed let-synonym)
            //   - Structured: `claim …` (any of the new structured-proof
            //     forms; chained by parseStructuredClaimSequence).
            // Disambiguate by lookahead — legacy needs `claim NAME :`.
            // If we're at the structured form, speculatively parse one
            // structured claim and peek at the next token:
            //   - `;`  →  mid-block statement. Wrap as an anonymous
            //              TypedLet so subsequent statements' auto-
            //              prover finds the proof by hypothesis match.
            //   - else →  not a statement (no proposition, no `;`,
            //              or followed by another `claim` for a chain).
            //              Restore position and let the existing break
            //              + parseExpression flow handle it (so
            //              parseStructuredClaimSequence keeps working).
            if ((peek().kind == TokenKind::KeywordClaim
                 && !looksLikeLegacyClaim())
                || peek().kind == TokenKind::KeywordDone
                || peek().kind == TokenKind::KeywordOkay) {
                Token claimToken = peek();
                size_t savedPosition = position_;
                int savedAnonymousClaimCounter = anonymousClaimCounter_;
                SurfaceExpressionPointer claimExpression =
                    parseStructuredClaim();
                auto* claimNode = std::get_if<SurfaceStructuredClaim>(
                    &claimExpression->node);
                if (claimNode && claimNode->proposition
                    && (peek().kind == TokenKind::Semicolon
                        || peek().kind == TokenKind::RightBrace)) {
                    // `claim P [by …];` mid-block, OR a final `claim P [by …]`
                    // immediately before `}` (the trailing `;` is optional —
                    // pure punctuation). Stash the proof under an anonymous
                    // name so the auto-prover — whether the next statement's or
                    // the implicit `done` that closes the block — finds it via
                    // structural hypothesis match.
                    SurfaceExpressionPointer propositionCopy =
                        claimNode->proposition;
                    if (peek().kind == TokenKind::Semicolon) {
                        consumeAny();  // ';'
                    }
                    BlockWrapper wrapper;
                    wrapper.kind = BlockWrapper::TypedLet;
                    wrapper.name = "_claim_anon_"
                        + std::to_string(claimToken.line) + "_"
                        + std::to_string(claimToken.column);
                    wrapper.type = std::move(propositionCopy);
                    wrapper.value = std::move(claimExpression);
                    wrapper.line = claimToken.line;
                    wrapper.column = claimToken.column;
                    wrappers.push_back(std::move(wrapper));
                    continue;
                }
                // Not the statement shape. Rewind and let the normal
                // break-and-parseExpression path handle it — that path
                // calls parseStructuredClaimSequence, which is the one
                // that knows how to chain `claim P` followed by another
                // `claim` via the implicit anonymous-let.
                position_ = savedPosition;
                anonymousClaimCounter_ = savedAnonymousClaimCounter;
                break;
            }
            Token statementToken = consumeAny();
            bool isClaim =
                statementToken.kind == TokenKind::KeywordClaim;
            bool isObtain =
                statementToken.kind == TokenKind::KeywordObtain;
            bool isSuppose =
                statementToken.kind == TokenKind::KeywordSuppose;
            bool isChoose =
                statementToken.kind == TokenKind::KeywordChoose;
            bool isSet =
                statementToken.kind == TokenKind::KeywordSet;
            bool isTake =
                statementToken.kind == TokenKind::KeywordTake;
            bool isNote =
                statementToken.kind == TokenKind::KeywordNote;
            bool isChange =
                statementToken.kind == TokenKind::KeywordChange;
            BlockWrapper wrapper;
            wrapper.line = statementToken.line;
            wrapper.column = statementToken.column;
            if (isSet) {
                if (!isIdentifierLike(peek().kind)) {
                    throwHere("expected identifier after 'set'");
                }
                Token nameToken = consumeAny();
                wrapper.kind = BlockWrapper::Set;
                wrapper.name = nameToken.lexeme;
                expect(TokenKind::Assign,
                       "after set name (set n := E;)");
                wrapper.value = parseExpression();
            } else if (isTake) {
                // `take <name> [as <pattern>] : <type>;` — introduce a
                // Pi-binder of type `<type>` named `<name>`. With the
                // optional `as <pattern>`, immediately destructure the
                // introduced binder via `cases <name> { | <pattern> => …}`.
                // The dispatch is type-directed at elaborate time: for
                // an inductive `<type>`, the standard cases path fires;
                // for a `Quotient(T, R)`, the quotient-cases path fires
                // (representative pattern). Reads as "let <name> be
                // <pattern>" / "let <name> = (a, b)".
                if (!isIdentifierLike(peek().kind)) {
                    throwHere("expected identifier after 'take'");
                }
                Token nameToken = consumeAny();
                SurfacePatternPointer destructurePattern;
                if (peek().kind == TokenKind::KeywordAs) {
                    consumeAny();  // 'as'
                    destructurePattern = parsePattern();
                }
                expect(TokenKind::Colon,
                       "after take name (take n : T; or take n as <pat> : T;)");
                wrapper.kind = BlockWrapper::Suppose;
                wrapper.name = nameToken.lexeme;
                wrapper.pattern = std::move(destructurePattern);
                wrapper.type = parseExpression();
                // `take x : T for proving Q { block };` — the
                // ∀-introduction analog of `suppose … for proving`: the
                // block proves Q under `x : T`, and `∀ (x : T). Q` enters
                // the context (anonymously) for the rest of the block.
                // Unrolls through the same wrapper as the suppose form —
                // a lambda over a data binder gives the Pi statement.
                if (peek().kind == TokenKind::Identifier
                    && peek().lexeme == "for"
                    && peekAt(1).kind == TokenKind::Identifier
                    && peekAt(1).lexeme == "proving") {
                    if (wrapper.pattern) {
                        throwHere("take … for proving takes a plain name, "
                                  "not an `as <pattern>` destructure");
                    }
                    consumeAny();  // 'for'
                    consumeAny();  // 'proving'
                    wrapper.kind = BlockWrapper::SupposeToProve;
                    wrapper.value = parseExpression();  // the goal Q
                    if (peek().kind != TokenKind::LeftBrace) {
                        throwHere("take … for proving Q needs a `{ … }` "
                                  "proof block "
                                  "(take x : T for proving Q { … });");
                    }
                    wrapper.source = parseExpression();  // the `{ block }`
                }
            } else if (isNote) {
                // `note goal : <type>;` — assert the current expected
                // type is definitionally equal to <type>. Reads as
                // math-prose "we need to show that …".
                //
                // `note <proposition>;` — assert that the proposition
                // is closable by the auto-prover. Reads as "note that
                // …" / "observe that …" — a parenthetical aside.
                //
                // Both are no-ops at the term level; the elaborator
                // runs the check then continues with the rest of the
                // block unchanged.
                if (peek().kind == TokenKind::KeywordGoal) {
                    consumeAny();  // 'goal'
                    expect(TokenKind::Colon,
                           "after 'note goal' (note goal : T;)");
                    wrapper.kind = BlockWrapper::NoteGoal;
                    wrapper.type = parseExpression();
                } else {
                    wrapper.kind = BlockWrapper::NoteAssertion;
                    wrapper.value = parseExpression();
                    // `note P by V;` — optional explicit proof (else the
                    // auto-prover closes P). Stashed in `wrapper.type`,
                    // which NoteAssertion otherwise leaves unused.
                    if (peek().kind == TokenKind::KeywordBy) {
                        consumeAny();  // 'by'
                        wrapper.type = parseExpression();
                    }
                }
            } else if (isChange) {
                // `change <type>;` — replace the current goal by the
                // definitionally-equal <type>, then continue the block AT
                // that type. The active counterpart of `note goal : T`.
                wrapper.kind = BlockWrapper::ChangeGoal;
                wrapper.type = parseExpression();
            } else if (isSuppose) {
                // `suppose <type> as <name>;` introduces a hypothesis.
                // With a complex `as <pattern>` (constructor or tuple
                // pattern), introduce a fresh hypothesis binder and
                // immediately destructure via `cases <fresh> { | <pat>
                // => body }`. Reads as "suppose ∃x. P(x), say
                // ⟨w, p⟩." with the destructure inline.
                //
                // Two trailing modifiers turn it into a classical or a
                // forward step:
                //   `suppose P [as h] for contradiction;` — assume P,
                //     derive False through the continuation, and prove
                //     the goal by double-negation elimination.
                //   `suppose P [as h] for proving Q { block };` — prove Q
                //     under the assumption P, adding `P → Q` to the
                //     context for the rest of the block.
                wrapper.type = parseExpression();
                // Optional `as <pattern>` — required for plain suppose,
                // optional for the modifier forms.
                SurfacePatternPointer asPattern;
                if (peek().kind == TokenKind::KeywordAs) {
                    consumeAny();  // 'as'
                    asPattern = parsePattern();
                }
                // `for`/`proving` are ordinary identifiers everywhere
                // except this slot — text-match so they stay usable as
                // variable names. One grammar, two exits:
                // `for contradiction` and `for proving Q`.
                bool isForModifier =
                    peek().kind == TokenKind::Identifier
                    && peek().lexeme == "for";
                bool isRetiredToProve =
                    peek().kind == TokenKind::Identifier
                    && peek().lexeme == "to"
                    && peekAt(1).kind == TokenKind::Identifier
                    && peekAt(1).lexeme == "prove";
                if (isRetiredToProve) {
                    throwHere("`suppose P to prove Q { … }` was renamed; "
                              "write `suppose P for proving Q { … }` "
                              "(one grammar with `for contradiction`)");
                }
                if (isForModifier) {
                    consumeAny();  // 'for'
                    if (peek().kind == TokenKind::Identifier
                        && peek().lexeme == "proving") {
                        consumeAny();  // 'proving'
                        wrapper.kind = BlockWrapper::SupposeToProve;
                        wrapper.value = parseExpression();  // the goal Q
                        if (peek().kind != TokenKind::LeftBrace) {
                            throwHere("suppose … for proving Q needs a "
                                      "`{ … }` proof block "
                                      "(suppose P for proving Q { … });");
                        }
                        wrapper.source = parseExpression();  // the `{ block }`
                    } else {
                        expect(TokenKind::KeywordContradiction,
                               "after 'for' in suppose "
                               "(suppose P for contradiction; / "
                               "suppose P for proving Q { … })");
                        // A braced `{ … }` makes it a forward step: the
                        // block derives False, the proven fact enters the
                        // context, and the rest of the proof continues at
                        // the original goal. Without braces the
                        // continuation IS the False-derivation and the
                        // construct proves the goal.
                        if (peek().kind == TokenKind::LeftBrace) {
                            wrapper.kind =
                                BlockWrapper::SupposeForContradictionForward;
                            wrapper.source = parseExpression();  // `{ block }`
                        } else {
                            wrapper.kind =
                                BlockWrapper::SupposeForContradiction;
                        }
                    }
                } else {
                    wrapper.kind = BlockWrapper::Suppose;
                    if (!asPattern) {
                        throwHere("expected 'as' after suppose proposition "
                                  "(suppose P as h;)");
                    }
                }
                // Resolve the `as` pattern into a name (bare) or, for
                // plain suppose, a fresh binder plus destructure pattern.
                if (asPattern) {
                    if (auto* bare = std::get_if<SurfacePatternBareName>(
                            &asPattern->node)) {
                        wrapper.name = bare->name;
                    } else if (wrapper.kind == BlockWrapper::Suppose) {
                        wrapper.name = "_supposed_"
                            + std::to_string(statementToken.line) + "_"
                            + std::to_string(statementToken.column);
                        wrapper.pattern = std::move(asPattern);
                    } else {
                        throwHere("suppose … for contradiction / for "
                                  "proving takes a plain `as <name>`, not "
                                  "a destructuring pattern");
                    }
                } else {
                    wrapper.name = "_supposed_"
                        + std::to_string(statementToken.line) + "_"
                        + std::to_string(statementToken.column);
                }
            } else if (isChoose) {
                wrapper.kind = BlockWrapper::Choose;
                if (!isIdentifierLike(peek().kind)) {
                    throwHere(
                        "expected identifier after 'choose'");
                }
                Token nameToken = consumeAny();
                wrapper.name = nameToken.lexeme;
                // Optional `such that <predicate>`. `such`/`that` are
                // ordinary identifiers everywhere except this slot —
                // text-match so they stay usable as variable names.
                if (peek().kind == TokenKind::Identifier
                    && peek().lexeme == "such") {
                    consumeAny();
                    if (peek().kind != TokenKind::Identifier
                        || peek().lexeme != "that") {
                        throwHere(
                            "expected 'that' after 'such' in choose");
                    }
                    consumeAny();
                    wrapper.value = parseExpression();
                }
                // Optional `as <conditionName>` — name the chosen fact
                // (otherwise it joins the context anonymously).
                if (peek().kind == TokenKind::KeywordAs) {
                    consumeAny();
                    if (!isIdentifierLike(peek().kind)) {
                        throwHere("expected a name after 'as' in choose");
                    }
                    wrapper.conditionName = consumeAny().lexeme;
                }
                // Optional `from <source>` — the existential's source: a
                // hypothesis to destructure, or a lemma to cite (shaped
                // by `such that`). Absent ⇒ scan scope for the most recent.
                if (peek().kind == TokenKind::KeywordFrom) {
                    consumeAny();
                    wrapper.source = parseExpression();
                }
                if (!wrapper.value && !wrapper.source) {
                    throwHere(
                        "choose needs `such that <prop>` and/or "
                        "`from <source>` (choose n such that P(n); "
                        "or choose n from h;)");
                }
            } else if (isObtain) {
                wrapper.kind = BlockWrapper::PatternLet;
                wrapper.pattern = parsePattern();
                // `obtain ⟨…⟩ from E;` destructures the value E.
                // `obtain ⟨…⟩ by Lemma;` cites Lemma with all explicit
                // arguments inferred (its premises recovered from context),
                // then destructures the result — the math-like "for some c,
                // … by <lemma>".
                if (peek().kind == TokenKind::KeywordBy) {
                    Token byToken = consumeAny();  // 'by'
                    wrapper.value = makeSurfaceCiteInferred(
                        parseExpression(), byToken.line, byToken.column);
                } else {
                    expect(TokenKind::KeywordFrom,
                           "after obtain-pattern (obtain ⟨…⟩ from E; "
                           "or obtain ⟨…⟩ by Lemma;)");
                    wrapper.value = parseExpression();
                }
            } else if (!isClaim && peek().kind == TokenKind::LeftAngle) {
                wrapper.kind = BlockWrapper::PatternLet;
                wrapper.pattern = parsePattern();
                expect(TokenKind::Assign,
                       "after let-pattern in block body");
                wrapper.value = parseExpression();
            } else if (!isClaim && isIdentifierLike(peek().kind)
                       && position_ + 1 < tokens_.size()
                       && tokens_[position_ + 1].kind
                           == TokenKind::ElementOf) {
                // `let <name> ∈ <type> [with <constraintPredicate>];`
                // — Phase 3 object intro with optional constraint
                // hypothesis. Desugars to one or two SurfaceLambda
                // wrappers (object binder, then anonymous constraint
                // binder if `with` is present). `∈` here parallels
                // set-membership in math; we keep `:` reserved for
                // type ascription in expressions.
                Token nameToken = consumeAny();
                consumeAny();  // '∈'
                SurfaceExpressionPointer objectType = parseExpression();
                // Stage the object binder as a Suppose wrapper (the
                // desugaring is identical to that of `suppose` — a
                // SurfaceLambda over the body).
                wrapper.kind = BlockWrapper::Suppose;
                wrapper.name = nameToken.lexeme;
                wrapper.type = std::move(objectType);
                wrappers.push_back(std::move(wrapper));
                // Optional `with <predicate>` clause adds an extra
                // wrapper for the anonymous constraint hypothesis;
                // single `;` at the end closes the whole statement.
                if (peek().kind == TokenKind::KeywordWith) {
                    Token withToken = consumeAny();
                    SurfaceExpressionPointer predicateExpression =
                        parseExpression();
                    BlockWrapper constraintWrapper;
                    constraintWrapper.kind = BlockWrapper::Suppose;
                    constraintWrapper.name = "_";
                    constraintWrapper.type =
                        std::move(predicateExpression);
                    constraintWrapper.line = withToken.line;
                    constraintWrapper.column = withToken.column;
                    wrappers.push_back(std::move(constraintWrapper));
                }
                expect(TokenKind::Semicolon,
                       "ending let-∈ statement");
                continue;
            } else if (isIdentifierLike(peek().kind)) {
                Token nameToken = consumeAny();
                wrapper.kind = BlockWrapper::TypedLet;
                wrapper.name = nameToken.lexeme;
                if (peek().kind != TokenKind::Colon) {
                    throwHere(isClaim
                        ? "claim requires ': type [by proof]'"
                        : "typed let in block body requires ': type "
                          "after the name (use let ⟨…⟩ := … ; for "
                          "destructuring without a type)");
                }
                consumeAny();  // ':'
                wrapper.type = parseExpression();
                if (isClaim) {
                    if (peek().kind == TokenKind::LeftBrace) {
                        // Footnote form: `claim P : T { proof_block };` is
                        // sugar for `claim P : T by { proof_block };`. Build
                        // the same structured-claim node, with the block as
                        // the by-hint, so it elaborates identically to the
                        // anonymous form.
                        wrapper.value = makeSurfaceStructuredClaim(
                            wrapper.type, /*label=*/"",
                            parseExpression(), /*byCases=*/false,
                            /*arms=*/{}, statementToken.line,
                            statementToken.column);
                    } else {
                        // A named claim is exactly an anonymous claim plus a
                        // let-binding: parse the `[by …]` tail with the SAME
                        // routine the anonymous `claim P by …` form uses, so
                        // the two elaborate identically (autoFillHintForClaim,
                        // `recalling`, the redundant-`by` check, diff-coerce
                        // fallback). Handles by cases / substitution /
                        // induction / EXPR and the no-`by` auto-prover case.
                        wrapper.value = parseStructuredClaimTail(
                            statementToken, wrapper.type, wrapper.name);
                    }
                } else {
                    expect(TokenKind::Assign, "after let type");
                    wrapper.value = parseExpression();
                }
            } else {
                throwHere(isClaim
                    ? "expected identifier after 'claim'"
                    : "expected identifier or '⟨' after 'let'");
            }
            const char* terminator =
                isClaim  ? "ending claim statement"
              : isObtain ? "ending obtain statement"
              : isSuppose ? "ending suppose statement"
              : isChoose ? "ending choose statement"
              : isSet    ? "ending set statement"
                         : "ending let statement in block body";
            // The `;` separates statements; on the LAST one (next token is
            // `}`) it is optional — a trailing `;` is pure punctuation, like a
            // trailing comma in a list, never a behaviour change. Between
            // statements it stays required.
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            } else if (peek().kind != TokenKind::RightBrace) {
                expect(TokenKind::Semicolon, terminator);
            }
            wrappers.push_back(std::move(wrapper));
        }
        SurfaceExpressionPointer finalExpression;
        if (peek().kind == TokenKind::KeywordSuffices) {
            // `suffices Q by Reduction; <rest>` becomes
            // `Reduction(<rest as a block>)` — the rest of the
            // statements prove Q, and Reduction : Q → current_goal
            // closes the original.
            Token sufficesToken = consumeAny();
            auto reducedGoal = parseExpression();
            expect(TokenKind::KeywordBy,
                   "after suffices goal");
            auto reductionLemma = parseExpression();
            expect(TokenKind::Semicolon,
                   "ending suffices statement");
            // The continuation must prove `reducedGoal`; we ascribe so
            // the elaborator typechecks accordingly.
            auto continuation = parseBlockContents();
            auto ascribedContinuation = makeSurfaceAscription(
                std::move(continuation), reducedGoal,
                sufficesToken.line, sufficesToken.column);
            std::vector<SurfaceExpressionPointer> arguments;
            arguments.push_back(std::move(ascribedContinuation));
            finalExpression = makeSurfaceApplication(
                std::move(reductionLemma),
                std::move(arguments),
                sufficesToken.line, sufficesToken.column);
        } else if (peek().kind == TokenKind::KeywordApply) {
            // `apply Expr;` — terminal block statement. Reads as "we
            // apply Lemma, producing this conclusion". The expression
            // becomes the block's trailing value. No new semantics
            // beyond letting the user mark the conclusion with the
            // math keyword.
            consumeAny();  // 'apply'
            finalExpression = parseExpression();
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            }
        } else if (peek().kind == TokenKind::KeywordContradiction) {
            // `contradiction;` — terminal. Defers the proof to the
            // auto-prover, which scans the local context for a pair
            // (H : P, H' : ¬P) and closes the goal via
            // `False.eliminate*(goal, H'(H))`.
            Token contradictionToken = consumeAny();
            if (peek().kind == TokenKind::Semicolon) consumeAny();
            finalExpression = makeSurfaceStructuredClaim(
                /*proposition=*/nullptr,
                /*label=*/"",
                /*byHint=*/nullptr,
                /*byCases=*/false,
                /*arms=*/{},
                contradictionToken.line,
                contradictionToken.column);
        } else if (parsedFinalCalc) {
            // The wrapper loop already parsed a `calc` and discovered it
            // wasn't followed by `as` or `;`, so it's the block's final
            // expression. Use the pre-parsed value directly.
            finalExpression = std::move(parsedFinalCalc);
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            }
        } else if (parsedFinalExpression) {
            // The A1 bare-statement fallthrough parsed an expression and
            // discovered it is the block's final expression (no `;`, or
            // a trailing `;` right before `}` — the old grammar's
            // optional final semicolon).
            finalExpression = std::move(parsedFinalExpression);
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            }
        } else if (peek().kind == TokenKind::RightBrace) {
            // No explicit final expression: the closing `}` engages the
            // auto-prover on the block's goal, with every prior step (claims,
            // calcs, hypotheses) in scope — an implicit `done`. So
            // `{ …; claim x < x; }` closes a `False` goal, and a plain
            // `{ …; claim <goal>; }` closes by finding that fact, neither
            // needing a written `done`. The prior steps stay as bindings (not
            // popped), so their facts reach the prover. This is literally the
            // `done` desugaring — `claim goal` — so closing a block, a `claim`,
            // and a `calc` step all run the one auto-prover, no exception.
            // An explicit `done`/`okay`/`goal`/proof term still works and is
            // preferred when an illuminating `by <reason>` is worth keeping.
            Token brace = peek();
            finalExpression = makeSurfaceStructuredClaim(
                makeSurfaceGoal(brace.line, brace.column), /*label=*/"",
                /*byHint=*/nullptr, /*byCases=*/false, /*arms=*/{},
                brace.line, brace.column);
        } else {
            finalExpression = parseExpression();
            // Optional trailing semicolon for the final expression.
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            }
        }
        // Apply wrappers in reverse order around the final expression.
        SurfaceExpressionPointer result = std::move(finalExpression);
        for (auto iterator = wrappers.rbegin();
             iterator != wrappers.rend(); ++iterator) {
            switch (iterator->kind) {
                case BlockWrapper::PatternLet: {
                    SurfaceCasesClause clause;
                    clause.pattern = std::move(iterator->pattern);
                    clause.body = std::move(result);
                    clause.line = iterator->line;
                    clause.column = iterator->column;
                    std::vector<SurfaceCasesClause> clauses;
                    clauses.push_back(std::move(clause));
                    result = makeSurfaceCases(
                        std::move(iterator->value),
                        std::move(clauses),
                        iterator->line, iterator->column);
                    break;
                }
                case BlockWrapper::TypedLet:
                    result = makeSurfaceLet(
                        std::move(iterator->name),
                        std::move(iterator->type),
                        std::move(iterator->value),
                        std::move(result),
                        iterator->line, iterator->column,
                        iterator->fromCalcAsBinding);
                    break;
                case BlockWrapper::Suppose: {
                    // With a destructure pattern (`take n as <pat> : T;`):
                    // wrap the rest of the block in
                    // `cases <name> { | <pat> => <result> }` first, then
                    // wrap that in the Pi-intro lambda. The cases
                    // elaboration dispatches on T's head (inductive →
                    // standard cases; Quotient → quotient-cases path).
                    if (iterator->pattern) {
                        SurfaceExpressionPointer scrutinee =
                            makeSurfaceIdentifier(iterator->name, {},
                                                   iterator->line,
                                                   iterator->column);
                        SurfaceCasesClause innerClause;
                        innerClause.pattern = iterator->pattern;
                        innerClause.body = std::move(result);
                        innerClause.line = iterator->line;
                        innerClause.column = iterator->column;
                        std::vector<SurfaceCasesClause> innerClauses;
                        innerClauses.push_back(std::move(innerClause));
                        result = makeSurfaceCases(
                            std::move(scrutinee),
                            std::move(innerClauses),
                            iterator->line, iterator->column);
                    }
                    SurfaceBinder binder;
                    binder.names.push_back(std::move(iterator->name));
                    binder.type = std::move(iterator->type);
                    binder.isImplicit = false;
                    result = makeSurfaceLambda(
                        std::move(binder),
                        std::move(result),
                        iterator->line, iterator->column,
                        /*fromStatementIntro=*/true);
                    break;
                }
                case BlockWrapper::SupposeForContradiction: {
                    // `suppose P as h for contradiction;` proves the goal
                    // Q by reductio: the continuation derives `False`
                    // under `h : P`, so `(h : P) ↦ <continuation>` proves
                    // `Not(P)`. With `P` the negation of the goal this is
                    // `Not(Not(Q))`, and `Logic.by_contradiction`
                    // eliminates the double negation — `proposition` is
                    // implicit, recovered from the goal.
                    SurfaceBinder binder;
                    binder.names.push_back(std::move(iterator->name));
                    binder.type = std::move(iterator->type);
                    binder.isImplicit = false;
                    SurfaceExpressionPointer refutation = makeSurfaceLambda(
                        std::move(binder),
                        std::move(result),
                        iterator->line, iterator->column,
                        /*fromStatementIntro=*/true);
                    std::vector<SurfaceExpressionPointer> arguments;
                    arguments.push_back(std::move(refutation));
                    result = makeSurfaceApplication(
                        makeSurfaceIdentifier("Logic.by_contradiction", {},
                                              iterator->line,
                                              iterator->column),
                        std::move(arguments),
                        iterator->line, iterator->column);
                    break;
                }
                case BlockWrapper::SupposeForContradictionForward: {
                    // `suppose P as h for contradiction { block };` is the
                    // forward step: the braced block derives False under
                    // `h : P`, establishing a fact into the context
                    // (anonymously, for the auto-prover to pick up by type)
                    // while the rest of the block continues at the original
                    // goal. What it establishes depends on `P`:
                    //   * `P = Not(X)` — `(h : Not(X)) ↦ block` proves
                    //     `Not(Not(X))`, and `Logic.by_contradiction`
                    //     eliminates the double negation to `X` (the inner
                    //     proposition, recovered by unifying `P` with
                    //     `Not(X)`). Reads "suppose ¬X for contradiction;
                    //     hence X".
                    //   * `P` not a negation — `(h : P) ↦ (block : False)`
                    //     is plain negation-introduction, establishing
                    //     `Not(P)` (a totality lemma then bridges, e.g.
                    //     `¬(0 < x)` to `x ≤ 0`).
                    bool assumptionIsNegation = false;
                    if (auto* unary = std::get_if<SurfaceUnaryOperation>(
                            &iterator->type->node)) {
                        assumptionIsNegation = unary->opSymbol == "¬";
                    } else if (auto* application =
                                   std::get_if<SurfaceApplication>(
                                       &iterator->type->node)) {
                        if (auto* head = std::get_if<SurfaceIdentifier>(
                                &application->function->node)) {
                            assumptionIsNegation =
                                head->qualifiedName == "Not"
                                && application->arguments.size() == 1;
                        }
                    } else if (auto* binary =
                                   std::get_if<SurfaceBinaryOperation>(
                                       &iterator->type->node)) {
                        // `a ≠ b` IS a negation — `suppose a ≠ b for
                        // contradiction { … }` establishes `a = b`.
                        assumptionIsNegation = binary->opSymbol == "≠";
                    }
                    // The braced block derives `False` under `h : P` in
                    // EVERY case, so ascribe it — a bare `done` inside the
                    // block then finds its goal. When `P = Not(X)` the
                    // `(h : Not(X)) ↦ (… : False)` lambda has type
                    // `Not(Not(X))`, which both feeds `Logic.by_contradiction`
                    // below and pins `proposition = X` from the argument
                    // itself (no longer leaning on the goal).
                    SurfaceExpressionPointer body =
                        makeSurfaceAscription(
                            std::move(iterator->source),
                            makeSurfaceIdentifier("False", {},
                                                  iterator->line,
                                                  iterator->column),
                            iterator->line, iterator->column);
                    SurfaceBinder binder;
                    binder.names.push_back(std::move(iterator->name));
                    binder.type = std::move(iterator->type);
                    binder.isImplicit = false;
                    SurfaceExpressionPointer refutation = makeSurfaceLambda(
                        std::move(binder),
                        std::move(body),
                        iterator->line, iterator->column,
                        /*fromStatementIntro=*/true);
                    SurfaceExpressionPointer provenFact;
                    if (assumptionIsNegation) {
                        std::vector<SurfaceExpressionPointer> arguments;
                        arguments.push_back(std::move(refutation));
                        provenFact = makeSurfaceApplication(
                            makeSurfaceIdentifier("Logic.by_contradiction", {},
                                                  iterator->line,
                                                  iterator->column),
                            std::move(arguments),
                            iterator->line, iterator->column);
                    } else {
                        provenFact = std::move(refutation);
                    }
                    result = makeSurfaceLet(
                        "_contradiction_fact_"
                            + std::to_string(iterator->line) + "_"
                            + std::to_string(iterator->column),
                        /*type=*/nullptr,
                        std::move(provenFact),
                        std::move(result),
                        iterator->line, iterator->column);
                    break;
                }
                case BlockWrapper::SupposeToProve: {
                    // `suppose P as h for proving Q { block };` proves Q under
                    // `h : P`, then binds the resulting `P → Q` into the
                    // context (anonymously, for the auto-prover to pick up
                    // by type) for the rest of the block. The block is
                    // ascribed to Q so it elaborates at that goal.
                    SurfaceExpressionPointer provedGoal =
                        makeSurfaceAscription(
                            std::move(iterator->source),
                            std::move(iterator->value),
                            iterator->line, iterator->column);
                    SurfaceBinder binder;
                    binder.names.push_back(std::move(iterator->name));
                    binder.type = std::move(iterator->type);
                    binder.isImplicit = false;
                    SurfaceExpressionPointer implication = makeSurfaceLambda(
                        std::move(binder),
                        std::move(provedGoal),
                        iterator->line, iterator->column,
                        /*fromStatementIntro=*/true);
                    result = makeSurfaceLet(
                        "_toprove_"
                            + std::to_string(iterator->line) + "_"
                            + std::to_string(iterator->column),
                        /*type=*/nullptr,
                        std::move(implication),
                        std::move(result),
                        iterator->line, iterator->column);
                    break;
                }
                case BlockWrapper::NoteGoal:
                    result = makeSurfaceNote(
                        std::move(iterator->type),
                        /*proposition=*/nullptr,
                        std::move(result),
                        iterator->line, iterator->column);
                    break;
                case BlockWrapper::NoteAssertion:
                    result = makeSurfaceNote(
                        /*goalType=*/nullptr,
                        std::move(iterator->value),
                        std::move(result),
                        iterator->line, iterator->column,
                        /*changesGoal=*/false,
                        /*proof=*/std::move(iterator->type));
                    break;
                case BlockWrapper::ChangeGoal:
                    result = makeSurfaceNote(
                        std::move(iterator->type),
                        /*proposition=*/nullptr,
                        std::move(result),
                        iterator->line, iterator->column,
                        /*changesGoal=*/true);
                    break;
                case BlockWrapper::Choose: {
                    result = makeSurfaceChoose(
                        std::move(iterator->name),
                        std::move(iterator->value),
                        std::move(result),
                        iterator->line, iterator->column,
                        std::move(iterator->conditionName),
                        std::move(iterator->source));
                    break;
                }
                case BlockWrapper::Set:
                    // Eager surface substitution: every reference to
                    // `name` in the rest of the block becomes a fresh
                    // copy of `value`, which then elaborates afresh at
                    // each site. This makes `n` and its definition
                    // definitionally interchangeable, sidestepping the
                    // kernel's lack of contextual zeta-reduction.
                    result = substituteSurfaceName(
                        std::move(result),
                        iterator->name,
                        std::move(iterator->value));
                    break;
            }
        }
        return result;
    }

    SurfacePatternCase parsePatternCase() {
        Token pipeToken = consumeAny();  // '|'
        SurfacePatternCase patternCase;
        patternCase.line = pipeToken.line;
        patternCase.column = pipeToken.column;
        patternCase.patterns.push_back(parsePattern());
        while (peek().kind == TokenKind::Comma) {
            consumeAny();
            patternCase.patterns.push_back(parsePattern());
        }
        expect(TokenKind::FatArrow, "between pattern and body");
        patternCase.body = parseExpression();
        return patternCase;
    }

    SurfacePatternPointer parsePattern() {
        // A pattern is either:
        //   name                       (variable binding, or nullary constructor)
        //   Foo.bar(pat, pat, ...)     (constructor application; qualified name allowed)
        //   _                          (wildcard)
        //   ⟨pat, pat, ...⟩            (anonymous tuple — destructures a
        //                                single-constructor inductive whose
        //                                identity the elaborator picks from
        //                                the scrutinee's type)
        if (peek().kind == TokenKind::LeftAngle) {
            Token openAngle = consumeAny();
            std::vector<SurfacePatternPointer> components;
            if (peek().kind == TokenKind::RightAngle) {
                throwHere("anonymous tuple pattern needs at least one "
                          "component");
            }
            components.push_back(parsePattern());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                components.push_back(parsePattern());
            }
            expect(TokenKind::RightAngle, "ending anonymous tuple pattern");
            return makeSurfacePatternTuple(std::move(components),
                                            openAngle.line, openAngle.column);
        }
        // Numeral patterns: `0` matches `zero` and `1 + n` matches
        // `successor(n)`; in general `N` and `N + p` desugar to N `successor`
        // wrappers around `zero` / the inner pattern `p`. This lets structural
        // recursion over a Natural read `| 0 => … | 1 + n => …` without naming
        // the constructors (the same `1 + n` form `by_induction` presents).
        if (peek().kind == TokenKind::NumericLiteral) {
            Token numeralToken = consumeAny();
            int successorCount = std::stoi(numeralToken.lexeme);
            SurfacePatternPointer inner;
            if (peek().kind == TokenKind::Plus) {
                consumeAny();  // '+'
                inner = parsePattern();
            } else {
                inner = makeSurfacePatternBareName(
                    "zero", numeralToken.line, numeralToken.column);
            }
            for (int i = 0; i < successorCount; ++i) {
                std::vector<SurfacePatternPointer> wrapped;
                wrapped.push_back(std::move(inner));
                inner = makeSurfacePatternConstructor(
                    "successor", std::move(wrapped),
                    numeralToken.line, numeralToken.column);
            }
            return inner;
        }
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected pattern");
        }
        Token nameToken = consumeAny();
        std::string fullName = nameToken.lexeme;
        while (peek().kind == TokenKind::Dot) {
            consumeAny();
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected identifier after '.' in pattern");
            }
            fullName += ".";
            fullName += consumeAny().lexeme;
        }
        if (peek().kind == TokenKind::LeftParen) {
            consumeAny();
            std::vector<SurfacePatternPointer> arguments;
            if (peek().kind == TokenKind::RightParen) {
                throwHere("constructor pattern arguments cannot be empty; "
                          "use bare '" + fullName
                          + "' for nullary constructors");
            }
            arguments.push_back(parsePattern());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                arguments.push_back(parsePattern());
            }
            expect(TokenKind::RightParen, "ending constructor pattern");
            return makeSurfacePatternConstructor(std::move(fullName),
                                                  std::move(arguments),
                                                  nameToken.line,
                                                  nameToken.column);
        }
        return makeSurfacePatternBareName(std::move(fullName),
                                           nameToken.line,
                                           nameToken.column);
    }

    // Consumes a dotted qualified name like "Natural.add_zero" and
    // returns the raw string. Distinct from parseQualifiedIdentifier
    // (which builds an expression node) — declarations need only the
    // name itself.
    std::string consumeQualifiedNameString() {
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected identifier");
        }
        std::string name = consumeAny().lexeme;
        while (peek().kind == TokenKind::Dot) {
            consumeAny();
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected identifier after '.'");
            }
            name += ".";
            name += consumeAny().lexeme;
        }
        return name;
    }

    // Universe parameter declaration form: `.{u, v}` after a name in a
    // declaration introduces u and v as universe-parameter names. Empty
    // result if no `.{...}` is present.
    std::vector<std::string> parseUniverseParameterList() {
        std::vector<std::string> parameters;
        if (peek().kind != TokenKind::DotLeftBrace) return parameters;
        consumeAny();
        if (peek().kind != TokenKind::RightBrace) {
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected universe parameter name");
            }
            parameters.push_back(consumeAny().lexeme);
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                if (!isIdentifierLike(peek().kind)) {
                    throwHere("expected universe parameter name");
                }
                parameters.push_back(consumeAny().lexeme);
            }
        }
        expect(TokenKind::RightBrace, "ending universe parameter list");
        return parameters;
    }

private:
    SurfaceExpressionPointer parseExpression() {
        if (peek().kind == TokenKind::KeywordLet) return parseLet();
        if (looksLikeMapsToLambda()) return parseMapsToLambda();
        return parseImplication();
    }

    // Lookahead for the keyword-free lambda `(binders)+ ↦ body`: skip the
    // leading run of balanced `(...)`/`{...}` binder groups and check that a
    // `↦` follows. Pure lookahead, so an ordinary parenthesised expression,
    // an ascription `(e : T)`, or a `{ … }` proof block (none followed by
    // `↦`) falls through to the normal expression parser.
    bool looksLikeMapsToLambda() {
        size_t index = position_;
        if (index >= tokens_.size()
            || !(tokens_[index].kind == TokenKind::LeftParen
                 || tokens_[index].kind == TokenKind::LeftBrace)) {
            return false;
        }
        while (index < tokens_.size()
               && (tokens_[index].kind == TokenKind::LeftParen
                   || tokens_[index].kind == TokenKind::LeftBrace)) {
            int depth = 0;
            do {
                TokenKind kind = tokens_[index].kind;
                // `.{` (a universe-argument list, as in `Equality.{0}`) opens
                // a brace closed by `}`, so it must count toward depth too —
                // otherwise a binder type mentioning `.{…}` unbalances the scan.
                if (kind == TokenKind::LeftParen || kind == TokenKind::LeftBrace
                    || kind == TokenKind::DotLeftBrace) {
                    depth++;
                } else if (kind == TokenKind::RightParen
                           || kind == TokenKind::RightBrace) {
                    depth--;
                }
                index++;
            } while (index < tokens_.size() && depth > 0);
        }
        return index < tokens_.size()
               && tokens_[index].kind == TokenKind::MapsTo;
    }

    // `(binders)+ ↦ body` — the lambda. Mirrors parseLambda but takes its
    // binders directly (no leading keyword) and closes on `↦`.
    SurfaceExpressionPointer parseMapsToLambda() {
        const Token start = peek();
        std::vector<SurfaceBinder> binders;
        while (peek().kind == TokenKind::LeftParen
               || peek().kind == TokenKind::LeftBrace) {
            binders.push_back(parseExplicitBinder());
        }
        if (binders.empty()) {
            throwHere("expected at least one binder before '↦'");
        }
        expect(TokenKind::MapsTo, "after binders in lambda");
        auto body = parseExpression();
        for (auto iterator = binders.rbegin(); iterator != binders.rend();
             ++iterator) {
            body = makeSurfaceLambda(std::move(*iterator), std::move(body),
                                      start.line, start.column);
        }
        return body;
    }

    SurfaceExpressionPointer parseLet() {
        const Token& start = consumeAny();  // 'let'
        if (peek().kind == TokenKind::LeftAngle) {
            // Pattern-form destructuring let: `let ⟨a, b⟩ := value in body`.
            // Desugars to a single-clause `cases value { | ⟨a, b⟩ => body }`
            // — the elaborator picks the destructuring constructor from
            // the value's type.
            auto pattern = parsePattern();
            expect(TokenKind::Assign, "after let pattern");
            auto value = parseExpression();
            expect(TokenKind::KeywordIn, "after let value");
            auto body = parseExpression();
            SurfaceCasesClause clause;
            clause.pattern = std::move(pattern);
            clause.body = std::move(body);
            clause.line = start.line;
            clause.column = start.column;
            std::vector<SurfaceCasesClause> clauses;
            clauses.push_back(std::move(clause));
            return makeSurfaceCases(std::move(value), std::move(clauses),
                                     start.line, start.column);
        }
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected identifier or anonymous tuple pattern "
                      "after 'let'");
        }
        std::string name = consumeAny().lexeme;
        expect(TokenKind::Colon, "after let name");
        auto type = parseExpression();
        expect(TokenKind::Assign, "after let type");
        auto value = parseExpression();
        expect(TokenKind::KeywordIn, "after let value");
        auto body = parseExpression();
        return makeSurfaceLet(std::move(name), std::move(type),
                              std::move(value), std::move(body),
                              start.line, start.column);
    }

    // Helper used by lambda parsing. Accepts `(name+ : type)` for an
    // explicit binder and `{name+ : type}` for an implicit binder.
    // Throws on malformed binders.
    SurfaceBinder parseExplicitBinder() {
        bool isImplicit = false;
        TokenKind closing = TokenKind::RightParen;
        if (peek().kind == TokenKind::LeftBrace) {
            isImplicit = true;
            closing = TokenKind::RightBrace;
            consumeAny();  // '{'
        } else {
            expect(TokenKind::LeftParen, "starting binder");
        }
        std::vector<std::string> names;
        for (;;) {
            if (isIdentifierLike(peek().kind)) {
                names.push_back(consumeAny().lexeme);
                continue;
            }
            // `(<op>)` introduces an operator-symbol-named parameter
            // (e.g. `((·) : G → G → G)`).
            if (peek().kind == TokenKind::LeftParen
                && position_ + 2 < tokens_.size()
                && isOperatorSymbolToken(tokens_[position_ + 1].kind)
                && tokens_[position_ + 2].kind ==
                       TokenKind::RightParen) {
                consumeAny();  // '('
                names.push_back(consumeAny().lexeme);
                consumeAny();  // ')'
                continue;
            }
            break;
        }
        if (names.empty()) {
            if (isKeyword(peek().kind)) {
                throwHere(
                    "'" + peek().lexeme + "' is a reserved word and cannot "
                    "be used as a binder name — choose another name");
            }
            throwHere("expected at least one name in binder");
        }
        expect(TokenKind::Colon, "in binder");
        auto type = parseExpression();
        expect(closing,
               isImplicit ? "ending implicit binder"
                          : "ending binder");
        SurfaceBinder binder{std::move(names), std::move(type),
                              isImplicit};
        return binder;
    }

    // Lookahead-with-restore variant for parseImplication. Returns
    // nullopt if the input doesn't match a binder; restores the parser
    // position so the caller can fall back to expression parsing.
    std::optional<SurfaceBinder> tryParseExplicitBinder() {
        size_t save = position_;
        bool isImplicit = false;
        TokenKind closing = TokenKind::RightParen;
        if (peek().kind == TokenKind::LeftBrace) {
            isImplicit = true;
            closing = TokenKind::RightBrace;
            consumeAny();  // '{'
        } else if (peek().kind == TokenKind::LeftParen) {
            consumeAny();  // '('
        } else {
            return std::nullopt;
        }
        std::vector<std::string> names;
        for (;;) {
            if (isIdentifierLike(peek().kind)) {
                names.push_back(consumeAny().lexeme);
                continue;
            }
            if (peek().kind == TokenKind::LeftParen
                && position_ + 2 < tokens_.size()
                && isOperatorSymbolToken(tokens_[position_ + 1].kind)
                && tokens_[position_ + 2].kind ==
                       TokenKind::RightParen) {
                consumeAny();  // '('
                names.push_back(consumeAny().lexeme);
                consumeAny();  // ')'
                continue;
            }
            break;
        }
        if (names.empty() || peek().kind != TokenKind::Colon) {
            position_ = save;
            return std::nullopt;
        }
        consumeAny();  // ':'
        SurfaceExpressionPointer type;
        try {
            type = parseExpression();
        } catch (const ParseError&) {
            position_ = save;
            return std::nullopt;
        }
        if (peek().kind != closing) {
            position_ = save;
            return std::nullopt;
        }
        consumeAny();
        SurfaceBinder binder{std::move(names), std::move(type),
                              isImplicit};
        return binder;
    }

    // Pi types and implication. Right-associative. Tries explicit
    // `(name+ : T) → U` or implicit `{name+ : T} → U` form first;
    // otherwise parses a regular expression and looks for a following `→`.
    SurfaceExpressionPointer parseImplication() {
        size_t save = position_;
        if (peek().kind == TokenKind::LeftParen
            || peek().kind == TokenKind::LeftBrace) {
            auto binderOpt = tryParseExplicitBinder();
            if (binderOpt) {
                if (peek().kind == TokenKind::Arrow) {
                    Token arrowToken = consumeAny();
                    auto codomain = parseImplication();
                    return makeSurfacePiType(std::move(*binderOpt),
                                              std::move(codomain),
                                              arrowToken.line,
                                              arrowToken.column);
                }
                // Not followed by `→`; reinterpret as a plain expression.
                position_ = save;
            }
        }
        auto left = parseLogicalOr();
        if (peek().kind == TokenKind::Arrow) {
            Token arrowToken = consumeAny();
            auto codomain = parseImplication();
            SurfaceBinder anonymous{{}, std::move(left)};
            return makeSurfacePiType(std::move(anonymous), std::move(codomain),
                                      arrowToken.line, arrowToken.column);
        }
        return left;
    }

    // ∧ and ∨ are RIGHT-associative — `a ∧ b ∧ c` parses as
    // `a ∧ (b ∧ c)`, matching the kernel's `And(A, B)` shape (whose
    // second component is the inductive itself) and standard math
    // convention.
    SurfaceExpressionPointer parseLogicalOr() {
        auto left = parseLogicalAnd();
        if (peek().kind == TokenKind::LogicalOr) {
            Token op = consumeAny();
            auto right = parseLogicalOr();
            return makeSurfaceBinaryOperation("∨", std::move(left),
                                                std::move(right),
                                                op.line, op.column);
        }
        return left;
    }

    SurfaceExpressionPointer parseLogicalAnd() {
        auto left = parseEquality();
        if (peek().kind == TokenKind::LogicalAnd) {
            Token op = consumeAny();
            auto right = parseLogicalAnd();
            return makeSurfaceBinaryOperation("∧", std::move(left),
                                                std::move(right),
                                                op.line, op.column);
        }
        return left;
    }

    // Non-associative: `a = b = c` is a parse error. Forces users to
    // reach for `calc` chains or explicit parens.
    SurfaceExpressionPointer parseEquality() {
        auto left = parseRelational();
        TokenKind kind = peek().kind;
        if (kind == TokenKind::Equal || kind == TokenKind::NotEqual) {
            Token op = consumeAny();
            auto right = parseRelational();
            if (peek().kind == TokenKind::Equal
                || peek().kind == TokenKind::NotEqual) {
                throwHere("equality operators are non-associative; "
                          "parenthesise or use a calc chain");
            }
            const char* sym = (op.kind == TokenKind::Equal) ? "=" : "≠";
            left = makeSurfaceBinaryOperation(sym, std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    static bool isRelationalKind(TokenKind kind) {
        return kind == TokenKind::Less || kind == TokenKind::LessOrEqual
            || kind == TokenKind::Greater || kind == TokenKind::GreaterOrEqual
            || kind == TokenKind::Divides
            || kind == TokenKind::NotDivides
            || kind == TokenKind::NotLessOrEqual
            || kind == TokenKind::ElementOf
            || kind == TokenKind::NotElementOf
            || kind == TokenKind::SubsetOf
            || kind == TokenKind::NotSubsetOf;
    }

    SurfaceExpressionPointer parseRelational() {
        auto left = parseAdditive();
        if (isRelationalKind(peek().kind)) {
            Token op = consumeAny();
            auto right = parseAdditive();
            if (isRelationalKind(peek().kind)) {
                throwHere("relational operators are non-associative");
            }
            // `>` / `≥` are pure notation for the reverse of `<` / `≤`:
            // `a > b` is `b < a` and `a ≥ b` is `b ≤ a`. We desugar them
            // here by swapping the operands and emitting `<` / `≤`, so only
            // those two operators ever need a registered meaning and every
            // ordered type gets `>` / `≥` for free. (The calc machinery does
            // the same swap for backward chains — see the calc renderer.)
            const char* sym = "?";
            bool reversed = false;
            switch (op.kind) {
                case TokenKind::Less:           sym = "<"; break;
                case TokenKind::LessOrEqual:    sym = "≤"; break;
                case TokenKind::Greater:        sym = "<"; reversed = true; break;
                case TokenKind::GreaterOrEqual: sym = "≤"; reversed = true; break;
                case TokenKind::Divides:        sym = "∣"; break;
                case TokenKind::NotDivides:     sym = "∤"; break;
                case TokenKind::NotLessOrEqual: sym = "≰"; break;
                case TokenKind::ElementOf:      sym = "∈"; break;
                case TokenKind::NotElementOf:   sym = "∉"; break;
                case TokenKind::SubsetOf:       sym = "⊆"; break;
                case TokenKind::NotSubsetOf:    sym = "⊈"; break;
                default: break;
            }
            if (reversed) std::swap(left, right);
            left = makeSurfaceBinaryOperation(sym, std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    // Flatten a left-associated chain of `symbol` nodes into the ellipsis
    // prefix list. A node under a DIFFERENT operator at the same
    // precedence level is the §9 mixed-operator error; any non-operator
    // node is a single prefix term.
    void flattenEllipsisPrefix(const SurfaceExpressionPointer& node,
                               const std::string& symbol,
                               std::vector<SurfaceExpressionPointer>& out) {
        if (auto* binary =
                std::get_if<SurfaceBinaryOperation>(&node->node)) {
            if (binary->opSymbol == symbol) {
                flattenEllipsisPrefix(binary->left, symbol, out);
                out.push_back(binary->right);
                return;
            }
            // Only a SAME-PRECEDENCE sibling operator is a mixed chain
            // (`1 + 2 - ... - n`). A tighter-binding operator is a
            // legitimate leaf (`1*0 + ... + k*(k-1)`, `1/1 + 1/2 + …`).
            auto precedenceGroup = [](const std::string& op) {
                if (op == "+" || op == "-") return 1;
                if (op == "*" || op == "/" || op == "·") return 2;
                return 0;
            };
            if (precedenceGroup(binary->opSymbol) != 0
                && precedenceGroup(binary->opSymbol)
                       == precedenceGroup(symbol)) {
                throwHere("ellipsis requires a single operation; found `"
                          + symbol + "` and `" + binary->opSymbol + "`");
            }
        }
        out.push_back(node);
    }

    SurfaceExpressionPointer parseAdditive() {
        auto left = parseMultiplicative();
        while (peek().kind == TokenKind::Plus
               || peek().kind == TokenKind::Minus) {
            Token op = consumeAny();
            const char* sym = (op.kind == TokenKind::Plus) ? "+" : "-";
            if (peek().kind == TokenKind::Ellipsis) {
                // `t₁ op … op ... op g` — ellipsis fold notation.
                consumeAny();  // '...'
                if (peek().kind != op.kind) {
                    throwHere(std::string("after `...` expected `") + sym
                              + "` and the general term "
                              "(t₁ " + sym + " … " + sym + " ... " + sym
                              + " g)");
                }
                consumeAny();  // the operator after '...'
                auto general = parseMultiplicative();
                std::vector<SurfaceExpressionPointer> prefix;
                flattenEllipsisPrefix(left, sym, prefix);
                // Trailing `op ...` after the general term: an infinite
                // SERIES (`1/2 + 1/4 + ... + g + ... = S`), legal only as
                // one side of an equality.
                if (peek().kind == op.kind
                    && peekAt(1).kind == TokenKind::Ellipsis) {
                    consumeAny();  // the operator
                    consumeAny();  // '...'
                    return makeSurfaceSeriesFold(
                        sym, std::move(prefix), std::move(general),
                        op.line, op.column);
                }
                return makeSurfaceEllipsisFold(
                    sym, std::move(prefix), std::move(general),
                    op.line, op.column);
            }
            auto right = parseMultiplicative();
            left = makeSurfaceBinaryOperation(sym, std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    SurfaceExpressionPointer parseMultiplicative() {
        auto left = parsePower();
        while (peek().kind == TokenKind::Star
               || peek().kind == TokenKind::Slash
               || peek().kind == TokenKind::CenterDot) {
            Token op = consumeAny();
            const char* sym = nullptr;
            switch (op.kind) {
                case TokenKind::Star:      sym = "*"; break;
                case TokenKind::Slash:     sym = "/"; break;
                case TokenKind::CenterDot: sym = "·"; break;
                default: break;
            }
            if (peek().kind == TokenKind::Ellipsis) {
                consumeAny();  // '...'
                if (peek().kind != op.kind) {
                    throwHere(std::string("after `...` expected `") + sym
                              + "` and the general term "
                              "(t₁ " + sym + " … " + sym + " ... " + sym
                              + " g)");
                }
                consumeAny();  // the operator after '...'
                auto general = parsePower();
                std::vector<SurfaceExpressionPointer> prefix;
                flattenEllipsisPrefix(left, sym, prefix);
                if (peek().kind == op.kind
                    && peekAt(1).kind == TokenKind::Ellipsis) {
                    consumeAny();  // the operator
                    consumeAny();  // '...'
                    return makeSurfaceSeriesFold(
                        sym, std::move(prefix), std::move(general),
                        op.line, op.column);
                }
                return makeSurfaceEllipsisFold(
                    sym, std::move(prefix), std::move(general),
                    op.line, op.column);
            }
            auto right = parsePower();
            left = makeSurfaceBinaryOperation(sym, std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    // Right-associative: a ^ b ^ c parses as a ^ (b ^ c).
    SurfaceExpressionPointer parsePower() {
        auto left = parseUnary();
        if (peek().kind == TokenKind::Caret) {
            Token op = consumeAny();
            auto right = parsePower();
            left = makeSurfaceBinaryOperation("^", std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    SurfaceExpressionPointer parseUnary() {
        if (peek().kind == TokenKind::Minus) {
            Token op = consumeAny();
            auto operand = parseUnary();
            return makeSurfaceUnaryOperation("-", std::move(operand),
                                              op.line, op.column);
        }
        if (peek().kind == TokenKind::LogicalNot) {
            Token op = consumeAny();
            auto operand = parseUnary();
            return makeSurfaceUnaryOperation("¬", std::move(operand),
                                              op.line, op.column);
        }
        // Postfix operators bind tighter than any binary operator and
        // attach to the application/atom just parsed. `g⁻¹` wraps `g`;
        // `a · b⁻¹` parses as `a · (b⁻¹)`; `g⁻¹⁻¹` chains; `k!` likewise.
        // `k²` is parse-time sugar for `k * k` (the shared immutable
        // surface node appears twice), so every downstream system —
        // operator resolution at any carrier, `ring`, the indexes —
        // sees ordinary multiplication.
        auto base = parseApplication();
        while (peek().kind == TokenKind::InverseSuperscript
               || peek().kind == TokenKind::Bang
               || peek().kind == TokenKind::SquareSuperscript) {
            Token op = consumeAny();
            if (op.kind == TokenKind::SquareSuperscript) {
                base = makeSurfaceBinaryOperation(
                    "*", base, base, op.line, op.column);
            } else {
                base = makeSurfaceUnaryOperation(
                    op.lexeme, std::move(base), op.line, op.column);
            }
        }
        return base;
    }

    // Function call: head(arg1, arg2, ...). Tighter than any operator.
    // Empty argument lists `f()` are disallowed; a bare name `f` is a
    // valid expression (the function value itself).
    SurfaceExpressionPointer parseApplication() {
        auto head = parseAtom();
        while (peek().kind == TokenKind::LeftParen) {
            Token openParen = consumeAny();
            if (peek().kind == TokenKind::RightParen) {
                throwHere("empty argument list 'f()' is not allowed");
            }
            std::vector<SurfaceArgument> arguments;
            arguments.push_back(parseArgument());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                arguments.push_back(parseArgument());
            }
            expect(TokenKind::RightParen, "ending argument list");
            head = makeSurfaceApplication(std::move(head),
                                           std::move(arguments),
                                           openParen.line, openParen.column);
        }
        return head;
    }

    // A single argument: either `<identifier> := <expr>` (named) or
    // just `<expr>` (positional). Named args use `:=` because `=` is
    // the equality operator. The leading-identifier lookahead is
    // restoring (an expression starting with an identifier that
    // *isn't* followed by `:=` falls back to expression parsing).
    SurfaceArgument parseArgument() {
        size_t save = position_;
        if (isIdentifierLike(peek().kind)) {
            Token nameToken = consumeAny();
            if (peek().kind == TokenKind::Assign) {
                consumeAny();  // ':='
                SurfaceArgument argument;
                argument.name = nameToken.lexeme;
                argument.value = parseExpression();
                return argument;
            }
            position_ = save;
        }
        SurfaceArgument argument;
        argument.name = "";
        argument.value = parseExpression();
        return argument;
    }

    // `sum k from LO to HI of BODY` / `product k from LO to HI of BODY` /
    // `fold (op) k from LO to HI of BODY` — the explicit fold binder form.
    // `to` and `of` are text-matched identifiers (the `suppose … for
    // proving` treatment), so they stay usable as variable names; the bounds parse
    // as full expressions and stop at them naturally (no juxtaposition
    // application exists). The body takes the longest expression to the
    // right — parenthesise the whole form to continue an enclosing
    // expression: `(sum k from 0 to n of f(k)) + 1`.
    SurfaceExpressionPointer parseFoldBinder() {
        Token head = consumeAny();  // 'sum' / 'product' / 'fold'
        std::string operatorSymbol;
        if (head.lexeme == "sum") {
            operatorSymbol = "+";
        } else if (head.lexeme == "product") {
            operatorSymbol = "*";
        } else {
            expect(TokenKind::LeftParen,
                   "after 'fold' (fold (op) k from LO to HI of BODY)");
            if (peek().kind == TokenKind::Identifier
                || peek().kind == TokenKind::EndOfFile) {
                throwHere("expected an operator symbol like '+' or '*' "
                          "inside the parentheses of `fold (op)`");
            }
            operatorSymbol = consumeAny().lexeme;
            expect(TokenKind::RightParen,
                   "after the operator symbol in `fold (op)`");
        }
        if (peek().kind != TokenKind::Identifier) {
            throwHere("expected the bound index variable "
                      "(sum k from LO to HI of BODY)");
        }
        std::string binderName = consumeAny().lexeme;
        expect(TokenKind::KeywordFrom,
               "before the lower bound (sum k from LO to HI of BODY)");
        SurfaceExpressionPointer lowerBound = parseExpression();
        if (peek().kind != TokenKind::Identifier || peek().lexeme != "to") {
            throwHere("expected 'to' between the fold bounds "
                      "(sum k from LO to HI of BODY)");
        }
        consumeAny();  // 'to'
        SurfaceExpressionPointer upperBound = parseExpression();
        if (peek().kind != TokenKind::Identifier || peek().lexeme != "of") {
            throwHere("expected 'of' before the fold body "
                      "(sum k from LO to HI of BODY)");
        }
        consumeAny();  // 'of'
        SurfaceExpressionPointer body = parseExpression();
        return makeSurfaceFoldBinder(
            std::move(operatorSymbol), std::move(binderName),
            std::move(lowerBound), std::move(upperBound), std::move(body),
            head.line, head.column);
    }

    SurfaceExpressionPointer parseAtom() {
        const Token& current = peek();
        // The fold binder form (A8): `sum k from … to … of …`,
        // `product k from … to … of …`, `fold (op) k from … to … of …`.
        // `sum`/`product`/`fold` stay ordinary identifiers everywhere
        // else (the library uses `product` as a local name), so the form
        // is claimed by lookahead only: head word, then a bound-variable
        // identifier (after `(op)` for `fold`), then the `from` keyword —
        // a shape no other expression can start with (there is no
        // juxtaposition application).
        if (current.kind == TokenKind::Identifier
            && (current.lexeme == "sum" || current.lexeme == "product")
            && peekAt(1).kind == TokenKind::Identifier
            && peekAt(2).kind == TokenKind::KeywordFrom) {
            return parseFoldBinder();
        }
        if (current.kind == TokenKind::Identifier
            && current.lexeme == "fold"
            && peekAt(1).kind == TokenKind::LeftParen
            && peekAt(2).kind != TokenKind::Identifier
            && peekAt(3).kind == TokenKind::RightParen
            && peekAt(4).kind == TokenKind::Identifier
            && peekAt(5).kind == TokenKind::KeywordFrom) {
            return parseFoldBinder();
        }
        // `sorry` and `ring` must short-circuit before the
        // identifier-like path because they're also contextual
        // keywords (so they can appear as name segments inside
        // qualified identifiers like `Internal.sorry` or
        // `Integer.ring`); in expression position the keyword form
        // takes priority.
        if (current.kind == TokenKind::KeywordSorry) {
            Token sorryToken = consumeAny();
            return makeSurfaceSorry(sorryToken.line,
                                     sorryToken.column);
        }
        if (current.kind == TokenKind::KeywordRing) {
            Token ringToken = consumeAny();
            return makeSurfaceRing(ringToken.line, ringToken.column);
        }
        if (current.kind == TokenKind::KeywordGroup) {
            Token token = consumeAny();
            return makeSurfaceGroup(true, token.line, token.column);
        }
        if (current.kind == TokenKind::KeywordMonoid) {
            Token token = consumeAny();
            return makeSurfaceGroup(false, token.line, token.column);
        }
        if (current.kind == TokenKind::KeywordField) {
            Token fieldToken = consumeAny();
            std::vector<SurfaceExpressionPointer> hypotheses;
            // `field(h1, …)` lists one nonzero hypothesis per
            // `reciprocal_function` argument (the total-reciprocal form). A
            // bare `field` (or `field()`) supplies none: over a partial
            // reciprocal the nonzero proof rides on each `/`, so the tactic
            // synthesises the cancellations itself.
            if (peek().kind == TokenKind::LeftParen) {
                consumeAny();  // '('
                if (peek().kind != TokenKind::RightParen) {
                    hypotheses.push_back(parseExpression());
                    while (peek().kind == TokenKind::Comma) {
                        consumeAny();
                        hypotheses.push_back(parseExpression());
                    }
                }
                expect(TokenKind::RightParen,
                       "ending `field` argument list");
            }
            return makeSurfaceField(std::move(hypotheses),
                                     fieldToken.line, fieldToken.column);
        }
        if (current.kind == TokenKind::KeywordLinearCombination) {
            Token tok = consumeAny();
            if (peek().kind != TokenKind::LeftParen) {
                throwHere("`linear_combination` requires a parenthesized "
                          "equation proof (e.g. `linear_combination(h)`)");
            }
            consumeAny();  // '('
            SurfaceExpressionPointer combination = parseExpression();
            expect(TokenKind::RightParen,
                   "ending `linear_combination` argument");
            return makeSurfaceLinearCombination(std::move(combination),
                                                 tok.line, tok.column);
        }
        // `claim` at expression position starts a structured proof.
        // Checked BEFORE isIdentifierLike, because `claim` is a
        // contextual keyword (and so would otherwise be treated as a
        // bare identifier). Block-statement `claim NAME : T [by V];`
        // is parsed earlier via parseBlockContents and never reaches
        // here, so the two forms don't collide. A claim immediately
        // followed by another `claim` chains via SurfaceLet so the
        // proposition of the first is in scope for the rest.
        if (current.kind == TokenKind::KeywordClaim
            || current.kind == TokenKind::KeywordDone
            || current.kind == TokenKind::KeywordOkay) {
            // `done` and `okay` are bare-`claim` synonyms — math-
            // style closers ("the proof is done here" / Aroca-style
            // "okay, that proves it"). Both lex distinctly but
            // dispatch to the same parser path; parseStructuredClaim
            // detects the alternate spellings and treats them as a
            // bare claim with no proposition and no `by` hint.
            return parseStructuredClaimSequence();
        }
        if (current.kind == TokenKind::KeywordGiven) {
            return parseGiven();
        }
        // The `decide P { yes/no }` construct is RETIRED (A4). The check
        // must short-circuit BEFORE the isIdentifierLike fallthrough
        // (`decide` stays a contextual keyword so `Natural.decide` and
        // similar qualified names still parse) and steer to the settled
        // spellings.
        if (current.kind == TokenKind::KeywordDecide
            && peekAt(1).kind != TokenKind::Dot) {
            throw ParseError(
                "the `decide P { yes/no }` construct was retired; split "
                "propositionally with `by cases { case P: … otherwise: … }` "
                "(reasoning through a definition's characterizing equations "
                "where the goal must reduce), or use the value-level "
                "conditional `if P then a else b` (line "
                + std::to_string(current.line) + ")");
        }
        if (current.kind == TokenKind::KeywordIf) {
            return parseIfExpression();
        }
        if (isIdentifierLike(current.kind)) {
            return parseQualifiedIdentifier();
        }
        if (current.kind == TokenKind::NumericLiteral) {
            Token token = consumeAny();
            return makeSurfaceNumericLiteral(token.lexeme,
                                              token.line, token.column);
        }
        if (current.kind == TokenKind::LeftAngle) {
            return parseAnonymousTuple();
        }
        if (current.kind == TokenKind::KeywordCases) {
            return parseCasesExpression();
        }
        if (current.kind == TokenKind::KeywordCalc) {
            return parseCalc();
        }
        if (current.kind == TokenKind::ForAll
            || current.kind == TokenKind::Exists) {
            return parseQuantifier();
        }
        if (current.kind == TokenKind::KeywordWitness) {
            return parseWitnessExpression();
        }
        if (current.kind == TokenKind::KeywordByInduction) {
            return parseByInduction();
        }
        if (current.kind == TokenKind::KeywordByStrongInduction) {
            return parseByStrongInduction();
        }
        if (current.kind == TokenKind::KeywordByRepresentatives) {
            return parseByRepresentatives();
        }
        if (current.kind == TokenKind::LeftBrace) {
            // `{ let pat := v; ...; final_expr }` as an expression.
            // Same shape as the theorem-body block form; useful inside
            // case clauses or anywhere an expression is expected.
            return parseBlockBody();
        }
        if (current.kind == TokenKind::KeywordSorry) {
            Token sorryToken = consumeAny();
            return makeSurfaceSorry(sorryToken.line,
                                     sorryToken.column);
        }
        if (current.kind == TokenKind::KeywordType) {
            Token token = consumeAny();
            if (peek().kind == TokenKind::LeftParen) {
                consumeAny();
                auto level = parseLevel();
                expect(TokenKind::RightParen, "after level expression");
                return makeSurfaceType(std::move(level),
                                        token.line, token.column);
            }
            // Bare `Type` — universe is a metavariable that the elaborator
            // resolves (Stage 3 auto-binds unresolved ones as universe
            // parameters of the enclosing declaration).
            return makeSurfaceType(
                makeSurfaceLevelMeta(token.line, token.column),
                token.line, token.column);
        }
        if (current.kind == TokenKind::KeywordProposition) {
            Token token = consumeAny();
            return makeSurfaceProposition(token.line, token.column);
        }
        if (current.kind == TokenKind::KeywordGoal) {
            // `goal` is just the NAME of the type we are trying to prove —
            // a type reference (used as `claim goal [by …]`, `note goal :
            // T`, etc.). It is NOT a standalone proof-closer: to close the
            // goal write `done` / `okay` (≡ `claim goal`). A bare `goal`
            // (or `goal by …`) in proof position is therefore as ill-formed
            // as a bare proposition `a + b = b + a` without `claim`/`calc`.
            Token token = consumeAny();
            return makeSurfaceGoal(token.line, token.column);
        }
        if (current.kind == TokenKind::Question) {
            // `?` — placeholder for an argument the elaborator should
            // infer (goal-unification + supplied-args-types + scope
            // hypothesis search). Lets the user write
            // `Natural.successor_injective(?, ?, eq)` for a lemma whose
            // first two args are recoverable from the goal type.
            Token token = consumeAny();
            return makeSurfaceHole(token.line, token.column);
        }
        if (current.kind == TokenKind::KeywordUnfold) {
            // `unfold X [, Y, ...] in <body>` — temporarily flips
            // X (and friends) from opaque to transparent while
            // elaborating <body>. Restored on return.
            Token unfoldToken = consumeAny();  // 'unfold'
            std::vector<std::string> names;
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an identifier (the definition "
                          "name to unfold) after 'unfold'");
            }
            names.push_back(consumeQualifiedNameString());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();  // ','
                if (!isIdentifierLike(peek().kind)) {
                    throwHere("expected another identifier after ','");
                }
                names.push_back(consumeQualifiedNameString());
            }
            expect(TokenKind::KeywordIn,
                   "after 'unfold <name>[, <name>...]'");
            auto body = parseExpression();
            return makeSurfaceUnfold(
                std::move(names), std::move(body),
                unfoldToken.line, unfoldToken.column);
        }
        if (current.kind == TokenKind::LeftParen) {
            // `(<op>)` — refer to an operator-symbol-named binder
            // (e.g. `((·) : G → G → G)` bound earlier; in expression
            // position, `(·)` is an identifier referring to it).
            if (position_ + 2 < tokens_.size()
                && isOperatorSymbolToken(tokens_[position_ + 1].kind)
                && tokens_[position_ + 2].kind ==
                       TokenKind::RightParen) {
                Token openParen = consumeAny();
                Token opToken = consumeAny();
                consumeAny();  // ')'
                return makeSurfaceIdentifier(
                    opToken.lexeme, {}, openParen.line, openParen.column);
            }
            Token openParen = consumeAny();
            auto inner = parseExpression();
            if (peek().kind == TokenKind::Colon) {
                consumeAny();
                auto type = parseExpression();
                expect(TokenKind::RightParen, "after ascription");
                return makeSurfaceAscription(std::move(inner), std::move(type),
                                              openParen.line, openParen.column);
            }
            expect(TokenKind::RightParen, "matching '('");
            return inner;
        }
        throwHere("expected expression");
    }

    // `⟨a, b, ...⟩` — anonymous tuple expression. At least one component.
    SurfaceExpressionPointer parseAnonymousTuple() {
        Token openAngle = consumeAny();  // '⟨'
        if (peek().kind == TokenKind::RightAngle) {
            throwHere("anonymous tuple needs at least one component");
        }
        std::vector<SurfaceExpressionPointer> components;
        components.push_back(parseExpression());
        while (peek().kind == TokenKind::Comma) {
            consumeAny();
            components.push_back(parseExpression());
        }
        expect(TokenKind::RightAngle, "ending anonymous tuple");
        return makeSurfaceAnonymousTuple(std::move(components),
                                          openAngle.line, openAngle.column);
    }

    // `cases scrutinee { | pattern => body  | pattern => body  ... }`
    // — the original form. Also accepts the math-style form
    // `cases scrutinee { case pattern: body;  case pattern: body;  ... }`
    // alongside (a single block may pick either, but the two cannot be
    // mixed inside the same `cases`). Builds an inductive eliminator at
    // elaboration time; the motive is derived from the enclosing
    // expected type.
    // A `cases` scrutinee, allowing `cases by <lemma> { … }` — case-split on
    // the (disjunction / inductive) result of citing <lemma> with all explicit
    // arguments inferred (its premises recovered from context). Parallels
    // `obtain ⟨…⟩ by <lemma>`.
    SurfaceExpressionPointer parseCasesScrutinee() {
        if (peek().kind == TokenKind::KeywordBy) {
            Token byToken = consumeAny();  // 'by'
            return makeSurfaceCiteInferred(
                parseExpression(), byToken.line, byToken.column);
        }
        return parseExpression();
    }

    SurfaceExpressionPointer parseCasesExpression() {
        Token casesToken = consumeAny();  // 'cases'
        auto scrutinee = parseCasesScrutinee();
        // Optional `with <equalityHypothesisName>`: each arm gets an
        // additional binder `<name> : <scrutinee> = <constructor pattern>`
        // in scope, generated via the standard convoy desugaring.
        std::string equalityHypothesisName;
        if (peek().kind == TokenKind::KeywordWith) {
            consumeAny();  // 'with'
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an equality-hypothesis name after "
                          "`cases X with`");
            }
            Token nameToken = consumeAny();
            equalityHypothesisName = nameToken.lexeme;
        }
        // Optional `refining <name1>, <name2>, …`: each listed
        // in-scope binder has its type refined per arm (the scrutinee
        // appearing in the binder's type is substituted by the arm's
        // constructor pattern). Hides the convoy-pattern boilerplate.
        std::vector<std::string> refiningNames =
            parseOptionalRefiningList();
        expect(TokenKind::LeftBrace, "after cases scrutinee");
        auto clauses = parseCasesClauseBlock(
            /*injectedIhName=*/std::string(),
            /*caseFollowedBy=*/TokenKind::Colon);
        expect(TokenKind::RightBrace, "ending cases expression");
        if (equalityHypothesisName.empty() && refiningNames.empty()) {
            return makeSurfaceCases(std::move(scrutinee),
                                     std::move(clauses),
                                     casesToken.line, casesToken.column);
        }
        return makeSurfaceCasesWithRefining(
            std::move(scrutinee), std::move(clauses),
            std::move(equalityHypothesisName),
            std::move(refiningNames),
            casesToken.line, casesToken.column);
    }

    // `by_representatives x as <pat>, y as <pat>, … => body` —
    // "WLOG pick representatives" elimination over one or more quotient
    // values that are already in scope (typically the theorem's binders).
    // Pure parse-time sugar: desugars to nested quotient-`cases`, one per
    // scrutinee, innermost-last. The pattern after `as` is any pattern the
    // quotient-cases path accepts — a bare name (bind the representative),
    // a tuple `⟨a, b⟩` (destructure via the carrier's sole constructor,
    // hiding the constructor name), or an explicit `Carrier.make(a, b)`.
    SurfaceExpressionPointer parseByRepresentatives() {
        consumeAny();  // 'by_representatives'
        struct Scrutinee {
            SurfaceExpressionPointer expression;
            SurfacePatternPointer pattern;
            int line;
            int column;
        };
        std::vector<Scrutinee> scrutinees;
        while (true) {
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected a quotient-value variable name in "
                          "`by_representatives`");
            }
            Token nameToken = consumeAny();
            SurfaceExpressionPointer scrutineeExpression =
                makeSurfaceIdentifier(nameToken.lexeme, {},
                                      nameToken.line, nameToken.column);
            expect(TokenKind::KeywordAs,
                   "after the scrutinee name in `by_representatives`");
            SurfacePatternPointer pattern = parsePattern();
            scrutinees.push_back({std::move(scrutineeExpression),
                                  std::move(pattern),
                                  nameToken.line, nameToken.column});
            if (peek().kind == TokenKind::Comma) {
                consumeAny();
                continue;
            }
            break;
        }
        expect(TokenKind::FatArrow,
               "before the `by_representatives` body");
        SurfaceExpressionPointer body = parseExpression();
        // Fold right: the body is the innermost arm; each scrutinee wraps
        // it in `cases <scrutinee> { | <pattern> => <inner> }`.
        SurfaceExpressionPointer result = std::move(body);
        for (auto it = scrutinees.rbegin(); it != scrutinees.rend(); ++it) {
            std::vector<SurfaceCasesClause> clauses;
            clauses.push_back(SurfaceCasesClause{
                it->pattern, std::move(result), it->line, it->column});
            result = makeSurfaceCases(it->expression, std::move(clauses),
                                       it->line, it->column);
        }
        return result;
    }

    // `if P then a else b` — surface sugar for
    // `decide P { | yes _ => a | no _ => b }`. A value-level conditional on
    // any (classically decidable) proposition P, so a definition branches on
    // a mathematical condition rather than a constructor pattern. `then` and
    // `else` are keywords, so `parseExpression` for P / a / b stops cleanly
    // at each.
    SurfaceExpressionPointer parseIfExpression() {
        Token ifToken = consumeAny();  // 'if'
        SurfaceExpressionPointer proposition = parseExpression();
        expect(TokenKind::KeywordThen, "after `if P`");
        SurfaceExpressionPointer yesBody = parseExpression();
        expect(TokenKind::KeywordElse, "after `if P then a`");
        SurfaceExpressionPointer noBody = parseExpression();
        return makeSurfaceDecide(
            std::move(proposition),
            std::string("_"), std::move(yesBody),
            std::string("_"), std::move(noBody),
            ifToken.line, ifToken.column);
    }

    // Parses an optional `refining <name>[, <name>]*` clause used by
    // `cases` and `by_induction` to mark in-scope binders whose types
    // should be refined per arm. Empty vector if the keyword isn't
    // present.
    std::vector<std::string> parseOptionalRefiningList() {
        std::vector<std::string> names;
        if (peek().kind != TokenKind::KeywordRefining) {
            return names;
        }
        consumeAny();  // 'refining'
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a binder name after 'refining'");
        }
        names.push_back(consumeAny().lexeme);
        while (peek().kind == TokenKind::Comma) {
            consumeAny();
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected a binder name after ',' in "
                          "'refining' list");
            }
            names.push_back(consumeAny().lexeme);
        }
        return names;
    }

    // Parses the inside of a `{ … }` of a cases-style block: either a
    // sequence of `| pattern => body` clauses (legacy form) or a
    // sequence of `case pattern <separator> body;` clauses (math-style
    // form). When `injectedIhName` is non-empty (set by `by_induction`),
    // an extra bare-name pattern with that name is appended to each
    // constructor pattern that has any recursive arguments — the
    // existing IH-naming convention in cases patterns picks it up.
    std::vector<SurfaceCasesClause> parseCasesClauseBlock(
        const std::string& injectedIhName,
        TokenKind caseFollowedBy) {
        std::vector<SurfaceCasesClause> clauses;
        bool sawCaseForm = false;
        bool sawPipeForm = false;
        while (peek().kind == TokenKind::Pipe
               || peek().kind == TokenKind::KeywordCase) {
            SurfaceCasesClause clause;
            if (peek().kind == TokenKind::Pipe) {
                if (sawCaseForm) {
                    throwHere("can't mix '|' clauses and 'case' clauses "
                              "in the same cases block");
                }
                sawPipeForm = true;
                Token pipeToken = consumeAny();
                clause.line = pipeToken.line;
                clause.column = pipeToken.column;
                clause.pattern = parsePattern();
                expect(TokenKind::FatArrow,
                       "between cases pattern and body");
                clause.body = parseExpression();
            } else {
                if (sawPipeForm) {
                    throwHere("can't mix 'case' clauses and '|' clauses "
                              "in the same cases block");
                }
                sawCaseForm = true;
                Token caseToken = consumeAny();
                clause.line = caseToken.line;
                clause.column = caseToken.column;
                clause.pattern = parsePattern();
                if (!injectedIhName.empty()) {
                    if (auto* constructorPattern =
                            std::get_if<SurfacePatternConstructor>(
                                &clause.pattern->node)) {
                        std::vector<SurfacePatternPointer>
                            extendedArguments(
                                constructorPattern->arguments);
                        extendedArguments.push_back(
                            makeSurfacePatternBareName(
                                injectedIhName,
                                clause.line, clause.column));
                        clause.pattern =
                            makeSurfacePatternConstructor(
                                constructorPattern->constructorName,
                                std::move(extendedArguments),
                                clause.line, clause.column);
                    }
                }
                expect(caseFollowedBy,
                       caseFollowedBy == TokenKind::Colon
                           ? "between case pattern and body"
                           : "between case pattern and body");
                clause.body = parseExpression();
                if (peek().kind == TokenKind::Semicolon) {
                    consumeAny();
                }
            }
            clauses.push_back(std::move(clause));
        }
        if (clauses.empty()) {
            throwHere("cases block needs at least one clause "
                      "('| pattern => body' or 'case pattern: body;')");
        }
        return clauses;
    }

    // Shared parser for the structured-hint forms that follow `by` —
    // `cases { … }` / `cases on E …`, `substitution`, `substituting <eq>`,
    // `induction on E …`. Assumes `by` has already been consumed and the
    // next token is the hint keyword. Returns a `SurfaceStructuredClaim`
    // carrying the right flags and the supplied `proposition` (null for a
    // calc step, where the relation type is the expected type), or nullptr
    // when the next token is NOT one of these keywords (the caller then
    // parses a plain proof expression). `eqAtAdditiveLevel` parses the
    // `substituting` equality at the calc-safe `parseAdditive` precedence
    // so a following calc separator (`=`/`≤`/…) ends the step instead of
    // being swallowed; claims (delimited by `;`) pass false.
    //
    // One source of truth shared by `parseStructuredClaimTail` (claims)
    // and `parseCalcStepProof` (calc steps), so `claim P by H` and a calc
    // step `= P by H` accept the exact same hint grammar.
    SurfaceExpressionPointer tryParseStructuredByHint(
        Token claimToken, const SurfaceExpressionPointer& proposition,
        bool eqAtAdditiveLevel) {
        if (peek().kind == TokenKind::KeywordCases) {
            Token casesToken = consumeAny();  // 'cases'
            if (peek().kind == TokenKind::KeywordOn) {
                SurfaceExpressionPointer byHint =
                    parseClaimByCasesOnScrutinee(casesToken);
                return makeSurfaceStructuredClaim(
                    proposition, /*label=*/"",
                    std::move(byHint), /*byCases=*/false, {},
                    claimToken.line, claimToken.column,
                    /*byInduction=*/true, /*bySubstitution=*/false);
            }
            std::vector<SurfaceStructuredClaimArm> arms;
            expect(TokenKind::LeftBrace, "after 'by cases'");
            while (peek().kind == TokenKind::KeywordIn
                   || peek().kind == TokenKind::KeywordCase
                   || (isIdentifierLike(peek().kind)
                       && peek().lexeme == "otherwise")) {
                arms.push_back(parseStructuredClaimArm());
            }
            expect(TokenKind::RightBrace, "ending 'by cases' arms block");
            for (size_t i = 0; i < arms.size(); ++i) {
                if (!arms[i].isOtherwise) continue;
                if (i == 0) {
                    throw ParseError(
                        "`otherwise:` needs at least one `case P:` before "
                        "it — with no stated cases there is nothing to "
                        "take the complement of (line "
                        + std::to_string(arms[i].line) + ")");
                }
                if (i + 1 != arms.size()) {
                    throw ParseError(
                        "`otherwise:` must be the LAST arm of a `by cases` "
                        "block — it covers the complement of the cases "
                        "before it (line "
                        + std::to_string(arms[i].line) + ")");
                }
            }
            return makeSurfaceStructuredClaim(
                proposition, /*label=*/"",
                /*byHint=*/nullptr, /*byCases=*/true, std::move(arms),
                claimToken.line, claimToken.column,
                /*byInduction=*/false, /*bySubstitution=*/false);
        }
        if (peek().kind == TokenKind::KeywordSubstitution) {
            consumeAny();  // 'substitution'
            return makeSurfaceStructuredClaim(
                proposition, /*label=*/"",
                /*byHint=*/nullptr, /*byCases=*/false, {},
                claimToken.line, claimToken.column,
                /*byInduction=*/false, /*bySubstitution=*/true);
        }
        if (peek().kind == TokenKind::KeywordSubstituting) {
            consumeAny();  // 'substituting'
            SurfaceExpressionPointer eq = eqAtAdditiveLevel
                ? parseAdditive() : parseExpression();
            return makeSurfaceStructuredClaim(
                proposition, /*label=*/"",
                std::move(eq), /*byCases=*/false, {},
                claimToken.line, claimToken.column,
                /*byInduction=*/false, /*bySubstitution=*/true);
        }
        if (peek().kind == TokenKind::KeywordInduction) {
            SurfaceExpressionPointer byHint = parseClaimByInduction();
            return makeSurfaceStructuredClaim(
                proposition, /*label=*/"",
                std::move(byHint), /*byCases=*/false, {},
                claimToken.line, claimToken.column,
                /*byInduction=*/true, /*bySubstitution=*/false);
        }
        return nullptr;
    }

    // Calc-step proof bodies are parsed at a precedence below `=` so the
    // next calc-separator token (`=`, `≤`, `<`, `≥`, `>`) starts the
    // next calc step rather than being consumed as part of this step's
    // proof. `function`/`let` are still allowed at the top of a step
    // proof; users who need a top-level `→`, `∧`, `∨`, `=`, or any
    // inequality inside a step proof must parenthesise.
    //
    // The structured-hint keywords (`cases`/`substituting`/`induction`/…)
    // are parsed by the same `tryParseStructuredByHint` a `claim` uses, so
    // a calc step `= P by substituting <eq>` works exactly like
    // `claim P by substituting <eq>` (both route to elaborateStructuredClaim
    // with the goal as expected type).
    SurfaceExpressionPointer parseCalcStepProof() {
        if (peek().kind == TokenKind::KeywordLet)      return parseLet();
        if (looksLikeMapsToLambda()) return parseMapsToLambda();
        Token hintToken = peek();
        // `= P by unfolding X` standalone — auto-prover with X transparent.
        if (peek().kind == TokenKind::KeywordUnfolding) {
            return parseUnfoldingWrap(defaultGoalCloser(hintToken));
        }
        if (SurfaceExpressionPointer structured = tryParseStructuredByHint(
                hintToken, /*proposition=*/nullptr,
                /*eqAtAdditiveLevel=*/true)) {
            return parseUnfoldingWrap(std::move(structured));
        }
        return parseUnfoldingWrap(parseAdditive());
    }

    // `calc <initial> R1 <next1> by <proof1> R2 <next2> by <proof2> …`.
    // Each `Rₖ` is `=` or `≤`, each `proofₖ` proves
    // `<previous-expression> Rₖ <nextₖ>`. The elaborator composes the
    // chain via Equality.transitivity / <T>.LessOrEqual.transitive,
    // upgrading `=` to `≤` by rewrite-of-reflexivity wherever the chain
    // mixes relations.
    //
    // Note: initial and step expressions are parsed at the parseAdditive
    // level, not parseRelational — `≤` (and friends, as we add them) is
    // the calc separator, not an in-expression operator. Step
    // expressions containing `≤`/`<` etc. must be parenthesised, just
    // as they must already be for `=`.
    SurfaceExpressionPointer parseCalc(bool consumeCalcKeyword = true) {
        // A1 keyword-free chains parse the same grammar with no
        // anchor keyword — `consumeCalcKeyword=false` starts directly
        // at the initial expression.
        Token calcToken = peek();
        if (consumeCalcKeyword) consumeAny();  // 'calc'
        auto initialExpression = parseAdditive();
        std::vector<SurfaceCalcStep> steps;
        while (peek().kind == TokenKind::Equal
               || peek().kind == TokenKind::LessOrEqual
               || peek().kind == TokenKind::Less
               || peek().kind == TokenKind::GreaterOrEqual
               || peek().kind == TokenKind::Greater
               || peek().kind == TokenKind::Divides
               || peek().kind == TokenKind::SubsetOf
               || peek().kind == TokenKind::Approx) {
            Token relationToken = consumeAny();
            CalcRelation relation = CalcRelation::Equality;
            std::string relationOperator;
            switch (relationToken.kind) {
                case TokenKind::LessOrEqual:
                    relation = CalcRelation::LessOrEqual; break;
                case TokenKind::Less:
                    relation = CalcRelation::LessThan; break;
                case TokenKind::GreaterOrEqual:
                    relation = CalcRelation::GreaterOrEqual; break;
                case TokenKind::Greater:
                    relation = CalcRelation::GreaterThan; break;
                // Generic preorder relations: keep `relation` at its
                // Equality placeholder and record the operator symbol; the
                // elaborator routes the whole chain to the preorder fold.
                case TokenKind::Divides:
                    relationOperator = "∣"; break;
                case TokenKind::SubsetOf:
                    relationOperator = "⊆"; break;
                case TokenKind::Approx:
                    relationOperator = "≈"; break;
                default:
                    relation = CalcRelation::Equality; break;
            }
            auto nextExpression = parseAdditive();
            SurfaceCalcStep step;
            step.relation = relation;
            step.relationOperator = std::move(relationOperator);
            step.nextExpression = std::move(nextExpression);
            step.line = relationToken.line;
            step.column = relationToken.column;
            // `by <proof>` is optional. When omitted, the elaborator
            // runs an auto-prover that tries reflexivity (def-eq) and
            // single-position diffs categorized as commutativity /
            // associativity / local hypothesis. If the auto-prover
            // can't close the step, the user gets an error and supplies
            // `by <reason>`. (Auto-prover currently runs for `=` steps
            // only; `≤` steps must supply `by`.)
            if (peek().kind == TokenKind::KeywordBy) {
                consumeAny();  // 'by'
                step.stepProof = parseCalcStepProof();
            } else {
                step.stepProof = nullptr;
            }
            steps.push_back(std::move(step));
        }
        if (steps.empty()) {
            throwHere("calc block needs at least one "
                      "'= <expression> [by <proof>]' or "
                      "'≤ <expression> by <proof>' step");
        }
        return makeSurfaceCalc(std::move(initialExpression),
                                std::move(steps),
                                calcToken.line, calcToken.column);
    }

    // One `claim` step. Forms:
    //   `claim P`                       — prove / introduce P (lookup)
    //   `claim P by Hint`               — prove P from Hint, args filled
    //   `claim P by cases { in (A): … in (B): … }`
    //                                   — prove P by case-split on a
    //                                     disjunction found in scope
    //   `claim by Hint`                 — discharge current goal via Hint
    //   `claim by cases { … }`          — discharge by case-split
    //   `claim`                         — discharge current goal by lookup
    //   `done` / `okay`                 — bare-`claim` synonyms (no
    //                                     proposition, no `by`); read as
    //                                     "QED" / Aroca-style "okay".
    // Coexists with block-statement `claim NAME : TYPE [by V];` — that
    // form is handled by parseBlockContents and never reaches here.
    SurfaceExpressionPointer parseStructuredClaim() {
        Token claimToken = consumeAny();  // 'claim' / 'done' / 'okay'
        // `done` and `okay` are math-style closers, synonyms of `goal`:
        // they take no proposition (it comes from the expected type) but DO
        // accept an optional `by <hint>` — so `done by IH`
        // and `okay by add_zero` read as "…and we're done, by <reason>".
        // A bare `done` / `okay` still means "discharge the goal by lookup".
        bool isBareCloser =
            claimToken.kind == TokenKind::KeywordDone
            || claimToken.kind == TokenKind::KeywordOkay;
        if (isBareCloser) {
            // `done` / `okay` are precisely `claim goal`: a claim whose
            // proposition is the `goal` type-reference (resolved from the
            // expected type). They accept the same optional `by <hint>` /
            // `by <hint>` tail, so `done by IH` ≡ `claim goal by IH`.
            SurfaceExpressionPointer goalProposition =
                makeSurfaceGoal(claimToken.line, claimToken.column);
            if (peek().kind == TokenKind::KeywordBy) {
                return parseStructuredClaimTail(
                    claimToken, std::move(goalProposition));
            }
            return makeSurfaceStructuredClaim(
                std::move(goalProposition), /*label=*/"",
                /*byHint=*/nullptr, /*byCases=*/false, /*arms=*/{},
                claimToken.line, claimToken.column);
        }
        SurfaceExpressionPointer proposition;
        // Bare `claim` / `claim by …` — terminal-shaped, no proposition.
        if (peek().kind != TokenKind::KeywordBy
            && !isStructuredClaimTerminator()) {
            proposition = parseExpression();
        }
        return parseStructuredClaimTail(
            claimToken, std::move(proposition));
    }

    // Shared "after the keyword + optional proposition" parser. Called
    // from parseStructuredClaim and from the `goal by …` entry point
    // in parseAtom (`goal by Hint` is just `claim by Hint` with a
    // friendlier reading-as-math keyword).
    // `label` (when non-empty) is the let-binding name of a NAMED claim —
    // carried onto the claim node so elaborator diagnostics (e.g. the
    // redundant-`by` warning) can say WHICH claim they are about.
    SurfaceExpressionPointer parseStructuredClaimTail(
        Token claimToken, SurfaceExpressionPointer proposition,
        std::string label = "") {
        SurfaceExpressionPointer byHint;
        bool byCases = false;
        bool byInduction = false;
        bool bySubstitution = false;
        std::vector<SurfaceStructuredClaimArm> arms;
        if (peek().kind == TokenKind::KeywordBy) {
            Token byToken = consumeAny();  // 'by'
            // `unfolding X[, …]` is a postfix transparency modifier that
            // piles onto ANY hint (a plain lemma, a structured claim, or —
            // standalone — the bare auto-prover): the hint is discharged
            // with X transparent. Standalone form first, since `unfolding`
            // can't start a proof expression.
            if (peek().kind == TokenKind::KeywordUnfolding) {
                byHint = parseUnfoldingWrap(defaultGoalCloser(byToken));
            } else if (SurfaceExpressionPointer structured =
                    // Structured-hint keywords (`cases { … }` / `cases on E
                    // …`, `substitution`, `substituting <eq>`, `induction on
                    // E …`) are parsed by the shared `tryParseStructuredByHint`
                    // — the same one a calc step uses, so the two forms can
                    // never drift. A trailing `unfolding X` may still modify
                    // the structured hint.
                    tryParseStructuredByHint(
                        claimToken, proposition,
                        /*eqAtAdditiveLevel=*/false)) {
                return parseUnfoldingWrap(std::move(structured));
            } else {
                // Plain `by <proof> [recalling …] [unfolding X]`.
                byHint = parseUnfoldingWrap(
                    parseRecallingWrap(parseExpression()));
            }
        }
        return makeSurfaceStructuredClaim(
            std::move(proposition), std::move(label),
            std::move(byHint), byCases, std::move(arms),
            claimToken.line, claimToken.column, byInduction,
            bySubstitution);
    }

    // `<hint> recalling <fact>, <fact>, …` — bring extra named facts into
    // the discharge scope of a `by <lemma>` hint. Desugars to nested
    // `let`-bindings wrapping the hint, so each fact becomes a local
    // hypothesis the side-condition discharge can match (a bounded,
    // context-local search — no global library scan). Returns the hint
    // unchanged when there is no `recalling` clause.
    SurfaceExpressionPointer parseRecallingWrap(
        SurfaceExpressionPointer hint) {
        if (peek().kind != TokenKind::KeywordRecalling) return hint;
        Token recallToken = consumeAny();  // 'recalling'
        std::vector<SurfaceExpressionPointer> facts;
        facts.push_back(parseExpression());
        while (peek().kind == TokenKind::Comma) {
            consumeAny();  // ','
            facts.push_back(parseExpression());
        }
        SurfaceExpressionPointer body = std::move(hint);
        for (int i = static_cast<int>(facts.size()) - 1; i >= 0; --i) {
            body = makeSurfaceLet(
                "_recalled_" + std::to_string(i),
                /*type=*/nullptr, std::move(facts[i]), std::move(body),
                recallToken.line, recallToken.column,
                /*fromCalcAsBinding=*/false, /*fromRecallingFact=*/true);
        }
        return body;
    }

    // Parse the comma-separated definition names after `unfolding`.
    // Assumes `unfolding` has already been consumed; the next token must
    // be an identifier. Mirrors the name list of `unfold X[, Y, …] in …`.
    std::vector<std::string> parseUnfoldingNames() {
        std::vector<std::string> names;
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a definition name after 'unfolding'");
        }
        names.push_back(consumeQualifiedNameString());
        while (peek().kind == TokenKind::Comma) {
            consumeAny();  // ','
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected another definition name after ','");
            }
            names.push_back(consumeQualifiedNameString());
        }
        return names;
    }

    // A bare auto-prover closer (`claim goal` ≡ `done`), used as the body
    // when `by unfolding X` carries no explicit proof.
    SurfaceExpressionPointer defaultGoalCloser(Token at) {
        return makeSurfaceStructuredClaim(
            makeSurfaceGoal(at.line, at.column), /*label=*/"",
            /*byHint=*/nullptr, /*byCases=*/false, /*arms=*/{},
            at.line, at.column);
    }

    // `<hint> unfolding X[, Y, …]` — the postfix transparency modifier.
    // Wraps `hint` so it is elaborated with X (and friends) made
    // transparent, reusing the same `SurfaceUnfold` machinery as
    // `unfold X in <body>`. Returns the hint unchanged when no
    // `unfolding` clause follows. Parallels `parseRecallingWrap`.
    SurfaceExpressionPointer parseUnfoldingWrap(
        SurfaceExpressionPointer hint) {
        if (peek().kind != TokenKind::KeywordUnfolding) return hint;
        Token unfoldingToken = consumeAny();  // 'unfolding'
        return makeSurfaceUnfold(
            parseUnfoldingNames(), std::move(hint),
            unfoldingToken.line, unfoldingToken.column);
    }

    // Parses the tail of `claim P by induction on E [with ih]
    // [refining …] { case …: body … }`. The opening `claim P by`
    // and the `induction` keyword have already been consumed by the
    // caller (parseStructuredClaim). Builds the same SurfaceCases /
    // SurfaceCasesWithRefining the standalone `by_induction on E …
    // { … }` form produces — only the surrounding wrapper differs.
    SurfaceExpressionPointer parseClaimByInduction() {
        Token inductionToken = consumeAny();  // 'induction'
        expect(TokenKind::KeywordOn, "after 'by induction'");
        auto scrutinee = parseExpression();
        // `with ih` is optional; when absent we leave ihName empty
        // (recursive arms get no user-visible IH binding, matching
        // the bare `cases` form).
        std::string ihName;
        if (peek().kind == TokenKind::KeywordWith) {
            consumeAny();  // 'with'
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an identifier (the induction "
                          "hypothesis name) after 'with'");
            }
            ihName = consumeAny().lexeme;
        }
        std::vector<std::string> refiningNames =
            parseOptionalRefiningList();
        expect(TokenKind::LeftBrace,
               "after 'by induction on <expr>'");
        auto clauses = parseCasesClauseBlock(
            ihName, TokenKind::Colon);
        expect(TokenKind::RightBrace,
               "ending 'by induction' block");
        if (refiningNames.empty()) {
            return makeSurfaceCases(
                std::move(scrutinee), std::move(clauses),
                inductionToken.line, inductionToken.column,
                ihName);
        }
        return makeSurfaceCasesWithRefining(
            std::move(scrutinee), std::move(clauses),
            /*equalityHypothesisName=*/std::string(),
            std::move(refiningNames),
            inductionToken.line, inductionToken.column,
            ihName);
    }

    // `claim P by cases on E [refining …] { case zero: …  case
    // successor(k): … }` — structural case-split on a constructor.
    // Same shape as `claim P by induction on E` but no `with <ih>`
    // (the `cases` flavour deliberately doesn't bind an IH; users
    // who want one write `by induction` instead). The opening
    // `claim P by cases` has already been consumed by the caller.
    // We share the SurfaceCases / SurfaceCasesWithRefining produced
    // by the induction path; the elaborator dispatches by passing
    // the claim's proposition as the expected type.
    SurfaceExpressionPointer parseClaimByCasesOnScrutinee(
            const Token& casesToken) {
        expect(TokenKind::KeywordOn, "after 'by cases'");
        auto scrutinee = parseCasesScrutinee();
        std::vector<std::string> refiningNames =
            parseOptionalRefiningList();
        expect(TokenKind::LeftBrace,
               "after 'by cases on <expr>'");
        auto clauses = parseCasesClauseBlock(
            /*ihName=*/std::string(), TokenKind::Colon);
        expect(TokenKind::RightBrace,
               "ending 'by cases on <expr>' block");
        if (refiningNames.empty()) {
            return makeSurfaceCases(
                std::move(scrutinee), std::move(clauses),
                casesToken.line, casesToken.column);
        }
        return makeSurfaceCasesWithRefining(
            std::move(scrutinee), std::move(clauses),
            /*equalityHypothesisName=*/std::string(),
            std::move(refiningNames),
            casesToken.line, casesToken.column);
    }

    // A run of one or more `claim`s. Each non-terminal claim (one that
    // is followed by another `claim`) is wrapped in a SurfaceLet that
    // introduces its proof under an auto-generated anonymous binder
    // name (`_anonymousClaim_<n>`). The final claim becomes the
    // sequence's value. Anonymous binders are searchable via Step 5's
    // hypothesis lookup and `given (P)`.
    SurfaceExpressionPointer parseStructuredClaimSequence() {
        SurfaceExpressionPointer first = parseStructuredClaim();
        // Chain to a following `claim` / `done` / `okay`. The
        // latter two are bare-`claim` synonyms; they always end the
        // chain (parseStructuredClaim returns them with no
        // proposition).
        TokenKind next = peek().kind;
        if (next != TokenKind::KeywordClaim
            && next != TokenKind::KeywordDone
            && next != TokenKind::KeywordOkay) {
            return first;
        }
        // First is non-terminal. Must have a proposition for its
        // type — anonymous let-bindings can't have inferred types
        // yet.
        const SurfaceStructuredClaim* claim =
            std::get_if<SurfaceStructuredClaim>(&first->node);
        if (!claim || !claim->proposition) {
            throwHere("a `claim` followed by another `claim` must "
                      "have an explicit proposition (so it can be "
                      "introduced as an anonymous local fact)");
        }
        int firstLine = first->line;
        int firstColumn = first->column;
        SurfaceExpressionPointer proposition = claim->proposition;
        SurfaceExpressionPointer rest = parseStructuredClaimSequence();
        std::string anonymousName =
            "_anonymousClaim_" + std::to_string(anonymousClaimCounter_++);
        return makeSurfaceLet(
            std::move(anonymousName),
            std::move(proposition),
            std::move(first),
            std::move(rest),
            firstLine, firstColumn);
    }

    // Lookahead for the legacy block-statement `claim NAME : TYPE`
    // shape. The current token is `claim`; if the next-next sequence
    // is identifier followed by `:`, this is the legacy form (handled
    // by parseBlockContents' wrapper loop). Otherwise it's one of the
    // new structured-proof forms, which the structured-claim parser
    // handles via parseExpression. Restoring lookahead by saving and
    // resetting position_ — non-destructive.
    bool looksLikeLegacyClaim() {
        if (position_ + 2 >= tokens_.size()) return false;
        return isIdentifierLike(tokens_[position_ + 1].kind)
            && tokens_[position_ + 2].kind == TokenKind::Colon;
    }

    // True if the next token can only end a bare `claim` (no
    // proposition). Used to decide whether `claim` is bare or
    // followed by a proposition expression. Covers block / file
    // boundaries and `in` (which always introduces a sibling arm,
    // never an expression).
    bool isStructuredClaimTerminator() {
        TokenKind k = peek().kind;
        return k == TokenKind::Semicolon
            || k == TokenKind::RightBrace
            || k == TokenKind::EndOfFile
            || k == TokenKind::KeywordIn
            || k == TokenKind::KeywordTheorem
            || k == TokenKind::KeywordDefinition
            || k == TokenKind::KeywordAxiom
            || k == TokenKind::KeywordInductive
            || k == TokenKind::KeywordImport
            || k == TokenKind::KeywordModule
            // `|` ends the body of a pattern-match arm — without
            // this, a bare `claim` as an arm body greedily tries
            // to parse the next pattern's `|` as a proposition.
            || k == TokenKind::Pipe
            // `case` similarly ends the body of a `cases E
            // { case … : body  case … : body }` arm.
            || k == TokenKind::KeywordCase;
    }

    // `given (P)` — refer to the unique in-scope hypothesis of type P.
    // Parens are required; the proposition can be any expression.
    SurfaceExpressionPointer parseGiven() {
        Token givenToken = consumeAny();  // 'given'
        expect(TokenKind::LeftParen, "after 'given'");
        auto proposition = parseExpression();
        expect(TokenKind::RightParen, "ending 'given (...)'");
        return makeSurfaceGiven(std::move(proposition),
                                 givenToken.line, givenToken.column);
    }

    // `in (Proposition) [as name]: body` — one arm of a `claim by
    // cases` block. The optional `as name` lets the user bind the
    // disjunct hypothesis under an identifier (matching how legacy
    // `function (h : T) =>` handlers named their inputs); without
    // `as` the hypothesis is anonymous and reachable only via
    // `given (P)` or Step 5's lookup.
    SurfaceStructuredClaimArm parseStructuredClaimArm() {
        // Two shapes:
        //   `in (T) [as h]: body`  — legacy; T parenthesised.
        //   `case T [as h]: body`  — new; T parsed up to `as`/`:`
        //                            (parseExpression stops cleanly
        //                            at either since neither is an
        //                            expression-position operator).
        Token armToken = consumeAny();  // 'case' or 'otherwise'
        if (armToken.kind == TokenKind::KeywordIn) {
            // Retired spelling — steer to the settled clause syntax.
            throw ParseError(
                "the `in (P):` arm spelling was retired; write "
                "`case P:` (line " + std::to_string(armToken.line)
                + ")");
        }
        bool isOtherwise = armToken.kind != TokenKind::KeywordCase
            && armToken.lexeme == "otherwise";
        SurfaceExpressionPointer disjunctType;
        if (isOtherwise) {
            // `otherwise [as h]: body` — no proposition; the hypothesis
            // is the complement of the other cases, synthesized later.
        } else {
            // 'case T [as h]: body'.
            disjunctType = parseExpression();
        }
        // `case <equation> for some k:` / `for some (k : T):` — the
        // structural-case witness binder (A4). The arm's hypothesis
        // becomes `∃ k. <equation>`, with the witness and the equation
        // both in scope in the arm body. One binder for now.
        std::string witnessName;
        SurfaceExpressionPointer witnessType;
        if (!isOtherwise && disjunctType
            && isIdentifierLike(peek().kind) && peek().lexeme == "for") {
            consumeAny();  // 'for'
            if (!(isIdentifierLike(peek().kind)
                  && peek().lexeme == "some")) {
                throwHere("expected 'some' after 'for' in a case arm "
                          "(`case P for some k:`)");
            }
            consumeAny();  // 'some'
            if (peek().kind == TokenKind::LeftParen) {
                consumeAny();  // '('
                if (!isIdentifierLike(peek().kind)) {
                    throwHere("expected the witness name in "
                              "'for some (k : T)'");
                }
                witnessName = consumeAny().lexeme;
                expect(TokenKind::Colon, "after the witness name");
                witnessType = parseExpression();
                expect(TokenKind::RightParen,
                       "ending 'for some (k : T)'");
            } else if (isIdentifierLike(peek().kind)) {
                witnessName = consumeAny().lexeme;
            } else {
                throwHere("expected a witness name after 'for some'");
            }
            if (peek().kind == TokenKind::Comma) {
                throwHere("one witness binder per case for now "
                          "(`for some k`)");
            }
        }
        std::string binderName;
        SurfacePatternPointer destructurePattern;
        if (peek().kind == TokenKind::KeywordAs) {
            consumeAny();  // 'as'
            if (peek().kind == TokenKind::LeftAngle) {
                // `as ⟨pattern⟩` — bind the disjunct hypothesis under a fresh
                // name and immediately destructure it (e.g. an existential
                // into its witness and proof), like `take … as ⟨⟩` /
                // `suppose … as ⟨⟩`. Desugars below to
                // `cases <fresh> { | <pattern> => body }`.
                destructurePattern = parsePattern();
                binderName = "_disjunct_"
                    + std::to_string(armToken.line) + "_"
                    + std::to_string(armToken.column);
            } else if (isIdentifierLike(peek().kind)) {
                binderName = consumeAny().lexeme;
            } else {
                throwHere("expected an identifier or a ⟨…⟩ pattern after 'as'");
            }
        }
        expect(TokenKind::Colon, "after arm header");
        auto body = parseExpression();
        if (destructurePattern) {
            // Wrap the body in a destructure of the disjunct hypothesis.
            SurfaceExpressionPointer scrutinee = makeSurfaceIdentifier(
                binderName, {}, armToken.line, armToken.column);
            SurfaceCasesClause clause;
            clause.pattern = std::move(destructurePattern);
            clause.body = std::move(body);
            clause.line = armToken.line;
            clause.column = armToken.column;
            std::vector<SurfaceCasesClause> clauses;
            clauses.push_back(std::move(clause));
            body = makeSurfaceCases(std::move(scrutinee), std::move(clauses),
                                    armToken.line, armToken.column);
        }
        SurfaceStructuredClaimArm arm;
        arm.disjunctType = std::move(disjunctType);
        arm.binderName = std::move(binderName);
        arm.body = std::move(body);
        arm.isOtherwise = isOtherwise;
        arm.witnessName = std::move(witnessName);
        arm.witnessType = std::move(witnessType);
        arm.line = armToken.line;
        arm.column = armToken.column;
        return arm;
    }

    // `by_induction on E with ih { case P: body; … }`, or
    // `by_induction on E using L with subject, ih { body }`. Both parse
    // as regular expressions so they can sit anywhere a value belongs
    // (and be applied to further arguments via parseApplication).
    // (Structural case-split without an IH uses `cases E { … }` — see
    // parseCasesExpression.)
    SurfaceExpressionPointer parseByInduction() {
        Token byToken = consumeAny();  // 'by_induction'
        expect(TokenKind::KeywordOn, "after 'by_induction'");
        auto scrutinee = parseExpression();
        if (peek().kind == TokenKind::KeywordUsing) {
            consumeAny();  // 'using'
            auto inductionLemma = parseExpression();
            expect(TokenKind::KeywordWith,
                   "after 'by_induction on <expr> using <lemma>'");
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an identifier (the subject "
                          "name) after 'with'");
            }
            std::string subjectName = consumeAny().lexeme;
            expect(TokenKind::Comma,
                   "between subject name and ih name");
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an identifier (the ih name) "
                          "after ','");
            }
            std::string ihNameUsing = consumeAny().lexeme;
            expect(TokenKind::LeftBrace,
                   "after 'by_induction … using … with <subject>, <ih>'");
            auto inductionBody = parseBlockContents();
            expect(TokenKind::RightBrace,
                   "ending by_induction-using block");
            return makeSurfaceByInductionUsing(
                std::move(scrutinee),
                std::move(inductionLemma),
                std::move(subjectName),
                std::move(ihNameUsing),
                std::move(inductionBody),
                byToken.line, byToken.column);
        }
        expect(TokenKind::KeywordWith,
               "after 'by_induction on <expr>'");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected an identifier (the "
                      "induction hypothesis name) after 'with'");
        }
        std::string ihName = consumeAny().lexeme;
        // Optional `refining <name>[, <name>]*`: each listed in-scope
        // binder has its type refined per arm. See parseOptionalRefiningList.
        std::vector<std::string> refiningNames =
            parseOptionalRefiningList();
        expect(TokenKind::LeftBrace,
               "after 'by_induction on <expr> with <ih>'");
        auto clauses = parseCasesClauseBlock(
            ihName, TokenKind::Colon);
        expect(TokenKind::RightBrace, "ending by_induction block");
        if (refiningNames.empty()) {
            return makeSurfaceCases(
                std::move(scrutinee), std::move(clauses),
                byToken.line, byToken.column,
                ihName);
        }
        return makeSurfaceCasesWithRefining(
            std::move(scrutinee), std::move(clauses),
            /*equalityHypothesisName=*/std::string(),
            std::move(refiningNames),
            byToken.line, byToken.column,
            ihName);
    }

    // `by_strong_induction on m with hypothesis ih { body }` —
    // single-step strong induction. The generalized subject keeps the
    // inducted variable's name (shadowing it), so the body speaks the
    // statement's vocabulary; `hypothesis` (contextual word) marks the
    // one name in the clause as the induction hypothesis. The verbose
    // `with <subject>, <ih>` form names the subject explicitly — for
    // an `on` expression that isn't a plain variable, or when a
    // distinct subject name genuinely helps.
    SurfaceExpressionPointer parseByStrongInduction() {
        Token byToken = consumeAny();  // 'by_strong_induction'
        expect(TokenKind::KeywordOn,
               "after 'by_strong_induction'");
        SurfaceExpressionPointer scrutinee = parseExpression();
        expect(TokenKind::KeywordWith,
               "after 'by_strong_induction on <expr>'");
        if (!isIdentifierLike(peek().kind)) {
            throwHere(
                "expected 'hypothesis <name>' or '<subject>, <ih>' "
                "after 'with'");
        }
        std::string subjectName;
        std::string ihName;
        if (peek().kind == TokenKind::Identifier
            && peek().lexeme == "hypothesis") {
            consumeAny();  // 'hypothesis'
            if (!isIdentifierLike(peek().kind)) {
                throwHere(
                    "expected the induction hypothesis name after "
                    "'with hypothesis'");
            }
            ihName = consumeAny().lexeme;
            auto* onIdentifier = std::get_if<SurfaceIdentifier>(
                &scrutinee->node);
            if (!onIdentifier
                || onIdentifier->qualifiedName.find('.')
                       != std::string::npos) {
                throwHere(
                    "'with hypothesis <ih>' names the generalized "
                    "subject after the inducted variable, so "
                    "'by_strong_induction on <expr>' needs a plain "
                    "variable — use 'with <subject>, <ih>' to name "
                    "the subject explicitly");
            }
            subjectName = onIdentifier->qualifiedName;
        } else {
            subjectName = consumeAny().lexeme;
            expect(TokenKind::Comma,
                   "between subject name and ih name in "
                   "by_strong_induction");
            if (!isIdentifierLike(peek().kind)) {
                throwHere(
                    "expected the induction hypothesis name "
                    "after ','");
            }
            ihName = consumeAny().lexeme;
        }
        expect(TokenKind::LeftBrace,
               "after the by_strong_induction with-clause");
        SurfaceExpressionPointer body = parseBlockContents();
        expect(TokenKind::RightBrace,
               "ending by_strong_induction block");
        return makeSurfaceByStrongInduction(
            std::move(scrutinee),
            std::move(subjectName),
            std::move(ihName),
            std::move(body),
            byToken.line, byToken.column);
    }

    // `witness E with P` — a shorthand for the anonymous tuple
    // `⟨E, P⟩`. Works anywhere an expression is expected, including
    // as the trailing expression of a block or the body of a `case`
    // clause.
    SurfaceExpressionPointer parseWitnessExpression() {
        Token witnessToken = consumeAny();  // 'witness'
        auto witnessExpression = parseRelational();
        expect(TokenKind::KeywordWith,
               "after witness expression");
        auto witnessProof = parseExpression();
        std::vector<SurfaceExpressionPointer> components;
        components.push_back(std::move(witnessExpression));
        components.push_back(std::move(witnessProof));
        return makeSurfaceAnonymousTuple(
            std::move(components),
            witnessToken.line, witnessToken.column,
            /*userWritten=*/false);
    }

    // `∀ (binder)+ . body` desugars to a Pi chain `(binder)+ → body`.
    // `∃ (binder)+ . body` desugars to a nested `Exists` chain
    //   `Exists(T₁, function (x : T₁) => Exists(T₂, … body))`.
    // Each binder must be parenthesised (`(name+ : type)`); a bare-name
    // form would leave the `.` separator ambiguous with qualified
    // identifiers like `Natural.add`.
    SurfaceExpressionPointer parseQuantifier() {
        Token quantifierToken = consumeAny();  // '∀' or '∃'
        bool isUniversal = quantifierToken.kind == TokenKind::ForAll;
        std::vector<SurfaceBinder> binders;
        while (peek().kind == TokenKind::LeftParen
               || peek().kind == TokenKind::LeftBrace) {
            binders.push_back(parseExplicitBinder());
        }
        if (binders.empty()) {
            throwHere("quantifier needs at least one "
                      "'(name+ : type)' binder");
        }
        expect(TokenKind::Dot,
               isUniversal
                   ? "after binders in '∀'"
                   : "after binders in '∃'");
        auto body = parseExpression();
        if (isUniversal) {
            // Build a Pi chain from the binders, right-to-left.
            for (auto iterator = binders.rbegin();
                 iterator != binders.rend(); ++iterator) {
                body = makeSurfacePiType(
                    std::move(*iterator), std::move(body),
                    quantifierToken.line, quantifierToken.column);
            }
            return body;
        }
        // Existential: one Exists application per binder name. A binder
        // `(x y z : T)` expands to three nested Exists.
        for (auto binderIterator = binders.rbegin();
             binderIterator != binders.rend(); ++binderIterator) {
            for (auto nameIterator = binderIterator->names.rbegin();
                 nameIterator != binderIterator->names.rend();
                 ++nameIterator) {
                SurfaceBinder lambdaBinder;
                lambdaBinder.names = {*nameIterator};
                lambdaBinder.type = binderIterator->type;
                lambdaBinder.isImplicit = false;
                SurfaceExpressionPointer predicate = makeSurfaceLambda(
                    std::move(lambdaBinder), std::move(body),
                    quantifierToken.line, quantifierToken.column);
                SurfaceExpressionPointer existsHead =
                    makeSurfaceIdentifier("Exists", {},
                                           quantifierToken.line,
                                           quantifierToken.column);
                std::vector<SurfaceExpressionPointer> arguments;
                arguments.push_back(binderIterator->type);
                arguments.push_back(std::move(predicate));
                body = makeSurfaceApplication(
                    std::move(existsHead),
                    std::move(arguments),
                    quantifierToken.line, quantifierToken.column);
            }
        }
        return body;
    }

    // A qualified name like Natural.add_zero with an optional universe
    // argument list. The lexer hands us bare Dot tokens for namespace
    // qualification; the parser concatenates them. A `.{...}` opener
    // (its own token, DotLeftBrace) introduces universe arguments.
    SurfaceExpressionPointer parseQualifiedIdentifier() {
        Token first = consumeAny();
        std::string name = first.lexeme;
        while (peek().kind == TokenKind::Dot) {
            consumeAny();
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected identifier after '.'");
            }
            name += ".";
            name += consumeAny().lexeme;
        }
        std::vector<SurfaceLevelPointer> universeArguments;
        if (peek().kind == TokenKind::DotLeftBrace) {
            consumeAny();
            if (peek().kind != TokenKind::RightBrace) {
                universeArguments.push_back(parseLevel());
                while (peek().kind == TokenKind::Comma) {
                    consumeAny();
                    universeArguments.push_back(parseLevel());
                }
            }
            expect(TokenKind::RightBrace, "ending universe arguments");
        }
        return makeSurfaceIdentifier(std::move(name),
                                      std::move(universeArguments),
                                      first.line, first.column);
    }

    // Level expressions. A level atom optionally followed by `+ <digits>`.
    SurfaceLevelPointer parseLevel() {
        auto base = parseLevelAtom();
        while (peek().kind == TokenKind::Plus) {
            Token op = consumeAny();
            if (peek().kind != TokenKind::NumericLiteral) {
                throwHere("level '+' must be followed by a numeric literal");
            }
            Token amountToken = consumeAny();
            int amount = std::stoi(amountToken.lexeme);
            base = makeSurfaceLevelAdd(std::move(base), amount,
                                        op.line, op.column);
        }
        return base;
    }

    SurfaceLevelPointer parseLevelAtom() {
        const Token& current = peek();
        if (current.kind == TokenKind::NumericLiteral) {
            Token token = consumeAny();
            return makeSurfaceLevelNumeric(std::stoi(token.lexeme),
                                            token.line, token.column);
        }
        if (isIdentifierLike(current.kind)) {
            Token token = consumeAny();
            return makeSurfaceLevelName(token.lexeme, token.line, token.column);
        }
        if (current.kind == TokenKind::KeywordMax
            || current.kind == TokenKind::KeywordImax) {
            bool isImax = (current.kind == TokenKind::KeywordImax);
            Token token = consumeAny();
            expect(TokenKind::LeftParen,
                   isImax ? "after 'ImaxUniverse'" : "after 'MaxUniverse'");
            auto left = parseLevel();
            expect(TokenKind::Comma,
                   isImax ? "in 'ImaxUniverse'" : "in 'MaxUniverse'");
            auto right = parseLevel();
            expect(TokenKind::RightParen,
                   isImax ? "ending 'ImaxUniverse'" : "ending 'MaxUniverse'");
            if (isImax) {
                return makeSurfaceLevelImax(std::move(left), std::move(right),
                                             token.line, token.column);
            }
            return makeSurfaceLevelMax(std::move(left), std::move(right),
                                        token.line, token.column);
        }
        if (current.kind == TokenKind::LeftParen) {
            consumeAny();
            auto inner = parseLevel();
            expect(TokenKind::RightParen, "matching '('");
            return inner;
        }
        throwHere("expected level");
    }

    // Token-stream helpers.

    const Token& peek() const { return tokens_[position_]; }

    // Lookahead k tokens past the cursor, clamped to the trailing
    // EndOfFile token so deep lookahead near the end is safe.
    const Token& peekAt(size_t k) const {
        size_t index = position_ + k;
        if (index >= tokens_.size()) index = tokens_.size() - 1;
        return tokens_[index];
    }

    const Token& consumeAny() {
        const Token& token = tokens_[position_];
        position_++;
        return token;
    }

    void expect(TokenKind kind, const char* context) {
        if (peek().kind != kind) {
            throwHere(std::string("expected ") + tokenKindName(kind)
                       + " " + context);
        }
        consumeAny();
    }

    [[noreturn]] void throwHere(const std::string& message) {
        const Token& current = peek();
        throw ParseError(message + " at line " + std::to_string(current.line)
                          + ", column " + std::to_string(current.column)
                          + " (got " + tokenKindName(current.kind) + ")");
    }

    const std::vector<Token>& tokens_;
    size_t position_ = 0;
    int anonymousClaimCounter_ = 0;
    // True while parsing an `interface module` body: enables the
    // `type`/`constant` forms and proofless theorem signatures.
    bool interfaceModuleMode_ = false;
};

}  // namespace

// External-linkage wrapper over the file-local substituteSurfaceName
// worker (whose pattern helpers live in the anonymous namespace above).
SurfaceExpressionPointer substituteSurfaceIdentifier(
    SurfaceExpressionPointer expression,
    const std::string& targetName,
    SurfaceExpressionPointer replacement) {
    return substituteSurfaceName(std::move(expression), targetName,
                                 std::move(replacement));
}

SurfaceExpressionPointer parseExpression(const std::vector<Token>& tokens) {
    ParserImpl parser(tokens);
    return parser.parseTopLevelExpression();
}

SurfaceModule parseModule(const std::vector<Token>& tokens) {
    ParserImpl parser(tokens);
    return parser.parseModule();
}
