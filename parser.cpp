#include "parser.hpp"

#include <optional>
#include <string>
#include <utility>

namespace {

// Tactic-block keywords that are contextual: they have meaning only at
// specific positions inside `{ ... }` block bodies, `by_cases` / `by_
// induction` constructs, or `obtain ... from ...` statements. Outside
// those contexts they have no syntactic role at all, so the parser
// accepts them as ordinary identifiers — letting mathematicians use
// `claim`, `case`, `with`, etc. as binder or variable names. (The
// "wide" tactic keywords `cases`, `calc`, `witness`, `by_cases`, and
// `by_induction` still dispatch to special parsers from `parseAtom`,
// so they remain reserved everywhere; freeing them would require
// expression-position backtracking.)
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
        case TokenKind::KeywordField:
        case TokenKind::KeywordOperator:
        case TokenKind::KeywordOverload:
        case TokenKind::KeywordCoercion:
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
        case TokenKind::SubsetOf:
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
        || std::get_if<SurfaceProposition>(&node.node)
        || std::get_if<SurfaceHammer>(&node.node)) {
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
    if (auto* tuple = std::get_if<SurfaceAnonymousTuple>(&node.node)) {
        std::vector<SurfaceExpressionPointer> newComponents;
        for (const auto& component : tuple->components) {
            newComponents.push_back(substituteSurfaceName(
                component, targetName, replacement));
        }
        return makeSurfaceAnonymousTuple(std::move(newComponents),
                                          line, column);
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
            SurfaceCalcStep newStep;
            newStep.relation = step.relation;
            newStep.nextExpression = substituteSurfaceName(
                step.nextExpression, targetName, replacement);
            newStep.stepProof = substituteSurfaceName(
                step.stepProof, targetName, replacement);
            newStep.line = step.line;
            newStep.column = step.column;
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
        expect(TokenKind::KeywordModule, "at start of file");
        module.moduleName = consumeQualifiedNameString();
        while (peek().kind != TokenKind::EndOfFile) {
            module.statements.push_back(parseTopStatement());
        }
        return module;
    }

private:
    SurfaceTopStatement parseTopStatement() {
        switch (peek().kind) {
            case TokenKind::KeywordImport:     return parseImportDeclaration();
            case TokenKind::KeywordUsing:      return parseUsingDeclaration();
            case TokenKind::KeywordInductive:  return parseInductiveDeclaration();
            case TokenKind::KeywordAxiom:      return parseAxiomDeclaration();
            case TokenKind::KeywordDefinition: return parseDefinitionDeclaration(false);
            case TokenKind::KeywordTheorem:    return parseDefinitionDeclaration(true);
            case TokenKind::KeywordOperator:   return parseOperatorDeclaration();
            case TokenKind::KeywordOverload:   return parseOverloadDeclaration();
            case TokenKind::KeywordCoercion:   return parseCoercionDeclaration();
            case TokenKind::KeywordConvention: return parseConventionDeclaration();
            default:
                throwHere("expected top-level statement keyword "
                          "(import / using / inductive / axiom / "
                          "definition / theorem / operator / overload / "
                          "convention)");
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
        expect(TokenKind::Comma,
               "expected ',' between operand-type names");
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected a type name (right operand type)");
        }
        declaration.rightTypeName = consumeQualifiedNameString();
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
        if (!isIdentifierLike(peek().kind)) {
            throwHere("expected at least one name after 'convention'");
        }
        declaration.names.push_back(consumeAny().lexeme);
        // Optional additional names share the same type/propositions.
        while (peek().kind != TokenKind::Colon) {
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected ':' or another name in convention "
                          "declaration");
            }
            declaration.names.push_back(consumeAny().lexeme);
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
            declaration.body = parseExpression();
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
        } else {
            throwHere("expected ':=', '|', or '{' after declaration type");
        }
        return declaration;
    }

    // Parses a `{ stmt; stmt; ...; final_expr }` block. Statement
    // forms supported:
    //   - `let pat := value;`            (tuple-pattern destructure)
    //   - `let name : type := value;`    (typed binding)
    //   - `claim name : type [by expr];` (let synonym; hammer fills if
    //                                     no `by`)
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
            enum Kind { TypedLet, PatternLet, Suppose, Choose, Set };
            Kind kind = TypedLet;
            SurfacePatternPointer pattern;     // PatternLet
            std::string name;                  // TypedLet, Suppose, Choose, Set
            SurfaceExpressionPointer type;     // TypedLet, Suppose
            SurfaceExpressionPointer value;    // TypedLet, PatternLet, Choose, Set
            int line = 0;
            int column = 0;
        };
        std::vector<BlockWrapper> wrappers;
        // `calc … as NAME;` or bare `calc …;` at statement position
        // gets parsed below and may turn out to NOT be a statement
        // (it's the final expression). In that case we stash the parsed
        // calc here and skip the trailing parseExpression() call.
        SurfaceExpressionPointer parsedFinalCalc;
        while (peek().kind == TokenKind::KeywordLet
               || peek().kind == TokenKind::KeywordClaim
               || peek().kind == TokenKind::KeywordObtain
               || peek().kind == TokenKind::KeywordSuppose
               || peek().kind == TokenKind::KeywordChoose
               || peek().kind == TokenKind::KeywordSet
               || peek().kind == TokenKind::KeywordCalc) {
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
            if (peek().kind == TokenKind::KeywordCalc) {
                Token calcToken = peek();
                SurfaceExpressionPointer calcExpression = parseCalc();
                if (peek().kind != TokenKind::KeywordAs
                    && peek().kind != TokenKind::Semicolon) {
                    parsedFinalCalc = std::move(calcExpression);
                    break;
                }
                std::string statementName;
                if (peek().kind == TokenKind::KeywordAs) {
                    consumeAny();  // 'as'
                    if (!isIdentifierLike(peek().kind)) {
                        throwHere("expected identifier after 'as'");
                    }
                    statementName = consumeAny().lexeme;
                } else {
                    // Anonymous: synthesise a name that won't collide.
                    statementName = "_calc_"
                        + std::to_string(calcToken.line) + "_"
                        + std::to_string(calcToken.column);
                }
                expect(TokenKind::Semicolon,
                       "ending calc statement");
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
                for (const auto& step : calcNode->steps) {
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
                const char* relationSymbol;
                if (seenStrict) {
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
            // If we're at the structured form, leave the wrapper loop;
            // parseExpression() at the end of parseBlockContents picks
            // up the structured-claim chain.
            if (peek().kind == TokenKind::KeywordClaim
                && !looksLikeLegacyClaim()) {
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
            } else if (isSuppose) {
                wrapper.kind = BlockWrapper::Suppose;
                wrapper.type = parseExpression();
                expect(TokenKind::KeywordAs,
                       "after suppose proposition (suppose P as h;)");
                if (!isIdentifierLike(peek().kind)) {
                    throwHere(
                        "expected identifier after 'as' in suppose");
                }
                Token nameToken = consumeAny();
                wrapper.name = nameToken.lexeme;
            } else if (isChoose) {
                wrapper.kind = BlockWrapper::Choose;
                if (!isIdentifierLike(peek().kind)) {
                    throwHere(
                        "expected identifier after 'choose'");
                }
                Token nameToken = consumeAny();
                wrapper.name = nameToken.lexeme;
                // `such` and `that` are ordinary identifiers
                // everywhere except in this slot — text-match here
                // so they remain usable as variable names elsewhere.
                if (peek().kind != TokenKind::Identifier
                    || peek().lexeme != "such") {
                    throwHere(
                        "expected 'such' after choose name "
                        "(choose n such that P(n);)");
                }
                consumeAny();
                if (peek().kind != TokenKind::Identifier
                    || peek().lexeme != "that") {
                    throwHere(
                        "expected 'that' after 'such' in choose");
                }
                consumeAny();
                wrapper.value = parseExpression();
            } else if (isObtain) {
                wrapper.kind = BlockWrapper::PatternLet;
                wrapper.pattern = parsePattern();
                expect(TokenKind::KeywordFrom,
                       "after obtain-pattern (obtain ⟨…⟩ from E;)");
                wrapper.value = parseExpression();
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
                    if (peek().kind == TokenKind::KeywordBy) {
                        consumeAny();  // 'by'
                        wrapper.value = parseExpression();
                    } else if (peek().kind == TokenKind::LeftBrace) {
                        // Footnote form: `claim P : T { proof_block };`
                        // is sugar for `claim P : T by { proof_block };`.
                        // The block is a normal expression-position
                        // block, so parseExpression handles it.
                        wrapper.value = parseExpression();
                    } else {
                        // No `by` or `{`: the hammer fills the proof.
                        // We build a `?` placeholder so the standard
                        // let-binding path sees the same machinery.
                        wrapper.value = makeSurfaceHammer(
                            statementToken.line, statementToken.column);
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
            expect(TokenKind::Semicolon, terminator);
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
            // (with any `?` placeholders the hammer fills) becomes the
            // block's trailing value. No new semantics beyond letting
            // the user mark the conclusion with the math keyword.
            consumeAny();  // 'apply'
            finalExpression = parseExpression();
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            }
        } else if (peek().kind == TokenKind::KeywordContradiction) {
            // `contradiction;` — terminal. The trailing expression is
            // a `?` hammer placeholder; the elaborator's contradiction
            // strategy scans the local context for a pair (H : P,
            // H' : ¬P) and builds `False.eliminate*(goal, H'(H))`.
            Token contradictionToken = consumeAny();
            if (peek().kind == TokenKind::Semicolon) consumeAny();
            finalExpression = makeSurfaceHammer(
                contradictionToken.line, contradictionToken.column);
        } else if (parsedFinalCalc) {
            // The wrapper loop already parsed a `calc` and discovered it
            // wasn't followed by `as` or `;`, so it's the block's final
            // expression. Use the pre-parsed value directly.
            finalExpression = std::move(parsedFinalCalc);
            if (peek().kind == TokenKind::Semicolon) {
                consumeAny();
            }
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
                        iterator->line, iterator->column);
                    break;
                case BlockWrapper::Suppose: {
                    SurfaceBinder binder;
                    binder.names.push_back(std::move(iterator->name));
                    binder.type = std::move(iterator->type);
                    binder.isImplicit = false;
                    result = makeSurfaceLambda(
                        std::move(binder),
                        std::move(result),
                        iterator->line, iterator->column);
                    break;
                }
                case BlockWrapper::Choose: {
                    result = makeSurfaceChoose(
                        std::move(iterator->name),
                        std::move(iterator->value),
                        std::move(result),
                        iterator->line, iterator->column);
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
        if (peek().kind == TokenKind::KeywordFunction) return parseLambda();
        if (peek().kind == TokenKind::KeywordLet) return parseLet();
        return parseImplication();
    }

    SurfaceExpressionPointer parseLambda() {
        const Token& start = consumeAny();  // 'function'
        std::vector<SurfaceBinder> binders;
        while (peek().kind == TokenKind::LeftParen
               || peek().kind == TokenKind::LeftBrace
               || isIdentifierLike(peek().kind)) {
            if (peek().kind == TokenKind::LeftParen
                || peek().kind == TokenKind::LeftBrace) {
                binders.push_back(parseExplicitBinder());
            } else {
                // Untyped binder: a bare name. The elaborator must be
                // able to recover the binder's type from context
                // (currently supported only for select special-cased
                // call sites like congruenceOf's first argument).
                Token nameToken = consumeAny();
                binders.push_back({{nameToken.lexeme}, nullptr, false});
            }
        }
        if (binders.empty()) {
            throwHere("expected at least one binder after 'function'");
        }
        expect(TokenKind::FatArrow, "after binders in 'function'");
        auto body = parseExpression();
        // Curry: fun (b1) (b2) ... => body  ↦  λ b1. λ b2. ... body
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
            || kind == TokenKind::SubsetOf;
    }

    SurfaceExpressionPointer parseRelational() {
        auto left = parseAdditive();
        if (isRelationalKind(peek().kind)) {
            Token op = consumeAny();
            auto right = parseAdditive();
            if (isRelationalKind(peek().kind)) {
                throwHere("relational operators are non-associative");
            }
            const char* sym = "?";
            switch (op.kind) {
                case TokenKind::Less:           sym = "<"; break;
                case TokenKind::LessOrEqual:    sym = "≤"; break;
                case TokenKind::Greater:        sym = ">"; break;
                case TokenKind::GreaterOrEqual: sym = "≥"; break;
                case TokenKind::Divides:        sym = "∣"; break;
                case TokenKind::NotDivides:     sym = "∤"; break;
                case TokenKind::NotLessOrEqual: sym = "≰"; break;
                case TokenKind::ElementOf:      sym = "∈"; break;
                case TokenKind::SubsetOf:       sym = "⊆"; break;
                default: break;
            }
            left = makeSurfaceBinaryOperation(sym, std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    SurfaceExpressionPointer parseAdditive() {
        auto left = parseMultiplicative();
        while (peek().kind == TokenKind::Plus
               || peek().kind == TokenKind::Minus) {
            Token op = consumeAny();
            auto right = parseMultiplicative();
            const char* sym = (op.kind == TokenKind::Plus) ? "+" : "-";
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
        return parseApplication();
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

    SurfaceExpressionPointer parseAtom() {
        const Token& current = peek();
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
        if (current.kind == TokenKind::KeywordField) {
            Token fieldToken = consumeAny();
            // `field` REQUIRES an argument list of nonzero hypotheses.
            // The argument list is parsed exactly like a function call.
            if (peek().kind != TokenKind::LeftParen) {
                throwHere(
                    "`field` requires a parenthesized argument list of "
                    "nonzero hypotheses (e.g. `field(aNonzero, bNonzero)`)");
            }
            consumeAny();  // '('
            if (peek().kind == TokenKind::RightParen) {
                throwHere(
                    "`field()` with no arguments is not allowed — supply "
                    "one nonzero hypothesis per `reciprocal_function` "
                    "argument appearing in the goal");
            }
            std::vector<SurfaceExpressionPointer> hypotheses;
            hypotheses.push_back(parseExpression());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                hypotheses.push_back(parseExpression());
            }
            expect(TokenKind::RightParen,
                   "ending `field` argument list");
            return makeSurfaceField(std::move(hypotheses),
                                     fieldToken.line, fieldToken.column);
        }
        // `claim` at expression position starts a structured proof.
        // Checked BEFORE isIdentifierLike, because `claim` is a
        // contextual keyword (and so would otherwise be treated as a
        // bare identifier). Block-statement `claim NAME : T [by V];`
        // is parsed earlier via parseBlockContents and never reaches
        // here, so the two forms don't collide. A claim immediately
        // followed by another `claim` chains via SurfaceLet so the
        // proposition of the first is in scope for the rest.
        if (current.kind == TokenKind::KeywordClaim) {
            return parseStructuredClaimSequence();
        }
        if (current.kind == TokenKind::KeywordGiven) {
            return parseGiven();
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
        if (current.kind == TokenKind::KeywordByCases
            || current.kind == TokenKind::KeywordByInduction) {
            return parseByCasesOrInduction();
        }
        if (current.kind == TokenKind::KeywordByStrongInduction) {
            return parseByStrongInduction();
        }
        if (current.kind == TokenKind::LeftBrace) {
            // `{ let pat := v; ...; final_expr }` as an expression.
            // Same shape as the theorem-body block form; useful inside
            // case clauses or anywhere an expression is expected.
            return parseBlockBody();
        }
        if (current.kind == TokenKind::Question) {
            Token questionToken = consumeAny();
            return makeSurfaceHammer(questionToken.line,
                                      questionToken.column);
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
    SurfaceExpressionPointer parseCasesExpression() {
        Token casesToken = consumeAny();  // 'cases'
        auto scrutinee = parseExpression();
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

    // Parses an optional `refining <name>[, <name>]*` clause used by
    // `cases`, `by_cases`, and `by_induction` to mark in-scope binders
    // whose types should be refined per arm. Empty vector if the
    // keyword isn't present.
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

    // Calc-step proof bodies are parsed at a precedence below `=` so the
    // next calc-separator token (`=`, `≤`, `<`, `≥`, `>`) starts the
    // next calc step rather than being consumed as part of this step's
    // proof. `function`/`let` are still allowed at the top of a step
    // proof; users who need a top-level `→`, `∧`, `∨`, `=`, or any
    // inequality inside a step proof must parenthesise.
    SurfaceExpressionPointer parseCalcStepProof() {
        if (peek().kind == TokenKind::KeywordFunction) return parseLambda();
        if (peek().kind == TokenKind::KeywordLet)      return parseLet();
        return parseAdditive();
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
    SurfaceExpressionPointer parseCalc() {
        Token calcToken = consumeAny();  // 'calc'
        auto initialExpression = parseAdditive();
        std::vector<SurfaceCalcStep> steps;
        while (peek().kind == TokenKind::Equal
               || peek().kind == TokenKind::LessOrEqual
               || peek().kind == TokenKind::Less
               || peek().kind == TokenKind::GreaterOrEqual
               || peek().kind == TokenKind::Greater) {
            Token relationToken = consumeAny();
            CalcRelation relation;
            switch (relationToken.kind) {
                case TokenKind::LessOrEqual:
                    relation = CalcRelation::LessOrEqual; break;
                case TokenKind::Less:
                    relation = CalcRelation::LessThan; break;
                case TokenKind::GreaterOrEqual:
                    relation = CalcRelation::GreaterOrEqual; break;
                case TokenKind::Greater:
                    relation = CalcRelation::GreaterThan; break;
                default:
                    relation = CalcRelation::Equality; break;
            }
            auto nextExpression = parseAdditive();
            SurfaceCalcStep step;
            step.relation = relation;
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
    // Coexists with block-statement `claim NAME : TYPE [by V];` — that
    // form is handled by parseBlockContents and never reaches here.
    SurfaceExpressionPointer parseStructuredClaim() {
        Token claimToken = consumeAny();  // 'claim'
        SurfaceExpressionPointer proposition;
        SurfaceExpressionPointer byHint;
        bool byCases = false;
        std::vector<SurfaceStructuredClaimArm> arms;
        // Bare `claim` / `claim by …` — terminal-shaped, no proposition.
        if (peek().kind != TokenKind::KeywordBy
            && !isStructuredClaimTerminator()) {
            proposition = parseExpression();
        }
        if (peek().kind == TokenKind::KeywordBy) {
            consumeAny();  // 'by'
            if (peek().kind == TokenKind::KeywordCases) {
                consumeAny();  // 'cases'
                byCases = true;
                expect(TokenKind::LeftBrace, "after 'by cases'");
                while (peek().kind == TokenKind::KeywordIn) {
                    arms.push_back(parseStructuredClaimArm());
                }
                expect(TokenKind::RightBrace,
                       "ending 'by cases' arms block");
            } else {
                byHint = parseExpression();
            }
        }
        return makeSurfaceStructuredClaim(
            std::move(proposition), /*label=*/"",
            std::move(byHint), byCases, std::move(arms),
            claimToken.line, claimToken.column);
    }

    // A run of one or more `claim`s. Each non-terminal claim (one that
    // is followed by another `claim`) is wrapped in a SurfaceLet that
    // introduces its proof under an auto-generated anonymous binder
    // name (`_anonymousClaim_<n>`). The final claim becomes the
    // sequence's value. Anonymous binders are searchable via Step 5's
    // hypothesis lookup and `given (P)`.
    SurfaceExpressionPointer parseStructuredClaimSequence() {
        SurfaceExpressionPointer first = parseStructuredClaim();
        if (peek().kind != TokenKind::KeywordClaim) {
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
            || k == TokenKind::KeywordModule;
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
        Token inToken = consumeAny();  // 'in'
        expect(TokenKind::LeftParen, "after 'in'");
        auto disjunctType = parseExpression();
        expect(TokenKind::RightParen,
               "after disjunct type in 'in (T) …'");
        std::string binderName;
        if (peek().kind == TokenKind::KeywordAs) {
            consumeAny();  // 'as'
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an identifier after 'as'");
            }
            binderName = consumeAny().lexeme;
        }
        expect(TokenKind::Colon, "after arm header");
        auto body = parseExpression();
        SurfaceStructuredClaimArm arm;
        arm.disjunctType = std::move(disjunctType);
        arm.binderName = std::move(binderName);
        arm.body = std::move(body);
        arm.line = inToken.line;
        arm.column = inToken.column;
        return arm;
    }

    // `by_cases on E { case P: body; … }`, or
    // `by_induction on E with ih { case P: body; … }`, or
    // `by_induction on E using L with subject, ih { body }`. All three
    // parse as regular expressions so they can sit anywhere a value
    // belongs (and be applied to further arguments via parseApplication).
    SurfaceExpressionPointer parseByCasesOrInduction() {
        Token byToken = consumeAny();
        bool isInduction =
            byToken.kind == TokenKind::KeywordByInduction;
        expect(TokenKind::KeywordOn,
               isInduction ? "after 'by_induction'"
                           : "after 'by_cases'");
        auto scrutinee = parseExpression();
        if (isInduction
            && peek().kind == TokenKind::KeywordUsing) {
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
        std::string ihName;
        if (isInduction) {
            expect(TokenKind::KeywordWith,
                   "after 'by_induction on <expr>'");
            if (!isIdentifierLike(peek().kind)) {
                throwHere("expected an identifier (the "
                          "induction hypothesis name) after "
                          "'with'");
            }
            ihName = consumeAny().lexeme;
        }
        // Optional `refining <name>[, <name>]*`: each listed in-scope
        // binder has its type refined per arm. See parseOptionalRefiningList.
        std::vector<std::string> refiningNames =
            parseOptionalRefiningList();
        expect(TokenKind::LeftBrace,
               isInduction
                   ? "after 'by_induction on <expr> with <ih>'"
                   : "after 'by_cases on <expr>'");
        auto clauses = parseCasesClauseBlock(
            ihName, TokenKind::Colon);
        expect(TokenKind::RightBrace,
               isInduction ? "ending by_induction block"
                           : "ending by_cases block");
        if (refiningNames.empty()) {
            return makeSurfaceCases(
                std::move(scrutinee), std::move(clauses),
                byToken.line, byToken.column);
        }
        return makeSurfaceCasesWithRefining(
            std::move(scrutinee), std::move(clauses),
            /*equalityHypothesisName=*/std::string(),
            std::move(refiningNames),
            byToken.line, byToken.column);
    }

    // `by_strong_induction on E with subject, ih { body }` —
    // single-step strong induction. Same surface shape as the
    // explicit `by_induction on E using L with subject, ih { body }`
    // but with the induction lemma resolved at elaboration time as
    // `<CarrierTypeName>.strong_induction`.
    SurfaceExpressionPointer parseByStrongInduction() {
        Token byToken = consumeAny();  // 'by_strong_induction'
        expect(TokenKind::KeywordOn,
               "after 'by_strong_induction'");
        SurfaceExpressionPointer scrutinee = parseExpression();
        expect(TokenKind::KeywordWith,
               "after 'by_strong_induction on <expr>'");
        if (!isIdentifierLike(peek().kind)) {
            throwHere(
                "expected the subject name after 'with'");
        }
        std::string subjectName = consumeAny().lexeme;
        expect(TokenKind::Comma,
               "between subject name and ih name in "
               "by_strong_induction");
        if (!isIdentifierLike(peek().kind)) {
            throwHere(
                "expected the induction hypothesis name "
                "after ','");
        }
        std::string ihName = consumeAny().lexeme;
        expect(TokenKind::LeftBrace,
               "after 'by_strong_induction on … with <subject>, <ih>'");
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
            witnessToken.line, witnessToken.column);
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
                   isImax ? "after 'imax'" : "after 'max'");
            auto left = parseLevel();
            expect(TokenKind::Comma,
                   isImax ? "in 'imax'" : "in 'max'");
            auto right = parseLevel();
            expect(TokenKind::RightParen,
                   isImax ? "ending 'imax'" : "ending 'max'");
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
};

}  // namespace

SurfaceExpressionPointer parseExpression(const std::vector<Token>& tokens) {
    ParserImpl parser(tokens);
    return parser.parseTopLevelExpression();
}

SurfaceModule parseModule(const std::vector<Token>& tokens) {
    ParserImpl parser(tokens);
    return parser.parseModule();
}
