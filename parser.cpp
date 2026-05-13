#include "parser.hpp"

#include <optional>
#include <string>
#include <utility>

namespace {

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
            default:
                throwHere("expected top-level statement keyword "
                          "(import / using / inductive / axiom / "
                          "definition / theorem)");
        }
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
        if (peek().kind == TokenKind::Identifier) {
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
                if (peek().kind != TokenKind::Identifier) {
                    throwHere("expected name in using list");
                }
                declaration.names.push_back(consumeAny().lexeme);
                while (peek().kind == TokenKind::Comma) {
                    consumeAny();
                    if (peek().kind != TokenKind::Identifier) {
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
            if (peek().kind != TokenKind::Identifier) {
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

    // Parses a `{ let pat := v; ...; final_expr }` block. Each `let pat
    // := value;` statement becomes a nested let-in around the trailing
    // expression. Tuple-patterned lets desugar to single-clause cases
    // (same as `let ⟨...⟩ := v in body` in expression position).
    SurfaceExpressionPointer parseBlockBody() {
        Token openBrace = consumeAny();  // '{'
        // Collect (line, column, builder) for each let statement.
        // We'll apply them in reverse order around the final expression.
        struct LetWrapper {
            SurfacePatternPointer pattern;     // null if name-with-type form
            std::string name;                  // populated when pattern is null
            SurfaceExpressionPointer type;     // populated for name-with-type form
            SurfaceExpressionPointer value;
            int line = 0;
            int column = 0;
        };
        std::vector<LetWrapper> wrappers;
        while (peek().kind == TokenKind::KeywordLet) {
            Token letToken = consumeAny();
            LetWrapper wrapper;
            wrapper.line = letToken.line;
            wrapper.column = letToken.column;
            if (peek().kind == TokenKind::LeftAngle) {
                wrapper.pattern = parsePattern();
                expect(TokenKind::Assign,
                       "after let-pattern in block body");
                wrapper.value = parseExpression();
            } else if (peek().kind == TokenKind::Identifier) {
                Token nameToken = consumeAny();
                wrapper.name = nameToken.lexeme;
                if (peek().kind != TokenKind::Colon) {
                    throwHere("typed let in block body requires ': type "
                              "after the name (use let ⟨…⟩ := … ; for "
                              "destructuring without a type)");
                }
                consumeAny();  // ':'
                wrapper.type = parseExpression();
                expect(TokenKind::Assign, "after let type");
                wrapper.value = parseExpression();
            } else {
                throwHere("expected identifier or '⟨' after 'let'");
            }
            expect(TokenKind::Semicolon,
                   "ending let statement in block body");
            wrappers.push_back(std::move(wrapper));
        }
        SurfaceExpressionPointer finalExpression = parseExpression();
        // Optional trailing semicolon for the final expression.
        if (peek().kind == TokenKind::Semicolon) {
            consumeAny();
        }
        expect(TokenKind::RightBrace, "ending block body");
        // Apply wrappers in reverse order around the final expression.
        SurfaceExpressionPointer result = std::move(finalExpression);
        for (auto iterator = wrappers.rbegin();
             iterator != wrappers.rend(); ++iterator) {
            if (iterator->pattern) {
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
            } else {
                result = makeSurfaceLet(
                    std::move(iterator->name),
                    std::move(iterator->type),
                    std::move(iterator->value),
                    std::move(result),
                    iterator->line, iterator->column);
            }
        }
        (void)openBrace;
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
        if (peek().kind != TokenKind::Identifier) {
            throwHere("expected pattern");
        }
        Token nameToken = consumeAny();
        std::string fullName = nameToken.lexeme;
        while (peek().kind == TokenKind::Dot) {
            consumeAny();
            if (peek().kind != TokenKind::Identifier) {
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
        if (peek().kind != TokenKind::Identifier) {
            throwHere("expected identifier");
        }
        std::string name = consumeAny().lexeme;
        while (peek().kind == TokenKind::Dot) {
            consumeAny();
            if (peek().kind != TokenKind::Identifier) {
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
            if (peek().kind != TokenKind::Identifier) {
                throwHere("expected universe parameter name");
            }
            parameters.push_back(consumeAny().lexeme);
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                if (peek().kind != TokenKind::Identifier) {
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
               || peek().kind == TokenKind::Identifier) {
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
        if (peek().kind != TokenKind::Identifier) {
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
        while (peek().kind == TokenKind::Identifier) {
            names.push_back(consumeAny().lexeme);
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
        while (peek().kind == TokenKind::Identifier) {
            names.push_back(consumeAny().lexeme);
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

    SurfaceExpressionPointer parseLogicalOr() {
        auto left = parseLogicalAnd();
        while (peek().kind == TokenKind::LogicalOr) {
            Token op = consumeAny();
            auto right = parseLogicalAnd();
            left = makeSurfaceBinaryOperation("∨", std::move(left),
                                               std::move(right),
                                               op.line, op.column);
        }
        return left;
    }

    SurfaceExpressionPointer parseLogicalAnd() {
        auto left = parseEquality();
        while (peek().kind == TokenKind::LogicalAnd) {
            Token op = consumeAny();
            auto right = parseEquality();
            left = makeSurfaceBinaryOperation("∧", std::move(left),
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
            || kind == TokenKind::Divides;
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
               || peek().kind == TokenKind::Slash) {
            Token op = consumeAny();
            auto right = parsePower();
            const char* sym = (op.kind == TokenKind::Star) ? "*" : "/";
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
            std::vector<SurfaceExpressionPointer> arguments;
            arguments.push_back(parseExpression());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                arguments.push_back(parseExpression());
            }
            expect(TokenKind::RightParen, "ending argument list");
            head = makeSurfaceApplication(std::move(head),
                                           std::move(arguments),
                                           openParen.line, openParen.column);
        }
        return head;
    }

    SurfaceExpressionPointer parseAtom() {
        const Token& current = peek();
        if (current.kind == TokenKind::Identifier) {
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

    // `cases scrutinee { | pattern => body  | pattern => body  ... }`.
    // Builds an inductive eliminator at elaboration time; the motive is
    // derived from the enclosing expected type.
    SurfaceExpressionPointer parseCasesExpression() {
        Token casesToken = consumeAny();  // 'cases'
        auto scrutinee = parseExpression();
        expect(TokenKind::LeftBrace, "after cases scrutinee");
        std::vector<SurfaceCasesClause> clauses;
        while (peek().kind == TokenKind::Pipe) {
            Token pipeToken = consumeAny();
            SurfaceCasesClause clause;
            clause.line = pipeToken.line;
            clause.column = pipeToken.column;
            clause.pattern = parsePattern();
            expect(TokenKind::FatArrow, "between cases pattern and body");
            clause.body = parseExpression();
            clauses.push_back(std::move(clause));
        }
        if (clauses.empty()) {
            throwHere("cases expression needs at least one '|' clause");
        }
        expect(TokenKind::RightBrace, "ending cases expression");
        return makeSurfaceCases(std::move(scrutinee), std::move(clauses),
                                 casesToken.line, casesToken.column);
    }

    // Calc-step proof bodies are parsed at a precedence below `=` so the
    // next `=` (if any) starts the next calc step rather than being
    // consumed as a top-level equality. `function`/`let` are still
    // allowed at the top of a step proof; users who need a top-level
    // `→`, `∧`, `∨`, or `=` inside a step proof must parenthesise.
    SurfaceExpressionPointer parseCalcStepProof() {
        if (peek().kind == TokenKind::KeywordFunction) return parseLambda();
        if (peek().kind == TokenKind::KeywordLet)      return parseLet();
        return parseRelational();
    }

    // `calc <initial> = <next1> by <proof1> = <next2> by <proof2> …`.
    // Each `proofₖ` proves `<previous-expression> = <nextₖ>`. The
    // elaborator turns the chain into nested Equality.transitivity calls.
    SurfaceExpressionPointer parseCalc() {
        Token calcToken = consumeAny();  // 'calc'
        auto initialExpression = parseRelational();
        std::vector<SurfaceCalcStep> steps;
        while (peek().kind == TokenKind::Equal) {
            Token equalToken = consumeAny();  // '='
            auto nextExpression = parseRelational();
            expect(TokenKind::KeywordBy,
                   "after target expression in calc step");
            auto stepProof = parseCalcStepProof();
            SurfaceCalcStep step;
            step.nextExpression = std::move(nextExpression);
            step.stepProof = std::move(stepProof);
            step.line = equalToken.line;
            step.column = equalToken.column;
            steps.push_back(std::move(step));
        }
        if (steps.empty()) {
            throwHere("calc block needs at least one "
                      "'= <expression> by <proof>' step");
        }
        return makeSurfaceCalc(std::move(initialExpression),
                                std::move(steps),
                                calcToken.line, calcToken.column);
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
            if (peek().kind != TokenKind::Identifier) {
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
        if (current.kind == TokenKind::Identifier) {
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
