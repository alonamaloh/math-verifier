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
            case TokenKind::KeywordImport:     return parseImportDecl();
            case TokenKind::KeywordUsing:      return parseUsingDecl();
            case TokenKind::KeywordInductive:  return parseInductiveDecl();
            case TokenKind::KeywordAxiom:      return parseAxiomDecl();
            case TokenKind::KeywordDefinition: return parseDefinitionDecl(false);
            case TokenKind::KeywordTheorem:    return parseDefinitionDecl(true);
            default:
                throwHere("expected top-level statement keyword "
                          "(import / using / inductive / axiom / "
                          "definition / theorem)");
        }
    }

    SurfaceImportDecl parseImportDecl() {
        consumeAny();  // 'import'
        SurfaceImportDecl decl;
        decl.moduleName = consumeQualifiedNameString();
        return decl;
    }

    SurfaceUsingDecl parseUsingDecl() {
        consumeAny();  // 'using'
        SurfaceUsingDecl decl;
        decl.namespacePath = consumeQualifiedNameString();
        expect(TokenKind::Dot, "in using directive");
        if (peek().kind == TokenKind::Identifier) {
            // either "operators" or "literals" — we accept them by spelling
            std::string target = consumeAny().lexeme;
            if (target != "operators" && target != "literals") {
                throwHere("expected 'operators', 'literals', or a name "
                          "list in using directive");
            }
            decl.target = target;
        } else if (peek().kind == TokenKind::LeftBrace) {
            consumeAny();
            decl.target = "names";
            if (peek().kind != TokenKind::RightBrace) {
                if (peek().kind != TokenKind::Identifier) {
                    throwHere("expected name in using list");
                }
                decl.names.push_back(consumeAny().lexeme);
                while (peek().kind == TokenKind::Comma) {
                    consumeAny();
                    if (peek().kind != TokenKind::Identifier) {
                        throwHere("expected name in using list");
                    }
                    decl.names.push_back(consumeAny().lexeme);
                }
            }
            expect(TokenKind::RightBrace, "ending using name list");
        } else {
            throwHere("expected 'operators', 'literals', or '{' after '.'"
                      " in using directive");
        }
        return decl;
    }

    SurfaceInductiveDecl parseInductiveDecl() {
        consumeAny();  // 'inductive'
        SurfaceInductiveDecl decl;
        decl.name = consumeQualifiedNameString();
        decl.universeParameters = parseUniverseParameterList();
        while (peek().kind == TokenKind::LeftParen) {
            decl.parameters.push_back(parseExplicitBinder());
        }
        expect(TokenKind::Colon, "before inductive kind");
        decl.kind = parseExpression();
        expect(TokenKind::KeywordWhere, "before inductive constructors");
        while (peek().kind == TokenKind::Pipe) {
            consumeAny();  // '|'
            SurfaceConstructorSpec spec;
            if (peek().kind != TokenKind::Identifier) {
                throwHere("expected constructor name after '|'");
            }
            spec.name = consumeQualifiedNameString();
            expect(TokenKind::Colon, "before constructor type");
            spec.type = parseExpression();
            decl.constructors.push_back(std::move(spec));
        }
        return decl;
    }

    SurfaceAxiomDecl parseAxiomDecl() {
        consumeAny();  // 'axiom'
        SurfaceAxiomDecl decl;
        decl.name = consumeQualifiedNameString();
        decl.universeParameters = parseUniverseParameterList();
        expect(TokenKind::Colon, "before axiom type");
        decl.type = parseExpression();
        return decl;
    }

    SurfaceDefinitionDecl parseDefinitionDecl(bool isTheorem) {
        consumeAny();  // 'definition' / 'theorem'
        SurfaceDefinitionDecl decl;
        decl.isTheorem = isTheorem;
        decl.name = consumeQualifiedNameString();
        decl.universeParameters = parseUniverseParameterList();
        while (peek().kind == TokenKind::LeftParen) {
            decl.arguments.push_back(parseExplicitBinder());
        }
        expect(TokenKind::Colon, "before declaration type");
        decl.type = parseExpression();
        if (peek().kind == TokenKind::Assign) {
            consumeAny();  // ':='
            decl.body = parseExpression();
        } else if (peek().kind == TokenKind::Pipe) {
            while (peek().kind == TokenKind::Pipe) {
                decl.cases.push_back(parsePatternCase());
            }
        } else {
            throwHere("expected ':=' or '|' after declaration type");
        }
        return decl;
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
        //   name                  (variable binding, or nullary constructor)
        //   name(pat, pat, ...)   (constructor application)
        //   _                     (wildcard, treated as variable named "_")
        if (peek().kind != TokenKind::Identifier) {
            throwHere("expected pattern");
        }
        Token nameToken = consumeAny();
        if (peek().kind == TokenKind::LeftParen) {
            consumeAny();
            std::vector<SurfacePatternPointer> arguments;
            if (peek().kind == TokenKind::RightParen) {
                throwHere("constructor pattern arguments cannot be empty; "
                          "use bare '" + nameToken.lexeme
                          + "' for nullary constructors");
            }
            arguments.push_back(parsePattern());
            while (peek().kind == TokenKind::Comma) {
                consumeAny();
                arguments.push_back(parsePattern());
            }
            expect(TokenKind::RightParen, "ending constructor pattern");
            return makeSurfacePatternConstructor(nameToken.lexeme,
                                                  std::move(arguments),
                                                  nameToken.line,
                                                  nameToken.column);
        }
        return makeSurfacePatternBareName(nameToken.lexeme,
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
        if (peek().kind == TokenKind::KeywordFun) return parseLambda();
        if (peek().kind == TokenKind::KeywordLet) return parseLet();
        return parseImplication();
    }

    SurfaceExpressionPointer parseLambda() {
        const Token& start = consumeAny();  // 'fun'
        std::vector<SurfaceBinder> binders;
        while (peek().kind == TokenKind::LeftParen) {
            binders.push_back(parseExplicitBinder());
        }
        if (binders.empty()) {
            throwHere("expected at least one parenthesised binder after 'fun'");
        }
        expect(TokenKind::FatArrow, "after binders in 'fun'");
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
        if (peek().kind != TokenKind::Identifier) {
            throwHere("expected identifier after 'let'");
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

    // Helper used by lambda parsing. Requires an explicit `(name+ : type)`
    // form; throws on malformed binders.
    SurfaceBinder parseExplicitBinder() {
        expect(TokenKind::LeftParen, "starting binder");
        std::vector<std::string> names;
        while (peek().kind == TokenKind::Identifier) {
            names.push_back(consumeAny().lexeme);
        }
        if (names.empty()) {
            throwHere("expected at least one name in binder");
        }
        expect(TokenKind::Colon, "in binder");
        auto type = parseExpression();
        expect(TokenKind::RightParen, "ending binder");
        return SurfaceBinder{std::move(names), std::move(type)};
    }

    // Lookahead-with-restore variant for parseImplication. Returns
    // nullopt if the input doesn't match `(name+ : type)`, restoring
    // the parser position so the caller can fall back to expression
    // parsing.
    std::optional<SurfaceBinder> tryParseExplicitBinder() {
        size_t save = position_;
        if (peek().kind != TokenKind::LeftParen) return std::nullopt;
        consumeAny();  // '('
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
        if (peek().kind != TokenKind::RightParen) {
            position_ = save;
            return std::nullopt;
        }
        consumeAny();  // ')'
        return SurfaceBinder{std::move(names), std::move(type)};
    }

    // Pi types and implication. Right-associative. Tries explicit
    // `(name+ : T) → U` form first; otherwise parses a regular
    // expression and looks for a following `→`.
    SurfaceExpressionPointer parseImplication() {
        size_t save = position_;
        if (peek().kind == TokenKind::LeftParen) {
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
            || kind == TokenKind::Greater || kind == TokenKind::GreaterOrEqual;
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
        if (current.kind == TokenKind::KeywordProp) {
            Token token = consumeAny();
            return makeSurfaceProp(token.line, token.column);
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
