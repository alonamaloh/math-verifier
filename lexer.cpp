#include "lexer.hpp"

#include <cctype>
#include <optional>
#include <string>
#include <unordered_map>

namespace {

const std::unordered_map<std::string, TokenKind>& keywordTable() {
    static const std::unordered_map<std::string, TokenKind> table = {
        {"module",        TokenKind::KeywordModule},
        {"import",        TokenKind::KeywordImport},
        {"using",         TokenKind::KeywordUsing},
        {"inductive",     TokenKind::KeywordInductive},
        {"definition",    TokenKind::KeywordDefinition},
        {"axiom",         TokenKind::KeywordAxiom},
        {"theorem",       TokenKind::KeywordTheorem},
        {"where",         TokenKind::KeywordWhere},
        {"function",      TokenKind::KeywordFunction},
        {"let",           TokenKind::KeywordLet},
        {"in",            TokenKind::KeywordIn},
        {"Type",          TokenKind::KeywordType},
        {"Proposition",   TokenKind::KeywordProposition},
        {"max",           TokenKind::KeywordMax},
        {"imax",          TokenKind::KeywordImax},
        {"calc",          TokenKind::KeywordCalc},
        {"by",            TokenKind::KeywordBy},
        {"on",            TokenKind::KeywordOn},
        {"case",          TokenKind::KeywordCase},
        {"cases",         TokenKind::KeywordCases},
        {"with",          TokenKind::KeywordWith},
        {"apply",         TokenKind::KeywordApply},
        {"claim",         TokenKind::KeywordClaim},
        {"witness",       TokenKind::KeywordWitness},
        {"suffices",      TokenKind::KeywordSuffices},
        {"by_cases",      TokenKind::KeywordByCases},
        {"by_induction",  TokenKind::KeywordByInduction},
        {"contradiction", TokenKind::KeywordContradiction},
        {"obtain",        TokenKind::KeywordObtain},
        {"suppose",       TokenKind::KeywordSuppose},
        {"from",          TokenKind::KeywordFrom},
        {"set",           TokenKind::KeywordSet},
        {"operator",      TokenKind::KeywordOperator},
        {"overload",      TokenKind::KeywordOverload},
        {"coercion",      TokenKind::KeywordCoercion},
        {"sorry",         TokenKind::KeywordSorry},
        {"ring",          TokenKind::KeywordRing},
        {"field",         TokenKind::KeywordField},
        {"convention",    TokenKind::KeywordConvention},
        {"given",         TokenKind::KeywordGiven},
        {"as",            TokenKind::KeywordAs},
        {"refining",      TokenKind::KeywordRefining},
    };
    return table;
}

bool isIdentifierStart(char character) {
    return std::isalpha(static_cast<unsigned char>(character)) || character == '_';
}

bool isIdentifierContinuation(char character) {
    return std::isalnum(static_cast<unsigned char>(character))
        || character == '_' || character == '\'';
}

// A small state machine. Public entry is run(); everything else is
// internal helpers. We carry line/column for error messages but use
// byte offsets for matching — Unicode operators are matched by their
// UTF-8 byte sequence.
class Lexer {
public:
    explicit Lexer(const std::string& source) : source_(source) {}

    std::vector<Token> run() {
        std::vector<Token> tokens;
        while (true) {
            skipWhitespaceAndComments();
            if (position_ >= source_.size()) break;
            tokens.push_back(nextToken());
        }
        tokens.push_back({TokenKind::EndOfFile, "", line_, column_});
        return tokens;
    }

private:
    void skipWhitespaceAndComments() {
        while (position_ < source_.size()) {
            char character = source_[position_];
            if (character == ' ' || character == '\t' || character == '\r') {
                advanceOne();
            } else if (character == '\n') {
                position_++;
                line_++;
                column_ = 1;
            } else if (matchPrefix("--")) {
                while (position_ < source_.size() && source_[position_] != '\n') {
                    advanceOne();
                }
            } else if (matchPrefix("/-")) {
                skipBlockComment();
            } else {
                return;
            }
        }
    }

    void skipBlockComment() {
        int startLine = line_;
        consume("/-");
        int depth = 1;
        while (position_ < source_.size() && depth > 0) {
            if (matchPrefix("/-")) {
                consume("/-");
                depth++;
            } else if (matchPrefix("-/")) {
                consume("-/");
                depth--;
            } else if (source_[position_] == '\n') {
                position_++;
                line_++;
                column_ = 1;
            } else {
                advanceOne();
            }
        }
        if (depth != 0) {
            throw LexError("Unterminated block comment starting at line "
                           + std::to_string(startLine));
        }
    }

    Token nextToken() {
        int startLine = line_;
        int startColumn = column_;
        char character = source_[position_];

        if (isIdentifierStart(character)) {
            std::string lexeme;
            while (position_ < source_.size()
                   && isIdentifierContinuation(source_[position_])) {
                lexeme.push_back(source_[position_]);
                advanceOne();
            }
            auto iterator = keywordTable().find(lexeme);
            TokenKind kind = (iterator != keywordTable().end())
                                 ? iterator->second
                                 : TokenKind::Identifier;
            return {kind, std::move(lexeme), startLine, startColumn};
        }

        if (std::isdigit(static_cast<unsigned char>(character))) {
            std::string lexeme;
            while (position_ < source_.size()
                   && std::isdigit(static_cast<unsigned char>(source_[position_]))) {
                lexeme.push_back(source_[position_]);
                advanceOne();
            }
            return {TokenKind::NumericLiteral, std::move(lexeme),
                    startLine, startColumn};
        }

        // Multi-character ASCII punctuation and operators. Longest first so
        // ":=" wins over ":" and "<=" over "<".
        if (auto tok = tryMultiCharOperator(startLine, startColumn)) return *tok;

        // Unicode operators (UTF-8 byte sequences).
        if (auto tok = tryUnicodeOperator(startLine, startColumn)) return *tok;

        switch (character) {
            case '(':  advanceOne(); return {TokenKind::LeftParen,   "(", startLine, startColumn};
            case ')':  advanceOne(); return {TokenKind::RightParen,  ")", startLine, startColumn};
            case '{':  advanceOne(); return {TokenKind::LeftBrace,   "{", startLine, startColumn};
            case '}':  advanceOne(); return {TokenKind::RightBrace,  "}", startLine, startColumn};
            case ',':  advanceOne(); return {TokenKind::Comma,       ",", startLine, startColumn};
            case ':':  advanceOne(); return {TokenKind::Colon,       ":", startLine, startColumn};
            case ';':  advanceOne(); return {TokenKind::Semicolon,   ";", startLine, startColumn};
            case '?':  advanceOne(); return {TokenKind::Question,    "?", startLine, startColumn};
            case '|':  advanceOne(); return {TokenKind::Pipe,        "|", startLine, startColumn};
            case '.':  advanceOne(); return {TokenKind::Dot,         ".", startLine, startColumn};
            case '+':  advanceOne(); return {TokenKind::Plus,        "+", startLine, startColumn};
            case '-':  advanceOne(); return {TokenKind::Minus,       "-", startLine, startColumn};
            case '*':  advanceOne(); return {TokenKind::Star,        "*", startLine, startColumn};
            case '/':  advanceOne(); return {TokenKind::Slash,       "/", startLine, startColumn};
            case '^':  advanceOne(); return {TokenKind::Caret,       "^", startLine, startColumn};
            case '<':  advanceOne(); return {TokenKind::Less,        "<", startLine, startColumn};
            case '>':  advanceOne(); return {TokenKind::Greater,     ">", startLine, startColumn};
            case '=':  advanceOne(); return {TokenKind::Equal,       "=", startLine, startColumn};
        }

        throw LexError("Unexpected character '" + std::string(1, character)
                       + "' at line " + std::to_string(startLine)
                       + ", column " + std::to_string(startColumn));
    }

    std::optional<Token> tryMultiCharOperator(int startLine, int startColumn) {
        struct Entry { const char* text; TokenKind kind; };
        static const Entry table[] = {
            {":=",  TokenKind::Assign},
            {"=>",  TokenKind::FatArrow},
            {"->",  TokenKind::Arrow},
            {"<=",  TokenKind::LessOrEqual},
            {">=",  TokenKind::GreaterOrEqual},
            {"!=",  TokenKind::NotEqual},
            {"/\\", TokenKind::LogicalAnd},
            {"\\/", TokenKind::LogicalOr},
            {".{",  TokenKind::DotLeftBrace},
        };
        for (const auto& entry : table) {
            if (matchPrefix(entry.text)) {
                std::string lexeme = entry.text;
                consume(entry.text);
                return Token{entry.kind, std::move(lexeme),
                             startLine, startColumn};
            }
        }
        return std::nullopt;
    }

    std::optional<Token> tryUnicodeOperator(int startLine, int startColumn) {
        struct Entry { const char* text; TokenKind kind; };
        static const Entry table[] = {
            {"→", TokenKind::Arrow},
            {"≤", TokenKind::LessOrEqual},
            {"≥", TokenKind::GreaterOrEqual},
            {"≠", TokenKind::NotEqual},
            {"∧", TokenKind::LogicalAnd},
            {"∨", TokenKind::LogicalOr},
            {"¬", TokenKind::LogicalNot},
            {"∣", TokenKind::Divides},
            {"∤", TokenKind::NotDivides},
            {"≰", TokenKind::NotLessOrEqual},
            {"∈", TokenKind::ElementOf},
            {"⊆", TokenKind::SubsetOf},
            {"∀", TokenKind::ForAll},
            {"∃", TokenKind::Exists},
            {"⟨", TokenKind::LeftAngle},
            {"⟩", TokenKind::RightAngle},
            {"·", TokenKind::CenterDot},
        };
        for (const auto& entry : table) {
            if (matchPrefix(entry.text)) {
                std::string lexeme = entry.text;
                consume(entry.text);
                return Token{entry.kind, std::move(lexeme),
                             startLine, startColumn};
            }
        }
        return std::nullopt;
    }

    bool matchPrefix(const char* prefix) {
        size_t length = std::char_traits<char>::length(prefix);
        if (position_ + length > source_.size()) return false;
        return source_.compare(position_, length, prefix) == 0;
    }

    void consume(const char* expected) {
        size_t length = std::char_traits<char>::length(expected);
        for (size_t i = 0; i < length; ++i) advanceOne();
    }

    void advanceOne() {
        position_++;
        column_++;
    }

    const std::string& source_;
    size_t position_ = 0;
    int line_ = 1;
    int column_ = 1;
};

}  // namespace

std::vector<Token> lex(const std::string& source) {
    Lexer lexer(source);
    return lexer.run();
}

bool isKeyword(TokenKind kind) {
    switch (kind) {
        case TokenKind::KeywordModule:
        case TokenKind::KeywordImport:
        case TokenKind::KeywordUsing:
        case TokenKind::KeywordInductive:
        case TokenKind::KeywordDefinition:
        case TokenKind::KeywordAxiom:
        case TokenKind::KeywordTheorem:
        case TokenKind::KeywordWhere:
        case TokenKind::KeywordFunction:
        case TokenKind::KeywordLet:
        case TokenKind::KeywordIn:
        case TokenKind::KeywordType:
        case TokenKind::KeywordProposition:
        case TokenKind::KeywordMax:
        case TokenKind::KeywordImax:
        case TokenKind::KeywordCalc:
        case TokenKind::KeywordBy:
        case TokenKind::KeywordOn:
        case TokenKind::KeywordCase:
        case TokenKind::KeywordCases:
        case TokenKind::KeywordWith:
        case TokenKind::KeywordApply:
        case TokenKind::KeywordClaim:
        case TokenKind::KeywordWitness:
        case TokenKind::KeywordSuffices:
        case TokenKind::KeywordByCases:
        case TokenKind::KeywordByInduction:
        case TokenKind::KeywordContradiction:
        case TokenKind::KeywordObtain:
        case TokenKind::KeywordSuppose:
        case TokenKind::KeywordFrom:
        case TokenKind::KeywordSet:
            return true;
        default:
            return false;
    }
}

const char* tokenKindName(TokenKind kind) {
    switch (kind) {
        case TokenKind::Identifier:           return "identifier";
        case TokenKind::NumericLiteral:       return "numeric literal";
        case TokenKind::KeywordModule:        return "'module'";
        case TokenKind::KeywordImport:        return "'import'";
        case TokenKind::KeywordUsing:         return "'using'";
        case TokenKind::KeywordInductive:     return "'inductive'";
        case TokenKind::KeywordDefinition:    return "'definition'";
        case TokenKind::KeywordAxiom:         return "'axiom'";
        case TokenKind::KeywordTheorem:       return "'theorem'";
        case TokenKind::KeywordWhere:         return "'where'";
        case TokenKind::KeywordFunction:           return "'function'";
        case TokenKind::KeywordLet:           return "'let'";
        case TokenKind::KeywordIn:            return "'in'";
        case TokenKind::KeywordType:          return "'Type'";
        case TokenKind::KeywordProposition:   return "'Proposition'";
        case TokenKind::KeywordMax:           return "'max'";
        case TokenKind::KeywordImax:          return "'imax'";
        case TokenKind::KeywordCalc:          return "'calc'";
        case TokenKind::KeywordBy:            return "'by'";
        case TokenKind::KeywordOn:            return "'on'";
        case TokenKind::KeywordCase:          return "'case'";
        case TokenKind::KeywordCases:         return "'cases'";
        case TokenKind::KeywordWith:          return "'with'";
        case TokenKind::KeywordApply:         return "'apply'";
        case TokenKind::KeywordClaim:         return "'claim'";
        case TokenKind::KeywordWitness:       return "'witness'";
        case TokenKind::KeywordSuffices:      return "'suffices'";
        case TokenKind::KeywordByCases:       return "'by_cases'";
        case TokenKind::KeywordByInduction:   return "'by_induction'";
        case TokenKind::KeywordContradiction: return "'contradiction'";
        case TokenKind::KeywordObtain:        return "'obtain'";
        case TokenKind::KeywordSuppose:       return "'suppose'";
        case TokenKind::KeywordFrom:          return "'from'";
        case TokenKind::KeywordSet:           return "'set'";
        case TokenKind::KeywordOperator:      return "'operator'";
        case TokenKind::KeywordOverload:      return "'overload'";
        case TokenKind::KeywordCoercion:      return "'coercion'";
        case TokenKind::KeywordSorry:         return "'sorry'";
        case TokenKind::KeywordRing:          return "'ring'";
        case TokenKind::KeywordField:         return "'field'";
        case TokenKind::KeywordConvention:    return "'convention'";
        case TokenKind::KeywordGiven:         return "'given'";
        case TokenKind::KeywordAs:            return "'as'";
        case TokenKind::KeywordRefining:      return "'refining'";
        case TokenKind::LeftParen:            return "'('";
        case TokenKind::RightParen:           return "')'";
        case TokenKind::LeftBrace:            return "'{'";
        case TokenKind::RightBrace:           return "'}'";
        case TokenKind::LeftAngle:            return "'⟨'";
        case TokenKind::RightAngle:           return "'⟩'";
        case TokenKind::Comma:                return "','";
        case TokenKind::Colon:                return "':'";
        case TokenKind::Semicolon:            return "';'";
        case TokenKind::Question:             return "'?'";
        case TokenKind::Pipe:                 return "'|'";
        case TokenKind::Dot:                  return "'.'";
        case TokenKind::DotLeftBrace:         return "'.{'";
        case TokenKind::Assign:               return "':='";
        case TokenKind::FatArrow:             return "'=>'";
        case TokenKind::Plus:                 return "'+'";
        case TokenKind::Minus:                return "'-'";
        case TokenKind::Star:                 return "'*'";
        case TokenKind::Slash:                return "'/'";
        case TokenKind::Caret:                return "'^'";
        case TokenKind::CenterDot:            return "'·'";
        case TokenKind::Less:                 return "'<'";
        case TokenKind::Greater:              return "'>'";
        case TokenKind::LessOrEqual:          return "'<=' or '≤'";
        case TokenKind::GreaterOrEqual:       return "'>=' or '≥'";
        case TokenKind::Equal:                return "'='";
        case TokenKind::NotEqual:             return "'!=' or '≠'";
        case TokenKind::LogicalAnd:           return "'/\\' or '∧'";
        case TokenKind::LogicalOr:            return "'\\/' or '∨'";
        case TokenKind::LogicalNot:           return "'¬'";
        case TokenKind::Divides:              return "'∣'";
        case TokenKind::NotDivides:           return "'∤'";
        case TokenKind::NotLessOrEqual:       return "'≰'";
        case TokenKind::ElementOf:            return "'∈'";
        case TokenKind::SubsetOf:             return "'⊆'";
        case TokenKind::ForAll:               return "'∀'";
        case TokenKind::Exists:               return "'∃'";
        case TokenKind::Arrow:                return "'->' or '→'";
        case TokenKind::EndOfFile:            return "end of file";
    }
    return "(unknown token kind)";
}
