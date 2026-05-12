#pragma once

#include <stdexcept>
#include <string>
#include <vector>

// Token categories for the .math surface language. Keywords get their own
// kinds so the parser can dispatch on TokenKind without re-comparing
// strings. Operator tokens cover both their Unicode and ASCII spellings.
enum class TokenKind {
    // Atoms and literals
    Identifier,
    NumericLiteral,

    // Top-level / declaration keywords
    KeywordModule, KeywordImport, KeywordUsing,
    KeywordInductive, KeywordDefinition, KeywordAxiom, KeywordTheorem,
    KeywordWhere,

    // Expression keywords
    KeywordFun, KeywordLet, KeywordIn,
    KeywordType, KeywordProp,
    KeywordMax, KeywordImax,

    // Proof keywords
    KeywordProof, KeywordQed,
    KeywordHave, KeywordShow, KeywordCalc, KeywordBy,
    KeywordInduction, KeywordOn,
    KeywordCase, KeywordOf, KeywordWith, KeywordHypothesis,
    KeywordApply, KeywordReduction,
    KeywordMotive, KeywordTarget,

    // Punctuation
    LeftParen, RightParen,
    LeftBrace, RightBrace,
    Comma, Colon, Pipe,
    Dot,
    DotLeftBrace,    // ".{"  introduces universe-argument list
    Assign,          // ":="
    FatArrow,        // "=>"

    // Operators
    Plus, Minus, Star, Slash, Caret,
    Less, Greater, LessOrEqual, GreaterOrEqual,
    Equal, NotEqual,
    LogicalAnd, LogicalOr, LogicalNot,
    Arrow,           // "→" or "->"

    EndOfFile,
};

// Returns true if `kind` names a keyword (any KeywordX variant). Useful
// for the parser when it needs to test "this is some keyword" generically.
bool isKeyword(TokenKind kind);

// Returns a human-readable name for a token kind (for error messages and
// debugging). Stable across compiles; not a localised user-facing string.
const char* tokenKindName(TokenKind kind);

struct Token {
    TokenKind kind;
    std::string lexeme;
    int line;
    int column;
};

struct LexError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

// Tokenises `source` into a sequence of Tokens, terminated by an
// EndOfFile token whose lexeme is empty. Throws LexError on unexpected
// characters or unterminated block comments.
std::vector<Token> lex(const std::string& source);
