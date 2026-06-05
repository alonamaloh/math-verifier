#pragma once

#include "syntax/lexer.hpp"
#include "syntax/surface.hpp"

#include <stdexcept>
#include <vector>

struct ParseError : std::runtime_error {
    using std::runtime_error::runtime_error;
};

// Parses an expression from the token stream. Useful for testing the
// expression sub-grammar; the production driver uses parseModule.
SurfaceExpressionPointer parseExpression(const std::vector<Token>& tokens);

// Parses a whole .math file: the module declaration followed by
// imports, usings, and top-level declarations (inductive / axiom /
// definition / theorem). Throws ParseError on malformed input.
SurfaceModule parseModule(const std::vector<Token>& tokens);
