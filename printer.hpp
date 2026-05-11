#pragma once

#include "expression.hpp"

#include <string>

// Renders an Expression to a readable string. BoundVariables are resolved
// by walking outward through enclosing binders to recover their displayHint;
// any hint that would collide with one already in scope is freshened first.
// The output uses Π (capital pi) for dependent function types and λ (lambda)
// for function values.
std::string prettyPrint(ExpressionPointer expression);
