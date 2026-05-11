#include "kernel.hpp"

#include <algorithm>
#include <string>

namespace {

// Kernel-private builder for Internal-origin free variables. Lives here
// (not in expression.hpp) so clients of the kernel cannot construct them
// through the public API.
ExpressionPointer makeInternalFreeVariable(std::string name) {
    return std::make_shared<Expression>(
        FreeVariable{std::move(name), FreeVariableOrigin::Internal});
}

// Lean's imax rule on level expressions: makeLevelIMax already encodes the
// Prop-collapsing behaviour for concrete codomains and falls back to a
// symbolic LevelIMax otherwise.
LevelPointer impredicativeMaxLevel(LevelPointer domainLevel,
                                   LevelPointer codomainLevel) {
    return makeLevelIMax(std::move(domainLevel), std::move(codomainLevel));
}

// Walks `expression`, replacing each universe parameter that appears in any
// Sort or in a Constant's universe arguments with the supplied substitution.
// Used by inferType when a polymorphic constant is referenced with explicit
// level arguments — every internal Sort and Constant in the declared type
// needs its level parameters instantiated.
ExpressionPointer substituteUniverseLevels(
    ExpressionPointer expression,
    const std::vector<std::string>& parameterNames,
    const std::vector<LevelPointer>& replacements) {
    if (parameterNames.size() != replacements.size()) {
        throw TypeError(
            "internal: substituteUniverseLevels called with mismatched "
            "parameter/replacement counts (" +
            std::to_string(parameterNames.size()) + " vs " +
            std::to_string(replacements.size()) + ")");
    }
    auto substituteOneLevel = [&](LevelPointer level) {
        for (std::size_t i = 0; i < parameterNames.size(); ++i) {
            level = substituteLevelParameter(level, parameterNames[i],
                                             replacements[i]);
        }
        return level;
    };

    if (auto* sort = std::get_if<Sort>(&expression->node)) {
        return makeSort(substituteOneLevel(sort->level));
    }
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        std::vector<LevelPointer> newArguments;
        newArguments.reserve(constant->universeArguments.size());
        for (auto& argument : constant->universeArguments) {
            newArguments.push_back(substituteOneLevel(argument));
        }
        return makeConstant(constant->name, std::move(newArguments));
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      substituteUniverseLevels(pi->domain,   parameterNames, replacements),
                      substituteUniverseLevels(pi->codomain, parameterNames, replacements));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          substituteUniverseLevels(lambda->domain, parameterNames, replacements),
                          substituteUniverseLevels(lambda->body,   parameterNames, replacements));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            substituteUniverseLevels(application->function, parameterNames, replacements),
            substituteUniverseLevels(application->argument, parameterNames, replacements));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       substituteUniverseLevels(let->type,  parameterNames, replacements),
                       substituteUniverseLevels(let->value, parameterNames, replacements),
                       substituteUniverseLevels(let->body,  parameterNames, replacements));
    }
    // BoundVariable, FreeVariable: no levels inside, return as-is.
    return expression;
}

// Helper accessor: every Declaration variant carries a list of universe
// parameter names. Returns it.
const std::vector<std::string>& declarationUniverseParameters(
    const Declaration& declaration) {
    if (auto* axiom       = std::get_if<Axiom>(&declaration))       return axiom->universeParameters;
    if (auto* definition  = std::get_if<Definition>(&declaration))  return definition->universeParameters;
    if (auto* inductive   = std::get_if<Inductive>(&declaration))   return inductive->universeParameters;
    if (auto* constructor = std::get_if<Constructor>(&declaration)) return constructor->universeParameters;
    if (auto* recursor    = std::get_if<Recursor>(&declaration))    return recursor->universeParameters;
    static const std::vector<std::string> empty;
    return empty;
}

// Returns the declared type of any Declaration. (For Inductive this is the
// `kind` field; for everything else it's `type`.)
ExpressionPointer declarationType(const Declaration& declaration) {
    if (auto* axiom       = std::get_if<Axiom>(&declaration))       return axiom->type;
    if (auto* definition  = std::get_if<Definition>(&declaration))  return definition->type;
    if (auto* inductive   = std::get_if<Inductive>(&declaration))   return inductive->kind;
    if (auto* constructor = std::get_if<Constructor>(&declaration)) return constructor->type;
    if (auto* recursor    = std::get_if<Recursor>(&declaration))    return recursor->type;
    throw TypeError("internal: unhandled Declaration variant");
}

} // namespace

ExpressionPointer shift(ExpressionPointer expression, int amount, int cutoff) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        if (boundVariable->deBruijnIndex >= cutoff) {
            return makeBoundVariable(boundVariable->deBruijnIndex + amount);
        }
        return expression;
    }
    if (std::holds_alternative<FreeVariable>(expression->node)) return expression;
    if (std::holds_alternative<Sort>(expression->node))         return expression;
    if (std::holds_alternative<Constant>(expression->node))     return expression;
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      shift(pi->domain,   amount, cutoff),
                      shift(pi->codomain, amount, cutoff + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          shift(lambda->domain, amount, cutoff),
                          shift(lambda->body,   amount, cutoff + 1));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(shift(application->function, amount, cutoff),
                               shift(application->argument, amount, cutoff));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       shift(let->type,  amount, cutoff),
                       shift(let->value, amount, cutoff),
                       shift(let->body,  amount, cutoff + 1));
    }
    throw TypeError("internal: unhandled Expression variant in shift");
}

ExpressionPointer substitute(ExpressionPointer expression,
                         int targetIndex,
                         ExpressionPointer replacement) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        if (boundVariable->deBruijnIndex == targetIndex) return replacement;
        if (boundVariable->deBruijnIndex >  targetIndex) {
            return makeBoundVariable(boundVariable->deBruijnIndex - 1);
        }
        return expression;
    }
    if (std::holds_alternative<FreeVariable>(expression->node)) return expression;
    if (std::holds_alternative<Sort>(expression->node))         return expression;
    if (std::holds_alternative<Constant>(expression->node))     return expression;
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      substitute(pi->domain,   targetIndex,     replacement),
                      substitute(pi->codomain, targetIndex + 1, shift(replacement, 1)));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          substitute(lambda->domain, targetIndex,     replacement),
                          substitute(lambda->body,   targetIndex + 1, shift(replacement, 1)));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            substitute(application->function, targetIndex, replacement),
            substitute(application->argument, targetIndex, replacement));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       substitute(let->type,  targetIndex,     replacement),
                       substitute(let->value, targetIndex,     replacement),
                       substitute(let->body,  targetIndex + 1, shift(replacement, 1)));
    }
    throw TypeError("internal: unhandled Expression variant in substitute");
}

ExpressionPointer openBinder(ExpressionPointer expression,
                             const std::string& freshName,
                             FreeVariableOrigin origin) {
    auto freeVar = std::make_shared<Expression>(
        FreeVariable{freshName, origin});
    return substitute(std::move(expression), 0, std::move(freeVar));
}

namespace {

// Recursive helper for closeBinder. Walks `expression` while tracking the
// current binder depth (how many enclosing binders we've descended past
// since the close started).
ExpressionPointer closeAtDepth(ExpressionPointer expression,
                           const std::string& name,
                           FreeVariableOrigin origin,
                           int depth) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        // Any bound index referring to something outside `expression`
        // (i.e. an enclosing binder) must shift up by one because we are
        // adding a new binder at the outside. Indices below `depth` refer
        // to binders inside `expression` and are unchanged.
        if (boundVariable->deBruijnIndex >= depth) {
            return makeBoundVariable(boundVariable->deBruijnIndex + 1);
        }
        return expression;
    }
    if (auto* freeVariable = std::get_if<FreeVariable>(&expression->node)) {
        if (freeVariable->name == name && freeVariable->origin == origin) {
            return makeBoundVariable(depth);
        }
        return expression;
    }
    if (std::holds_alternative<Sort>(expression->node))     return expression;
    if (std::holds_alternative<Constant>(expression->node)) return expression;
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      closeAtDepth(pi->domain,   name, origin, depth),
                      closeAtDepth(pi->codomain, name, origin, depth + 1));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          closeAtDepth(lambda->domain, name, origin, depth),
                          closeAtDepth(lambda->body,   name, origin, depth + 1));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            closeAtDepth(application->function, name, origin, depth),
            closeAtDepth(application->argument, name, origin, depth));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       closeAtDepth(let->type,  name, origin, depth),
                       closeAtDepth(let->value, name, origin, depth),
                       closeAtDepth(let->body,  name, origin, depth + 1));
    }
    throw TypeError("internal: unhandled Expression variant in closeBinder");
}

} // namespace

ExpressionPointer closeBinder(ExpressionPointer expression,
                              const std::string& name,
                              FreeVariableOrigin origin) {
    return closeAtDepth(std::move(expression), name, origin, 0);
}

namespace {

// Peels an Application spine. Given `f a_1 a_2 ... a_n`, returns
// (f, [a_1, ..., a_n]) where the args are in application order.
struct AppSpine {
    ExpressionPointer head;
    std::vector<ExpressionPointer> args;
};
AppSpine peelApplicationSpine(ExpressionPointer expression) {
    AppSpine spine;
    spine.head = std::move(expression);
    while (auto* application = std::get_if<Application>(&spine.head->node)) {
        spine.args.push_back(application->argument);
        spine.head = application->function;
    }
    std::reverse(spine.args.begin(), spine.args.end());
    return spine;
}

// Re-applies a head to a sequence of arguments. The inverse of peelApplicationSpine.
ExpressionPointer applyArguments(ExpressionPointer head,
                                 const std::vector<ExpressionPointer>& args,
                                 std::size_t fromIndex = 0) {
    for (std::size_t i = fromIndex; i < args.size(); ++i) {
        head = makeApplication(head, args[i]);
    }
    return head;
}

// Builds the ι-reduction result for `recursor motive case_1 ... case_k target`
// where target is `constructor v_1 ... v_n` for the given Constructor.
// For each constructor arg v_j whose declared type is the inductive itself
// (recursive arg), we apply the case to v_j AND to a recursive call of the
// recursor on v_j.
ExpressionPointer buildIotaReduction(const std::string& recursorName,
                                     const std::vector<LevelPointer>& recursorUniverseArguments,
                                     const Recursor& recursor,
                                     const Constructor& constructor,
                                     const std::vector<ExpressionPointer>& recursorArgs,
                                     const std::vector<ExpressionPointer>& constructorArgs) {
    // The case for this constructor sits at index (1 + constructorIndex) in
    // recursorArgs (after motive at index 0). The target sits at the next
    // position (1 + numConstructors). Any args beyond that are extras the
    // caller will re-apply.
    auto result = recursorArgs[1 + constructor.constructorIndex];

    // Walk the constructor's declared type to know which args are recursive.
    auto walker = constructor.type;
    int argIndex = 0;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        auto argValue = constructorArgs[argIndex];
        result = makeApplication(result, argValue);

        bool isRecursive = false;
        if (auto* c = std::get_if<Constant>(&pi->domain->node)) {
            if (c->name == recursor.inductiveName) isRecursive = true;
        }
        if (isRecursive) {
            // Build the recursive call, preserving universe arguments on the
            // recursor head:  recursor.{us} motive case_1 ... case_k argValue.
            auto recursiveCall = makeConstant(recursorName, recursorUniverseArguments);
            // recursorArgs[0..numConstructors] are motive + cases.
            for (int i = 0; i <= recursor.numConstructors; ++i) {
                recursiveCall = makeApplication(recursiveCall, recursorArgs[i]);
            }
            recursiveCall = makeApplication(recursiveCall, argValue);
            result = makeApplication(result, recursiveCall);
        }
        // The codomain may reference earlier args via BoundVariable(0);
        // substitute to keep indices coherent.
        walker = substitute(pi->codomain, 0, argValue);
        argIndex++;
    }
    return result;
}

} // namespace

ExpressionPointer weakHeadNormalForm(const Environment& environment,
                                     ExpressionPointer expression,
                                     int fuel) {
    while (true) {
        if (--fuel <= 0) {
            throw TypeError(
                "weakHeadNormalForm: reduction did not terminate within "
                "fuel limit; expression may be ill-typed");
        }
        // δ-reduction on a bare Constant referring to a Definition. If the
        // definition is universe-polymorphic, instantiate its body with the
        // supplied universe arguments before unfolding. Refuses to reduce
        // (and throws) if the Constant's universe arity disagrees with the
        // Definition's — this can only happen on malformed input, since
        // inferType would have caught it; the check is defensive.
        if (auto* constant = std::get_if<Constant>(&expression->node)) {
            if (auto* declaration = environment.lookup(constant->name)) {
                if (auto* definition = std::get_if<Definition>(declaration)) {
                    if (definition->universeParameters.size()
                            != constant->universeArguments.size()) {
                        throw TypeError(
                            "weakHeadNormalForm: constant " + constant->name +
                            " referenced with " +
                            std::to_string(constant->universeArguments.size()) +
                            " universe argument(s); definition declares " +
                            std::to_string(definition->universeParameters.size()));
                    }
                    auto body = definition->body;
                    if (!definition->universeParameters.empty()) {
                        body = substituteUniverseLevels(
                            body,
                            definition->universeParameters,
                            constant->universeArguments);
                    }
                    expression = body;
                    continue;
                }
            }
            return expression;
        }
        // ζ-reduction on a Let.
        if (auto* let = std::get_if<Let>(&expression->node)) {
            expression = substitute(let->body, 0, let->value);
            continue;
        }
        // Application: peel the spine, reduce the head, then try β or ι.
        if (std::holds_alternative<Application>(expression->node)) {
            auto spine = peelApplicationSpine(expression);
            spine.head = weakHeadNormalForm(environment, spine.head, fuel);

            // β-reduction: if the head is a Lambda and we have at least one arg.
            if (auto* lambda = std::get_if<Lambda>(&spine.head->node);
                lambda && !spine.args.empty()) {
                expression = substitute(lambda->body, 0, spine.args[0]);
                expression = applyArguments(expression, spine.args, 1);
                continue;
            }

            // ι-reduction: if the head is a Constant referring to a Recursor
            // and we have enough args, with the target being a constructor
            // application of the right inductive type.
            if (auto* headConstant = std::get_if<Constant>(&spine.head->node)) {
                auto* declaration = environment.lookup(headConstant->name);
                if (auto* recursor = (declaration ? std::get_if<Recursor>(declaration)
                                                  : nullptr)) {
                    int needed = 1 + recursor->numConstructors + 1;
                    if ((int)spine.args.size() >= needed) {
                        // Reduce the target to whnf and inspect.
                        auto reducedTarget =
                            weakHeadNormalForm(environment, spine.args[needed - 1], fuel);
                        auto targetSpine = peelApplicationSpine(reducedTarget);
                        if (auto* ctorConstant =
                                std::get_if<Constant>(&targetSpine.head->node)) {
                            auto* targetDecl =
                                environment.lookup(ctorConstant->name);
                            if (auto* constructor =
                                    (targetDecl ? std::get_if<Constructor>(targetDecl)
                                                : nullptr);
                                constructor &&
                                constructor->inductiveName == recursor->inductiveName) {
                                // Defensive universe-argument compatibility
                                // check: the constructor's universe args
                                // must match the prefix of the recursor's.
                                // (Currently the two sets are the same size;
                                // when universe-polymorphic motives land,
                                // the recursor will have one extra trailing
                                // universe arg for the motive level.) On
                                // mismatch, refuse to ι-reduce; the
                                // expression is stuck.
                                const auto& recursorArgs =
                                    headConstant->universeArguments;
                                const auto& constructorArgs =
                                    ctorConstant->universeArguments;
                                bool prefixMatches =
                                    constructorArgs.size() <= recursorArgs.size();
                                for (std::size_t i = 0;
                                     prefixMatches && i < constructorArgs.size();
                                     ++i) {
                                    if (!levelsDefinitionallyEqual(
                                            recursorArgs[i],
                                            constructorArgs[i])) {
                                        prefixMatches = false;
                                    }
                                }
                                if (!prefixMatches) {
                                    return applyArguments(spine.head, spine.args);
                                }
                                // ι-reduce.
                                auto reduced = buildIotaReduction(
                                    headConstant->name,
                                    headConstant->universeArguments,
                                    *recursor, *constructor,
                                    spine.args, targetSpine.args);
                                // Re-apply any extra arguments past `needed`.
                                expression = applyArguments(reduced, spine.args, needed);
                                continue;
                            }
                        }
                    }
                }
            }

            // No reduction possible. Rebuild and return.
            return applyArguments(spine.head, spine.args);
        }
        return expression;
    }
}

namespace {

// Generates a name for an Internal-origin free variable, used by
// isDefinitionallyEqual / isSubtype to open a Pi or Lambda binder for
// recursion. Uniqueness within the call tree comes from the context size,
// which strictly increases with each opening. The name itself is plain
// text — collision with user-supplied names is impossible because user
// names live in the User origin and these in the Internal origin.
std::string makeOpeningName(const Context& context) {
    return "v" + std::to_string(context.size());
}

} // namespace

bool isDefinitionallyEqual(const Environment& environment,
                           const Context& context,
                           ExpressionPointer left,
                           ExpressionPointer right,
                           int fuel) {
    if (--fuel <= 0) {
        // Conservative on exhaustion: don't claim equality we can't prove.
        return false;
    }
    auto leftReduced  = weakHeadNormalForm(environment, std::move(left),  fuel);
    auto rightReduced = weakHeadNormalForm(environment, std::move(right), fuel);

    // Structural cases. When recursing into a Pi or Lambda body/codomain,
    // we *open* the binder with a fresh free variable and extend the
    // context with that variable's type, so the comparison context tracks
    // every variable in scope. This is what makes proof irrelevance below
    // able to call inferType on subterms.
    if (auto* leftBound = std::get_if<BoundVariable>(&leftReduced->node)) {
        auto* rightBound = std::get_if<BoundVariable>(&rightReduced->node);
        if (rightBound &&
            leftBound->deBruijnIndex == rightBound->deBruijnIndex) {
            return true;
        }
    } else if (auto* leftFree = std::get_if<FreeVariable>(&leftReduced->node)) {
        auto* rightFree = std::get_if<FreeVariable>(&rightReduced->node);
        if (rightFree && leftFree->name == rightFree->name
                      && leftFree->origin == rightFree->origin) {
            return true;
        }
    } else if (auto* leftSort = std::get_if<Sort>(&leftReduced->node)) {
        auto* rightSort = std::get_if<Sort>(&rightReduced->node);
        if (rightSort && levelsDefinitionallyEqual(leftSort->level,
                                                   rightSort->level)) {
            return true;
        }
    } else if (auto* leftConstant = std::get_if<Constant>(&leftReduced->node)) {
        // After weakHeadNormalForm, a Constant at the head can only be an
        // Axiom / Inductive / Constructor / Recursor (Definitions were
        // unfolded). Two such constants are equal iff they have the same
        // name AND the same universe arguments — distinct universe
        // instantiations of a polymorphic constant are NOT interchangeable.
        if (auto* rightConstant = std::get_if<Constant>(&rightReduced->node);
            rightConstant && leftConstant->name == rightConstant->name &&
            leftConstant->universeArguments.size()
                == rightConstant->universeArguments.size()) {
            bool allLevelsAgree = true;
            for (std::size_t i = 0;
                 i < leftConstant->universeArguments.size(); ++i) {
                if (!levelsDefinitionallyEqual(
                        leftConstant->universeArguments[i],
                        rightConstant->universeArguments[i])) {
                    allLevelsAgree = false;
                    break;
                }
            }
            if (allLevelsAgree) return true;
        }
    } else if (auto* leftPi = std::get_if<Pi>(&leftReduced->node)) {
        if (auto* rightPi = std::get_if<Pi>(&rightReduced->node)) {
            if (!isDefinitionallyEqual(environment, context,
                                       leftPi->domain, rightPi->domain, fuel)) {
                return false;
            }
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, leftPi->domain, FreeVariableOrigin::Internal});
            return isDefinitionallyEqual(
                environment, extendedContext,
                openBinder(leftPi->codomain,  fresh, FreeVariableOrigin::Internal),
                openBinder(rightPi->codomain, fresh, FreeVariableOrigin::Internal),
                fuel);
        }
    } else if (auto* leftLambda = std::get_if<Lambda>(&leftReduced->node)) {
        if (auto* rightLambda = std::get_if<Lambda>(&rightReduced->node)) {
            if (!isDefinitionallyEqual(environment, context,
                                       leftLambda->domain,
                                       rightLambda->domain, fuel)) {
                return false;
            }
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, leftLambda->domain, FreeVariableOrigin::Internal});
            return isDefinitionallyEqual(
                environment, extendedContext,
                openBinder(leftLambda->body,  fresh, FreeVariableOrigin::Internal),
                openBinder(rightLambda->body, fresh, FreeVariableOrigin::Internal),
                fuel);
        }
    } else if (auto* leftApplication = std::get_if<Application>(&leftReduced->node)) {
        if (auto* rightApplication = std::get_if<Application>(&rightReduced->node)) {
            if (isDefinitionallyEqual(environment, context,
                                      leftApplication->function,
                                      rightApplication->function, fuel)
             && isDefinitionallyEqual(environment, context,
                                      leftApplication->argument,
                                      rightApplication->argument, fuel)) {
                return true;
            }
            // Otherwise fall through — proof irrelevance might still apply.
        }
    }

    // η-conversion: λx. f x  ≡  f  (when x is not free in f). If exactly
    // one side is a Lambda, η-expand the other and compare.
    {
        auto* leftLambda  = std::get_if<Lambda>(&leftReduced->node);
        auto* rightLambda = std::get_if<Lambda>(&rightReduced->node);
        if (leftLambda && !rightLambda) {
            auto etaExpandedRight = makeApplication(
                shift(rightReduced, 1), makeBoundVariable(0));
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, leftLambda->domain, FreeVariableOrigin::Internal});
            if (isDefinitionallyEqual(
                    environment, extendedContext,
                    openBinder(leftLambda->body, fresh, FreeVariableOrigin::Internal),
                    openBinder(etaExpandedRight, fresh, FreeVariableOrigin::Internal),
                    fuel)) {
                return true;
            }
        }
        if (rightLambda && !leftLambda) {
            auto etaExpandedLeft = makeApplication(
                shift(leftReduced, 1), makeBoundVariable(0));
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, rightLambda->domain, FreeVariableOrigin::Internal});
            if (isDefinitionallyEqual(
                    environment, extendedContext,
                    openBinder(etaExpandedLeft, fresh, FreeVariableOrigin::Internal),
                    openBinder(rightLambda->body, fresh, FreeVariableOrigin::Internal),
                    fuel)) {
                return true;
            }
        }
    }

    // Proof irrelevance: any two terms whose type lives in Prop are
    // definitionally equal. We infer the types and check whether their
    // kind (the type of the type) is Sort 0 (= Prop).
    try {
        auto leftType = inferType(environment, context, leftReduced);
        auto leftKind = weakHeadNormalForm(
            environment, inferType(environment, context, leftType), fuel);
        if (auto* sort = std::get_if<Sort>(&leftKind->node)) {
            auto concreteLevel = levelAsConstant(sort->level);
            if (concreteLevel && *concreteLevel == 0) {
                // leftReduced is a proof of leftType, a proposition.
                auto rightType = inferType(environment, context, rightReduced);
                if (isDefinitionallyEqual(environment, context,
                                          leftType, rightType, fuel)) {
                    return true;
                }
            }
        }
    } catch (const TypeError&) {
        // One side isn't well-typed in this context — skip irrelevance.
    }

    return false;
}

bool isSubtype(const Environment& environment,
               const Context& context,
               ExpressionPointer subType,
               ExpressionPointer superType,
               int fuel) {
    if (--fuel <= 0) {
        return false;
    }
    auto subReduced   = weakHeadNormalForm(environment, std::move(subType),   fuel);
    auto superReduced = weakHeadNormalForm(environment, std::move(superType), fuel);

    // Sort cumulativity: Sort m <: Sort n iff m <= n.
    if (auto* subSort = std::get_if<Sort>(&subReduced->node)) {
        if (auto* superSort = std::get_if<Sort>(&superReduced->node)) {
            return levelLessOrEqual(subSort->level, superSort->level);
        }
    }

    // Pi: equal domains, subtype codomains (under the binder).
    if (auto* subPi = std::get_if<Pi>(&subReduced->node)) {
        if (auto* superPi = std::get_if<Pi>(&superReduced->node)) {
            if (!isDefinitionallyEqual(environment, context,
                                       subPi->domain, superPi->domain, fuel)) {
                return false;
            }
            auto fresh = makeOpeningName(context);
            Context extendedContext = context;
            extendedContext.push_back(
                {fresh, subPi->domain, FreeVariableOrigin::Internal});
            return isSubtype(environment, extendedContext,
                             openBinder(subPi->codomain,   fresh, FreeVariableOrigin::Internal),
                             openBinder(superPi->codomain, fresh, FreeVariableOrigin::Internal),
                             fuel);
        }
    }

    // Everything else: definitional equality is sufficient.
    return isDefinitionallyEqual(environment, context, subReduced, superReduced, fuel);
}

std::string freshName(const std::string& displayHint, const Context& context) {
    auto isInUse = [&](const std::string& candidate) {
        for (const auto& entry : context) {
            if (entry.name == candidate) return true;
        }
        return false;
    };
    std::string base = displayHint.empty() ? "x" : displayHint;
    if (!isInUse(base)) return base;
    for (int suffix = 1;; ++suffix) {
        auto candidate = base + "_" + std::to_string(suffix);
        if (!isInUse(candidate)) return candidate;
    }
}

ExpressionPointer inferType(const Environment& environment,
                        const Context& context,
                        ExpressionPointer expression) {
    if (auto* boundVariable = std::get_if<BoundVariable>(&expression->node)) {
        throw TypeError(
            "internal: bare BoundVariable reached inferType (index " +
            std::to_string(boundVariable->deBruijnIndex) +
            "); binders should be opened before recursing");
    }
    if (auto* freeVariable = std::get_if<FreeVariable>(&expression->node)) {
        for (auto entry = context.rbegin(); entry != context.rend(); ++entry) {
            if (entry->name == freeVariable->name &&
                entry->origin == freeVariable->origin) {
                return entry->type;
            }
        }
        throw TypeError(
            std::string(freeVariable->origin == FreeVariableOrigin::User
                            ? "unbound free variable: "
                            : "unbound internal variable: ")
            + freeVariable->name);
    }
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        auto* declaration = environment.lookup(constant->name);
        if (!declaration) {
            throw TypeError("undefined constant: " + constant->name);
        }
        const auto& parameters = declarationUniverseParameters(*declaration);
        if (parameters.size() != constant->universeArguments.size()) {
            throw TypeError(
                "constant " + constant->name + ": expected " +
                std::to_string(parameters.size()) +
                " universe argument(s), got " +
                std::to_string(constant->universeArguments.size()));
        }
        auto type = declarationType(*declaration);
        if (!parameters.empty()) {
            type = substituteUniverseLevels(type, parameters,
                                            constant->universeArguments);
        }
        return type;
    }
    if (auto* sort = std::get_if<Sort>(&expression->node)) {
        return makeSort(makeLevelSucc(sort->level));
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        auto domainKind = weakHeadNormalForm(
            environment, inferType(environment, context, pi->domain));
        auto* domainSort = std::get_if<Sort>(&domainKind->node);
        if (!domainSort) {
            throw TypeError("Pi: domain is not a type");
        }
        auto introducedName = freshName(pi->displayHint, context);
        Context extendedContext = context;
        extendedContext.push_back({introducedName, pi->domain});
        auto codomainKind = weakHeadNormalForm(
            environment,
            inferType(environment, extendedContext,
                      openBinder(pi->codomain, introducedName)));
        auto* codomainSort = std::get_if<Sort>(&codomainKind->node);
        if (!codomainSort) {
            throw TypeError("Pi: codomain is not a type");
        }
        return makeSort(
            impredicativeMaxLevel(domainSort->level, codomainSort->level));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        auto domainKind = weakHeadNormalForm(
            environment, inferType(environment, context, lambda->domain));
        if (!std::holds_alternative<Sort>(domainKind->node)) {
            throw TypeError("Lambda: domain is not a type");
        }
        auto introducedName = freshName(lambda->displayHint, context);
        Context extendedContext = context;
        extendedContext.push_back({introducedName, lambda->domain});
        auto bodyType = inferType(environment, extendedContext,
                                  openBinder(lambda->body, introducedName));
        return makePi(lambda->displayHint,
                      lambda->domain,
                      closeBinder(bodyType, introducedName));
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        auto functionType = weakHeadNormalForm(
            environment,
            inferType(environment, context, application->function));
        auto* functionAsPi = std::get_if<Pi>(&functionType->node);
        if (!functionAsPi) {
            throw TypeError("Application: function is not of Pi type");
        }
        auto argumentType = inferType(environment, context, application->argument);
        if (!isSubtype(environment, context, argumentType, functionAsPi->domain)) {
            throw TypeError("Application: argument type does not match Pi domain");
        }
        return substitute(functionAsPi->codomain, 0, application->argument);
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        // Check the declared type is itself a type.
        auto kindOfType = weakHeadNormalForm(
            environment, inferType(environment, context, let->type));
        if (!std::holds_alternative<Sort>(kindOfType->node)) {
            throw TypeError("Let: declared type is not a type");
        }
        // Check the value's inferred type matches the declared type.
        auto inferredValueType = inferType(environment, context, let->value);
        if (!isSubtype(environment, context, inferredValueType, let->type)) {
            throw TypeError("Let: value type does not match declared type");
        }
        // Substitute the value into the body and infer that.
        return inferType(environment, context,
                         substitute(let->body, 0, let->value));
    }
    throw TypeError("internal: unhandled Expression variant in inferType");
}

void addAxiom(Environment& environment,
              std::string name,
              std::vector<std::string> universeParameters,
              ExpressionPointer declaredType) {
    if (environment.declarations.count(name)) {
        throw TypeError("addAxiom: name already declared: " + name);
    }
    auto kindOfType = weakHeadNormalForm(
        environment, inferType(environment, {}, declaredType));
    if (!std::holds_alternative<Sort>(kindOfType->node)) {
        throw TypeError("addAxiom: declared type is not a type for " + name);
    }
    environment.declarations.emplace(
        std::move(name),
        Axiom{std::move(universeParameters), std::move(declaredType)});
}

void addDefinition(Environment& environment,
                   std::string name,
                   std::vector<std::string> universeParameters,
                   ExpressionPointer declaredType,
                   ExpressionPointer body) {
    if (environment.declarations.count(name)) {
        throw TypeError("addDefinition: name already declared: " + name);
    }
    auto kindOfType = weakHeadNormalForm(
        environment, inferType(environment, {}, declaredType));
    if (!std::holds_alternative<Sort>(kindOfType->node)) {
        throw TypeError(
            "addDefinition: declared type is not a type for " + name);
    }
    auto inferredBodyType = inferType(environment, {}, body);
    if (!isSubtype(environment, {}, inferredBodyType, declaredType)) {
        throw TypeError(
            "addDefinition: body type does not match declared type for " + name);
    }
    environment.declarations.emplace(
        std::move(name),
        Definition{std::move(universeParameters),
                   std::move(declaredType), std::move(body)});
}

namespace {

// True if `expression` syntactically contains a Constant with the given
// name anywhere. Used by the strict-positivity check below — and only by
// it; it's a cheap structural walk, not a semantic test.
bool mentionsConstant(ExpressionPointer expression,
                      const std::string& constantName) {
    if (auto* c = std::get_if<Constant>(&expression->node)) {
        return c->name == constantName;
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return mentionsConstant(pi->domain,   constantName)
            || mentionsConstant(pi->codomain, constantName);
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return mentionsConstant(lambda->domain, constantName)
            || mentionsConstant(lambda->body,   constantName);
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return mentionsConstant(application->function, constantName)
            || mentionsConstant(application->argument, constantName);
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return mentionsConstant(let->type,  constantName)
            || mentionsConstant(let->value, constantName)
            || mentionsConstant(let->body,  constantName);
    }
    return false;  // BoundVariable, FreeVariable, Sort: no Constant inside.
}

// Strict positivity: the inductive type's name may appear in constructor
// argument types only in "strictly positive" positions. Concretely:
//   - it may appear nowhere (a non-recursive argument), OR
//   - it may be the entire type (a direct recursive argument), OR
//   - the type may be Π(_ : A). B where A doesn't mention it and B is
//     strictly positive in it (a higher-order recursive argument, like
//     mkInfTree : (Nat → Tree) → Tree).
// The rule rejects pathological declarations like
//   Bad : Type 0 := mkBad : (Bad → Bool) → Bad,
// which would otherwise let the user derive False.
bool isStrictlyPositive(ExpressionPointer expression,
                        const std::string& inductiveName) {
    // Case 1: doesn't mention the inductive at all.
    if (!mentionsConstant(expression, inductiveName)) return true;
    // Case 2: is exactly the inductive (a direct recursive argument).
    if (auto* c = std::get_if<Constant>(&expression->node)) {
        return c->name == inductiveName;
    }
    // Case 3: Π(_ : A). B with A not mentioning T and B strictly positive.
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return !mentionsConstant(pi->domain, inductiveName)
            && isStrictlyPositive(pi->codomain, inductiveName);
    }
    // All other shapes (Application, Lambda, Let, ...) that mention T:
    // not strictly positive.
    return false;
}

// Verifies that every argument of `constructor` is strictly positive in
// `inductiveName`. Walks the constructor's type as a Pi-chain. Returns the
// codomain-after-stripping (the conclusion of the constructor) so the
// caller can also check it ends in the inductive.
ExpressionPointer checkConstructorStrictlyPositive(
    const std::string& inductiveName,
    const ConstructorSpec& constructor) {
    auto walker = constructor.type;
    int argumentIndex = 0;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        if (!isStrictlyPositive(pi->domain, inductiveName)) {
            throw TypeError(
                "addInductive: constructor " + constructor.name +
                " argument " + std::to_string(argumentIndex) +
                " has non-strictly-positive occurrence of " + inductiveName);
        }
        // Walk into the codomain. The codomain may reference the bound
        // variable via BoundVariable(0); we don't need to track it for
        // the positivity check (we only inspect each Pi's domain), but
        // we must advance through the binder structure.
        walker = pi->codomain;
        argumentIndex++;
    }
    return walker;
}

// Builds the type of the case for a single constructor in the recursor's
// signature. The case binds each constructor argument; for arguments whose
// type is the inductive itself (direct recursive arguments), an extra
// hypothesis binder is inserted that gives access to the recursive result.
// The result of the case is `motive (constructor arg_1 ... arg_n)`.
//
// During construction, every binder is represented by an Internal-origin
// free variable. closeBinder converts those back to BoundVariables in the
// right order. The motive placeholder stays free in the result; the caller
// closes it after assembling the whole recursor type.
ExpressionPointer buildCaseType(const std::string& motivePlaceholder,
                                const std::string& inductiveName,
                                const ConstructorSpec& constructor) {
    struct ArgumentInfo {
        std::string freeName;
        std::string displayHint;
        ExpressionPointer domain;
        bool isRecursive;
    };
    std::vector<ArgumentInfo> arguments;
    auto walker = constructor.type;
    int argumentIndex = 0;
    while (auto* pi = std::get_if<Pi>(&walker->node)) {
        std::string freeName = "arg_" + std::to_string(argumentIndex);
        bool recursive = false;
        if (auto* c = std::get_if<Constant>(&pi->domain->node)) {
            if (c->name == inductiveName) recursive = true;
        }
        arguments.push_back({freeName, pi->displayHint, pi->domain, recursive});
        walker = substitute(pi->codomain, 0,
                            makeInternalFreeVariable(freeName));
        argumentIndex++;
    }

    // Innermost result: motive (constructor arg_1 ... arg_n).
    auto constructorApplied = makeConstant(constructor.name);
    for (const auto& argument : arguments) {
        constructorApplied = makeApplication(
            constructorApplied, makeInternalFreeVariable(argument.freeName));
    }
    auto result = makeApplication(
        makeInternalFreeVariable(motivePlaceholder), constructorApplied);

    // Wrap from innermost to outermost. For each argument in reverse order:
    //   - if the argument is recursive, first wrap with the hypothesis Pi
    //     (whose type is `motive arg_j`),
    //   - then wrap with the argument Pi itself, closing the free name.
    for (int j = (int)arguments.size() - 1; j >= 0; --j) {
        const auto& argument = arguments[j];
        if (argument.isRecursive) {
            auto hypothesisType = makeApplication(
                makeInternalFreeVariable(motivePlaceholder),
                makeInternalFreeVariable(argument.freeName));
            // Hypothesis binder is not referenced by name in the rest of the
            // case type, so no closeBinder is needed for its name.
            result = makePi("hypothesis_" + argument.displayHint,
                            hypothesisType, result);
        }
        result = closeBinder(result, argument.freeName,
                             FreeVariableOrigin::Internal);
        result = makePi(argument.displayHint, argument.domain, result);
    }
    return result;
}

// Builds the full type of the recursor for an inductive declaration. The
// motive's codomain is `Sort motiveLevelName` — a level parameter, so the
// generated recursor is universe-polymorphic in the motive. Callers supply
// the level at the use site (e.g. recursor.{u_inductive..., motiveLevel}).
ExpressionPointer buildRecursorType(
    const std::string& inductiveName,
    const std::string& motiveLevelName,
    const std::vector<ConstructorSpec>& constructors) {
    // Internal-origin placeholders for the motive and target. They are
    // closed by closeBinder below before the recursor type is returned;
    // because they live in the Internal origin they cannot collide with
    // anything the user can construct.
    const std::string motivePlaceholder = "motive";
    const std::string targetPlaceholder = "target";

    auto motiveType =
        makePi("_", makeConstant(inductiveName),
               makeSort(makeLevelParam(motiveLevelName)));

    std::vector<ExpressionPointer> caseTypes;
    caseTypes.reserve(constructors.size());
    for (const auto& constructor : constructors) {
        caseTypes.push_back(
            buildCaseType(motivePlaceholder, inductiveName, constructor));
    }

    // Innermost return type: motive target.
    auto core = makeApplication(makeInternalFreeVariable(motivePlaceholder),
                                makeInternalFreeVariable(targetPlaceholder));
    auto recursorType = closeBinder(core, targetPlaceholder,
                                    FreeVariableOrigin::Internal);
    recursorType = makePi("target", makeConstant(inductiveName), recursorType);

    // Wrap each case binder (innermost to outermost). The cases are unused
    // in the rest of the type's body, so no name-closing is needed; we just
    // wrap.
    for (int i = (int)constructors.size() - 1; i >= 0; --i) {
        recursorType = makePi("case_" + constructors[i].name,
                              caseTypes[i], recursorType);
    }

    // Wrap with the motive binder, closing the free motive placeholder
    // throughout.
    recursorType = closeBinder(recursorType, motivePlaceholder,
                               FreeVariableOrigin::Internal);
    recursorType = makePi("motive", motiveType, recursorType);
    return recursorType;
}

} // namespace

void addInductive(Environment& environment, std::string inductiveName,
                  std::vector<std::string> universeParameters,
                  ExpressionPointer kind,
                  std::vector<ConstructorSpec> constructors) {
    if (environment.declarations.count(inductiveName)) {
        throw TypeError("addInductive: name already declared: " + inductiveName);
    }
    // The kind must itself be a well-formed type, and for v1 it must be a
    // Sort (no parameters or indices).
    auto kindOfKind = weakHeadNormalForm(
        environment, inferType(environment, {}, kind));
    if (!std::holds_alternative<Sort>(kindOfKind->node)) {
        throw TypeError("addInductive: kind is not a type: " + inductiveName);
    }
    if (!std::holds_alternative<Sort>(kind->node)) {
        throw TypeError(
            "addInductive: kind must be a Sort (parameters and indices "
            "are not yet supported): " + inductiveName);
    }

    // Pre-register the inductive so that constructor types can reference it.
    std::vector<std::string> constructorNames;
    constructorNames.reserve(constructors.size());
    for (const auto& constructor : constructors) {
        constructorNames.push_back(constructor.name);
    }
    environment.declarations.emplace(
        inductiveName,
        Inductive{universeParameters, kind, constructorNames});

    // A small lambda that rolls back partial registration on error.
    auto rollback = [&]() {
        environment.declarations.erase(inductiveName);
        for (const auto& constructor : constructors) {
            environment.declarations.erase(constructor.name);
        }
        environment.declarations.erase(inductiveName + "_recursor");
    };

    // Type-check and register each constructor. Each constructor type
    // must (a) itself be a well-formed type, (b) have only strictly-
    // positive occurrences of the inductive being declared, and (c) end
    // in the inductive (its conclusion is a Constant referring to it).
    for (int i = 0; i < (int)constructors.size(); ++i) {
        const auto& constructor = constructors[i];
        if (environment.declarations.count(constructor.name)) {
            rollback();
            throw TypeError(
                "addInductive: constructor name already taken: " + constructor.name);
        }
        try {
            auto kindOfConstructorType = weakHeadNormalForm(
                environment, inferType(environment, {}, constructor.type));
            if (!std::holds_alternative<Sort>(kindOfConstructorType->node)) {
                rollback();
                throw TypeError(
                    "addInductive: constructor type is not a type: " +
                    constructor.name);
            }
            auto conclusion =
                checkConstructorStrictlyPositive(inductiveName, constructor);
            if (auto* c = std::get_if<Constant>(&conclusion->node);
                !c || c->name != inductiveName) {
                rollback();
                throw TypeError(
                    "addInductive: constructor " + constructor.name +
                    " does not end in " + inductiveName);
            }
        } catch (const TypeError&) {
            rollback();
            throw;
        }
        environment.declarations.emplace(
            constructor.name,
            Constructor{universeParameters, inductiveName, i, constructor.type});
    }

    // Generate and register the recursor. The recursor is universe-
    // polymorphic in the motive's codomain: it gains one extra universe
    // parameter (call it motiveLevel) beyond what the inductive has.
    // We pick a name that doesn't collide with the inductive's existing
    // universe parameters; this is purely a naming convenience since user
    // code refers to it positionally.
    std::string recursorName = inductiveName + "_recursor";
    if (environment.declarations.count(recursorName)) {
        rollback();
        throw TypeError(
            "addInductive: recursor name already taken: " + recursorName);
    }
    std::string motiveLevelName = "motiveLevel";
    {
        auto inUse = [&](const std::string& candidate) {
            for (const auto& p : universeParameters) {
                if (p == candidate) return true;
            }
            return false;
        };
        for (int suffix = 1; inUse(motiveLevelName); ++suffix) {
            motiveLevelName = "motiveLevel_" + std::to_string(suffix);
        }
    }
    auto recursorType = buildRecursorType(
        inductiveName, motiveLevelName, constructors);
    try {
        auto kindOfRecursorType = weakHeadNormalForm(
            environment, inferType(environment, {}, recursorType));
        if (!std::holds_alternative<Sort>(kindOfRecursorType->node)) {
            rollback();
            throw TypeError(
                "internal: generated recursor type is ill-formed: " + recursorName);
        }
    } catch (const TypeError&) {
        rollback();
        throw;
    }
    std::vector<std::string> recursorUniverseParameters = universeParameters;
    recursorUniverseParameters.push_back(motiveLevelName);
    environment.declarations.emplace(
        recursorName,
        Recursor{std::move(recursorUniverseParameters), inductiveName,
                 recursorType, (int)constructors.size()});
}
