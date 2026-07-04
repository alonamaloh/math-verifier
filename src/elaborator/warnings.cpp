// Out-of-line Elaborator method definitions: unused-name / unused-binder warnings + surface-tree queries
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

bool Elaborator::referencesAnyBoundInRange(
        ExpressionPointer expression, int low, int high,
        int currentDepth) const {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            int idx = bv->deBruijnIndex - currentDepth;
            return idx >= low && idx < high;
        }
        if (auto* app =
                std::get_if<Application>(&expression->node)) {
            return referencesAnyBoundInRange(
                       app->function, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       app->argument, low, high, currentDepth);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesAnyBoundInRange(
                       pi->domain, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       pi->codomain, low, high, currentDepth + 1);
        }
        if (auto* lam = std::get_if<Lambda>(&expression->node)) {
            return referencesAnyBoundInRange(
                       lam->domain, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       lam->body, low, high, currentDepth + 1);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return referencesAnyBoundInRange(
                       let->type, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       let->value, low, high, currentDepth)
                || referencesAnyBoundInRange(
                       let->body, low, high, currentDepth + 1);
        }
        return false;
    }

void Elaborator::warnIfBinderUnused(
        const std::string& name,
        ExpressionPointer bodyUnderBinder,
        int line, int column,
        const char* form) {
        warnIfBinderUnusedAtIndex(
            name, bodyUnderBinder, /*relativeIndex=*/0,
            line, column, form);
    }

void Elaborator::warnIfBinderUnusedAtIndex(
        const std::string& name,
        ExpressionPointer bodyUnderBinders,
        int relativeIndex,
        int line, int column,
        const char* form) {
        if (!reportUnusedNames_) return;
        if (name.empty() || name[0] == '_') return;
        if (referencesBoundVariable(bodyUnderBinders, relativeIndex)) return;
        emitUnusedNameWarning(name, line, column, form);
    }

void Elaborator::warnIfSurfaceNameUnused(
        const std::string& name,
        const SurfaceExpression& body,
        int line, int column,
        const char* form) {
        if (!reportUnusedNames_) return;
        if (name.empty() || name[0] == '_') return;
        if (surfaceMentionsName(body, name)) return;
        emitUnusedNameWarning(name, line, column, form);
    }

bool Elaborator::surfaceContainsAutoProverInvocation(
        const SurfaceExpression& expression) {
        if (std::get_if<SurfaceStructuredClaim>(&expression.node)) {
            return true;
        }
        // Walk children of every surface variant we know about,
        // looking for nested auto-prover-using constructs. Cheapest
        // by far is reusing surfaceMentionsName's tree walk via a
        // lambda — but its body is large and special-cased per
        // variant; easier to walk the same shape here.
        if (auto* app =
                std::get_if<SurfaceApplication>(&expression.node)) {
            if (app->function
                && surfaceContainsAutoProverInvocation(*app->function))
                return true;
            for (const auto& arg : app->arguments) {
                if (arg.value && surfaceContainsAutoProverInvocation(
                                      *arg.value))
                    return true;
            }
            return false;
        }
        if (auto* lambda =
                std::get_if<SurfaceLambda>(&expression.node)) {
            return lambda->body
                && surfaceContainsAutoProverInvocation(*lambda->body);
        }
        if (auto* let = std::get_if<SurfaceLet>(&expression.node)) {
            if (let->value
                && surfaceContainsAutoProverInvocation(*let->value))
                return true;
            return let->body
                && surfaceContainsAutoProverInvocation(*let->body);
        }
        if (auto* asc =
                std::get_if<SurfaceAscription>(&expression.node)) {
            return asc->expression
                && surfaceContainsAutoProverInvocation(*asc->expression);
        }
        if (auto* cas = std::get_if<SurfaceCases>(&expression.node)) {
            if (cas->scrutinee
                && surfaceContainsAutoProverInvocation(*cas->scrutinee))
                return true;
            for (const auto& clause : cas->clauses) {
                if (clause.body
                    && surfaceContainsAutoProverInvocation(
                            *clause.body))
                    return true;
            }
            return false;
        }
        if (auto* calcNode =
                std::get_if<SurfaceCalc>(&expression.node)) {
            // A `by`-less calc step IS an auto-prover invocation.
            for (const auto& step : calcNode->steps) {
                if (!step.stepProof) return true;
                if (step.stepProof
                    && surfaceContainsAutoProverInvocation(
                            *step.stepProof))
                    return true;
            }
            return calcNode->initialExpression
                && surfaceContainsAutoProverInvocation(
                        *calcNode->initialExpression);
        }
        if (auto* tup =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            for (const auto& c : tup->components) {
                if (c && surfaceContainsAutoProverInvocation(*c))
                    return true;
            }
            return false;
        }
        if (auto* choose =
                std::get_if<SurfaceChoose>(&expression.node)) {
            if (choose->predicate
                && surfaceContainsAutoProverInvocation(
                        *choose->predicate))
                return true;
            return choose->body
                && surfaceContainsAutoProverInvocation(*choose->body);
        }
        if (auto* given =
                std::get_if<SurfaceGiven>(&expression.node)) {
            return given->proposition
                && surfaceContainsAutoProverInvocation(
                        *given->proposition);
        }
        if (auto* unfold =
                std::get_if<SurfaceUnfold>(&expression.node)) {
            return unfold->body
                && surfaceContainsAutoProverInvocation(*unfold->body);
        }
        if (auto* note =
                std::get_if<SurfaceNote>(&expression.node)) {
            // `note <prop>;` itself invokes the auto-prover.
            if (note->proposition) return true;
            return note->body
                && surfaceContainsAutoProverInvocation(*note->body);
        }
        if (auto* decide =
                std::get_if<SurfaceDecide>(&expression.node)) {
            if (decide->yesBody
                && surfaceContainsAutoProverInvocation(*decide->yesBody))
                return true;
            return decide->noBody
                && surfaceContainsAutoProverInvocation(*decide->noBody);
        }
        // Leaves (identifier, numeric literal, sort, type, etc.) and
        // any variants not enumerated above can't host an auto-prover
        // call — return false.
        return false;
    }

void Elaborator::emitUnusedNameWarning(
        const std::string& name, int line, int column,
        const char* form) {
        std::cerr << "warning: " << moduleName_
            << ":" << line << ":" << column
            << ": unused name `" << name
            << "` introduced by " << form
            << " — the body never references it; drop it\n";
    }

bool Elaborator::surfaceMentionsName(
        const SurfaceExpression& expression,
        const std::string& name) {
        if (auto* id =
                std::get_if<SurfaceIdentifier>(&expression.node)) {
            return id->qualifiedName == name;
        }
        if (auto* app =
                std::get_if<SurfaceApplication>(&expression.node)) {
            if (surfaceMentionsName(*app->function, name)) return true;
            for (const auto& arg : app->arguments) {
                if (arg.value
                    && surfaceMentionsName(*arg.value, name)) {
                    return true;
                }
            }
            return false;
        }
        if (auto* pi =
                std::get_if<SurfacePiType>(&expression.node)) {
            if (pi->binder.type
                && surfaceMentionsName(*pi->binder.type, name))
                return true;
            return pi->codomain
                && surfaceMentionsName(*pi->codomain, name);
        }
        if (auto* lambda =
                std::get_if<SurfaceLambda>(&expression.node)) {
            if (lambda->binder.type
                && surfaceMentionsName(*lambda->binder.type, name))
                return true;
            return lambda->body
                && surfaceMentionsName(*lambda->body, name);
        }
        if (auto* let =
                std::get_if<SurfaceLet>(&expression.node)) {
            if (let->type
                && surfaceMentionsName(*let->type, name)) return true;
            if (let->value
                && surfaceMentionsName(*let->value, name)) return true;
            return let->body
                && surfaceMentionsName(*let->body, name);
        }
        if (auto* asc =
                std::get_if<SurfaceAscription>(&expression.node)) {
            if (asc->expression
                && surfaceMentionsName(*asc->expression, name))
                return true;
            return asc->type
                && surfaceMentionsName(*asc->type, name);
        }
        if (auto* bin =
                std::get_if<SurfaceBinaryOperation>(&expression.node)) {
            if (bin->left
                && surfaceMentionsName(*bin->left, name)) return true;
            return bin->right
                && surfaceMentionsName(*bin->right, name);
        }
        if (auto* un =
                std::get_if<SurfaceUnaryOperation>(&expression.node)) {
            return un->operand
                && surfaceMentionsName(*un->operand, name);
        }
        if (auto* tup =
                std::get_if<SurfaceAnonymousTuple>(&expression.node)) {
            for (const auto& c : tup->components) {
                if (c && surfaceMentionsName(*c, name)) return true;
            }
            return false;
        }
        if (auto* cas =
                std::get_if<SurfaceCases>(&expression.node)) {
            if (cas->scrutinee
                && surfaceMentionsName(*cas->scrutinee, name))
                return true;
            // A `cases … refining h1, h2 { … }` consumes the listed
            // names — they are stored as strings, not identifier
            // expressions, so the structural walk below misses them
            // (false "unused name" on claims consumed only by a
            // refining list).
            for (const auto& refined : cas->refiningNames) {
                if (refined == name) return true;
            }
            for (const auto& clause : cas->clauses) {
                if (clause.body
                    && surfaceMentionsName(*clause.body, name))
                    return true;
            }
            return false;
        }
        if (auto* calcNode =
                std::get_if<SurfaceCalc>(&expression.node)) {
            if (calcNode->initialExpression
                && surfaceMentionsName(
                    *calcNode->initialExpression, name))
                return true;
            for (const auto& step : calcNode->steps) {
                if (step.nextExpression
                    && surfaceMentionsName(
                        *step.nextExpression, name)) return true;
                if (step.stepProof
                    && surfaceMentionsName(
                        *step.stepProof, name)) return true;
            }
            return false;
        }
        if (auto* claim =
                std::get_if<SurfaceStructuredClaim>(&expression.node)) {
            if (claim->proposition
                && surfaceMentionsName(*claim->proposition, name))
                return true;
            if (claim->byHint
                && surfaceMentionsName(*claim->byHint, name))
                return true;
            for (const auto& arm : claim->arms) {
                if (arm.body
                    && surfaceMentionsName(*arm.body, name))
                    return true;
                if (arm.disjunctType
                    && surfaceMentionsName(
                        *arm.disjunctType, name)) return true;
            }
            return false;
        }
        if (auto* choose =
                std::get_if<SurfaceChoose>(&expression.node)) {
            if (choose->predicate
                && surfaceMentionsName(*choose->predicate, name))
                return true;
            // `choose v … from <source>` destructures <source>: a bare
            // hypothesis name there IS a reference to it. Without this the
            // walker missed `h` in `choose v from h;` and flagged the claim
            // that introduced `h` as unused (the fact is consumed by the
            // destructure, not by type-match).
            if (choose->source
                && surfaceMentionsName(*choose->source, name))
                return true;
            return choose->body
                && surfaceMentionsName(*choose->body, name);
        }
        if (auto* given =
                std::get_if<SurfaceGiven>(&expression.node)) {
            return given->proposition
                && surfaceMentionsName(*given->proposition, name);
        }
        if (auto* note =
                std::get_if<SurfaceNote>(&expression.node)) {
            if (note->goalType
                && surfaceMentionsName(*note->goalType, name))
                return true;
            if (note->proposition
                && surfaceMentionsName(*note->proposition, name))
                return true;
            if (note->proof
                && surfaceMentionsName(*note->proof, name))
                return true;
            return note->body
                && surfaceMentionsName(*note->body, name);
        }
        if (auto* decide =
                std::get_if<SurfaceDecide>(&expression.node)) {
            if (decide->proposition
                && surfaceMentionsName(*decide->proposition, name))
                return true;
            if (decide->yesBody
                && surfaceMentionsName(*decide->yesBody, name))
                return true;
            return decide->noBody
                && surfaceMentionsName(*decide->noBody, name);
        }
        if (auto* fieldTactic =
                std::get_if<SurfaceField>(&expression.node)) {
            // `field(h1, h2, ...)` references each h_i positionally.
            // Without this case the walker missed `smNonzero` /
            // `snNonzero` inside `field(smNonzero, snNonzero)` and
            // emitted spurious "unused name" warnings.
            for (const auto& hypothesis : fieldTactic->nonzeroHypotheses) {
                if (hypothesis
                    && surfaceMentionsName(*hypothesis, name))
                    return true;
            }
            return false;
        }
        if (auto* linearCombination =
                std::get_if<SurfaceLinearCombination>(&expression.node)) {
            // `linear_combination(c1 * h1 + h2 - ...)` references each
            // hypothesis `h_i` inside the combination tree. Without this
            // case the walker missed those leaves and emitted spurious
            // "unused name" warnings (cf. the `SurfaceField` case above).
            return linearCombination->combination
                && surfaceMentionsName(*linearCombination->combination, name);
        }
        if (auto* byInd =
                std::get_if<SurfaceByInductionUsing>(&expression.node)) {
            if (byInd->scrutinee
                && surfaceMentionsName(*byInd->scrutinee, name))
                return true;
            if (byInd->inductionLemma
                && surfaceMentionsName(*byInd->inductionLemma, name))
                return true;
            return byInd->body
                && surfaceMentionsName(*byInd->body, name);
        }
        if (auto* byStrong =
                std::get_if<SurfaceByStrongInduction>(&expression.node)) {
            if (byStrong->scrutinee
                && surfaceMentionsName(*byStrong->scrutinee, name))
                return true;
            return byStrong->body
                && surfaceMentionsName(*byStrong->body, name);
        }
        if (auto* eventuallyScope =
                std::get_if<SurfaceEventuallyScope>(&expression.node)) {
            return eventuallyScope->binderName != name
                && eventuallyScope->body
                && surfaceMentionsName(*eventuallyScope->body, name);
        }
        if (auto* unfold =
                std::get_if<SurfaceUnfold>(&expression.node)) {
            return unfold->body
                && surfaceMentionsName(*unfold->body, name);
        }
        // Leaf / specialised nodes (numeric literal, Type,
        // Proposition, hammer, sorry, ring, etc.) don't have
        // identifier subterms to recurse into.
        return false;
    }

bool Elaborator::referencesBoundVariable(
        ExpressionPointer expression, int targetIndex) {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            return bv->deBruijnIndex == targetIndex;
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return referencesBoundVariable(
                       application->function, targetIndex)
                || referencesBoundVariable(
                       application->argument, targetIndex);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return referencesBoundVariable(pi->domain, targetIndex)
                || referencesBoundVariable(
                       pi->codomain, targetIndex + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return referencesBoundVariable(lambda->domain, targetIndex)
                || referencesBoundVariable(
                       lambda->body, targetIndex + 1);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return referencesBoundVariable(let->type, targetIndex)
                || referencesBoundVariable(let->value, targetIndex)
                || referencesBoundVariable(let->body, targetIndex + 1);
        }
        return false;
    }

bool Elaborator::binderReferencesAllBound(
        ExpressionPointer expression,
        const std::vector<ExpressionPointer>& bindings,
        int nestedBinderDepth) {
        if (auto* bv =
                std::get_if<BoundVariable>(&expression->node)) {
            if (bv->deBruijnIndex < nestedBinderDepth) return true;
            int relative = bv->deBruijnIndex - nestedBinderDepth;
            if (relative >= static_cast<int>(bindings.size())) {
                return true;
            }
            return bindings[relative] != nullptr;
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            return binderReferencesAllBound(
                       application->function, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       application->argument, bindings, nestedBinderDepth);
        }
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return binderReferencesAllBound(
                       pi->domain, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       pi->codomain, bindings, nestedBinderDepth + 1);
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return binderReferencesAllBound(
                       lambda->domain, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       lambda->body, bindings, nestedBinderDepth + 1);
        }
        if (auto* let = std::get_if<Let>(&expression->node)) {
            return binderReferencesAllBound(
                       let->type, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       let->value, bindings, nestedBinderDepth)
                && binderReferencesAllBound(
                       let->body, bindings, nestedBinderDepth + 1);
        }
        return true;
    }

// ---- B5 hint classifier (`MATH_CLASSIFY_HINTS`) ------------------------
// See the declaration comment in internal.hpp. The features are SHAPE
// classifications — the tiers they size do not exist yet, so this reads
// the goal's form (sign judgment, cast content, groundness) rather than
// running any prospective procedure. `closes` is the one live probe: the
// same budget-capped speculative re-proof the redundancy checker runs.

namespace {

// Pre-order visit of every subterm.
template <typename Visitor>
void visitEverySubterm(const ExpressionPointer& term,
                       const Visitor& visit) {
    if (!term) return;
    visit(term);
    if (auto* application = std::get_if<Application>(&term->node)) {
        visitEverySubterm(application->function, visit);
        visitEverySubterm(application->argument, visit);
    } else if (auto* pi = std::get_if<Pi>(&term->node)) {
        visitEverySubterm(pi->domain, visit);
        visitEverySubterm(pi->codomain, visit);
    } else if (auto* lambda = std::get_if<Lambda>(&term->node)) {
        visitEverySubterm(lambda->domain, visit);
        visitEverySubterm(lambda->body, visit);
    } else if (auto* let = std::get_if<Let>(&term->node)) {
        visitEverySubterm(let->type, visit);
        visitEverySubterm(let->value, visit);
        visitEverySubterm(let->body, visit);
    }
}

// Application-spine head constant name + spine arguments (outermost last).
std::string spineHeadAndArguments(
        ExpressionPointer term,
        std::vector<ExpressionPointer>& arguments) {
    arguments.clear();
    ExpressionPointer cursor = term;
    while (auto* application = std::get_if<Application>(&cursor->node)) {
        arguments.push_back(application->argument);
        cursor = application->function;
    }
    std::reverse(arguments.begin(), arguments.end());
    if (auto* constant = std::get_if<Constant>(&cursor->node)) {
        return constant->name;
    }
    return std::string();
}

} // namespace

bool Elaborator::classifyHintsEnabled() const {
    static const bool enabled = [] {
        const char* flag = std::getenv("MATH_CLASSIFY_HINTS");
        return flag && flag[0] != '\0' && flag[0] != '0';
    }();
    return enabled;
}

void Elaborator::emitHintClassification(
        const char* kind,
        const char* relationLabel,
        ExpressionPointer goalClosed,
        const SurfaceExpression* hint,
        bool bareCloses,
        int line) {
    if (!goalClosed) return;

    // Peel `Not(...)` so `x ≠ 0` classifies by its inner equality.
    ExpressionPointer subject = goalClosed;
    int negations = 0;
    std::vector<ExpressionPointer> arguments;
    std::string headName;
    for (;;) {
        headName = spineHeadAndArguments(subject, arguments);
        if (headName == "Not" && arguments.size() == 1) {
            subject = arguments[0];
            ++negations;
            continue;
        }
        break;
    }

    // Sign-judgment shape (tier-4 candidate): a relation whose subject is
    // anchored on the numeral 0 (`0 ≤ x`, `0 < x`, `x = 0` under Not), or
    // a unary nonnegativity predicate.
    bool signShape = false;
    if (arguments.size() >= 2) {
        for (size_t i = arguments.size() - 2; i < arguments.size(); ++i) {
            auto numeral = asNumeralLiteral(arguments[i]);
            if (numeral && numeral->second == 0) signShape = true;
        }
    }
    if (!signShape && headName.find("IsNonneg") != std::string::npos) {
        signShape = true;
    }

    bool containsCast = false;
    bool containsFree = false;
    visitEverySubterm(goalClosed, [&](const ExpressionPointer& sub) {
        if (auto* constant = std::get_if<Constant>(&sub->node)) {
            if (!containsCast && isCoercionFunctionName(constant->name)) {
                containsCast = true;
            }
        } else if (std::get_if<FreeVariable>(&sub->node)) {
            containsFree = true;
        }
    });
    // Ground (tier-2 candidate): no reference to any local binder — the
    // closed form's free-BV watermark is the whole check (-1 = closed).
    bool ground = !containsFree && goalClosed->maxFreeBoundVariable < 0;

    std::string hintName = "<term>";
    if (hint) {
        if (auto* identifier = std::get_if<SurfaceIdentifier>(&hint->node)) {
            hintName = identifier->qualifiedName;
        } else if (auto* application =
                       std::get_if<SurfaceApplication>(&hint->node)) {
            if (auto* head = std::get_if<SurfaceIdentifier>(
                    &application->function->node)) {
                hintName = head->qualifiedName + "(...)";
            } else {
                hintName = "<application>";
            }
        } else if (std::get_if<SurfaceUnfold>(&hint->node)) {
            hintName = "<unfolding>";
        }
    }

    std::string goalText = prettyPrint(goalClosed);
    for (char& character : goalText) {
        if (character == '\n' || character == '\t') character = ' ';
    }
    if (goalText.size() > 140) {
        goalText.resize(137);
        goalText += "...";
    }

    std::cerr << "[classify-hint]\t" << moduleName_ << ":" << line
        << "\tkind=" << kind
        << "\trel=" << relationLabel
        << "\t" << "by"
        << "\tcloses=" << (bareCloses ? 1 : 0)
        << "\tneg=" << negations
        << "\thead=" << (headName.empty() ? "<none>" : headName)
        << "\tsign=" << (signShape ? 1 : 0)
        << "\tcast=" << (containsCast ? 1 : 0)
        << "\tground=" << (ground ? 1 : 0)
        << "\thint=" << hintName
        << "\tgoal=" << goalText << "\n";
}

