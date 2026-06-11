// Out-of-line Elaborator method definitions: error formatting + diagnostic context stack (frames, throwElaborate), proof-step hints, search suggestions, definition well-formedness checks, display beta-normalization
//
// Part of the elaborator split (see internal.hpp): the class is
// declared in the header; each elaborator/*.cpp defines a topical
// slice of its methods as `Elaborator::method(...)`.

#include "elaborator/internal.hpp"

#include <limits>

ExpressionPointer Elaborator::betaNormalizeForDisplay(
        ExpressionPointer expression) const {
        if (auto* pi = std::get_if<Pi>(&expression->node)) {
            return makePi(pi->displayHint,
                betaNormalizeForDisplay(pi->domain),
                betaNormalizeForDisplay(pi->codomain));
        }
        if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            return makeLambda(lambda->displayHint,
                betaNormalizeForDisplay(lambda->domain),
                betaNormalizeForDisplay(lambda->body));
        }
        if (auto* application =
                std::get_if<Application>(&expression->node)) {
            ExpressionPointer fn = betaNormalizeForDisplay(
                application->function);
            ExpressionPointer arg = betaNormalizeForDisplay(
                application->argument);
            if (auto* lambda = std::get_if<Lambda>(&fn->node)) {
                ExpressionPointer reduced = substitute(
                    lambda->body, 0, arg);
                return betaNormalizeForDisplay(reduced);
            }
            return makeApplication(fn, arg);
        }
        return expression;
    }

std::string Elaborator::foldHeadKey(
        ExpressionPointer expression) const {
        ExpressionPointer cursor = expression;
        while (auto* app = std::get_if<Application>(&cursor->node)) {
            cursor = app->function;
        }
        if (auto* constant = std::get_if<Constant>(&cursor->node)) {
            return constant->name;
        }
        if (std::holds_alternative<Pi>(cursor->node)) {
            return "__Pi__";
        }
        return "";
    }

ExpressionPointer Elaborator::refoldForDisplay(
        ExpressionPointer expression) const {
        if (!expression) return expression;

        // (1) Re-fold children first (bottom-up), so a folded subterm's
        // arguments are themselves already in their nicest form.
        ExpressionPointer rebuilt = expression;
        if (auto* app = std::get_if<Application>(&expression->node)) {
            ExpressionPointer function = refoldForDisplay(app->function);
            ExpressionPointer argument = refoldForDisplay(app->argument);
            if (function.get() != app->function.get()
                || argument.get() != app->argument.get()) {
                rebuilt = makeApplication(function, argument);
            }
        } else if (auto* pi = std::get_if<Pi>(&expression->node)) {
            ExpressionPointer domain = refoldForDisplay(pi->domain);
            ExpressionPointer codomain = refoldForDisplay(pi->codomain);
            if (domain.get() != pi->domain.get()
                || codomain.get() != pi->codomain.get()) {
                rebuilt = makePi(pi->displayHint, domain, codomain);
            }
        } else if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
            ExpressionPointer domain = refoldForDisplay(lambda->domain);
            ExpressionPointer body = refoldForDisplay(lambda->body);
            if (domain.get() != lambda->domain.get()
                || body.get() != lambda->body.get()) {
                rebuilt = makeLambda(lambda->displayHint, domain, body);
            }
        }
        // (Let and atoms: nothing to descend into for display folding.)

        // (2) Try to fold `rebuilt` itself. Only when it is CLOSED (no
        // BoundVariable escapes it) — then the round-trip defeq check can
        // run in the empty context. A subterm under a binder that uses
        // that binder is "open" and is left as-is.
        if (referencesAnyBoundInRange(
                rebuilt, 0, std::numeric_limits<int>::max(), 0)) {
            return rebuilt;
        }
        std::string key = foldHeadKey(rebuilt);
        if (key.empty()) return rebuilt;

        for (const auto& entry : environment_.declarations) {
            auto* definition =
                std::get_if<Definition>(&entry.second);
            if (!definition) continue;
            // Opaque definitions never appear unfolded, and universe-
            // polymorphic ones would need their level arguments
            // reconstructed — skip both.
            if (definition->opacity == Opacity::Opaque) continue;
            if (!definition->universeParameters.empty()) continue;

            // Arity = leading lambdas of the body; the remainder is the
            // pattern, with those binders acting as match metavariables.
            int arity = 0;
            ExpressionPointer pattern = definition->body;
            while (auto* lambda = std::get_if<Lambda>(&pattern->node)) {
                pattern = lambda->body;
                arity++;
            }
            if (arity == 0) continue;  // nullary defs: skip (noise risk)
            if (foldHeadKey(pattern) != key) continue;

            std::vector<ExpressionPointer> bindings(arity);
            if (!const_cast<Elaborator*>(this)->matchAgainstPattern(
                    pattern, rebuilt, arity, bindings, 0)) {
                continue;
            }
            bool allFilled = true;
            for (const auto& binding : bindings) {
                if (!binding) { allFilled = false; break; }
            }
            if (!allFilled) continue;

            // Re-assemble `Name(arg0, …, arg_{arity-1})`. bindings is
            // innermost-binder-first, so parameter j (outermost-first)
            // is bindings[arity - 1 - j].
            ExpressionPointer candidate = makeConstant(entry.first);
            for (int j = arity - 1; j >= 0; --j) {
                candidate = makeApplication(candidate, bindings[j]);
            }

            // Round-trip: only display the fold if it is provably the
            // same proposition.
            if (isDefinitionallyEqual(
                    environment_, Context{}, candidate, rebuilt)) {
                return candidate;
            }
        }
        return rebuilt;
    }

std::string Elaborator::prettyPrintForDisplay(
        ExpressionPointer expression) const {
        std::string raw =
            prettyPrint(refoldForDisplay(
                betaNormalizeForDisplay(expression)));
        // The printer prefixes Internal-origin FreeVariables with '@'
        // so that any leak into user output is visible. In error
        // messages we deliberately open binders into named FreeVars,
        // so the `@` markers are noise; strip them.
        std::string stripped;
        stripped.reserve(raw.size());
        for (char character : raw) {
            if (character != '@') stripped.push_back(character);
        }
        return stripped;
    }

std::string Elaborator::prettyPrintInLocalScope(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders,
        size_t count) const {
        // Open with User-origin so the printer doesn't mark the
        // resulting FreeVariables with `@` (which is reserved for
        // signalling that an Internal-origin variable leaked).
        // Beta-normalise too so the printed form has no left-over
        // redexes (motive applications, etc.).
        ExpressionPointer opened = expression;
        for (size_t i = count; i > 0; --i) {
            opened = openBinder(opened, localBinders[i - 1].name,
                                 FreeVariableOrigin::User);
        }
        return prettyPrint(refoldForDisplay(
            betaNormalizeForDisplay(opened)));
    }

std::string Elaborator::prettyPrintInLocalScope(
        ExpressionPointer expression,
        const std::vector<LocalBinder>& localBinders) const {
        return prettyPrintInLocalScope(expression, localBinders,
                                         localBinders.size());
    }

std::string Elaborator::searchSuggestions(
        ExpressionPointer goalClosed,
        const std::vector<LocalBinder>& localBinders,
        size_t limit) const {
        try {
            ExpressionPointer goalOpened = goalClosed;
            for (size_t i = localBinders.size(); i > 0; --i) {
                goalOpened = openBinder(goalOpened,
                                        localBinders[i - 1].name,
                                        FreeVariableOrigin::User);
            }
            // Search the WHOLE library when a snapshot is available (the
            // verify-with-cache path), so a lemma that isn't imported yet
            // still surfaces — tagged with the import to add. Without the
            // snapshot (tests / verify without a cache), search the in-scope
            // environment alone. A hit is "in scope" iff it is already a
            // declaration in environment_; otherwise we cite its module.
            const LibrarySearchIndex* index =
                librarySearchProvider_ ? librarySearchProvider_() : nullptr;
            static const std::set<std::string> noExclusions;
            const Environment& searchEnvironment =
                index ? index->environment : environment_;
            const std::set<std::string>& excluded =
                index ? index->excludedNames : noExclusions;
            std::string head;
            std::vector<LemmaSearchHit> hits = computeGoalHits(
                searchEnvironment, goalOpened, head, excluded);
            if (hits.empty()) return "";
            std::string out =
                "\n  search by conclusion shape — candidates "
                "(cite one as `by <lemma>(…)`):";
            size_t shown = std::min(limit, hits.size());
            for (size_t i = 0; i < shown; ++i) {
                out += "\n    " + hits[i].name + " : "
                     + hits[i].signature;
                if (!hits[i].needs.empty()) {
                    out += "   [needs: ";
                    for (size_t j = 0; j < hits[i].needs.size(); ++j) {
                        if (j) out += ", ";
                        out += prettyPrint(hits[i].needs[j]);
                    }
                    out += "]";
                }
                // Tag lemmas that are not yet in scope with the import.
                if (index && !environment_.lookup(hits[i].name)) {
                    auto moduleIterator =
                        index->nameToModule.find(hits[i].name);
                    if (moduleIterator != index->nameToModule.end()) {
                        out += "\n        (needs import "
                             + moduleIterator->second + ")";
                    }
                }
            }
            return out;
        } catch (...) {
            return "";
        }
    }

std::string Elaborator::couldNotProveStepHint(
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        const std::string& relationSymbol,
        ExpressionPointer stepRelationType,
        const std::vector<LocalBinder>& localBinders) const {
        std::string goal;
        try {
            goal = "\n    goal: "
                 + prettyPrintInLocalScope(previousKernel, localBinders)
                 + " " + relationSymbol + " "
                 + prettyPrintInLocalScope(nextKernel, localBinders);
        } catch (...) { goal.clear(); }
        std::string hints;
        try {
            hints = searchSuggestions(stepRelationType, localBinders);
        } catch (...) { hints.clear(); }
        return goal + hints;
    }

void Elaborator::throwAutoProveCalcStepBudgetExceeded(
        ExpressionPointer previousKernel,
        ExpressionPointer nextKernel,
        const std::string& relationSymbol,
        ExpressionPointer stepRelationType,
        const std::vector<LocalBinder>& localBinders) {
        // Mirrors the "couldn't close" calc-step error (same goal + search
        // suggestions footer) but states the real reason — the auto-prover
        // hit its effort bound — and steers the user to an explicit `by`,
        // which lets the kernel check by definitional equality instead of
        // the prover searching. This is the kernel_quirks #19 fast-fail.
        throwElaborate(
            "the auto-prover gave up on this calc step after exhausting its "
            "effort budget — it explored too far without closing the goal "
            "(most often because an endpoint mentions a recursive definition "
            "that is expensive to unfold). Add an explicit `by <reason>` so "
            "the kernel can check the step by definitional equality instead "
            "of the prover searching for it. (Raise or disable the bound "
            "with MATH_AUTOPROVE_BUDGET if the step really should auto-close.)"
            + couldNotProveStepHint(previousKernel, nextKernel,
                  relationSymbol, stepRelationType, localBinders));
    }

void Elaborator::assertClosedOverLocalBinders(
        const ExpressionPointer& term,
        const std::vector<LocalBinder>& localBinders,
        const char* where) const {
        int n = static_cast<int>(localBinders.size());
        if (term->maxFreeBoundVariable >= n) {
            throw TypeError(
                std::string("internal: ") + where
                + " produced a term that is not closed over its local binders"
                  " (maxFreeBoundVariable="
                + std::to_string(term->maxFreeBoundVariable)
                + ", local binders=" + std::to_string(n)
                + ") — a bound variable escapes the local scope");
        }
    }

std::string Elaborator::formatErrorWithContext(const std::string& message) const {
        if (contextFrames_.empty()) return message;
        std::string result;
        // Most-recent frame first (innermost work), then progressively
        // outer frames. Each frame on its own line indented under the
        // last so the breadcrumb reads top-to-bottom from outer cause
        // to inner failure. For frames carrying a context snapshot
        // and/or a goal, dump those one indent deeper.
        for (auto iterator = contextFrames_.rbegin();
             iterator != contextFrames_.rend(); ++iterator) {
            result += iterator->description;
            result += "\n";
            // Context dump (suppressed when the snapshot is empty —
            // top-level frames before any binder is pushed don't add
            // anything by saying "(no binders)").
            if (!iterator->contextSnapshot.empty()) {
                result += "    context:\n";
                for (size_t i = 0;
                     i < iterator->contextSnapshot.size(); ++i) {
                    const auto& binder = iterator->contextSnapshot[i];
                    // Type may reference earlier binders (de Bruijn);
                    // open those names so the printout reads as the
                    // user wrote them.
                    std::string printedType;
                    try {
                        printedType = prettyPrintInLocalScope(
                            binder.type, iterator->contextSnapshot, i);
                    } catch (...) {
                        // Pretty-printing must never amplify the
                        // primary error. Fall back to a marker.
                        printedType = "<un-printable>";
                    }
                    result += "      " + binder.name + " : "
                            + printedType + "\n";
                }
            }
            // Goal dump (only when supplied — most internal frames
            // don't have a meaningful local goal to report).
            if (iterator->expectedType) {
                std::string printedGoal;
                try {
                    printedGoal = prettyPrintInLocalScope(
                        iterator->expectedType,
                        iterator->contextSnapshot);
                } catch (...) {
                    printedGoal = "<un-printable>";
                }
                result += "    goal: " + printedGoal + "\n";
            }
            result += "  ";
        }
        result += message;
        return result;
    }

std::pair<int, int> Elaborator::innermostFramePosition() const {
        for (auto iter = contextFrames_.rbegin();
             iter != contextFrames_.rend(); ++iter) {
            if (iter->line != 0) {
                return {iter->line, iter->column};
            }
        }
        return {0, 0};
    }

void Elaborator::checkDefinitionWellFormedOrThrow(
            const std::string& name,
            const ExpressionPointer& declaredType,
            const ExpressionPointer& body,
            const char* noun,
            const char* bodyNoun) {
        if (environment_.declarations.count(name)) {
            throwElaborate(std::string("a declaration named '") + name
                + "' already exists");
        }
        // The declared type must itself be a type (live in some `Sort`).
        ExpressionPointer declaredKind;
        try {
            declaredKind = weakHeadNormalForm(
                environment_, inferType(environment_, {}, declaredType));
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        if (!std::holds_alternative<Sort>(declaredKind->node)) {
            throwElaborate(std::string("the declared type of ") + noun + " '"
                + name + "' is not itself a type: `"
                + prettyPrintForDisplay(declaredType)
                + "` has type `" + prettyPrintForDisplay(declaredKind)
                + "`, which is not a proposition or a type");
        }
        // The body must have the declared type.
        ExpressionPointer inferredBodyType;
        try {
            inferredBodyType = inferType(environment_, {}, body);
        } catch (const TypeError& kernelError) {
            rethrowKernelError(kernelError);
        }
        if (!isDefinitionallyEqual(environment_, {}, inferredBodyType,
                                   declaredType)) {
            throwElaborate(std::string("the ") + bodyNoun + " of " + noun
                + " '" + name + "' does not have its declared type\n"
                "    declared type:        "
                + prettyPrintForDisplay(declaredType) + "\n"
                "    but this " + bodyNoun + " has type: "
                + prettyPrintForDisplay(inferredBodyType));
        }
    }

