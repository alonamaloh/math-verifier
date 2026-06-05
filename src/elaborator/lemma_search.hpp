#pragma once

// E1 — lemma search by goal shape (PLAN_READABILITY Track E1).
//
// The engine that answers "what proves this goal?" by the SHAPE of a
// lemma's conclusion rather than by its name. Shared between the
// `kernel search` CLI (main.cpp) and the elaborator's failing-proof
// error messages (elaborator.cpp), so both deliver the same ranked
// candidates from one implementation.

#include "kernel/expression.hpp"
#include "kernel/kernel.hpp"

#include <map>
#include <set>
#include <string>
#include <vector>

// A snapshot of the WHOLE built library, used by the elaborator's
// failing-proof suggestions to surface lemmas that aren't imported yet
// (tagged with the import to add). Built lazily by the verify driver —
// only when a proof actually fails — so the happy path pays nothing.
struct LibrarySearchIndex {
    Environment environment;                          // all declarations
    std::map<std::string, std::string> nameToModule;  // decl name → module
    std::set<std::string> excludedNames;              // Test/* fixtures
};

struct LemmaSearchHit {
    std::string name;
    ExpressionPointer declaredType;
    // The statement rendered in surface form — `(a b : T) → P → Q`
    // rather than the raw `Π(a : T). Π(b : T). …` chain. Precomputed by
    // computeGoalHits / computeMentionHits (which hold the environment
    // needed to classify each binder as a parameter vs. a hypothesis).
    std::string signature;
    // Unbound PROPOSITION premises — the hypotheses a caller would still
    // have to discharge after applying this lemma (the `[needs: …]`).
    std::vector<ExpressionPointer> needs;
    // Unbound DATA parameters — underdetermined; reported as a count.
    int unboundParameters = 0;
    // Matched Constant nodes in the conclusion (ranking tie-breaker).
    int specificity = 0;
};

// The declared type of a declaration usable as a lemma (axiom or
// definition/theorem). Returns nullptr for inductives / constructors /
// recursors.
ExpressionPointer searchableDeclarationType(const Declaration& declaration);

// Every Constant name occurring in `expression`.
void collectConstantNames(ExpressionPointer expression,
                          std::set<std::string>& names);

// conclusion-unifies-with-goal mode (apply?-style). Ranks library lemmas
// whose conclusion first-order-matches `goalType`'s conclusion. Sets
// `goalHead` to the goal conclusion's head Constant name (empty when the
// goal has no Constant head, in which case the result is empty).
// Declarations named in `excludedNames` are skipped (used to drop
// `library/Test/` fixtures from CLI results). Pure — no I/O.
std::vector<LemmaSearchHit> computeGoalHits(
    const Environment& environment, ExpressionPointer goalType,
    std::string& goalHead,
    const std::set<std::string>& excludedNames = {});

// mentions-these-symbols mode (Coq `Search`). Lemmas whose statement
// mentions every name in `wanted`, ranked by specificity (fewer total
// constants first). `excludedNames` as above.
std::vector<LemmaSearchHit> computeMentionHits(
    const Environment& environment, const std::vector<std::string>& wanted,
    const std::set<std::string>& excludedNames = {});
