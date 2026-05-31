#include "lemma_search.hpp"

#include "printer.hpp"

#include <algorithm>
#include <map>

namespace {

// Head Constant name of a proposition after WHNF (peel the App spine).
// Empty string when the head is not a Constant (a Pi, a free variable…).
std::string searchHeadName(const Environment& environment,
                           ExpressionPointer expression) {
    expression = weakHeadNormalForm(environment, expression);
    while (auto* application =
               std::get_if<Application>(&expression->node)) {
        expression = application->function;
    }
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        return constant->name;
    }
    return "";
}

struct PeeledType {
    // (opened binder name, binder domain in opened form) for each leading
    // Pi, outermost first.
    std::vector<std::pair<std::string, ExpressionPointer>> binders;
    ExpressionPointer conclusion;
};

// Peel every leading Pi, opening each binder as a fresh free variable of
// `origin`. Binder names come from the Pi display hints, deduped so the
// opened term is unambiguous. The stored domains reference earlier
// binders by their opened names.
PeeledType peelLeadingPis(ExpressionPointer type,
                          FreeVariableOrigin origin) {
    PeeledType result;
    std::set<std::string> used;
    while (auto* pi = std::get_if<Pi>(&type->node)) {
        std::string base = pi->displayHint.empty() ? "x" : pi->displayHint;
        std::string name = base;
        int suffix = 1;
        while (used.count(name)) {
            name = base + "_" + std::to_string(++suffix);
        }
        used.insert(name);
        result.binders.push_back({name, pi->domain});
        type = openBinder(pi->codomain, name, origin);
    }
    result.conclusion = type;
    return result;
}

// First-order match: does `pattern` match `target`, treating the
// Internal-origin free variables named in `metavars` as holes that bind
// to whatever they align with? On success `bindings` records each hole's
// value (consistent repeats checked up to defeq). Rigid mismatches fall
// back to a kernel defeq check so `successor(k)` matches `1 + k`.
bool searchMatch(const Environment& environment,
                 ExpressionPointer pattern,
                 ExpressionPointer target,
                 const std::set<std::string>& metavars,
                 std::map<std::string, ExpressionPointer>& bindings,
                 int& freshCounter) {
    if (auto* fv = std::get_if<FreeVariable>(&pattern->node)) {
        if (fv->origin == FreeVariableOrigin::Internal
            && metavars.count(fv->name)) {
            auto existing = bindings.find(fv->name);
            if (existing != bindings.end()) {
                return isDefinitionallyEqual(
                    environment, {}, existing->second, target);
            }
            bindings[fv->name] = target;
            return true;
        }
    }
    if (pattern->node.index() == target->node.index()) {
        if (auto* pc = std::get_if<Constant>(&pattern->node)) {
            auto* tc = std::get_if<Constant>(&target->node);
            if (pc->name == tc->name) return true;
        } else if (auto* pa = std::get_if<Application>(&pattern->node)) {
            auto* ta = std::get_if<Application>(&target->node);
            if (searchMatch(environment, pa->function, ta->function,
                            metavars, bindings, freshCounter)
                && searchMatch(environment, pa->argument, ta->argument,
                               metavars, bindings, freshCounter)) {
                return true;
            }
        } else if (auto* pp = std::get_if<Pi>(&pattern->node)) {
            auto* tp = std::get_if<Pi>(&target->node);
            std::string fresh = "__cmp_" + std::to_string(freshCounter++);
            if (searchMatch(environment, pp->domain, tp->domain,
                            metavars, bindings, freshCounter)
                && searchMatch(environment,
                               openBinder(pp->codomain, fresh,
                                          FreeVariableOrigin::Internal),
                               openBinder(tp->codomain, fresh,
                                          FreeVariableOrigin::Internal),
                               metavars, bindings, freshCounter)) {
                return true;
            }
        } else if (auto* pl = std::get_if<Lambda>(&pattern->node)) {
            auto* tl = std::get_if<Lambda>(&target->node);
            std::string fresh = "__cmp_" + std::to_string(freshCounter++);
            if (searchMatch(environment, pl->domain, tl->domain,
                            metavars, bindings, freshCounter)
                && searchMatch(environment,
                               openBinder(pl->body, fresh,
                                          FreeVariableOrigin::Internal),
                               openBinder(tl->body, fresh,
                                          FreeVariableOrigin::Internal),
                               metavars, bindings, freshCounter)) {
                return true;
            }
        } else if (auto* pb = std::get_if<BoundVariable>(&pattern->node)) {
            auto* tb = std::get_if<BoundVariable>(&target->node);
            if (pb->deBruijnIndex == tb->deBruijnIndex) return true;
        } else if (auto* pf = std::get_if<FreeVariable>(&pattern->node)) {
            auto* tf = std::get_if<FreeVariable>(&target->node);
            if (pf->name == tf->name && pf->origin == tf->origin) {
                return true;
            }
        }
    }
    // Rigid/shape mismatch: let the kernel decide up to reduction. Cheap
    // here because the head filter has already pruned to a handful of
    // candidates and the conclusion subterms are small.
    return isDefinitionallyEqual(environment, {}, pattern, target);
}

int countConstantNodes(ExpressionPointer expression) {
    if (std::get_if<Constant>(&expression->node)) return 1;
    if (auto* a = std::get_if<Application>(&expression->node)) {
        return countConstantNodes(a->function)
             + countConstantNodes(a->argument);
    }
    if (auto* p = std::get_if<Pi>(&expression->node)) {
        return countConstantNodes(p->domain)
             + countConstantNodes(p->codomain);
    }
    return 0;
}

// Rebuild `expression`, converting every Internal-origin FreeVariable to
// the same-named User-origin one. The lemma binders are opened as
// Internal vars (to mark them as match holes); the printer flags those
// with a leading `@`. Demoting them to User before printing a `[needs: …]`
// premise yields the clean `a ≤ c` reading in the lemma's own names.
ExpressionPointer demoteInternalFreeVars(ExpressionPointer expression) {
    if (auto* fv = std::get_if<FreeVariable>(&expression->node)) {
        if (fv->origin == FreeVariableOrigin::Internal) {
            return makeFreeVariable(fv->name);  // User-origin
        }
        return expression;
    }
    if (auto* application = std::get_if<Application>(&expression->node)) {
        return makeApplication(
            demoteInternalFreeVars(application->function),
            demoteInternalFreeVars(application->argument));
    }
    if (auto* pi = std::get_if<Pi>(&expression->node)) {
        return makePi(pi->displayHint,
                      demoteInternalFreeVars(pi->domain),
                      demoteInternalFreeVars(pi->codomain));
    }
    if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        return makeLambda(lambda->displayHint,
                          demoteInternalFreeVars(lambda->domain),
                          demoteInternalFreeVars(lambda->body));
    }
    if (auto* let = std::get_if<Let>(&expression->node)) {
        return makeLet(let->displayHint,
                       demoteInternalFreeVars(let->type),
                       demoteInternalFreeVars(let->value),
                       demoteInternalFreeVars(let->body));
    }
    return expression;
}

// Is `domain`, in the lemma's binder context, a Proposition (Sort 0)?
// Such a leftover binder is a hypothesis the caller must still prove; a
// non-Proposition leftover (e.g. `x : Natural`) is merely an
// underdetermined parameter. Conservative: returns false if the type
// cannot be inferred (treat as a parameter, not a need).
bool searchDomainIsProposition(const Environment& environment,
                               const Context& context,
                               ExpressionPointer domain) {
    try {
        ExpressionPointer sort = weakHeadNormalForm(
            environment, inferType(environment, context, domain));
        if (auto* sortNode = std::get_if<Sort>(&sort->node)) {
            if (auto* level =
                    std::get_if<LevelConst>(&sortNode->level->node)) {
                return level->value == 0;
            }
        }
    } catch (const TypeError&) {
    }
    return false;
}

// Render a lemma's type in surface form — `(a c b : Natural) → a ≤ c →
// a + b ≤ c + b` — instead of the raw `Π(a : Natural). Π(c : Natural). …`
// chain that prettyPrint emits. Leading data/type parameters become named
// binder groups (consecutive same-type ones collapsed: `(a c b : T)`);
// proposition premises render unnamed as the arrow chain leading to the
// conclusion. Binders are opened User-origin so subterms print with their
// names (and infix operators) rather than `@`-marked holes.
std::string formatLemmaSignature(const Environment& environment,
                                 ExpressionPointer type) {
    struct Binder {
        std::string name;
        ExpressionPointer domain;
        bool isProposition;
    };
    std::vector<Binder> binders;
    Context context;
    std::set<std::string> used;
    ExpressionPointer cursor = type;
    while (auto* pi = std::get_if<Pi>(&cursor->node)) {
        std::string base = pi->displayHint.empty() ? "x" : pi->displayHint;
        std::string name = base;
        int suffix = 1;
        while (used.count(name)) {
            name = base + "_" + std::to_string(++suffix);
        }
        used.insert(name);
        bool isProposition = searchDomainIsProposition(
            environment, context, pi->domain);
        binders.push_back({name, pi->domain, isProposition});
        context.push_back(
            {name, pi->domain, FreeVariableOrigin::User, nullptr});
        cursor = openBinder(pi->codomain, name, FreeVariableOrigin::User);
    }
    ExpressionPointer conclusion = cursor;

    // Leading run of data parameters → space-joined binder groups, with
    // consecutive equal-domain parameters collapsed.
    size_t i = 0;
    std::string prefix;
    while (i < binders.size() && !binders[i].isProposition) {
        std::string domainText = prettyPrint(binders[i].domain);
        std::string names = binders[i].name;
        size_t j = i + 1;
        while (j < binders.size() && !binders[j].isProposition
               && prettyPrint(binders[j].domain) == domainText) {
            names += " " + binders[j].name;
            ++j;
        }
        if (!prefix.empty()) prefix += " ";
        prefix += "(" + names + " : " + domainText + ")";
        i = j;
    }

    // Remaining binders (premises, plus any stray later parameters) and
    // the conclusion → arrow chain.
    std::vector<std::string> chain;
    for (; i < binders.size(); ++i) {
        if (binders[i].isProposition) {
            chain.push_back(prettyPrint(binders[i].domain));
        } else {
            chain.push_back("(" + binders[i].name + " : "
                            + prettyPrint(binders[i].domain) + ")");
        }
    }
    chain.push_back(prettyPrint(conclusion));
    std::string body;
    for (size_t k = 0; k < chain.size(); ++k) {
        if (k > 0) body += " → ";
        body += chain[k];
    }
    return prefix.empty() ? body : prefix + " → " + body;
}

}  // namespace

ExpressionPointer searchableDeclarationType(const Declaration& declaration) {
    if (auto* axiom = std::get_if<Axiom>(&declaration)) return axiom->type;
    if (auto* definition = std::get_if<Definition>(&declaration))
        return definition->type;
    return nullptr;
}

void collectConstantNames(ExpressionPointer expression,
                          std::set<std::string>& names) {
    if (auto* constant = std::get_if<Constant>(&expression->node)) {
        names.insert(constant->name);
    } else if (auto* application =
                   std::get_if<Application>(&expression->node)) {
        collectConstantNames(application->function, names);
        collectConstantNames(application->argument, names);
    } else if (auto* pi = std::get_if<Pi>(&expression->node)) {
        collectConstantNames(pi->domain, names);
        collectConstantNames(pi->codomain, names);
    } else if (auto* lambda = std::get_if<Lambda>(&expression->node)) {
        collectConstantNames(lambda->domain, names);
        collectConstantNames(lambda->body, names);
    } else if (auto* let = std::get_if<Let>(&expression->node)) {
        collectConstantNames(let->type, names);
        collectConstantNames(let->value, names);
        collectConstantNames(let->body, names);
    }
}

std::vector<LemmaSearchHit> computeGoalHits(
    const Environment& environment, ExpressionPointer goalType,
    std::string& goalHead, const std::set<std::string>& excludedNames) {
    PeeledType goal = peelLeadingPis(goalType, FreeVariableOrigin::User);
    goalHead = searchHeadName(environment, goal.conclusion);
    std::vector<LemmaSearchHit> hits;
    if (goalHead.empty()) return hits;
    for (const auto& [name, declaration] : environment.declarations) {
        if (excludedNames.count(name)) continue;
        ExpressionPointer type = searchableDeclarationType(declaration);
        if (!type) continue;
        PeeledType lemma =
            peelLeadingPis(type, FreeVariableOrigin::Internal);
        if (searchHeadName(environment, lemma.conclusion) != goalHead) {
            continue;
        }
        std::set<std::string> metavars;
        for (const auto& [binderName, binderType] : lemma.binders) {
            (void)binderType;
            metavars.insert(binderName);
        }
        std::map<std::string, ExpressionPointer> bindings;
        int freshCounter = 0;
        if (!searchMatch(environment, lemma.conclusion, goal.conclusion,
                         metavars, bindings, freshCounter)) {
            continue;
        }
        Context lemmaContext;
        for (const auto& [binderName, binderType] : lemma.binders) {
            lemmaContext.push_back(
                {binderName, binderType, FreeVariableOrigin::Internal,
                 nullptr});
        }
        LemmaSearchHit hit;
        hit.name = name;
        hit.declaredType = type;
        hit.signature = formatLemmaSignature(environment, type);
        for (const auto& [binderName, binderType] : lemma.binders) {
            if (bindings.count(binderName)) continue;
            if (searchDomainIsProposition(
                    environment, lemmaContext, binderType)) {
                hit.needs.push_back(demoteInternalFreeVars(binderType));
            } else {
                ++hit.unboundParameters;
            }
        }
        hit.specificity = countConstantNodes(lemma.conclusion);
        hits.push_back(std::move(hit));
    }
    std::sort(hits.begin(), hits.end(),
              [](const LemmaSearchHit& a, const LemmaSearchHit& b) {
                  if (a.needs.size() != b.needs.size())
                      return a.needs.size() < b.needs.size();
                  if (a.unboundParameters != b.unboundParameters)
                      return a.unboundParameters < b.unboundParameters;
                  if (a.specificity != b.specificity)
                      return a.specificity > b.specificity;
                  return a.name < b.name;
              });
    return hits;
}

std::vector<LemmaSearchHit> computeMentionHits(
    const Environment& environment, const std::vector<std::string>& wanted,
    const std::set<std::string>& excludedNames) {
    std::vector<LemmaSearchHit> hits;
    for (const auto& [name, declaration] : environment.declarations) {
        if (excludedNames.count(name)) continue;
        ExpressionPointer type = searchableDeclarationType(declaration);
        if (!type) continue;
        std::set<std::string> constants;
        collectConstantNames(type, constants);
        bool all = true;
        for (const auto& symbol : wanted) {
            if (!constants.count(symbol)) { all = false; break; }
        }
        if (!all) continue;
        LemmaSearchHit hit;
        hit.name = name;
        hit.declaredType = type;
        hit.signature = formatLemmaSignature(environment, type);
        hit.specificity = static_cast<int>(constants.size());
        hits.push_back(std::move(hit));
    }
    std::sort(hits.begin(), hits.end(),
              [](const LemmaSearchHit& a, const LemmaSearchHit& b) {
                  if (a.specificity != b.specificity)
                      return a.specificity < b.specificity;
                  return a.name < b.name;
              });
    return hits;
}
