#include "level.hpp"

#include <algorithm>
#include <sstream>

LevelPointer makeLevelConst(int value) {
    return std::make_shared<Level>(LevelConst{value});
}

LevelPointer makeLevelParam(std::string name) {
    return std::make_shared<Level>(LevelParam{std::move(name)});
}

LevelPointer makeLevelSucc(LevelPointer base) {
    // succ(const n) = const (n+1)
    if (auto* c = std::get_if<LevelConst>(&base->node)) {
        return makeLevelConst(c->value + 1);
    }
    return std::make_shared<Level>(LevelSucc{std::move(base)});
}

LevelPointer makeLevelMax(LevelPointer left, LevelPointer right) {
    auto* leftConst  = std::get_if<LevelConst>(&left->node);
    auto* rightConst = std::get_if<LevelConst>(&right->node);
    if (leftConst && rightConst) {
        return makeLevelConst(std::max(leftConst->value, rightConst->value));
    }
    if (leftConst  && leftConst->value  == 0) return right;
    if (rightConst && rightConst->value == 0) return left;
    if (levelsDefinitionallyEqual(left, right)) return left;
    return std::make_shared<Level>(LevelMax{std::move(left), std::move(right)});
}

LevelPointer makeLevelIMax(LevelPointer left, LevelPointer right) {
    auto* rightConst = std::get_if<LevelConst>(&right->node);
    if (rightConst) {
        if (rightConst->value == 0) return makeLevelConst(0);
        return makeLevelMax(std::move(left), std::move(right));
    }
    // succ(_) is never 0, so imax(_, succ(_)) = max(_, succ(_)).
    if (std::holds_alternative<LevelSucc>(right->node)) {
        return makeLevelMax(std::move(left), std::move(right));
    }
    return std::make_shared<Level>(LevelIMax{std::move(left), std::move(right)});
}

std::optional<int> levelAsConstant(LevelPointer level) {
    if (auto* c = std::get_if<LevelConst>(&level->node)) {
        return c->value;
    }
    return std::nullopt;
}

LevelPointer substituteLevelParameter(LevelPointer level,
                                      const std::string& parameterName,
                                      LevelPointer replacement) {
    if (std::holds_alternative<LevelConst>(level->node)) return level;
    if (auto* p = std::get_if<LevelParam>(&level->node)) {
        return p->name == parameterName ? replacement : level;
    }
    if (auto* s = std::get_if<LevelSucc>(&level->node)) {
        auto newBase = substituteLevelParameter(s->base, parameterName, replacement);
        return makeLevelSucc(newBase);
    }
    if (auto* m = std::get_if<LevelMax>(&level->node)) {
        auto newLeft  = substituteLevelParameter(m->left,  parameterName, replacement);
        auto newRight = substituteLevelParameter(m->right, parameterName, replacement);
        return makeLevelMax(newLeft, newRight);
    }
    if (auto* m = std::get_if<LevelIMax>(&level->node)) {
        auto newLeft  = substituteLevelParameter(m->left,  parameterName, replacement);
        auto newRight = substituteLevelParameter(m->right, parameterName, replacement);
        return makeLevelIMax(newLeft, newRight);
    }
    return level;
}

bool levelsDefinitionallyEqual(LevelPointer left, LevelPointer right) {
    if (left.get() == right.get()) return true;

    if (auto* leftConst = std::get_if<LevelConst>(&left->node)) {
        if (auto* rightConst = std::get_if<LevelConst>(&right->node)) {
            return leftConst->value == rightConst->value;
        }
        return false;
    }
    if (auto* leftParam = std::get_if<LevelParam>(&left->node)) {
        if (auto* rightParam = std::get_if<LevelParam>(&right->node)) {
            return leftParam->name == rightParam->name;
        }
        return false;
    }
    if (auto* leftSucc = std::get_if<LevelSucc>(&left->node)) {
        if (auto* rightSucc = std::get_if<LevelSucc>(&right->node)) {
            return levelsDefinitionallyEqual(leftSucc->base, rightSucc->base);
        }
        return false;
    }
    if (auto* leftMax = std::get_if<LevelMax>(&left->node)) {
        if (auto* rightMax = std::get_if<LevelMax>(&right->node)) {
            return levelsDefinitionallyEqual(leftMax->left,  rightMax->left)
                && levelsDefinitionallyEqual(leftMax->right, rightMax->right);
        }
        return false;
    }
    if (auto* leftImax = std::get_if<LevelIMax>(&left->node)) {
        if (auto* rightImax = std::get_if<LevelIMax>(&right->node)) {
            return levelsDefinitionallyEqual(leftImax->left,  rightImax->left)
                && levelsDefinitionallyEqual(leftImax->right, rightImax->right);
        }
        return false;
    }
    return false;
}

bool levelLessOrEqual(LevelPointer subLevel, LevelPointer superLevel) {
    if (levelsDefinitionallyEqual(subLevel, superLevel)) return true;
    // Concrete vs concrete.
    auto sub   = levelAsConstant(subLevel);
    auto super_ = levelAsConstant(superLevel);
    if (sub && super_) return *sub <= *super_;
    // sub <= max(a, b) if sub <= a OR sub <= b.
    if (auto* superMax = std::get_if<LevelMax>(&superLevel->node)) {
        return levelLessOrEqual(subLevel, superMax->left)
            || levelLessOrEqual(subLevel, superMax->right);
    }
    // max(a, b) <= super if a <= super AND b <= super.
    if (auto* subMax = std::get_if<LevelMax>(&subLevel->node)) {
        return levelLessOrEqual(subMax->left,  superLevel)
            && levelLessOrEqual(subMax->right, superLevel);
    }
    // succ(a) <= succ(b) iff a <= b.
    if (auto* subSucc = std::get_if<LevelSucc>(&subLevel->node)) {
        if (auto* superSucc = std::get_if<LevelSucc>(&superLevel->node)) {
            return levelLessOrEqual(subSucc->base, superSucc->base);
        }
        // succ(a) <= const n  iff  a <= const (n-1)  when n >= 1.
        if (super_ && *super_ >= 1) {
            return levelLessOrEqual(subSucc->base, makeLevelConst(*super_ - 1));
        }
    }
    return false;
}

namespace {

void writeLevel(std::ostringstream& out, LevelPointer level, int precedence);

void writeLevelAtomic(std::ostringstream& out, LevelPointer level) {
    if (auto* c = std::get_if<LevelConst>(&level->node)) {
        out << c->value;
        return;
    }
    if (auto* p = std::get_if<LevelParam>(&level->node)) {
        out << p->name;
        return;
    }
    out << "(";
    writeLevel(out, level, 0);
    out << ")";
}

void writeLevel(std::ostringstream& out, LevelPointer level, int precedence) {
    if (auto* s = std::get_if<LevelSucc>(&level->node)) {
        // succ over a const should have been folded by makeLevelSucc, but
        // print symbolically if not.
        bool parens = precedence > 0;
        if (parens) out << "(";
        writeLevelAtomic(out, s->base);
        out << "+1";
        if (parens) out << ")";
        return;
    }
    if (auto* m = std::get_if<LevelMax>(&level->node)) {
        out << "max(";
        writeLevel(out, m->left,  0);
        out << ", ";
        writeLevel(out, m->right, 0);
        out << ")";
        return;
    }
    if (auto* m = std::get_if<LevelIMax>(&level->node)) {
        out << "imax(";
        writeLevel(out, m->left,  0);
        out << ", ";
        writeLevel(out, m->right, 0);
        out << ")";
        return;
    }
    writeLevelAtomic(out, level);
}

} // namespace

std::string prettyPrintLevel(LevelPointer level) {
    std::ostringstream out;
    writeLevel(out, level, 0);
    return out.str();
}
