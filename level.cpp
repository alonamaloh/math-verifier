#include "level.hpp"

#include <algorithm>
#include <sstream>

LevelPointer makeLevelConst(int value) {
    return std::make_shared<Level>(LevelConst{value});
}

LevelPointer makeLevelParam(std::string name) {
    return std::make_shared<Level>(LevelParam{std::move(name)});
}

LevelPointer makeLevelSuccessor(LevelPointer base) {
    // successor(LevelConst n) = LevelConst (n+1)
    if (auto* concrete = std::get_if<LevelConst>(&base->node)) {
        return makeLevelConst(concrete->value + 1);
    }
    return std::make_shared<Level>(LevelSuccessor{std::move(base)});
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
    // successor(_) is never 0, so imax(_, successor(_)) =
    // max(_, successor(_)).
    if (std::holds_alternative<LevelSuccessor>(right->node)) {
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
    if (auto* successor = std::get_if<LevelSuccessor>(&level->node)) {
        auto newBase = substituteLevelParameter(
            successor->base, parameterName, replacement);
        return makeLevelSuccessor(newBase);
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
    if (auto* leftSuccessor =
            std::get_if<LevelSuccessor>(&left->node)) {
        if (auto* rightSuccessor =
                std::get_if<LevelSuccessor>(&right->node)) {
            return levelsDefinitionallyEqual(
                leftSuccessor->base, rightSuccessor->base);
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
    auto subConcrete   = levelAsConstant(subLevel);
    auto superConcrete = levelAsConstant(superLevel);
    if (subConcrete && superConcrete) {
        return *subConcrete <= *superConcrete;
    }
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
    // successor(a) <= successor(b) iff a <= b.
    if (auto* subSuccessor =
            std::get_if<LevelSuccessor>(&subLevel->node)) {
        if (auto* superSuccessor =
                std::get_if<LevelSuccessor>(&superLevel->node)) {
            return levelLessOrEqual(
                subSuccessor->base, superSuccessor->base);
        }
        // successor(a) <= LevelConst n  iff  a <= LevelConst (n-1)
        // when n >= 1.
        if (superConcrete && *superConcrete >= 1) {
            return levelLessOrEqual(
                subSuccessor->base, makeLevelConst(*superConcrete - 1));
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
    if (auto* successor = std::get_if<LevelSuccessor>(&level->node)) {
        // successor over a LevelConst should have been folded by
        // makeLevelSuccessor, but print symbolically if not.
        bool parens = precedence > 0;
        if (parens) out << "(";
        writeLevelAtomic(out, successor->base);
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
