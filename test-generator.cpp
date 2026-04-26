#include <vector>
#include <string>
#include <iostream>
#include <random>
#include <set>

std::mt19937 rng(42); // fixed seed for reproducibility

int randInt(int l, int r) {
    std::uniform_int_distribution<int> dist(l, r);
    return dist(rng);
}

template<typename T>
T pick(const std::vector<T>& vec) {
    return vec[randInt(0, vec.size() - 1)];
}

std::vector<std::string> props = {"p", "q", "r", "s", "t", "u"};
std::vector<std::string> preds = {"p", "q", "r", "s"};
std::vector<std::string> vars  = {"X", "Y", "Z"};
std::vector<std::string> consts = {"a", "b", "c"};

std::string atom() {
    return pick(props);
}

std::string predAtom(const std::string& term) {
    return pick(preds) + "(" + term + ")";
}

std::string constAtom() {
    return predAtom(pick(consts));
}

std::string varAtom(const std::string& var) {
    return predAtom(var);
}

// ── Propositional tautology templates ──────────────────────────────────────

std::string genProp() {
    std::string p = atom(), q = atom(), r = atom();
    int t = randInt(0, 19);
    switch(t) {
        case 0:  return "(" + p + " => " + p + ")";
        case 1:  return "(" + p + " => (" + q + " => " + p + "))";
        case 2:  return "((" + p + " & " + q + ") => " + p + ")";
        case 3:  return "((" + p + " & " + q + ") => " + q + ")";
        case 4:  return "(" + p + " => (" + p + " | " + q + "))";
        case 5:  return "(" + q + " => (" + p + " | " + q + "))";
        case 6:  return "((" + p + " => " + q + ") => ((" + q + " => " + r + ") => (" + p + " => " + r + ")))";
        case 7:  return "(" + p + " | ~" + p + ")";
        case 8:  return "(~~" + p + " => " + p + ")";
        case 9:  return "(" + p + " => ~~" + p + ")";
        case 10: return "((" + p + " => " + q + ") => (~" + q + " => ~" + p + "))";
        case 11: return "(((" + p + " | " + q + ") & ~" + p + ") => " + q + ")";
        case 12: return "((" + p + " & (" + q + " | " + r + ")) => ((" + p + " & " + q + ") | (" + p + " & " + r + ")))";
        case 13: return "(((" + p + " & " + q + ") | (" + p + " & " + r + ")) => (" + p + " & (" + q + " | " + r + ")))";
        case 14: return "((" + p + " => " + q + ") => ((" + p + " => ~" + q + ") => ~" + p + "))";
        case 15: return "(((" + p + " => " + q + ") & (" + q + " => " + r + ") & " + p + ") => " + r + ")";
        case 16: return "((" + p + " => " + q + ") & (" + p + " => " + r + ") => (" + p + " => (" + q + " & " + r + ")))";
        case 17: return "(((" + p + " | " + q + ") & (" + p + " => " + r + ") & (" + q + " => " + r + ")) => " + r + ")";
        case 18: return "(~(" + p + " & " + q + ") => (~" + p + " | ~" + q + "))";
        case 19: return "((~" + p + " | ~" + q + ") => ~(" + p + " & " + q + "))";
    }
    return "(" + p + " => " + p + ")";
}

// ── FOL tautology templates ─────────────────────────────────────────────────

std::string genFOL() {
    std::string v1 = pick(vars);
    std::string v2 = pick(vars);
    std::string c  = pick(consts);
    std::string pv1 = predAtom(v1);
    std::string qv1 = pick(preds) + "(" + v1 + ")";
    std::string rv1 = pick(preds) + "(" + v1 + ")";
    std::string pc  = predAtom(c);

    int t = randInt(0, 19);
    switch(t) {
        case 0:  return "(![" + v1 + "]: " + pv1 + " => " + pc + ")";
        case 1:  return "(" + pc + " => ?[" + v1 + "]: " + predAtom(v1) + ")";
        case 2:  return "(![" + v1 + "]: " + pv1 + " => ?[" + v1 + "]: " + predAtom(v1) + ")";
        case 3:  return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") => (![" + v1 + "]: " + pv1 + " => ![" + v1 + "]: " + qv1 + "))";
        case 4:  return "(![" + v1 + "]: (" + pv1 + " & " + qv1 + ") => (![" + v1 + "]: " + pv1 + " & ![" + v1 + "]: " + qv1 + "))";
        case 5:  return "(?[" + v1 + "]: (" + pv1 + " & " + qv1 + ") => ?[" + v1 + "]: " + pv1 + ")";
        case 6:  return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") & " + pc + " => ?[" + v1 + "]: " + predAtom(v1) + ")";
        case 7:  return "(?[" + v1 + "]: " + pv1 + " => ?[" + v2 + "]: " + predAtom(v2) + ")";
        case 8:  return "(![" + v1 + "]: " + pv1 + " => (![" + v2 + "]: " + predAtom(v2) + "))";
        case 9:  return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") & ![" + v1 + "]: (" + qv1 + " => " + rv1 + ") => ![" + v1 + "]: (" + pv1 + " => " + rv1 + "))";
        case 10: return "(?[" + v1 + "]: (" + pv1 + " | " + qv1 + ") => (?[" + v1 + "]: " + pv1 + " | ?[" + v1 + "]: " + qv1 + "))";
        case 11: return "(![" + v1 + "]: ~" + pv1 + " => ~?[" + v1 + "]: " + predAtom(v1) + ")";
        case 12: return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") => (~?[" + v1 + "]: " + qv1 + " => ~?[" + v1 + "]: " + pv1 + "))";
        case 13: return "(?[" + v1 + "]: " + pv1 + " & ![" + v1 + "]: (" + pv1 + " => " + qv1 + ") => ?[" + v1 + "]: " + qv1 + ")";
        case 14: return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") & ?[" + v1 + "]: (" + pv1 + " & " + rv1 + ") => ?[" + v1 + "]: (" + qv1 + " & " + rv1 + "))";
        case 15: return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") & ![" + v1 + "]: " + pv1 + " => ![" + v1 + "]: " + qv1 + ")";
        case 16: return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") & ?[" + v1 + "]: " + pv1 + " => ?[" + v1 + "]: " + qv1 + ")";
        case 17: return "(?[" + v1 + "]: (" + pv1 + " => " + qv1 + ") => (![" + v1 + "]: " + pv1 + " => ?[" + v1 + "]: " + qv1 + "))";
        case 18: return "(![" + v1 + "]: (" + pv1 + " => " + qv1 + ") => (![" + v1 + "]: (![" + v1 + "]: " + pv1 + " => ![" + v1 + "]: " + qv1 + ")))";
        case 19: return "(~?[" + v1 + "]: (" + pv1 + " & " + qv1 + ") => ![" + v1 + "]: (" + pv1 + " => ~" + qv1 + "))";
    }
    return "(![" + v1 + "]: " + pv1 + " => " + pc + ")";
}

int main() {
    int propCount = 600;
    int folCount  = 400;

    for (int i = 0; i < propCount; i++) {
        std::cout << "fof(gen_prop" << i << ", conjecture, " << genProp() << ").\n";
    }
    for (int i = 0; i < folCount; i++) {
        std::cout << "fof(gen_fol" << i << ", conjecture, " << genFOL() << ").\n";
    }
    return 0;
}
