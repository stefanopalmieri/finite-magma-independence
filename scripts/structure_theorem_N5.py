"""
Verify the N=5 R+D+H structure theorem via Z3:

  Theorem. Every R+D+H magma on Fin(5) with absorbers {0,1} satisfies:
    (i)  the core {2,3,4} has exactly 2 classifiers and 1 non-classifier g;
    (ii) any retraction pair has s = r = g (strong R is unsatisfiable);
    (iii) any H triple (a, b, c) has b = g and {a, c} = the two classifiers.

This script encodes R+D+H on Fin(5) plus the *negation* of each claim
separately, and verifies UNSAT for each. Three UNSATs together give the
structure theorem.

Usage: python3 structure_theorem_N5.py
"""

from __future__ import annotations

import itertools
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat


N = 5
CORE = [2, 3, 4]


def base_solver(strong_R=False):
    s = Solver()
    T = [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]
    for a in range(N):
        for b in range(N):
            s.add(T[a][b] >= 0, T[a][b] < N)
    for x in range(N):
        s.add(T[0][x] == 0)
        s.add(T[1][x] == 1)
    for y in CORE:
        s.add(Or([T[y][x] != y for x in range(N)]))

    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw
            pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))

    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    if strong_R:
        s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if strong_R and sv == rv: continue
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx))
        s.add(Or(srx))

    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    tau_cases = [And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
                 for tv in CORE]
    s.add(Or(*tau_cases))

    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(cases))
        diffs = [T[a][x1] != T[a][x2]
                 for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))

    return s, T, sR, rR, is_cls


def classifier_count(T, is_cls):
    """Return (num_classifiers, is_cls_map)."""
    return is_cls


def test_claim(label, add_negation):
    s, T, sR, rR, is_cls = base_solver(strong_R=False)
    add_negation(s, T, sR, rR, is_cls)
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == unsat:
        print(f"  [{dt:5.2f}s] UNSAT -- claim '{label}' holds")
        return True
    elif r == sat:
        m = s.model()
        print(f"  [{dt:5.2f}s] SAT   -- claim '{label}' FAILS. Counterexample:")
        for a in range(N):
            print("    " + " ".join(str(m.eval(T[a][b]).as_long())
                                     for b in range(N)))
        return False
    else:
        print(f"  [{dt:5.2f}s] UNKNOWN for claim '{label}'")
        return False


def main():
    print("N=5 R+D+H Structure Theorem verification")
    print("=========================================")

    # Claim (i): exactly 2 classifiers in core.
    print("\n(i) Exactly 2 classifiers in core:")
    def neg_exactly2(s, T, sR, rR, is_cls):
        # core classifier count
        def is_core_cls(y):
            return And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        cls_count = sum([(is_core_cls(y)) for y in CORE])  # symbolic sum
        # Use Int: sum of 1s where classifier
        cls_ints = [Int(f"cls_{y}") for y in CORE]
        for i, y in enumerate(CORE):
            s.add(Or(And(is_core_cls(y), cls_ints[i] == 1),
                     And(Not(is_core_cls(y)), cls_ints[i] == 0)))
        total = sum(cls_ints)
        s.add(total != 2)
    test_claim("exactly 2 classifiers in core", neg_exactly2)

    # Claim (ii): s = r for any retraction pair.
    # We negate: there exists a valid retraction pair with s != r.
    # i.e., there exists s', r' in core distinct satisfying the retraction.
    # The base solver picks *a* retraction pair (sR, rR). We directly require
    # sR != rR (strong R) and check UNSAT.
    print("\n(ii) Strong R unsatisfiable (no retraction pair with s != r):")
    def neg_strong_R(s, T, sR, rR, is_cls):
        s.add(sR != rR)
    test_claim("strong R UNSAT at N=5", neg_strong_R)

    # Claim (iii): H triple has b = non-classifier and {a,c} = two classifiers.
    # Negate: some valid H triple has b classifier OR (a,c) not both classifiers.
    # Since the base solver picks some valid H triple existentially inside
    # its Or(*h_clauses), we rebuild with tracker variables aH, bH, cH.
    print("\n(iii) H triple: b is the non-classifier, {a,c} are the two classifiers:")
    def neg_h_structure(s, T, sR, rR, is_cls):
        aH = Int("aH")
        bH = Int("bH")
        cH = Int("cH")
        s.add(Or([aH == c for c in CORE]))
        s.add(Or([bH == c for c in CORE]))
        s.add(Or([cH == c for c in CORE]))
        s.add(aH != bH, aH != cH, bH != cH)

        # b must be core-preserving: T[b][x] in CORE for x in CORE
        def core_preserving(b_val):
            conj = []
            for x in CORE:
                conj.append(Or(*[T[b_val][x] == cc for cc in CORE]))
            return And(*conj)
        # b_closed for bH: encode as disjunction over bH=bv
        b_closed_choice = Or(*[And(bH == bv, core_preserving(bv)) for bv in CORE])
        s.add(b_closed_choice)

        # a(x) = c(b(x)) for x in core
        for x in CORE:
            # encode T[aH][x] via enumeration over aH
            # and T[cH][T[bH][x]] via double enumeration
            clauses = []
            for av in CORE:
                for bv in CORE:
                    for cv in CORE:
                        if av == bv or av == cv or bv == cv: continue
                        # T[bH][x] = T[bv][x], take as intermediate
                        for iv in range(N):
                            clauses.append(And(aH == av, bH == bv, cH == cv,
                                                T[bv][x] == iv,
                                                T[av][x] == T[cv][iv]))
            s.add(Or(*clauses))

        # a nontrivial on core
        a_nontriv_cases = []
        for av in CORE:
            diffs = Or(*[T[av][x1] != T[av][x2]
                          for x1, x2 in itertools.combinations(CORE, 2)])
            a_nontriv_cases.append(And(aH == av, diffs))
        s.add(Or(*a_nontriv_cases))

        # Negation of structure: NOT (b is non-classifier AND a,c are classifiers)
        # i.e., b is a classifier OR a is non-classifier OR c is non-classifier
        def is_core_cls_expr(y_val):
            return And(*[Or(T[y_val][x] == 0, T[y_val][x] == 1) for x in CORE])
        def bH_is_cls():
            return Or(*[And(bH == bv, is_core_cls_expr(bv)) for bv in CORE])
        def aH_not_cls():
            return Or(*[And(aH == av, Not(is_core_cls_expr(av))) for av in CORE])
        def cH_not_cls():
            return Or(*[And(cH == cv, Not(is_core_cls_expr(cv))) for cv in CORE])

        s.add(Or(bH_is_cls(), aH_not_cls(), cH_not_cls()))
    test_claim("H structure (b = non-cls, {a,c} = 2 classifiers)", neg_h_structure)

    print("\nDone.")


if __name__ == "__main__":
    main()
