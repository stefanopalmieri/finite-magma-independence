"""
Verify candidate N=6 structure theorems for strong-R + D + H magmas.

From enumeration (scripts/enumerate_rdh_iso_N6_strongR.json, 500 classes
enumerated, all rigid):
  - every class has exactly 1 classifier in core (and hence 3 non-classifiers)
  - H_triple_count is 2 or 6 (499 classes: 6; 1 class: 2)

From the N=5 structure theorem (enumerate_rdh_iso_N5.json, 500 classes) we
had 2 classifiers + 1 non-classifier.  The ratio flips between N=5 and N=6.

Claims verified here by Z3 UNSAT of the negation:

  (N6.i)   every strong-R + D + H magma at N=6 has exactly 1 core classifier.
  (N6.ii)  every strong-R + D + H magma at N=6 has ≥ 2 H-triples.
  (N6.iii) every strong-R + D + H magma at N=6 has ≥ 6 H-triples OR has
           a core element acting as identity on some 2-element core subset.
           (a way to separate the "1 special class" from the rest).

(N6.iii) is a probe — unlikely to resolve UNSAT, but the resolution is
informative.
"""

from __future__ import annotations

import itertools
import time

from z3 import And, BoolVal, Distinct, Int, Not, Or, Solver, sat, unknown, unsat


N = 6
CORE = list(range(2, N))
TIMEOUT_MS = 300_000


def make_solver():
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    return s


def base_solver():
    """E2PM + strong R + D + H at N=6, with named tracker vars sR, rR."""
    s = make_solver()
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

    # strong R
    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if sv == rv:
                    continue
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx))
        s.add(Or(srx))

    # D
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

    # H
    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))

    return s, T, sR, rR, is_cls


def is_core_cls_expr(T, y):
    return And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])


def count_H_triples(T):
    """Return a Z3 expression counting the number of (a,b,c) ∈ core^3 distinct
    that form H-triples."""
    count = 0
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        is_triple = And(b_closed, And(*eqs), Or(*diffs))
        count = count + is_triple  # Z3 auto-converts Bool to 0/1 via If? No.
    return count


def test_claim(label, add_negation):
    s, T, sR, rR, is_cls = base_solver()
    add_negation(s, T, sR, rR, is_cls)
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == unsat:
        print(f"  [{dt:6.2f}s] UNSAT -- claim '{label}' holds")
        return True
    elif r == sat:
        m = s.model()
        print(f"  [{dt:6.2f}s] SAT   -- claim '{label}' FAILS. Counterexample:")
        for a in range(N):
            print("    " + " ".join(str(m.eval(T[a][b]).as_long()) for b in range(N)))
        return False
    else:
        print(f"  [{dt:6.2f}s] UNKNOWN for claim '{label}'")
        return False


def neg_exactly_1_classifier(s, T, sR, rR, is_cls):
    cls_ints = [Int(f"cls_{y}") for y in CORE]
    for i, y in enumerate(CORE):
        icls = is_core_cls_expr(T, y)
        s.add(Or(And(icls, cls_ints[i] == 1),
                 And(Not(icls), cls_ints[i] == 0)))
    total = sum(cls_ints)
    s.add(total != 1)


def neg_at_least_2_H_triples(s, T, sR, rR, is_cls):
    """Negation: at most 1 H-triple exists."""
    triple_ints = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        is_triple = And(b_closed, And(*eqs), Or(*diffs))
        ti = Int(f"h_{a}_{b}_{c}")
        s.add(Or(And(is_triple, ti == 1), And(Not(is_triple), ti == 0)))
        triple_ints.append(ti)
    total = sum(triple_ints)
    s.add(total < 2)


def neg_at_least_6_H_triples_or_has_order2_symmetry(s, T, sR, rR, is_cls):
    """Negation: (# H-triples < 6) AND (no 'symmetry' of the form described).
    For a probe, we take 'symmetry' = ∃ core element that acts as identity
    on a 2-element core subset (i.e., ∃ y, x1 ≠ x2 in core with y*x1 = x1
    and y*x2 = x2). This is a guess; may not resolve cleanly."""
    triple_ints = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
            eqs.append(Or(*cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        is_triple = And(b_closed, And(*eqs), Or(*diffs))
        ti = Int(f"h_{a}_{b}_{c}")
        s.add(Or(And(is_triple, ti == 1), And(Not(is_triple), ti == 0)))
        triple_ints.append(ti)
    total = sum(triple_ints)
    # Negation: <6 H-triples AND no 2-fixed-point-on-core element
    fixed_pair = Or(*[
        And(T[y][x1] == x1, T[y][x2] == x2)
        for y in CORE
        for x1, x2 in itertools.combinations(CORE, 2)
    ])
    s.add(total < 6)
    s.add(Not(fixed_pair))


def main():
    print("=" * 72)
    print("N=6 Structure Theorem (strong-R + D + H) verification")
    print("=" * 72)

    print("\n(N6.i) Every strong-R+D+H magma at N=6 has exactly 1 core classifier:")
    test_claim("exactly 1 classifier in core", neg_exactly_1_classifier)

    print("\n(N6.ii) Every strong-R+D+H magma at N=6 has ≥ 2 H-triples:")
    test_claim("at least 2 H-triples", neg_at_least_2_H_triples)

    print("\n(N6.ii') Every strong-R+D+H magma at N=6 has ≥ 3 H-triples:")
    def neg_geq_3(s, T, sR, rR, is_cls):
        triple_ints = []
        for a, b, c in itertools.permutations(CORE, 3):
            b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
            eqs = []
            for x in CORE:
                cases = [And(T[b][x] == iv, T[a][x] == T[c][iv]) for iv in range(N)]
                eqs.append(Or(*cases))
            diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
            is_triple = And(b_closed, And(*eqs), Or(*diffs))
            ti = Int(f"h_{a}_{b}_{c}_g3")
            s.add(Or(And(is_triple, ti == 1), And(Not(is_triple), ti == 0)))
            triple_ints.append(ti)
        s.add(sum(triple_ints) < 3)
    test_claim("at least 3 H-triples", neg_geq_3)

    print("\n(N6.iii probe) ≥ 6 H-triples OR ∃ core element fixing 2 core points:")
    test_claim("≥ 6 H-triples or 2-fixed-point-element", neg_at_least_6_H_triples_or_has_order2_symmetry)


if __name__ == "__main__":
    main()
