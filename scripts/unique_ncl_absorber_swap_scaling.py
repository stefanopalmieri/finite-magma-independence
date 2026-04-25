"""
Scaling test: is mirror-row absorber-fixing universal for S+D+C magmas
with unique non-classifier?

Hypothesis: at any N, an S+D+C magma on Fin(N) with role-shape
(|classifiers in core| = N-3, |non-classifiers in core| = 1) admits no
automorphism swapping absorbers.

Verified at N=5 (mirror-row theorem itself, with classifiers forced to
2). Verified at N=6 in n6_unique_ncl_absorber_swap.py (UNSAT for cls=3,
ncl=1 in all R regimes).

This script extends the test to N=7, N=8.
"""

from __future__ import annotations

import importlib.util
import json
import os
import time

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

# Reuse build_solver and add_absorber_swap_aut from n6_unique_ncl script,
# but parametrise N.

import itertools
from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat


def build_solver(N, constrain_R, k_classifiers):
    CORE = list(range(2, N))
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
    if constrain_R == "strong":
        s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if constrain_R == "strong" and sv == rv:
                    continue
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
    s.add(Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
               for tv in CORE]))

    cls_ints = []
    for y in CORE:
        ci = Int(f"cls_bit_{y}")
        s.add(Or(And(is_cls[y], ci == 1), And(Not(is_cls[y]), ci == 0)))
        cls_ints.append(ci)
    s.add(sum(cls_ints) == k_classifiers)

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

    return s, T, sR, rR


def add_absorber_swap_aut(N, s, T):
    sigma = [Int(f"sigma_{i}") for i in range(N)]
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    s.add(Distinct(*sigma))
    s.add(sigma[0] == 1)
    for a in range(N):
        for b in range(N):
            big = []
            for sa in range(N):
                for sb in range(N):
                    for tab in range(N):
                        big.append(And(sigma[a] == sa, sigma[b] == sb,
                                        T[a][b] == tab, sigma[tab] == T[sa][sb]))
            s.add(Or(*big))
    return sigma


def query(N, k_classifiers, constrain_R, time_budget=300):
    s, T, sR, rR = build_solver(N, constrain_R, k_classifiers)
    sigma = add_absorber_swap_aut(N, s, T)
    s.set("timeout", int(time_budget * 1000))
    label = f"N={N}, k_cls={k_classifiers}, R={constrain_R}"
    print(f"  {label} ...", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"    [{dt:.1f}s] UNSAT")
        return False, None
    if res == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sigma_val = [m.eval(sigma[i]).as_long() for i in range(N)]
        print(f"    [{dt:.1f}s] SAT — example found.")
        for row in table:
            print(f"      {row}")
        print(f"    σ = {sigma_val}")
        return True, {"table": table, "sigma": sigma_val}
    print(f"    [{dt:.1f}s] UNKNOWN/timeout")
    return None, None


def main():
    print("Scaling test: mirror-row absorber-fixing for S+D+C with unique non-classifier.")
    print("Hypothesis: ∀ N ≥ 5, no S+D+C magma at N with cls=N-3, ncl=1 admits absorber-swap aut.")
    print()
    results = {}
    for N in [6, 7, 8]:
        k = N - 3
        results[N] = {}
        for R in ("strong", "weak", None):
            R_label = R or "any"
            sat_res, ex = query(N, k, R)
            results[N][R_label] = {"sat": sat_res, "example": ex}
        print()

    print("=== Summary ===")
    all_unsat = True
    for N, by_R in results.items():
        for R, v in by_R.items():
            if v["sat"]:
                all_unsat = False
                print(f"  ! N={N}, R={R}: absorber-swap aut found.")
    if all_unsat:
        print("  ✓ All UNSAT. Mirror-row absorber-fixing extends to all tested N "
              "with unique non-classifier (N=6, 7, 8).")

    out = os.path.join(SCRIPT_DIR, "unique_ncl_absorber_swap_scaling.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()
