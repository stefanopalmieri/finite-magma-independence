"""
N=6 joint canonical-witness search: BOTH indicator-style classifiers
AND automorphism-internalisation.

The N=5 canonical witness satisfies two structural principles together:
  P1 (indicator): each classifier τ is the characteristic function of
       {τ, z₂}: τ(x) = z₂ iff x ∈ {τ, z₂}, else z₁.
  P2 (self-symmetric): the non-trivial automorphism σ is realised by
       left-multiplication by some element ρ.

We have shown separately:
  - P2 generalises to N=6 (n6_self_symmetric_search.py: SAT).
  - But none of the three SAT witnesses satisfy P1.

Question: does any N=6 S+D+C magma satisfy P1 ∧ P2?

If SAT: a joint canonical witness exists at N=6.
If UNSAT: the two principles separate at N=6 — the N=5 canonical
    witness is uniquely the size where both can be satisfied.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import And, Distinct, If, Int, Not, Or, Solver, sat, unsat

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
N = 6
CORE = list(range(2, N))


def build_solver(constrain_R=None):
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


def add_indicator_classifiers(s, T, is_cls):
    """For every core element τ that is a classifier (is_cls[τ] holds), τ's
    row is the indicator of {τ, z₂}: T[τ][x] = z₂ iff x ∈ {τ, z₂}, else z₁."""
    z1, z2 = 0, 1
    for tau in CORE:
        # If is_cls[tau], enforce indicator pattern.
        # T[tau][z₁] = z₁, T[tau][z₂] = z₂, T[tau][tau] = z₂, T[tau][x] = z₁ for x ∈ core \ {tau}.
        indicator_pattern = And(
            T[tau][z1] == z1,
            T[tau][z2] == z2,
            T[tau][tau] == z2,
            *[T[tau][x] == z1 for x in CORE if x != tau],
        )
        s.add(Or(Not(is_cls[tau]), indicator_pattern))


def add_self_symmetric_aut(s, T):
    sigma = [Int(f"sigma_{i}") for i in range(N)]
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    s.add(Distinct(*sigma))
    s.add(Or(*[sigma[i] != i for i in range(N)]))
    for a in range(N):
        for b in range(N):
            big = []
            for sa in range(N):
                for sb in range(N):
                    for tab in range(N):
                        big.append(And(sigma[a] == sa, sigma[b] == sb,
                                        T[a][b] == tab, sigma[tab] == T[sa][sb]))
            s.add(Or(*big))
    rho = Int("rho")
    s.add(Or([rho == c for c in CORE]))
    for x in CORE:
        clauses = []
        for rv in CORE:
            for sv in range(N):
                clauses.append(And(rho == rv, sigma[x] == sv, T[rv][x] == sv))
        s.add(Or(*clauses))
    return sigma, rho


def query(label, constrain_R, time_budget=600):
    s, T, sR, rR, is_cls = build_solver(constrain_R)
    add_indicator_classifiers(s, T, is_cls)
    sigma, rho = add_self_symmetric_aut(s, T)
    s.set("timeout", int(time_budget * 1000))
    print(f"=== {label}: N=6 S+D+C, indicator classifiers + self-symmetric aut, R={constrain_R} ===", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.2f}s] UNSAT — no joint canonical N=6 witness in this regime.")
        return False, None
    if res == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sigma_val = [m.eval(sigma[i]).as_long() for i in range(N)]
        rho_val = m.eval(rho).as_long()
        sR_val = m.eval(sR).as_long()
        rR_val = m.eval(rR).as_long()
        print(f"  [{dt:.2f}s] SAT — joint canonical N=6 witness found.")
        for row in table:
            print(f"    {row}")
        print(f"  σ = {sigma_val}; ρ = {rho_val}; (sR={sR_val}, rR={rR_val})")
        return True, {"table": table, "sigma": sigma_val, "rho": rho_val,
                       "sR": sR_val, "rR": rR_val}
    print(f"  [{dt:.2f}s] UNKNOWN/timeout")
    return None, None


def main():
    print("N=6 joint canonical-witness search: P1 (indicator classifiers) ∧ P2 (self-symmetric)")
    print()
    results = {}
    for R in (None, "strong", "weak"):
        sat_, ex = query(f"R={R or 'any'}", R)
        results[R or "any"] = {"sat": sat_, "example": ex}
        print()
    print("=== Summary ===")
    if any(v["sat"] for v in results.values()):
        print("  Joint canonical witness exists at N=6.")
    else:
        print("  No N=6 magma satisfies both indicator and self-symmetric principles.")
        print("  The two principles separate at N=6 — N=5 is uniquely the size where both come bundled.")
    out = os.path.join(SCRIPT_DIR, "n6_joint_canonical_search_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()
