"""
N=6 automorphism-internalisation (self-symmetric) search.

A magma M is **automorphism-internalising** (or "self-symmetric") if for
every non-trivial automorphism σ ∈ Aut(M), there exists ρ ∈ M with
σ(x) = ρ · x for all x ∈ core.

The N=5 canonical witness (paper Remark 4.X) is automorphism-internalising:
the swap σ = (τ₁ τ₂) is realised by ρ = g (the non-classifier).

Question for this script: does any N=6 S+D+C magma have a non-trivial
automorphism σ realised by left-multiplication by some element?

Z3 query: ∃ S+D+C magma M on Fin(6), ∃ non-trivial σ ∈ Equiv.Perm(Fin 6)
that is a magma homomorphism, ∃ ρ ∈ Fin(6) such that for all x in core,
T[ρ][x] = σ(x).

(ρ must be in core: σ permutes core so σ|core is non-constant, but a
left-absorber's row is constant. So ρ ∈ core.)

If SAT: N=6 self-symmetric S+D+C magma exists. Mirror-row's
automorphism-internalisation property generalises.

If UNSAT: the property is N=5-specific. Mirror-row's
automorphism-internalisation is the unique-non-classifier phenomenon at
its sharpest size.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat

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

    return s, T, sR, rR


def add_self_symmetric_aut(s, T):
    """Add a non-trivial automorphism σ AND ρ ∈ core with ρ·x = σ(x) on core."""
    sigma = [Int(f"sigma_{i}") for i in range(N)]
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    s.add(Distinct(*sigma))
    # σ is non-trivial.
    s.add(Or(*[sigma[i] != i for i in range(N)]))
    # σ is a magma homomorphism.
    for a in range(N):
        for b in range(N):
            big = []
            for sa in range(N):
                for sb in range(N):
                    for tab in range(N):
                        big.append(And(sigma[a] == sa, sigma[b] == sb,
                                        T[a][b] == tab, sigma[tab] == T[sa][sb]))
            s.add(Or(*big))
    # ρ ∈ core, and T[ρ][x] = σ(x) for x ∈ core.
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
    s, T, sR, rR = build_solver(constrain_R)
    sigma, rho = add_self_symmetric_aut(s, T)
    s.set("timeout", int(time_budget * 1000))
    print(f"=== {label}: N=6 S+D+C, R={constrain_R}, "
          f"non-trivial σ realised by left-mult by ρ on core ===", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.2f}s] UNSAT — no self-symmetric S+D+C magma at N=6.")
        return False, None
    if res == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sigma_val = [m.eval(sigma[i]).as_long() for i in range(N)]
        rho_val = m.eval(rho).as_long()
        sR_val = m.eval(sR).as_long()
        rR_val = m.eval(rR).as_long()
        print(f"  [{dt:.2f}s] SAT — self-symmetric witness found.")
        print(f"  Cayley table:")
        for row in table:
            print(f"    {row}")
        print(f"  σ = {sigma_val}")
        print(f"  ρ = {rho_val} (its row on core: "
              f"{[table[rho_val][x] for x in CORE]})")
        print(f"  σ on core: {[sigma_val[x] for x in CORE]}")
        print(f"  Retraction: sR={sR_val}, rR={rR_val}")
        return True, {"table": table, "sigma": sigma_val, "rho": rho_val,
                       "sR": sR_val, "rR": rR_val}
    print(f"  [{dt:.2f}s] UNKNOWN/timeout")
    return None, None


def main():
    print("N=6 automorphism-internalisation search:")
    print("does any N=6 S+D+C magma realise its non-trivial automorphism")
    print("via left-multiplication by an element of itself?")
    print()
    results = {}
    for R in (None, "strong", "weak"):
        label = f"R={R or 'any'}"
        sat_, ex = query(label, R)
        results[R or "any"] = {"sat": sat_, "example": ex}
        print()
    print("=== Summary ===")
    any_sat = any(v["sat"] for v in results.values())
    if any_sat:
        regimes = [k for k, v in results.items() if v["sat"]]
        print(f"  Self-symmetric S+D+C magmas exist at N=6 in regimes: {regimes}.")
        print(f"  The N=5 automorphism-internalisation principle generalises.")
    else:
        print("  No self-symmetric S+D+C magma at N=6 in any R regime.")
        print("  The N=5 canonical-witness principle is N=5-specific.")
    out = os.path.join(SCRIPT_DIR, "n6_self_symmetric_search_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()
