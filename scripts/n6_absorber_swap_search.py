"""
N=6 absorber-swap search: does any S+D+C magma at N=6 admit an
automorphism σ with σ(z₁) = z₂?

The N=5 mirror-row theorem (paper Thm 4.13) says no automorphism of an
N=5 S+D+C magma can swap absorbers. The paper's prop:N6-nonrigid notes
that AT N=8 under strong S an absorber-swap automorphism exists. The
question here: what happens at N=6?

This script poses three Z3 queries:

  Q1. Any S+D+C magma at N=6 with σ(0) = 1, σ a homomorphism (i.e.,
      a Cayley-table automorphism), σ a permutation. (No restriction
      on whether s = r.)
  Q2. Same, but with the strong-S restriction s ≠ r.
  Q3. Same, but explicitly requiring s = r (weak / non-strong S).

Q1 = Q2 ∨ Q3. If Q1 is UNSAT we have a clean theorem extending mirror-row
to N=6. If Q1 is SAT we examine the example and refine.
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


def build_sdc_solver(constrain_R=None):
    """Build Z3 solver encoding S+D+C on Fin(N). constrain_R is one of
    None (no restriction beyond S), 'strong' (sR != rR), 'weak' (sR == rR)."""
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

    # Extensionality.
    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw
            pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))

    # Retraction pair.
    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    if constrain_R == "strong":
        s.add(sR != rR)
    elif constrain_R == "weak":
        s.add(sR == rR)
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

    # D: classifier dichotomy.
    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    s.add(Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
               for tv in CORE]))

    # C: ICP triple.
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


def add_absorber_swap_automorphism(s, T):
    """Add an automorphism σ : Fin(N) → Fin(N) with σ(0) = 1."""
    sigma = [Int(f"sigma_{i}") for i in range(N)]
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    s.add(Distinct(*sigma))
    # σ(0) = 1: the absorber-swap.
    s.add(sigma[0] == 1)
    # σ is a homomorphism: σ(T[a][b]) = T[σ(a)][σ(b)].
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


def query(label, constrain_R):
    s, T, sR, rR = build_sdc_solver(constrain_R)
    sigma = add_absorber_swap_automorphism(s, T)
    print(f"=== Query {label}: N=6 S+D+C with absorber-swap aut, "
          f"R-constraint={constrain_R} ===")
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.1f}s] UNSAT — no such magma exists.")
        return False, None
    elif res == sat:
        print(f"  [{dt:.1f}s] SAT — absorber-swap aut exists at N=6.")
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sigma_val = [m.eval(sigma[i]).as_long() for i in range(N)]
        sR_val = m.eval(sR).as_long()
        rR_val = m.eval(rR).as_long()
        print(f"  Cayley table:")
        for row in table:
            print(f"    {row}")
        print(f"  σ = {sigma_val}")
        print(f"  Retraction: sR={sR_val}, rR={rR_val}")
        return True, {"table": table, "sigma": sigma_val, "sR": sR_val, "rR": rR_val}
    else:
        print(f"  [{dt:.1f}s] UNKNOWN")
        return None, None


def main():
    print("Goal: extend mirror-row absorber-fixing to N=6, or find a counterexample.")
    print()

    results = {}
    # Run the strong-R query first — fastest to either confirm or refute.
    sat_strong, ex_strong = query("Q2 strong-S", "strong")
    results["strong"] = {"sat": sat_strong, "example": ex_strong}
    print()
    sat_weak, ex_weak = query("Q3 weak-S (s = r)", "weak")
    results["weak"] = {"sat": sat_weak, "example": ex_weak}
    print()

    print("=== Summary ===")
    if sat_strong:
        print(f"  Strong S: absorber-swap aut EXISTS at N=6. "
              f"Mirror-row absorber-fixing fails at N=6 under strong S.")
    else:
        print(f"  Strong S: no absorber-swap aut. "
              f"Mirror-row absorber-fixing extends to N=6 strong S.")
    if sat_weak:
        print(f"  Weak S: absorber-swap aut EXISTS at N=6. "
              f"Mirror-row absorber-fixing fails at N=6 under weak S.")
    else:
        print(f"  Weak S: no absorber-swap aut. "
              f"Mirror-row absorber-fixing extends to N=6 weak S.")
    print()

    # Save results.
    out = os.path.join(SCRIPT_DIR, "n6_absorber_swap_search_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
