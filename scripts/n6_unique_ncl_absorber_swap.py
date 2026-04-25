"""
Refined N=6 mirror-row question: if a N=6 S+D+C magma has unique
non-classifier in core (role-shape cls=3, ncl=1), does mirror-row
absorber-fixing hold?

Background. The N=5 mirror-row theorem (paper Thm 4.13) leans on
uniqueness of the non-classifier: Lemma B's proof concludes g·g = g
because g·g must be σ-fixed and the only σ-fixed core element (when σ
swaps classifiers) is the unique non-classifier. At N=6 with multiple
non-classifiers, σ can fix several core elements and the argument
fails — confirmed empirically by n6_absorber_swap_search.py (both
strong and weak S counterexamples found in the 2-non-classifier shape).

The natural refinement: enforce role-shape (3 classifiers, 1
non-classifier) at N=6 and ask whether absorber-swap automorphisms still
exist.

If UNSAT: mirror-row absorber-fixing generalises to "single
non-classifier" S+D+C magmas at any N where this shape occurs (forced
at N=5; possible at N≥6 within a sub-shape).

If SAT: mirror-row is genuinely N=5-specific even relative to the
single-non-classifier shape.
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


def build_solver(constrain_R, k_classifiers):
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

    # Constrain exactly k_classifiers in core.
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


def add_absorber_swap_aut(s, T):
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


def query(constrain_R):
    s, T, sR, rR = build_solver(constrain_R, k_classifiers=3)
    sigma = add_absorber_swap_aut(s, T)
    print(f"=== N=6, k_classifiers=3, R={constrain_R}, σ(0)=1 ===")
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.2f}s] UNSAT — no absorber-swap aut in shape (cls=3, ncl=1) at N=6.")
        return False, None
    elif res == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sigma_val = [m.eval(sigma[i]).as_long() for i in range(N)]
        sR_val = m.eval(sR).as_long()
        rR_val = m.eval(rR).as_long()
        print(f"  [{dt:.2f}s] SAT — example exists.")
        print(f"  Cayley table:")
        for row in table:
            print(f"    {row}")
        print(f"  σ = {sigma_val}")
        print(f"  Retraction: sR={sR_val}, rR={rR_val}")
        return True, {"table": table, "sigma": sigma_val, "sR": sR_val, "rR": rR_val}
    else:
        print(f"  [{dt:.2f}s] UNKNOWN")
        return None, None


def main():
    print("Refined mirror-row question at N=6 (cls=3, ncl=1):")
    print("does enforcing unique non-classifier rule out absorber-swap auts?")
    print()
    results = {}
    sat_strong, ex_strong = query("strong")
    print()
    sat_weak, ex_weak = query("weak")
    print()
    sat_any, ex_any = query(None)
    print()
    results["strong"] = {"sat": sat_strong, "example": ex_strong}
    results["weak"] = {"sat": sat_weak, "example": ex_weak}
    results["any"] = {"sat": sat_any, "example": ex_any}

    print("=== Summary ===")
    if not (sat_strong or sat_weak or sat_any):
        print("  Mirror-row absorber-fixing extends to N=6 with unique non-classifier.")
    else:
        flagged = [k for k, v in results.items() if v["sat"]]
        print(f"  Mirror-row absorber-fixing FAILS at N=6 even with unique non-classifier "
              f"(in regimes: {flagged}).")

    out = os.path.join(SCRIPT_DIR, "n6_unique_ncl_absorber_swap_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
