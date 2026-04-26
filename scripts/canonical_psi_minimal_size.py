"""
Find the minimum N for canonical-witness + the *minimal* Lisp axiom set.

Drops all the decorative atomic axioms identified earlier:
  - Power-associativity (algebraic regularity, not evaluator-needed)
  - Y idempotent (atomic, not satisfied by Ψ-Lisp's own Y)
  - ρ_branch as a distinct element from ρ_swap (the σ-implementer can
    also serve as the branch primitive — same row, two roles)
  - Y as a distinct named element (recursion happens at term level)

Keeps only:
  - E2PM base (extensionality, 2 absorbers)
  - S + D + C (paper's structural axioms)
  - Indicator classifiers (canonical-witness P1)
  - Self-symmetric automorphism σ via ρ (canonical-witness P2; this ρ
    also serves as the branch primitive)
  - QE retraction (Q, E distinct, ∀x. E·(Q·x) = x — for homoiconicity)

So required distinct core elements:
  2 indicator classifiers (cls=2)
  ρ_swap (non-classifier, also branch primitive)
  Q (any class, distinct from E)
  E (any class, distinct from Q)

If Q, E are both non-classifiers (since indicator-style classifiers
have a fixed row pattern incompatible with QE retraction), then we
need 2 cls + 3 ncl = 5 core elements. Minimum N = 7.

If Q or E could be the same as another element... they can't (Q ≠ E is
required, and indicator classifiers have fixed rows preventing them
from being Q or E). So 5 core elements is a structural floor; N=7 is
the candidate.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def build_solver(N, constrain_R=None):
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
    return s, T, sR, rR, is_cls, CORE


def add_indicator_classifiers(s, T, is_cls, CORE):
    z1, z2 = 0, 1
    for tau in CORE:
        indicator_pattern = And(
            T[tau][z1] == z1, T[tau][z2] == z2, T[tau][tau] == z2,
            *[T[tau][x] == z1 for x in CORE if x != tau],
        )
        s.add(Or(Not(is_cls[tau]), indicator_pattern))


def add_self_symmetric_aut(s, T, N, CORE):
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


def add_QE(s, T, N, CORE):
    Q = Int("Q_atom"); E = Int("E_atom")
    s.add(Or([Q == c for c in CORE]))
    s.add(Or([E == c for c in CORE]))
    s.add(Q != E)
    for x in range(N):
        clauses = []
        for qv in CORE:
            for ev in CORE:
                if qv == ev: continue
                inner_cases = [And(T[qv][x] == iv, T[ev][iv] == x) for iv in range(N)]
                clauses.append(And(Q == qv, E == ev, Or(*inner_cases)))
        s.add(Or(*clauses))
    return Q, E


def query(N, time_budget=600):
    s, T, sR, rR, is_cls, CORE = build_solver(N, constrain_R=None)
    add_indicator_classifiers(s, T, is_cls, CORE)
    sigma, rho = add_self_symmetric_aut(s, T, N, CORE)
    Q, E = add_QE(s, T, N, CORE)
    s.set("timeout", int(time_budget * 1000))
    print(f"=== N={N} (minimal axioms) ===", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.2f}s] UNSAT")
        return False, None
    if res == sat:
        m = s.model()
        Q_v = m.eval(Q).as_long(); E_v = m.eval(E).as_long()
        rs = m.eval(rho).as_long()
        sigma_v = [m.eval(sigma[i]).as_long() for i in range(N)]
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        cls = [y for y in CORE if all(table[y][x] in (0, 1) for x in CORE)]
        ncl = [y for y in CORE if all(table[y][x] not in (0, 1) for x in CORE)]
        print(f"  [{dt:.2f}s] SAT  Q={Q_v}, E={E_v}, ρ_swap={rs}, σ={sigma_v}")
        print(f"    cls={cls}, ncl={ncl}")
        for row in table:
            print(f"    {row}")
        return True, {"table": table, "Q": Q_v, "E": E_v,
                       "rho_swap": rs, "sigma": sigma_v,
                       "cls": cls, "ncl": ncl}
    print(f"  [{dt:.2f}s] UNKNOWN/timeout")
    return None, None


def main():
    print("Minimum N for canonical-witness + minimal Lisp atomic axioms")
    print("(QE only; Y, PA, ρ_branch dropped as decorative)")
    print()
    results = {}
    for N in (6, 7, 8):
        sat_, info = query(N)
        results[N] = {"sat": sat_, "info": info}
        print()
    out = os.path.join(SCRIPT_DIR, "canonical_psi_minimal_size_result.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
