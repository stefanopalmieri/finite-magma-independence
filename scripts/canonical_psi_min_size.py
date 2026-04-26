"""
Find the minimum N at which canonical-witness + Lisp-style atomic axioms
(step 5: QE retraction + Y-idempotent + ρ-branch + power-associativity)
is SAT.

Counting argument: the axioms require at least 5 distinct core elements
(σ-implementer ρ_swap, Q, E, Y, ρ_branch). At N=5 |core|=3, at N=6
|core|=4, so SAT is structurally impossible until N=7 (|core|=5).
This script verifies: at N=6 UNSAT, at N=7+ likely SAT.
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


def add_QE_distinct(s, Q, E, rho):
    s.add(Q != rho); s.add(E != rho)


def add_Y_idempotent(s, T, Q, E, rho, CORE):
    Y = Int("Y_atom")
    s.add(Or([Y == c for c in CORE]))
    s.add(Y != Q); s.add(Y != E); s.add(Y != rho)
    clauses = []
    for yv in CORE:
        clauses.append(And(Y == yv, T[yv][yv] == yv))
    s.add(Or(*clauses))
    return Y


def add_rho_branch(s, T, is_cls, Q, E, rho_swap, Y, CORE):
    rho_branch = Int("rho_branch")
    s.add(Or([rho_branch == c for c in CORE]))
    s.add(rho_branch != Q); s.add(rho_branch != E)
    s.add(rho_branch != rho_swap); s.add(rho_branch != Y)
    not_cls_clauses = []
    for rv in CORE:
        not_cls_clauses.append(And(rho_branch == rv, Not(is_cls[rv])))
    s.add(Or(*not_cls_clauses))
    return rho_branch


def add_power_associativity(s, T, N):
    for a in range(N):
        clauses = []
        for v in range(N):
            clauses.append(And(T[a][a] == v, T[a][v] == T[v][a]))
        s.add(Or(*clauses))


def query(N, time_budget=600):
    s, T, sR, rR, is_cls, CORE = build_solver(N, constrain_R=None)
    add_indicator_classifiers(s, T, is_cls, CORE)
    sigma, rho = add_self_symmetric_aut(s, T, N, CORE)
    Q, E = add_QE(s, T, N, CORE)
    add_QE_distinct(s, Q, E, rho)
    Y = add_Y_idempotent(s, T, Q, E, rho, CORE)
    rho_branch = add_rho_branch(s, T, is_cls, Q, E, rho, Y, CORE)
    add_power_associativity(s, T, N)
    s.set("timeout", int(time_budget * 1000))
    print(f"=== N={N} (step-5 axioms) ===", flush=True)
    t0 = time.time()
    res = s.check()
    dt = time.time() - t0
    if res == unsat:
        print(f"  [{dt:.1f}s] UNSAT")
        return False
    if res == sat:
        m = s.model()
        Q_v = m.eval(Q).as_long(); E_v = m.eval(E).as_long()
        Y_v = m.eval(Y).as_long(); rb = m.eval(rho_branch).as_long()
        rs = m.eval(rho).as_long()
        sigma_v = [m.eval(sigma[i]).as_long() for i in range(N)]
        print(f"  [{dt:.1f}s] SAT  Q={Q_v}, E={E_v}, Y={Y_v}, "
              f"ρ_branch={rb}, ρ_swap={rs}, σ={sigma_v}")
        return True
    print(f"  [{dt:.1f}s] UNKNOWN/timeout")
    return None


def main():
    print("Finding minimum N for canonical-witness + Lisp atomic axioms (step 5)")
    print()
    results = {}
    for N in range(6, 12):
        results[N] = query(N)
        print()
    print("=== Summary ===")
    for N, sat_ in results.items():
        print(f"  N={N}: {'SAT' if sat_ else 'UNSAT' if sat_ is False else 'unknown'}")
    out = os.path.join(SCRIPT_DIR, "canonical_psi_min_size_result.json")
    with open(out, "w") as f:
        json.dump({k: ("SAT" if v else "UNSAT" if v is False else "unknown")
                   for k, v in results.items()}, f, indent=2)
    print(f"\nWrote {out}")


if __name__ == "__main__":
    main()
