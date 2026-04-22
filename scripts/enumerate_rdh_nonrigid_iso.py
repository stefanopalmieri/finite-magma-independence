"""
Enumerate NON-RIGID R+D+H iso classes at N under strong R.

Extends enumerate_rdh_iso.py by adding a symbolic non-trivial automorphism
sigma to the base solver. Each iteration returns one non-rigid iso class.
Block the orbit, repeat until UNSAT.

The goal is to bound the number of non-rigid iso classes at N=6 strong-R.

Usage: python3 enumerate_rdh_nonrigid_iso.py <N> [--limit K]
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
import time

from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


def apply_perm(table, sigma, N):
    inv = [0] * N
    for i, si in enumerate(sigma): inv[si] = i
    return [[sigma[table[inv[a]][inv[b]]] for b in range(N)] for a in range(N)]


def iso_orbit(table, N):
    orbit = set()
    core = list(range(2, N))
    for ap in itertools.permutations([0, 1]):
        for cp in itertools.permutations(core):
            sig = list(ap) + list(cp)
            img = apply_perm(table, sig, N)
            orbit.add(tuple(tuple(r) for r in img))
    return orbit


def automorphisms(table, N):
    auts = []
    for sigma in itertools.permutations(range(N)):
        if all(sigma[table[a][b]] == table[sigma[a]][sigma[b]]
               for a in range(N) for b in range(N)):
            auts.append(sigma)
    return auts


def canonical_form(orbit):
    flat = lambda t: tuple(v for row in t for v in row)
    return min(orbit, key=flat)


def build_solver(N):
    CORE = list(range(2, N))
    s = Solver()

    T = [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]
    for a in range(N):
        for b in range(N):
            s.add(T[a][b] >= 0, T[a][b] < N)
    for x in range(N):
        s.add(T[0][x] == 0); s.add(T[1][x] == 1)
    for y in CORE:
        s.add(Or([T[y][x] != y for x in range(N)]))

    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw; pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))

    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if sv == rv: continue
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx)); s.add(Or(srx))

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

    # Non-trivial automorphism sigma.
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

    return s, T, sigma, sR, rR


def run(N, limit=None):
    CORE = list(range(2, N))
    t0 = time.time()
    s, T, sigma, sR, rR = build_solver(N)
    print(f"=== Non-rigid R+D+H iso classes at N={N} strong-R ===")
    print(f"(setup: {time.time()-t0:.2f}s)")

    classes = []
    iteration = 0
    while True:
        iteration += 1
        ts = time.time()
        result = s.check()
        dt = time.time() - ts
        if result == unsat:
            print(f"[{iteration}] UNSAT after {dt:.2f}s. "
                  f"Total non-rigid iso classes: {len(classes)}.")
            break
        if result != sat:
            print(f"[{iteration}] unknown; stopping."); break

        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sig = [m.eval(sigma[i]).as_long() for i in range(N)]
        s_val = m.eval(sR).as_long(); r_val = m.eval(rR).as_long()

        orbit = iso_orbit(table, N)
        canon = canonical_form(orbit)
        canon_list = [list(r) for r in canon]
        auts = automorphisms(canon_list, N)
        assert len(auts) > 1, f"Z3 claimed non-rigid but |Aut|={len(auts)}"

        for img in orbit:
            s.add(Or(*[T[a][b] != img[a][b]
                        for a in range(N) for b in range(N)]))

        entry = {
            "iso_class": len(classes) + 1,
            "canonical": canon_list,
            "aut_order": len(auts),
            "orbit_size": len(orbit),
            "automorphisms": [list(a_) for a_ in auts],
            "sample_sigma": sig,
            "sample_R": {"s": s_val, "r": r_val},
        }
        classes.append(entry)
        print(f"[{iteration}] non-rigid class #{len(classes)}: "
              f"|Aut|={len(auts)} |orbit|={len(orbit)} "
              f"sigma={sig} ({dt:.2f}s)")

        if limit and len(classes) >= limit:
            print(f"Reached limit {limit}."); break

    out = os.path.join(SCRIPT_DIR, f"enumerate_rdh_nonrigid_N{N}_strongR.json")
    with open(out, "w") as f:
        json.dump({"N": N, "strong_R": True,
                   "total_nonrigid_iso_classes": len(classes),
                   "iso_classes": classes,
                   "runtime_seconds": time.time() - t0}, f, indent=2)
    print(f"Wrote {out}")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("N", type=int)
    ap.add_argument("--limit", type=int, default=None)
    args = ap.parse_args()
    run(args.N, args.limit)
