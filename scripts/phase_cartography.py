"""
Phase-transition cartography for S+D+C magmas.

Enumerates S+D+C magmas up to absorber-preserving isomorphism at each N,
recording the role-shape features that characterize the 'role landscape':

  - |Aut(M)|                      : full automorphism group order
  - core_cls_count                : # core classifiers
  - core_noncls_count             : # core non-classifiers
  - full_classifier_count         : # elements that are *full* classifiers
                                    (map all of Fin(N) into {z1,z2}, not just
                                    core inputs)
  - retr_pair_count               : # retraction pairs (s,r) in core with the
                                    retraction identities and r·z1=z1
  - strong_R_available            : bool: ∃ retraction pair with s ≠ r
  - H_triple_count                : # ICP witness triples

Purpose: find out whether the N=5→N=6 phase transition is unique, or whether
further sub-transitions appear as N grows (N=7, N=8, ...).

Usage:
    python3 phase_cartography.py <N> [--limit K] [--time T]

Writes phase_cartography_N<N>.json with per-class shape features and a
distribution summary.
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
import time
from collections import Counter, defaultdict
from z3 import And, Distinct, Int, Not, Or, Solver, sat, unsat

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


# ---------------------------------------------------------------------------
# Z3 solver encoding S+D+C on Fin(N) with absorbers {0,1}.
# (Same as enumerate_rdh_iso.build_base_solver with strong_R=False.)
# ---------------------------------------------------------------------------

def build_solver(N):
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

    # Retraction pair (weak S: s may equal r).
    sR, rR = Int("sR"), Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                rs_cases = [And(T[sv][x] == iv, T[rv][iv] == x) for iv in range(N)]
                sr_cases = [And(T[rv][x] == iv, T[sv][iv] == x) for iv in range(N)]
                rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(rsx))
        s.add(Or(srx))

    # D: every core row is all-in or all-out of {0,1}; some non-classifier; a
    # full classifier exists.
    is_core_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_core_cls[y] = all_in
    s.add(Or(*[Not(is_core_cls[y]) for y in CORE]))
    s.add(Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
               for tv in CORE]))

    # C: an ICP triple (a,b,c) with b core-preserving, a·x = c·(b·x) on core,
    # a non-constant on core.
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

    return s, T


# ---------------------------------------------------------------------------
# Iso-orbit and automorphism computation.
# ---------------------------------------------------------------------------

def apply_perm(table, sigma, N):
    inv = [0] * N
    for i, si in enumerate(sigma):
        inv[si] = i
    return [[sigma[table[inv[a]][inv[b]]] for b in range(N)] for a in range(N)]


def iso_orbit(table, N):
    core = list(range(2, N))
    orbit = set()
    for absorber_perm in itertools.permutations([0, 1]):
        for core_perm in itertools.permutations(core):
            sigma = list(absorber_perm) + list(core_perm)
            img = apply_perm(table, sigma, N)
            orbit.add(tuple(tuple(row) for row in img))
    return orbit


def automorphisms(table, N):
    auts = 0
    for sigma in itertools.permutations(range(N)):
        if all(sigma[table[a][b]] == table[sigma[a]][sigma[b]]
               for a in range(N) for b in range(N)):
            auts += 1
    return auts


def canonical_form(orbit):
    return min(orbit, key=lambda t: tuple(v for row in t for v in row))


# ---------------------------------------------------------------------------
# Shape features.
# ---------------------------------------------------------------------------

def shape_features(table, N):
    CORE = list(range(2, N))
    core_set = set(CORE)
    Z = (0, 1)

    core_cls, core_noncls, full_cls = [], [], []
    for y in CORE:
        core_row = [table[y][x] for x in CORE]
        if all(v in Z for v in core_row):
            core_cls.append(y)
            if all(v in Z for v in table[y]):
                full_cls.append(y)
        else:
            core_noncls.append(y)

    retr_pairs = []
    for s_ in CORE:
        for r_ in CORE:
            # Anchoring: r fixes at least one absorber (absorber-swap
            # isomorphisms may relocate which one).
            if table[r_][0] != 0 and table[r_][1] != 1:
                continue
            if all(table[r_][table[s_][x]] == x and table[s_][table[r_][x]] == x
                   for x in CORE):
                retr_pairs.append((s_, r_))
    strong_R = any(s != r for s, r in retr_pairs)

    h_triples = 0
    for a, b, c in itertools.permutations(CORE, 3):
        if not all(table[b][x] in core_set for x in CORE):
            continue
        if not all(table[a][x] == table[c][table[b][x]] for x in CORE):
            continue
        if len({table[a][x] for x in CORE}) < 2:
            continue
        h_triples += 1

    return {
        "core_cls_count": len(core_cls),
        "core_noncls_count": len(core_noncls),
        "full_cls_count": len(full_cls),
        "retr_pair_count": len(retr_pairs),
        "strong_R_available": strong_R,
        "H_triple_count": h_triples,
    }


# ---------------------------------------------------------------------------
# Main enumeration loop.
# ---------------------------------------------------------------------------

def enumerate_phase(N, limit=None, time_budget=None):
    t0 = time.time()
    s, T = build_solver(N)
    classes = []
    iteration = 0

    while True:
        iteration += 1
        if time_budget and (time.time() - t0) > time_budget:
            print(f"[{iteration}] Time budget {time_budget}s exceeded. Stopping.")
            break

        result = s.check()
        if result == unsat:
            print(f"[{iteration}] UNSAT. Enumeration complete at {len(classes)} classes.")
            break
        if result != sat:
            print(f"[{iteration}] Z3 unknown. Stopping.")
            break

        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]

        orbit = iso_orbit(table, N)
        canon = canonical_form(orbit)
        canon_list = [list(row) for row in canon]
        aut_n = automorphisms(canon_list, N)

        for img in orbit:
            s.add(Or(*[T[a][b] != img[a][b]
                       for a in range(N) for b in range(N)]))

        feats = shape_features(canon_list, N)
        entry = {
            "iso_class": len(classes) + 1,
            "canonical": canon_list,
            "orbit_size": len(orbit),
            "aut_order": aut_n,
            "rigid": aut_n == 1,
            **feats,
        }
        classes.append(entry)

        if len(classes) % 50 == 0:
            print(f"[{iteration}] {len(classes)} classes so far "
                  f"(elapsed {time.time() - t0:.1f}s)", flush=True)

        if limit and len(classes) >= limit:
            print(f"Reached class limit {limit}. Stopping.")
            break

    return classes, time.time() - t0


# ---------------------------------------------------------------------------
# Summary statistics.
# ---------------------------------------------------------------------------

def summarize(N, classes):
    if not classes:
        return {"N": N, "iso_class_count": 0}

    def dist(key, cast=None):
        c = Counter()
        for x in classes:
            v = x[key]
            if cast:
                v = cast(v)
            c[v] += 1
        return dict(sorted(c.items()))

    rigid = sum(1 for c in classes if c["rigid"])
    strong_R = sum(1 for c in classes if c["strong_R_available"])

    return {
        "N": N,
        "iso_class_count": len(classes),
        "rigid_count": rigid,
        "rigid_fraction": rigid / len(classes),
        "strong_R_available_count": strong_R,
        "strong_R_fraction": strong_R / len(classes),
        "aut_order_distribution": dist("aut_order"),
        "core_cls_count_distribution": dist("core_cls_count"),
        "core_noncls_count_distribution": dist("core_noncls_count"),
        "full_cls_count_distribution": dist("full_cls_count"),
        "retr_pair_count_distribution": dist("retr_pair_count"),
        "H_triple_count_distribution": dist("H_triple_count"),
        "role_shape_distribution": dist(
            key="role_shape",
            cast=None,
        ) if any("role_shape" in c for c in classes) else None,
    }


def add_role_shape(classes):
    """Derived field: (core_cls_count, core_noncls_count, retr_pair_count,
    H_triple_count, strong_R_available). This is the 'shape type' of a magma."""
    for c in classes:
        c["role_shape"] = f"cls{c['core_cls_count']}_ncl{c['core_noncls_count']}_Rp{c['retr_pair_count']}_H{c['H_triple_count']}_sR{int(c['strong_R_available'])}"


# ---------------------------------------------------------------------------
# CLI.
# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("N", type=int)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--time", type=float, default=None,
                    help="time budget in seconds")
    args = ap.parse_args()

    print(f"=== Phase cartography at N={args.N} "
          f"(limit={args.limit}, time={args.time}) ===")
    classes, elapsed = enumerate_phase(args.N,
                                       limit=args.limit,
                                       time_budget=args.time)
    add_role_shape(classes)
    summary = summarize(args.N, classes)

    print()
    print(f"=== Summary N={args.N} ===")
    print(f"  iso_class_count:     {summary['iso_class_count']}")
    print(f"  rigid_fraction:      {summary.get('rigid_fraction', 0):.3f}")
    print(f"  strong_R_fraction:   {summary.get('strong_R_fraction', 0):.3f}")
    for key in ("aut_order_distribution",
                "core_cls_count_distribution",
                "full_cls_count_distribution",
                "retr_pair_count_distribution",
                "H_triple_count_distribution",
                "role_shape_distribution"):
        d = summary.get(key)
        if d:
            items = list(d.items())
            if len(items) > 10:
                items = items[:10] + [("...", "")]
            print(f"  {key}: " + ", ".join(f"{k}→{v}" for k, v in items))

    out = os.path.join(SCRIPT_DIR, f"phase_cartography_N{args.N}.json")
    with open(out, "w") as f:
        json.dump({"N": args.N,
                   "elapsed_seconds": elapsed,
                   "summary": summary,
                   "iso_classes": classes}, f, indent=2)
    print(f"\nWrote {out} ({elapsed:.1f}s)")


if __name__ == "__main__":
    main()
