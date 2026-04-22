"""
Enumerate R+D+H magmas at N up to isomorphism.

Iso group: absorber-preserving permutations on Fin(N), i.e. Sym({0, 1}) x
Sym({2, ..., N-1}). Size = 2 * (N-2)!.

For each iso class we record the lex-smallest Cayley table (canonical form),
its orbit size, |Aut|, rigidity flag, and a sample (s, r) retraction witness.

Strategy: find a model, apply every absorber-preserving permutation to compute
the full iso-orbit, block each orbit element as a solver clause, repeat until
UNSAT. Each iteration produces one fresh iso class.

Usage:
    python3 enumerate_rdh_iso.py <N> [--strong-R] [--limit K] [--weak-H]

Writes enumerate_rdh_iso_N<N>[_strongR][_weakH].json
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


# ---------------------------------------------------------------------------
# Z3 encoding.
# ---------------------------------------------------------------------------

def build_base_solver(N, strong_R):
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
    if strong_R:
        s.add(sR != rR)
    s.add(Or([And(rR == rv, T[rv][0] == 0) for rv in CORE]))
    for x in CORE:
        rsx, srx = [], []
        for sv in CORE:
            for rv in CORE:
                if strong_R and sv == rv:
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

    return s, T, sR, rR


# ---------------------------------------------------------------------------
# Iso-orbit and automorphism computation (over concrete Python tables).
# ---------------------------------------------------------------------------

def apply_perm(table, sigma, N):
    inv = [0] * N
    for i, si in enumerate(sigma):
        inv[si] = i
    return [[sigma[table[inv[a]][inv[b]]] for b in range(N)] for a in range(N)]


def iso_orbit(table, N):
    """All images under absorber-preserving permutations."""
    orbit = set()
    core = list(range(2, N))
    for absorber_perm in itertools.permutations([0, 1]):
        for core_perm in itertools.permutations(core):
            sigma = list(absorber_perm) + list(core_perm)
            img = apply_perm(table, sigma, N)
            orbit.add(tuple(tuple(row) for row in img))
    return orbit


def automorphisms(table, N):
    """Full automorphism group (any permutation of Fin(N))."""
    auts = []
    for sigma in itertools.permutations(range(N)):
        if all(sigma[table[a][b]] == table[sigma[a]][sigma[b]]
               for a in range(N) for b in range(N)):
            auts.append(sigma)
    return auts


def canonical_form(orbit):
    flat = lambda t: tuple(v for row in t for v in row)
    return min(orbit, key=flat)


# ---------------------------------------------------------------------------
# Verification (independent of Z3 model).
# ---------------------------------------------------------------------------

def check_R(T, CORE, strong):
    for s_ in CORE:
        for r_ in CORE:
            if strong and s_ == r_:
                continue
            if T[r_][0] != 0:
                continue
            if all(T[r_][T[s_][x]] == x and T[s_][T[r_][x]] == x for x in CORE):
                return True, (s_, r_)
    return False, None


def check_D(T, CORE, N):
    classifiers = []
    for y in CORE:
        v = [T[y][x] for x in CORE]
        if all(u in (0, 1) for u in v):
            classifiers.append(y)
        elif all(u not in (0, 1) for u in v):
            pass
        else:
            return False, None, None
    if len(classifiers) == len(CORE):
        return False, None, None
    tau_cands = [y for y in CORE if all(T[y][x] in (0, 1) for x in range(N))]
    return (True, classifiers, tau_cands[0] if tau_cands else None)


def check_H(T, CORE):
    triples = []
    for a, b, c in itertools.permutations(CORE, 3):
        if not all(T[b][x] in CORE for x in CORE): continue
        if not all(T[a][x] == T[c][T[b][x]] for x in CORE): continue
        if len({T[a][x] for x in CORE}) < 2: continue
        triples.append((a, b, c))
    return triples


# ---------------------------------------------------------------------------
# Main loop.
# ---------------------------------------------------------------------------

def extract_table(model, T, N):
    return [[model.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]


def run(N, strong_R, limit=None, stop_on_nonrigid=False, k_classifiers=None):
    CORE = list(range(2, N))
    group_size = 2 * 1
    for k in range(1, len(CORE) + 1):
        group_size *= k

    print(f"=== Enumerate R+D+H iso classes at N={N} "
          f"(strong_R={strong_R}, k_classifiers={k_classifiers}, "
          f"group_size={group_size}) ===")

    t0 = time.time()
    s, T, sR, rR = build_base_solver(N, strong_R)

    # Optional constraint: exactly k_classifiers core classifiers.
    if k_classifiers is not None:
        cls_ints = []
        for y in CORE:
            is_core_cls = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
            ci = Int(f"cls_bit_{y}")
            s.add(Or(And(is_core_cls, ci == 1),
                     And(Not(is_core_cls), ci == 0)))
            cls_ints.append(ci)
        s.add(sum(cls_ints) == k_classifiers)

    print(f"(solver built: {time.time()-t0:.2f}s)")

    classes = []
    total_solve = 0.0
    total_orbit = 0.0
    iteration = 0

    while True:
        iteration += 1
        ts = time.time()
        result = s.check()
        solve_dt = time.time() - ts
        total_solve += solve_dt

        if result == unsat:
            print(f"[{iteration}] UNSAT after {solve_dt:.2f}s. Enumeration complete.")
            break
        if result != sat:
            print(f"[{iteration}] Z3 unknown. Stopping.")
            break

        m = s.model()
        table = extract_table(m, T, N)
        s_val = m.eval(sR).as_long()
        r_val = m.eval(rR).as_long()

        okR, rw = check_R(table, CORE, strong_R)
        okD, cls_list, tau = check_D(table, CORE, N)
        h_triples = check_H(table, CORE)
        if not (okR and okD and h_triples):
            print(f"[{iteration}] ERROR: Z3 model failed verification. "
                  f"okR={okR}, okD={okD}, |H|={len(h_triples)}")
            sys.exit(1)

        to = time.time()
        orbit = iso_orbit(table, N)
        canon = canonical_form(orbit)
        canon_list = [list(row) for row in canon]
        auts = automorphisms(canon_list, N)
        orbit_dt = time.time() - to
        total_orbit += orbit_dt

        for img in orbit:
            s.add(Or(*[T[a][b] != img[a][b]
                        for a in range(N) for b in range(N)]))

        # Count nontrivial-on-core classifiers.
        nontriv_cls = [y for y in cls_list
                       if len({canon_list[y][x] for x in CORE}) >= 2]

        entry = {
            "iso_class": len(classes) + 1,
            "canonical": canon_list,
            "orbit_size": len(orbit),
            "aut_order": len(auts),
            "rigid": len(auts) == 1,
            "sample_R": {"s": s_val, "r": r_val},
            "classifiers_core": cls_list,
            "nontriv_classifiers_core": nontriv_cls,
            "full_classifier_tau": tau,
            "H_triple_count": len(h_triples),
            "sample_H_triple": list(h_triples[0]) if h_triples else None,
        }
        classes.append(entry)
        flag = "!" if len(auts) > 1 else " "
        print(f"[{iteration}]{flag} class #{len(classes)}: "
              f"|orbit|={len(orbit)}, |Aut|={len(auts)}, "
              f"k_cls={len(cls_list)}, k_cls_nontriv={len(nontriv_cls)}, "
              f"|H|={len(h_triples)}  "
              f"(solve {solve_dt:.2f}s)")

        if stop_on_nonrigid and len(auts) > 1:
            print(f"Stopping: found first non-rigid class at iteration {iteration}.")
            break
        if limit and len(classes) >= limit:
            print(f"Reached limit {limit}.")
            break

    elapsed = time.time() - t0
    rigid_count = sum(1 for c in classes if c["rigid"])
    print()
    print(f"=== Summary N={N} strong_R={strong_R} ===")
    print(f"  Total iso classes: {len(classes)}")
    print(f"  Rigid (|Aut|=1):   {rigid_count}")
    print(f"  Non-rigid:         {len(classes) - rigid_count}")
    print(f"  Total time:        {elapsed:.2f}s  "
          f"(z3 {total_solve:.1f}s, orbit {total_orbit:.1f}s)")

    suffix = ("_strongR" if strong_R else "")
    if k_classifiers is not None:
        suffix += f"_k{k_classifiers}"
    out = os.path.join(SCRIPT_DIR, f"enumerate_rdh_iso_N{N}{suffix}.json")
    with open(out, "w") as f:
        json.dump({"N": N,
                   "strong_R": strong_R,
                   "iso_class_count": len(classes),
                   "rigid_count": rigid_count,
                   "iso_classes": classes,
                   "runtime_seconds": elapsed}, f, indent=2)
    print(f"  Wrote {out}")
    return classes


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("N", type=int)
    ap.add_argument("--strong-R", action="store_true",
                    help="Require retraction pair with s != r")
    ap.add_argument("--limit", type=int, default=None,
                    help="Stop after this many iso classes")
    ap.add_argument("--stop-on-nonrigid", action="store_true",
                    help="Stop as soon as the first non-rigid class is found")
    ap.add_argument("--k-classifiers", type=int, default=None,
                    help="Restrict to exactly K classifiers in core")
    args = ap.parse_args()
    run(args.N, args.strong_R, args.limit, args.stop_on_nonrigid,
        k_classifiers=args.k_classifiers)
