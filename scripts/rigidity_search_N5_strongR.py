"""
Rigidity search for R+D+H magmas at N = 5 under the *strong R* formulation.

Question: Does there exist a non-rigid (|Aut| >= 2) finite extensional 2-pointed
magma on Fin(5) = {0,1,2,3,4} satisfying R, D, H with the additional
constraint that the retraction pair has s != r (mutual inverse, not involution)?

Motivation:
  The previous search (rigidity_search_N5.py) found a non-rigid R+D+H witness
  at N=5 with s = r = 3. The retraction element's row on core was exactly the
  transposition (2 4), i.e., it algebraically encoded the automorphism. If we
  require s != r, the retraction structure is forced to be more elaborate
  (two distinct mutual-inverse elements), which may preclude this specific
  encoding mechanism.

  The paper already proves this formulation tight (Theorem 3.5: |S| >= 5
  under mutual-inverse with s != r), so N=5 is the smallest size where
  this question is meaningful.

This script modifies rigidity_search_N5.py by adding `sR != rR` to the
R constraints.
"""

from __future__ import annotations

import itertools
import json
import os
import sys
import time

from z3 import (
    And,
    Distinct,
    Int,
    Not,
    Or,
    Solver,
    sat,
    unsat,
)


N = 5
CORE = [2, 3, 4]
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(SCRIPT_DIR, "nonrigid_rdh_N5_strongR.json")
TXT_PATH = os.path.join(SCRIPT_DIR, "rigidity_search_N5_strongR_result.txt")


# -- Brute-force verification helpers (mirrors the original script) -----------

def check_absorbers(T):
    return all(T[0][x] == 0 and T[1][x] == 1 for x in range(N))


def check_extensional(T):
    return len({tuple(r) for r in T}) == N


def check_no_other_constant(T):
    for y in CORE:
        if all(T[y][x] == y for x in range(N)):
            return False
    return True


def check_R_strong(T):
    """R with s != r (mutual inverse on core, anchored at z1)."""
    for s_ in CORE:
        for r_ in CORE:
            if s_ == r_:
                continue
            if T[r_][0] != 0:
                continue
            ok = True
            for x in CORE:
                if T[r_][T[s_][x]] != x or T[s_][T[r_][x]] != x:
                    ok = False
                    break
            if ok:
                return True, (s_, r_)
    return False, None


def check_D(T):
    classifiers, non_classifiers = [], []
    for y in CORE:
        v = [T[y][x] for x in CORE]
        if all(u in (0, 1) for u in v):
            classifiers.append(y)
        elif all(u not in (0, 1) for u in v):
            non_classifiers.append(y)
        else:
            return False, None
    if not non_classifiers:
        return False, None
    for tau in CORE:
        if all(T[tau][x] in (0, 1) for x in range(N)):
            return True, tau
    return False, None


def check_H(T):
    for a, b, c in itertools.permutations(CORE, 3):
        if not all(T[b][x] in CORE for x in CORE):
            continue
        if not all(T[a][x] == T[c][T[b][x]] for x in CORE):
            continue
        if len({T[a][x] for x in CORE}) < 2:
            continue
        return True, (a, b, c)
    return False, None


def is_rdh_strong(T):
    if not check_absorbers(T): return False, "absorbers"
    if not check_extensional(T): return False, "extensionality"
    if not check_no_other_constant(T): return False, "other-constant-row"
    okR, _ = check_R_strong(T)
    if not okR: return False, "R_strong (s != r)"
    okD, _ = check_D(T)
    if not okD: return False, "D"
    okH, _ = check_H(T)
    if not okH: return False, "H"
    return True, None


def automorphisms(T):
    auts = []
    for sigma in itertools.permutations(range(N)):
        if all(sigma[T[a][b]] == T[sigma[a]][sigma[b]]
               for a in range(N) for b in range(N)):
            auts.append(sigma)
    return auts


# -- Z3 encoding --------------------------------------------------------------

def build_solver():
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

    # Extensionality: unique row ids.
    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw
            pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))

    # R (strong: s != r).
    sR = Int("sR")
    rR = Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))
    s.add(sR != rR)  # <-- the additional constraint

    r0 = []
    for rv in CORE:
        r0.append(And(rR == rv, T[rv][0] == 0))
    s.add(Or(r0))

    for x in CORE:
        clauses_rsx, clauses_srx = [], []
        for sv in CORE:
            for rv in CORE:
                if sv == rv:
                    continue  # enforce s != r directly in the enumeration
                inner_s, inner_r = T[sv][x], T[rv][x]
                rs_cases, sr_cases = [], []
                for iv in range(N):
                    rs_cases.append(And(inner_s == iv, T[rv][iv] == x))
                    sr_cases.append(And(inner_r == iv, T[sv][iv] == x))
                clauses_rsx.append(And(sR == sv, rR == rv, Or(rs_cases)))
                clauses_srx.append(And(sR == sv, rR == rv, Or(sr_cases)))
        s.add(Or(clauses_rsx))
        s.add(Or(clauses_srx))

    # D.
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

    # H.
    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        eqs = []
        for x in CORE:
            inner = T[b][x]
            cases = []
            for iv in range(N):
                cases.append(And(inner == iv, T[a][x] == T[c][iv]))
            eqs.append(Or(cases))
        diffs = [T[a][x1] != T[a][x2] for x1, x2 in itertools.combinations(CORE, 2)]
        h_clauses.append(And(b_closed, And(*eqs), Or(*diffs)))
    s.add(Or(*h_clauses))

    # Non-trivial automorphism.
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
                        big.append(And(
                            sigma[a] == sa,
                            sigma[b] == sb,
                            T[a][b] == tab,
                            sigma[tab] == T[sa][sb],
                        ))
            s.add(Or(*big))

    return s, T, sigma, (sR, rR)


def main():
    t0 = time.time()
    print("Z3 search: non-rigid R+D+H at N=5 with s != r ...")
    s, T, sigma, (sR, rR) = build_solver()
    result = s.check()
    elapsed = time.time() - t0
    print(f"Z3 result: {result}  ({elapsed:.2f}s)")

    if result == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sig = [m.eval(sigma[i]).as_long() for i in range(N)]
        s_val = m.eval(sR).as_long()
        r_val = m.eval(rR).as_long()

        print("\nZ3 witness:")
        print("    " + " ".join(str(c) for c in range(N)))
        for a in range(N):
            print(f"{a}:  " + " ".join(str(table[a][b]) for b in range(N)))
        print(f"\nsigma = {sig}")
        print(f"R witness: s = {s_val}, r = {r_val}  (s != r: {s_val != r_val})")

        print("\nIndependent verification:")
        ok, reason = is_rdh_strong(table)
        print(f"  R+D+H (strong R): {ok}, reason={reason}")
        auts = automorphisms(table)
        print(f"  |Aut| = {len(auts)}  orbits:")
        for a_ in auts:
            print(f"    {a_}")
        nontrivial = any(a_ != tuple(range(N)) for a_ in auts)
        print(f"  non-trivial automorphism present? {nontrivial}")

        if not (ok and nontrivial):
            print("ERROR: Z3 witness failed independent verification.")
            sys.exit(1)

        data = {
            "N": N,
            "cayley_table": table,
            "sigma": sig,
            "R_witness": {"s": s_val, "r": r_val},
            "automorphisms": [list(a_) for a_ in auts],
            "z3_runtime_seconds": elapsed,
            "constraint": "strong R (s != r)",
        }
        with open(JSON_PATH, "w") as f:
            json.dump(data, f, indent=2)
        print(f"\nWrote {JSON_PATH}")

    elif result == unsat:
        print("UNSAT: every R+D+H magma at N=5 with s != r is role-rigid.")
        with open(TXT_PATH, "w") as f:
            f.write("UNSAT at N=5 under strong R (s != r)\n")
            f.write(f"(z3 runtime: {elapsed:.2f}s)\n")
        print(f"Wrote {TXT_PATH}")
    else:
        print(f"Unknown result: {result}")
        sys.exit(2)


if __name__ == "__main__":
    main()
