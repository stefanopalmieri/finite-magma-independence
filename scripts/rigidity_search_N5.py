"""
Rigidity search for R+D+H magmas at N = 5.

Question: Does there exist a non-rigid (|Aut| >= 2) finite extensional 2-pointed
magma on Fin(5) = {0,1,2,3,4} satisfying R, D, and H capabilities?

Setup:
  - 0 and 1 are left-absorbers: 0.x = 0, 1.x = 1.
  - core = {2, 3, 4}.
  - Extensionality: all 5 rows of the Cayley table are distinct.
  - No other constant row: for each y in core, some x has y.x != y.

Capabilities:
  - R: exists s, r in core with r.(s.x) = x AND s.(r.x) = x for all x in core,
       and r.0 = 0.
  - D: exists tau in core with tau.x in {0,1} for all x; AND every y in core
       is either a "classifier" (y.x in {0,1} for all x in core) or a
       "non-classifier" (y.x not in {0,1} for all x in core); AND at least
       one non-classifier exists.
  - H: exists pairwise distinct a, b, c in core with b.x in core for all
       x in core, a.x = c.(b.x) for all x in core, and |{a.x : x in core}| >= 2.

Strategy:
  1. Encode the magma + R + D + H + existence of a non-trivial automorphism
     in Z3. If SAT, emit the witness and verify it independently by
     brute-force.
  2. If UNSAT, write a certificate. Optionally verify a known rigid witness
     (W5) satisfies R+D+H and has trivial Aut under the same semantics.
"""

from __future__ import annotations

import itertools
import json
import os
import sys
import time
from typing import List, Tuple

from z3 import (
    And,
    Distinct,
    Implies,
    Int,
    Not,
    Or,
    Solver,
    sat,
    unsat,
)


N = 5
CORE = [2, 3, 4]
ABSORB = [0, 1]
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(SCRIPT_DIR, "nonrigid_rdh_N5.json")
TXT_PATH = os.path.join(SCRIPT_DIR, "rigidity_search_N5_result.txt")


# ---------------------------------------------------------------------------
# Brute-force verification helpers (pure Python, no Z3).
# ---------------------------------------------------------------------------

def op_to_table(op):
    """Return the Cayley table as a list of lists from a callable op."""
    return [[op(a, b) for b in range(N)] for a in range(N)]


def check_absorbers(table):
    for x in range(N):
        if table[0][x] != 0:
            return False
        if table[1][x] != 1:
            return False
    return True


def check_extensional(table):
    rows = [tuple(r) for r in table]
    return len(set(rows)) == N


def check_no_other_constant_row(table):
    for y in CORE:
        row = table[y]
        if all(row[x] == y for x in range(N)):
            return False
    return True


def check_R(table):
    for s in CORE:
        for r in CORE:
            if table[r][0] != 0:
                continue
            ok = True
            for x in CORE:
                if table[r][table[s][x]] != x:
                    ok = False
                    break
                if table[s][table[r][x]] != x:
                    ok = False
                    break
            if ok:
                return True, (s, r)
    return False, None


def check_D(table):
    # Each y in core is either classifier (all y.x in {0,1} for x in core)
    # or non-classifier (all y.x not in {0,1} for x in core).
    classifiers = []
    non_classifiers = []
    for y in CORE:
        vals_on_core = [table[y][x] for x in CORE]
        all_in = all(v in (0, 1) for v in vals_on_core)
        all_out = all(v not in (0, 1) for v in vals_on_core)
        if all_in:
            classifiers.append(y)
        elif all_out:
            non_classifiers.append(y)
        else:
            return False, None
    if not non_classifiers:
        return False, None
    # Need tau in core with tau.x in {0,1} for all x (i.e. over full Fin(N)).
    for tau in CORE:
        if all(table[tau][x] in (0, 1) for x in range(N)):
            return True, tau
    return False, None


def check_H(table):
    for a, b, c in itertools.permutations(CORE, 3):
        # b maps core into core
        if not all(table[b][x] in CORE for x in CORE):
            continue
        # a.x = c.(b.x) for all x in core
        if not all(table[a][x] == table[c][table[b][x]] for x in CORE):
            continue
        # image of a on core has size >= 2
        if len({table[a][x] for x in CORE}) < 2:
            continue
        return True, (a, b, c)
    return False, None


def is_rdh(table):
    if not check_absorbers(table):
        return False, "absorbers"
    if not check_extensional(table):
        return False, "extensionality"
    if not check_no_other_constant_row(table):
        return False, "other-constant-row"
    okR, _ = check_R(table)
    if not okR:
        return False, "R"
    okD, _ = check_D(table)
    if not okD:
        return False, "D"
    okH, _ = check_H(table)
    if not okH:
        return False, "H"
    return True, None


def automorphisms(table):
    """Return all sigma: Fin(N) -> Fin(N) that are permutations and preserve .
    """
    auts = []
    for sigma in itertools.permutations(range(N)):
        ok = True
        for a in range(N):
            if not ok:
                break
            for b in range(N):
                if sigma[table[a][b]] != table[sigma[a]][sigma[b]]:
                    ok = False
                    break
        if ok:
            auts.append(sigma)
    return auts


# ---------------------------------------------------------------------------
# Z3 encoding.
# ---------------------------------------------------------------------------

def build_solver():
    """Build Z3 solver encoding a non-rigid R+D+H magma on Fin(5)."""
    s = Solver()

    # Cayley table T[a][b] : Int in [0, N).
    T = [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]
    for a in range(N):
        for b in range(N):
            s.add(T[a][b] >= 0, T[a][b] < N)

    # Absorbers.
    for x in range(N):
        s.add(T[0][x] == 0)
        s.add(T[1][x] == 1)

    # No other constant row (for y in core, exists x with T[y][x] != y).
    for y in CORE:
        s.add(Or([T[y][x] != y for x in range(N)]))

    # Extensionality: all N rows distinct.
    # Row y encoded as integer sum_{x} T[y][x] * N^x (unique id per row).
    row_ids = []
    for y in range(N):
        rid = 0
        pw = 1
        for x in range(N):
            rid = rid + T[y][x] * pw
            pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))

    # R: exists s_R, r_R in core with r.0 = 0 and for all x in core,
    # r.(s.x) = x and s.(r.x) = x. We existentially use symbolic choice
    # variables.
    sR = Int("sR")
    rR = Int("rR")
    s.add(Or([sR == c for c in CORE]))
    s.add(Or([rR == c for c in CORE]))

    # r.0 = 0 : encode by a big OR on rR's value.
    r0_constraint = []
    for rv in CORE:
        r0_constraint.append(And(rR == rv, T[rv][0] == 0))
    s.add(Or(r0_constraint))

    # r.(s.x) = x and s.(r.x) = x for x in core.
    for x in CORE:
        # T[sR][x] : select row sR at column x.
        # We need T[rR][ T[sR][x] ] == x. Encode via big disjunction.
        clauses_rsx = []
        clauses_srx = []
        for sv in CORE:
            for rv in CORE:
                # inner = T[sv][x] : a known constant-indexed Int expression.
                inner_s = T[sv][x]
                inner_r = T[rv][x]
                # T[rv][inner_s] == x : enumerate inner_s value.
                rs_cases = []
                sr_cases = []
                for iv in range(N):
                    rs_cases.append(And(inner_s == iv, T[rv][iv] == x))
                    sr_cases.append(And(inner_r == iv, T[sv][iv] == x))
                clauses_rsx.append(
                    And(sR == sv, rR == rv, Or(rs_cases))
                )
                clauses_srx.append(
                    And(sR == sv, rR == rv, Or(sr_cases))
                )
        s.add(Or(clauses_rsx))
        s.add(Or(clauses_srx))

    # D: every y in core is all-in-{0,1} on core, or all-out-of-{0,1} on core.
    # tau in core with tau.x in {0,1} for all x in Fin(N).
    # At least one non-classifier exists.
    is_classifier = {}
    for y in CORE:
        c_all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        c_all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(c_all_in, c_all_out))
        is_classifier[y] = c_all_in
    # At least one non-classifier.
    s.add(Or(*[Not(is_classifier[y]) for y in CORE]))
    # Some tau in core with tau.x in {0,1} for all x.
    tau_choices = []
    for tv in CORE:
        tau_ok = And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
        tau_choices.append(tau_ok)
    s.add(Or(*tau_choices))

    # H: exists pairwise distinct a, b, c in core such that
    #    b.x in core for all x in core,
    #    a.x = c.(b.x) for all x in core,
    #    |{a.x : x in core}| >= 2.
    h_clauses = []
    for a, b, c in itertools.permutations(CORE, 3):
        # b maps core to core.
        b_closed = And(*[Or(*[T[b][x] == cc for cc in CORE]) for x in CORE])
        # a.x = c.(b.x) : enumerate T[b][x] value.
        eq_constraints = []
        for x in CORE:
            inner = T[b][x]
            cases = []
            for iv in range(N):
                cases.append(And(inner == iv, T[a][x] == T[c][iv]))
            eq_constraints.append(Or(cases))
        eq_all = And(*eq_constraints)
        # image of a on core has >= 2 distinct values.
        diffs = []
        for x1, x2 in itertools.combinations(CORE, 2):
            diffs.append(T[a][x1] != T[a][x2])
        img_ge2 = Or(*diffs)
        h_clauses.append(And(b_closed, eq_all, img_ge2))
    s.add(Or(*h_clauses))

    # Non-trivial automorphism sigma.
    sigma = [Int(f"sigma_{i}") for i in range(N)]
    for i in range(N):
        s.add(sigma[i] >= 0, sigma[i] < N)
    s.add(Distinct(*sigma))  # permutation
    # sigma != identity.
    s.add(Or(*[sigma[i] != i for i in range(N)]))
    # sigma(a.b) = sigma(a).sigma(b) for all a, b.
    # Encode via enumeration of sigma[a], sigma[b], T[a][b].
    for a in range(N):
        for b in range(N):
            # sigma[T[a][b]] == T[sigma[a]][sigma[b]]
            # Enumerate sa, sb, tab.
            big_cases = []
            for sa in range(N):
                for sb in range(N):
                    for tab in range(N):
                        big_cases.append(
                            And(
                                sigma[a] == sa,
                                sigma[b] == sb,
                                T[a][b] == tab,
                                sigma[tab] == T[sa][sb],
                            )
                        )
            s.add(Or(*big_cases))

    return s, T, sigma, (sR, rR)


# ---------------------------------------------------------------------------
# Known W5 rigidity sanity check.
# ---------------------------------------------------------------------------

W5_TABLE = [
    [0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1],
    [0, 2, 2, 3, 4],
    [0, 0, 0, 1, 0],
    [0, 1, 0, 1, 0],
]


def verify_w5():
    print("W5 check:")
    ok, reason = is_rdh(W5_TABLE)
    print(f"  R+D+H: {ok}, reason={reason}")
    auts = automorphisms(W5_TABLE)
    print(f"  |Aut| = {len(auts)}")
    if len(auts) == 1:
        print(f"  Aut = {auts[0]} (identity only) -> rigid.")
    else:
        print(f"  Aut = {auts}")
    return ok and len(auts) == 1


# ---------------------------------------------------------------------------
# Main.
# ---------------------------------------------------------------------------

def main():
    t0 = time.time()
    print("Sanity check on W5...")
    verify_w5()

    print("\nBuilding Z3 model for non-rigid R+D+H magma at N=5...")
    s, T, sigma, (sR, rR) = build_solver()

    print("Solving...")
    result = s.check()
    elapsed = time.time() - t0
    print(f"Z3 result: {result}  (elapsed = {elapsed:.2f}s)")

    if result == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        sigma_val = [m.eval(sigma[i]).as_long() for i in range(N)]
        sR_val = m.eval(sR).as_long()
        rR_val = m.eval(rR).as_long()

        print("\nZ3 witness Cayley table:")
        header = "    " + " ".join(str(c) for c in range(N))
        print(header)
        for a in range(N):
            print(f"{a}:  " + " ".join(str(table[a][b]) for b in range(N)))
        print(f"\nsigma = {sigma_val}")
        print(f"R witness: s = {sR_val}, r = {rR_val}")

        # Independent brute-force verification.
        print("\nIndependent verification (Python brute-force):")
        ok, reason = is_rdh(table)
        print(f"  R+D+H: {ok}, reason={reason}")
        auts = automorphisms(table)
        print(f"  |Aut| = {len(auts)}")
        for a in auts:
            print(f"    aut = {a}")
        nontrivial = any(a != tuple(range(N)) for a in auts)
        print(f"  non-trivial automorphism present? {nontrivial}")

        if not (ok and nontrivial):
            print("ERROR: Z3 witness failed independent verification.")
            sys.exit(1)

        # Save.
        data = {
            "N": N,
            "cayley_table": table,
            "sigma": sigma_val,
            "R_witness": {"s": sR_val, "r": rR_val},
            "automorphisms": [list(a) for a in auts],
            "z3_runtime_seconds": elapsed,
        }
        with open(JSON_PATH, "w") as f:
            json.dump(data, f, indent=2)
        print(f"\nWrote {JSON_PATH}")

    elif result == unsat:
        print("UNSAT: no non-rigid R+D+H magma at N=5 exists.")
        with open(TXT_PATH, "w") as f:
            f.write("UNSAT at N=5\n")
            f.write(f"(z3 runtime: {elapsed:.2f}s)\n")
        print(f"Wrote {TXT_PATH}")
    else:
        print(f"Unknown result from Z3: {result}")
        sys.exit(2)


if __name__ == "__main__":
    main()
