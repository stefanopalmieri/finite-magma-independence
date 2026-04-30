"""
Independence probe: is `no_other_zeros` (E2PM clause iii) derivable from
the rest of the axioms together with D?

Setup
-----
The current E2PM encoding (mirrored from probe_axioms.py) imposes:
  (a) zero₁, zero₂ are left-absorbers (constant rows zero₁, zero₂);
  (b) extensionality (rows are pairwise distinct);
  (c) no_other_zeros: ∀ y ∈ core, ∃ x. y · x ≠ y.

If we drop (c), can D still force the conclusion of (c)? That is, in any
extensional 2-pointed magma satisfying D, is every left-absorber forced
to be one of {zero₁, zero₂}?

Probe queries (per N ∈ {4, 5, 6}):

  Q1: E2PM_minus_c + D + ∃y∈core. y is a left-absorber
        SAT  → independence holds: D does NOT force no_other_zeros.
        UNSAT → reduction: D + (a) + (b) implies no_other_zeros.

  Q2 (sanity): E2PM_full + D
        SAT expected — the canonical witnesses already prove this.

Per-query timeout: 60 seconds. Output: pass/fail per N plus, on SAT,
the third-absorber's index and a Cayley table snapshot.
"""

from __future__ import annotations

import itertools
import json
import os
import time

from z3 import (
    And, BoolVal, Distinct, Int, Not, Or, Solver, sat, unknown, unsat,
)


SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TIMEOUT_MS = 60_000
N_VALUES = [4, 5, 6]


def make_solver():
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    return s


def make_T(N):
    return [[Int(f"T_{a}_{b}") for b in range(N)] for a in range(N)]


def add_E2PM_minus_no_other_zeros(s, T, N):
    """E2PM minus clause (iii) — no_other_zeros."""
    for a in range(N):
        for b in range(N):
            s.add(T[a][b] >= 0, T[a][b] < N)
    # (a) zero₁ = 0, zero₂ = 1 are left-absorbers.
    for x in range(N):
        s.add(T[0][x] == 0)
        s.add(T[1][x] == 1)
    # (b) extensionality: all rows distinct.
    row_ids = []
    for y in range(N):
        rid, pw = 0, 1
        for x in range(N):
            rid = rid + T[y][x] * pw
            pw *= N
        row_ids.append(rid)
    s.add(Distinct(*row_ids))
    # NB: we deliberately omit
    #     for y in CORE: s.add(Or([T[y][x] != y for x in range(N)]))


def add_no_other_zeros(s, T, N):
    """E2PM clause (iii)."""
    CORE = list(range(2, N))
    for y in CORE:
        s.add(Or([T[y][x] != y for x in range(N)]))


def add_D(s, T, N):
    """Classifier dichotomy:
       - exists full classifier τ (row in {0,1});
       - every core element is all-{0,1} or all-out on core;
       - at least one non-classifier exists in core."""
    CORE = list(range(2, N))
    if not CORE:
        s.add(BoolVal(False))
        return
    is_cls = {}
    for y in CORE:
        all_in = And(*[Or(T[y][x] == 0, T[y][x] == 1) for x in CORE])
        all_out = And(*[And(T[y][x] != 0, T[y][x] != 1) for x in CORE])
        s.add(Or(all_in, all_out))
        is_cls[y] = all_in
    # Non-classifier exists.
    s.add(Or(*[Not(is_cls[y]) for y in CORE]))
    # Full classifier (row in {0,1} on the WHOLE carrier).
    s.add(Or(*[And(*[Or(T[tv][x] == 0, T[tv][x] == 1) for x in range(N)])
              for tv in CORE]))


def assert_third_absorber(s, T, N):
    """∃ y ∈ core such that y is a left-absorber: ∀ x. y · x = y."""
    CORE = list(range(2, N))
    if not CORE:
        s.add(BoolVal(False))
        return
    s.add(Or(*[And(*[T[y][x] == y for x in range(N)]) for y in CORE]))


def run_query(N, builder):
    s = make_solver()
    T = make_T(N)
    builder(s, T, N)
    t0 = time.time()
    r = s.check()
    dt = time.time() - t0
    if r == sat:
        m = s.model()
        table = [[m.eval(T[a][b]).as_long() for b in range(N)] for a in range(N)]
        return "sat", dt, table
    if r == unsat:
        return "unsat", dt, None
    return "unknown", dt, None


def find_third_absorber(table, N):
    """Return the (smallest) core index y with constant row y, or None."""
    for y in range(2, N):
        if all(table[y][x] == y for x in range(N)):
            return y
    return None


def main():
    print("=" * 72)
    print("no_other_zeros independence probe")
    print("=" * 72)

    entries = []

    for N in N_VALUES:
        print(f"\n--- N = {N} ---")
        per_N = {"N": N, "queries": {}}

        # Q2 sanity: E2PM (full) + D
        def Q2_builder(s, T, n, N=N):
            add_E2PM_minus_no_other_zeros(s, T, N)
            add_no_other_zeros(s, T, N)
            add_D(s, T, N)
        result, dt, _ = run_query(N, Q2_builder)
        print(f"  [{dt:6.2f}s] Q2 sanity (E2PM + D):                 {result}")
        per_N["queries"]["Q2_sanity"] = {
            "description": "E2PM (full) + D",
            "result": result,
            "time_seconds": dt,
        }
        if result != "sat":
            print(f"    !! sanity check failed at N={N}; aborting")
            entries.append(per_N)
            continue

        # Q1: E2PM_minus_c + D + ∃ third absorber
        def Q1_builder(s, T, n, N=N):
            add_E2PM_minus_no_other_zeros(s, T, N)
            add_D(s, T, N)
            assert_third_absorber(s, T, N)
        result, dt, table = run_query(N, Q1_builder)
        print(f"  [{dt:6.2f}s] Q1 indep (¬no_other_zeros + D + ext): {result}")
        q1_entry = {
            "description":
                "E2PM clauses (i)+(ii)+extensionality + D + ∃ third absorber",
            "result": result,
            "time_seconds": dt,
        }

        if result == "sat":
            print(f"    → INDEPENDENCE confirmed at N={N}: a third "
                  f"left-absorber consistent with D exists.")
            tab_str = format_table(table, N)
            third = find_third_absorber(table, N)
            print(f"    Third absorber: index {third}")
            print("    Cayley table:")
            for line in tab_str.splitlines():
                print(f"      {line}")
            q1_entry["verdict"] = "independence"
            q1_entry["third_absorber"] = third
            q1_entry["witness"] = table
        elif result == "unsat":
            print(f"    → REDUCTION at N={N}: in this regime, "
                  f"E2PM(a)+(b) + D forces no_other_zeros.")
            q1_entry["verdict"] = "reduction"
        else:
            print(f"    → solver returned unknown (timeout?)")
            q1_entry["verdict"] = "unknown"

        per_N["queries"]["Q1_independence"] = q1_entry
        entries.append(per_N)

    print()
    print("=" * 72)

    out_path = os.path.join(SCRIPT_DIR, "no_other_zeros_independence_result.json")
    with open(out_path, "w") as f:
        json.dump({
            "probe": "no_other_zeros_independence",
            "question": (
                "Is `no_other_zeros` (E2PM clause iii) derivable from "
                "the rest of the axioms together with D?"
            ),
            "schema": (
                "Q1 SAT  ⇒ independence (axiom is load-bearing); "
                "Q1 UNSAT ⇒ reduction (D + ext + named absorbers forces it)."
            ),
            "timeout_ms": TIMEOUT_MS,
            "N_values": N_VALUES,
            "entries": entries,
        }, f, indent=2)
    print(f"Wrote {out_path}")


def format_table(table, N):
    header = "  " + " ".join(str(j) for j in range(N))
    out = [header]
    out.append("  " + "-" * (2 * N - 1))
    for i in range(N):
        out.append(f"{i}: " + " ".join(str(table[i][j]) for j in range(N)))
    return "\n".join(out)


if __name__ == "__main__":
    main()
