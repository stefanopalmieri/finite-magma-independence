#!/usr/bin/env python3
"""
Scaling test: check each non-implication direction at every N from its
tight minimum up to N=15.

For the 4 tight directions (D⇏R, D⇏H, H⇏R, H⇏D):
  test from tight minimum to N=15.
For the 2 non-tight directions (R⇏D, R⇏H):
  test from N=3 to N=15, distinguishing vacuous from structural witnesses.

Uses Z3 with 60-second timeout per query.
"""

from __future__ import annotations
import sys
import time
from z3 import And, If, Int, Not, Or, Solver, sat, unsat


TIMEOUT_MS = 60000  # 60 seconds per query


def make_dot(n):
    return [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]


def ite_lookup(dot, row, col_expr, n):
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def add_e2pm(s, dot, n):
    """E2PM: domain, absorbers z1=0 z2=1, no extra absorbers, extensionality."""
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)
    for j in range(n):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))


# ═══════════════════════════════════════════════════════════════════
# Positive capability assertions
# ═══════════════════════════════════════════════════════════════════

def add_has_retract_pair(s, dot, n):
    """Assert HasRetractPair: ∃ (sec, ret) in core² with mutual inverse + anchor."""
    core = list(range(2, n))
    if len(core) < 1:
        s.add(False)
        return
    candidates = []
    for sec_i in core:
        for ret_i in core:
            ret_sec_ok = And([
                ite_lookup(dot, ret_i, dot[sec_i][x], n) == x
                for x in core
            ])
            sec_ret_ok = And([
                ite_lookup(dot, sec_i, dot[ret_i][x], n) == x
                for x in core
            ])
            anchor = (dot[ret_i][0] == 0)
            candidates.append(And(ret_sec_ok, sec_ret_ok, anchor))
    s.add(Or(candidates))


def add_has_dichotomy(s, dot, n):
    """Assert HasDichotomy: classifier exists, global purity, non-degeneracy."""
    core = list(range(2, n))
    if len(core) < 1:
        s.add(False)
        return

    # P1: ∃ classifier τ in core with τ·x ∈ {0,1} for ALL x (including absorbers)
    cls_candidates = []
    for tau in core:
        is_cls = And([Or(dot[tau][j] == 0, dot[tau][j] == 1) for j in range(n)])
        cls_candidates.append(is_cls)
    s.add(Or(cls_candidates))

    # P2: global dichotomy on core
    for y in core:
        all_bool = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        all_nonbool = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        s.add(Or(all_bool, all_nonbool))

    # P3: non-degeneracy — ∃ non-classifier
    noncls_candidates = []
    for y in core:
        has_nonbool = Or([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        noncls_candidates.append(has_nonbool)
    s.add(Or(noncls_candidates))


def add_has_icp(s, dot, n):
    """Assert HasICP: ∃ pairwise distinct a,b,c in core with ICP conditions."""
    core = list(range(2, n))
    if len(core) < 3:
        s.add(False)
        return

    candidates = []
    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                b_pres = And([And(dot[b][x] != 0, dot[b][x] != 1) for x in core])
                factor = And([
                    dot[a][x] == ite_lookup(dot, c, dot[b][x], n)
                    for x in core
                ])
                nontriv_pairs = []
                for x in core:
                    for y in core:
                        if x < y:
                            nontriv_pairs.append(dot[a][x] != dot[a][y])
                nontriv = Or(nontriv_pairs) if nontriv_pairs else False
                candidates.append(And(b_pres, factor, nontriv))

    if candidates:
        s.add(Or(candidates))
    else:
        s.add(False)


# ═══════════════════════════════════════════════════════════════════
# Negative capability assertions
# ═══════════════════════════════════════════════════════════════════

def add_no_retract_pair(s, dot, n):
    """Assert ¬HasRetractPair: for every (sec, ret) pair, at least one condition fails."""
    core = list(range(2, n))
    for sec_i in core:
        for ret_i in core:
            ret_sec_fails = [
                ite_lookup(dot, ret_i, dot[sec_i][x], n) != x
                for x in core
            ]
            sec_ret_fails = [
                ite_lookup(dot, sec_i, dot[ret_i][x], n) != x
                for x in core
            ]
            anchor_fails = (dot[ret_i][0] != 0)
            s.add(Or(ret_sec_fails + sec_ret_fails + [anchor_fails]))


def add_no_dichotomy_simple(s, dot, n):
    """Assert no classifier exists (simplest sufficient condition for ¬D).

    For every core element c, assert ∃ x with c·x ∉ {0,1}.
    This doesn't capture all ways D can fail, but captures the "no classifier" case.
    """
    core = list(range(2, n))
    if len(core) < 1:
        return  # Vacuously no dichotomy

    for tau in core:
        # tau is NOT a classifier: ∃ some x with tau·x ∉ {0,1}
        s.add(Or([And(dot[tau][j] != 0, dot[tau][j] != 1) for j in range(n)]))


def add_no_dichotomy_full(s, dot, n):
    """Assert ¬HasDichotomy (full negation): ¬P1 ∨ ¬P2 ∨ ¬P3."""
    core = list(range(2, n))
    if len(core) < 1:
        return

    # ¬P1: No classifier exists
    no_classifier = And([
        Or([And(dot[tau][j] != 0, dot[tau][j] != 1) for j in range(n)])
        for tau in core
    ])

    # ¬P2: Some element is mixed on core
    mixed_elements = []
    for y in core:
        has_bool = Or([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        has_nonbool = Or([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        mixed_elements.append(And(has_bool, has_nonbool))
    some_mixed = Or(mixed_elements)

    # ¬P3: All core elements are classifiers (no non-classifier)
    all_classifiers = And([
        And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        for y in core
    ])

    s.add(Or(no_classifier, some_mixed, all_classifiers))


def add_no_icp(s, dot, n):
    """Assert ¬HasICP: for every pairwise distinct (a,b,c), at least one condition fails."""
    core = list(range(2, n))
    if len(core) < 3:
        return  # ICP is vacuously false

    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                b_pres_fails = [Or(dot[b][x] == 0, dot[b][x] == 1) for x in core]
                factor_fails = [
                    dot[a][x] != ite_lookup(dot, c, dot[b][x], n)
                    for x in core
                ]
                nontriv_fails_parts = []
                for x in core:
                    for y in core:
                        if x < y:
                            nontriv_fails_parts.append(dot[a][x] != dot[a][y])
                if nontriv_fails_parts:
                    nontriv_fails = Not(Or(nontriv_fails_parts))
                else:
                    nontriv_fails = True
                s.add(Or(b_pres_fails + factor_fails + [nontriv_fails]))


# ═══════════════════════════════════════════════════════════════════
# Query runner
# ═══════════════════════════════════════════════════════════════════

def check_direction(direction, n):
    """Check if a non-implication direction is achievable at size N.

    Returns: 'SAT', 'UNSAT', or 'timeout'
    """
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    dot = make_dot(n)
    add_e2pm(s, dot, n)

    if direction == "D_not_R":
        add_has_dichotomy(s, dot, n)
        add_no_retract_pair(s, dot, n)
    elif direction == "D_not_H":
        add_has_dichotomy(s, dot, n)
        add_no_icp(s, dot, n)
    elif direction == "H_not_R":
        add_has_icp(s, dot, n)
        add_no_retract_pair(s, dot, n)
    elif direction == "H_not_D":
        # Use simple no-classifier negation as instructed
        add_has_icp(s, dot, n)
        add_no_dichotomy_simple(s, dot, n)
    elif direction == "R_not_D":
        add_has_retract_pair(s, dot, n)
        add_no_dichotomy_full(s, dot, n)
    elif direction == "R_not_H":
        add_has_retract_pair(s, dot, n)
        add_no_icp(s, dot, n)
    else:
        raise ValueError(f"Unknown direction: {direction}")

    result = s.check()
    if result == sat:
        return "SAT"
    elif result == unsat:
        return "UNSAT"
    else:
        return "timeout"


def is_vacuous(direction, n):
    """Check if one of the capabilities is vacuously false at this N.

    For R⇏D and R⇏H, the positive is R (retract pair) which needs core≥1,
    and the negation targets D or H.
    D requires core≥2 (classifier + non-classifier). ICP requires core≥3.
    Vacuousness: the negated property couldn't hold anyway at this size.
    """
    core_size = n - 2
    if direction == "R_not_D":
        # D needs at least 2 core elements (classifier + non-classifier)
        # At N=3, core=1, D is vacuously false (can't have both classifier and non-classifier)
        return core_size < 2
    elif direction == "R_not_H":
        # H (ICP) needs 3 pairwise distinct core elements
        return core_size < 3
    return False


# ═══════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════

# Tight directions with their minimum N from the Lean-verified witnesses
TIGHT_DIRECTIONS = [
    ("D_not_R", "D⇏R", 5),
    ("D_not_H", "D⇏H", 5),
    ("H_not_R", "H⇏R", 6),
    ("H_not_D", "H⇏D", 5),
]

# Non-tight directions (R is easy to have; the question is D/H failure)
NONTIGHT_DIRECTIONS = [
    ("R_not_D", "R⇏D", 3),
    ("R_not_H", "R⇏H", 3),
]

MAX_N = 15


def main():
    all_sizes = list(range(3, MAX_N + 1))

    print("=" * 90)
    print("  SCALING TEST: Non-implication directions from tight minimum to N=15")
    print("=" * 90)

    # Collect all results
    results = {}

    # --- Tight directions ---
    print("\n" + "─" * 90)
    print("  TIGHT DIRECTIONS (D⇏R, D⇏H, H⇏R, H⇏D)")
    print("─" * 90)

    for direction, label, min_n in TIGHT_DIRECTIONS:
        results[label] = {}
        print(f"\n  {label} (tight minimum: N={min_n})")
        for n in range(min_n, MAX_N + 1):
            t0 = time.time()
            sys.stdout.write(f"    N={n:2d}: ")
            sys.stdout.flush()

            res = check_direction(direction, n)
            elapsed = time.time() - t0
            results[label][n] = res
            print(f"{res:7s} ({elapsed:.1f}s)")

    # --- Non-tight directions ---
    print("\n" + "─" * 90)
    print("  NON-TIGHT DIRECTIONS (R⇏D, R⇏H)")
    print("─" * 90)

    for direction, label, min_n in NONTIGHT_DIRECTIONS:
        results[label] = {}
        print(f"\n  {label}")
        for n in range(min_n, MAX_N + 1):
            t0 = time.time()
            sys.stdout.write(f"    N={n:2d}: ")
            sys.stdout.flush()

            vac = is_vacuous(direction, n)
            res = check_direction(direction, n)
            elapsed = time.time() - t0

            if vac and res == "SAT":
                tag = "SAT(vac)"
            else:
                tag = res
            results[label][n] = tag
            print(f"{tag:10s} ({elapsed:.1f}s)")

    # ═══════════════════════════════════════════════════════════════
    # Summary table
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 90)
    print("  SUMMARY TABLE")
    print("=" * 90)

    # Build column headers
    col_ns = list(range(3, MAX_N + 1))
    header = f"| {'Direction':>10} |"
    for n in col_ns:
        header += f" N={n:<2} |"
    print(header)

    sep = f"|{'-' * 12}|"
    for _ in col_ns:
        sep += f"{'-' * 6}|"
    print(sep)

    # All directions in order
    all_dirs = TIGHT_DIRECTIONS + NONTIGHT_DIRECTIONS
    for direction, label, min_n in all_dirs:
        row = f"| {label:>10} |"
        for n in col_ns:
            if n in results[label]:
                val = results[label][n]
                # Abbreviate for table
                if val == "SAT(vac)":
                    cell = "vac"
                elif val == "SAT":
                    cell = "SAT"
                elif val == "UNSAT":
                    cell = "UNS"
                elif val == "timeout":
                    cell = "T/O"
                else:
                    cell = val[:3]
            else:
                cell = "---"
            row += f" {cell:>4} |"
        print(row)

    print()
    print("Legend: SAT = achievable, UNS = UNSAT (not achievable),")
    print("        T/O = timeout (60s), vac = vacuous (target property impossible at this N),")
    print("        --- = not tested (below tight minimum)")
    print()


if __name__ == "__main__":
    main()
