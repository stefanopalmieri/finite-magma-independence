#!/usr/bin/env python3
"""
Determine the minimum N for each of the 6 non-implication directions
among the three capabilities R, D, H over extensional 2-pointed magmas.

For each direction, search from N=3 upward until SAT.

Definitions (from the Lean formalization):
  - E2PM: z1=0, z2=1 absorbers, no other absorbers, extensionality (distinct rows)
  - HasRetractPair: ∃ sec,ret in core s.t. ret(sec(x))=x and sec(ret(x))=x
    for all core x, and ret(z1)=z1
  - HasDichotomy: (∃ classifier τ in core with τ·x ∈ {z1,z2} for all x) ∧
    (every y is absorber, or all-boolean on core, or all-non-boolean on core) ∧
    (∃ non-classifier: some y in core with y·x ∉ {z1,z2} for some core x)
  - HasICP: ∃ pairwise distinct a,b,c in core s.t.
    b preserves core (b·x ∉ {z1,z2} for core x),
    a·x = c·(b·x) for core x, and a takes ≥2 distinct values on core
"""

from __future__ import annotations
import sys
import time
from z3 import And, If, Int, Not, Or, Solver, sat, unsat, Bool

TIMEOUT_MS = 30000  # 30 seconds per query


def make_dot(n):
    """Create N×N integer variable matrix."""
    return [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]


def ite_lookup(dot, row, col_expr, n):
    """dot[row][col_expr] via nested If-Then-Else."""
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def add_e2pm(s, dot, n):
    """Add E2PM constraints: domain, absorbers, no extra absorbers, extensionality."""
    # Domain
    for i in range(n):
        for j in range(n):
            s.add(dot[i][j] >= 0, dot[i][j] < n)
    # Absorbers: row 0 all 0, row 1 all 1
    for j in range(n):
        s.add(dot[0][j] == 0)
        s.add(dot[1][j] == 1)
    # No other absorbers
    for x in range(2, n):
        s.add(Or([dot[x][j] != x for j in range(n)]))
    # Extensionality: all rows pairwise distinct
    for x in range(n):
        for y in range(x + 1, n):
            s.add(Or([dot[x][j] != dot[y][j] for j in range(n)]))


def add_has_retract_pair(s, dot, n, sec=None, ret=None):
    """Assert HasRetractPair existentially (witness sec, ret)."""
    if sec is None:
        sec = Int("rp_sec")
        ret = Int("rp_ret")
        s.add(sec >= 2, sec < n, ret >= 2, ret < n)
    # ret(sec(x)) = x for all core x
    for x in range(2, n):
        sx = ite_lookup(dot, sec, x, n) if isinstance(sec, int) is False else dot[sec][x]
        # Need to handle symbolic sec/ret
        pass

    # Actually, for symbolic sec/ret, this is very hard with ITE.
    # Let's enumerate all possible (sec, ret) pairs and use Or.
    # For small N this is fine.
    raise NotImplementedError("Use add_has_retract_pair_enum instead")


def add_has_retract_pair_enum(s, dot, n):
    """Assert HasRetractPair: at least one (sec, ret) pair works."""
    candidates = []
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            # ret(sec(x)) = x for all core x
            ret_sec_ok = And([
                ite_lookup(dot, ret_i, dot[sec_i][x], n) == x
                for x in range(2, n)
            ])
            # sec(ret(x)) = x for all core x
            sec_ret_ok = And([
                ite_lookup(dot, sec_i, dot[ret_i][x], n) == x
                for x in range(2, n)
            ])
            # ret(z1) = z1 (anchor)
            anchor = (dot[ret_i][0] == 0)
            candidates.append(And(ret_sec_ok, sec_ret_ok, anchor))
    s.add(Or(candidates))


def add_no_retract_pair(s, dot, n):
    """Assert ¬HasRetractPair: for every (sec, ret) pair, at least one condition fails."""
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            # At least one retraction equation fails
            ret_sec_fails = [
                ite_lookup(dot, ret_i, dot[sec_i][x], n) != x
                for x in range(2, n)
            ]
            sec_ret_fails = [
                ite_lookup(dot, sec_i, dot[ret_i][x], n) != x
                for x in range(2, n)
            ]
            anchor_fails = (dot[ret_i][0] != 0)
            # This pair must fail: NOT(all conditions hold)
            s.add(Or(ret_sec_fails + sec_ret_fails + [anchor_fails]))


def add_has_dichotomy(s, dot, n):
    """Assert HasDichotomy."""
    core = list(range(2, n))
    if len(core) < 1:
        s.add(False)  # Need at least 1 core element
        return

    # Part 1: ∃ classifier τ in core with τ·x ∈ {0,1} for all x
    cls_candidates = []
    for tau in core:
        is_cls = And([Or(dot[tau][j] == 0, dot[tau][j] == 1) for j in range(n)])
        cls_candidates.append(is_cls)
    s.add(Or(cls_candidates))

    # Part 2: Global dichotomy — every non-absorber is pure on core
    for y in core:
        # y is all-boolean on core OR all-non-boolean on core
        all_bool = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        all_nonbool = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        s.add(Or(all_bool, all_nonbool))

    # Part 3: Non-degeneracy — at least one non-classifier exists
    noncls_candidates = []
    for y in core:
        # y has some core output that is not boolean
        has_nonbool = Or([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        noncls_candidates.append(has_nonbool)
    s.add(Or(noncls_candidates))


def add_no_dichotomy(s, dot, n):
    """Assert ¬HasDichotomy.

    HasDichotomy = P1 ∧ P2 ∧ P3.
    ¬HasDichotomy = ¬P1 ∨ ¬P2 ∨ ¬P3.

    We use a disjunction of the three negations.
    """
    core = list(range(2, n))
    if len(core) < 1:
        return  # Trivially no dichotomy

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


def add_has_icp(s, dot, n):
    """Assert HasICP: ∃ pairwise distinct a,b,c in core satisfying ICP conditions."""
    core = list(range(2, n))
    if len(core) < 3:
        s.add(False)  # Need at least 3 core elements, so N >= 5
        return

    candidates = []
    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                # b preserves core
                b_pres = And([And(dot[b][x] != 0, dot[b][x] != 1) for x in core])
                # Factorization: a·x = c·(b·x) for all core x
                factor = And([
                    dot[a][x] == ite_lookup(dot, c, dot[b][x], n)
                    for x in core
                ])
                # Non-triviality: a takes ≥2 distinct values on core
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


def add_no_icp(s, dot, n):
    """Assert ¬HasICP: for every pairwise distinct (a,b,c) triple, at least one condition fails."""
    core = list(range(2, n))
    if len(core) < 3:
        return  # ICP is vacuously false, nothing to add

    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                # This triple must fail: NOT(b_pres ∧ factor ∧ nontriv)
                # = ¬b_pres ∨ ¬factor ∨ ¬nontriv

                # ¬b_pres: some core x has b·x ∈ {0,1}
                b_pres_fails = [Or(dot[b][x] == 0, dot[b][x] == 1) for x in core]

                # ¬factor: some core x has a·x ≠ c·(b·x)
                factor_fails = [
                    dot[a][x] != ite_lookup(dot, c, dot[b][x], n)
                    for x in core
                ]

                # ¬nontriv: a is constant on core (all values equal)
                # a·x = a·y for all core x,y
                nontriv_fails_parts = []
                for x in core:
                    for y in core:
                        if x < y:
                            nontriv_fails_parts.append(dot[a][x] != dot[a][y])
                if nontriv_fails_parts:
                    # nontriv = Or(pairs different)
                    # ¬nontriv = And(all pairs same) = Not(Or(pairs different))
                    nontriv_fails = Not(Or(nontriv_fails_parts))
                else:
                    nontriv_fails = True  # Can't be nontrivial

                s.add(Or(b_pres_fails + factor_fails + [nontriv_fails]))


def check_direction(direction, n, timeout_ms=TIMEOUT_MS):
    """Check if a non-implication direction is achievable at size N.

    Returns: 'sat', 'unsat', or 'timeout'
    """
    s = Solver()
    s.set("timeout", timeout_ms)
    dot = make_dot(n)
    add_e2pm(s, dot, n)

    if direction == "R_not_D":
        add_has_retract_pair_enum(s, dot, n)
        add_no_dichotomy(s, dot, n)
    elif direction == "R_not_H":
        add_has_retract_pair_enum(s, dot, n)
        add_no_icp(s, dot, n)
    elif direction == "D_not_R":
        add_has_dichotomy(s, dot, n)
        add_no_retract_pair(s, dot, n)
    elif direction == "D_not_H":
        add_has_dichotomy(s, dot, n)
        add_no_icp(s, dot, n)
    elif direction == "H_not_R":
        add_has_icp(s, dot, n)
        add_no_retract_pair(s, dot, n)
    elif direction == "H_not_D":
        add_has_icp(s, dot, n)
        add_no_dichotomy(s, dot, n)
    else:
        raise ValueError(f"Unknown direction: {direction}")

    result = s.check()
    if result == sat:
        return "sat", s, dot
    elif result == unsat:
        return "unsat", None, None
    else:
        return "timeout", None, None


def extract_table(s, dot, n):
    """Extract concrete Cayley table from a SAT model."""
    m = s.model()
    return [[m.evaluate(dot[i][j]).as_long() for j in range(n)] for i in range(n)]


def print_table(table, n):
    """Print a Cayley table."""
    header = "     " + "".join(f"{j:3d}" for j in range(n))
    print(header)
    print("     " + "---" * n)
    for i in range(n):
        row_str = "".join(f"{table[i][j]:3d}" for j in range(n))
        print(f"  {i:2d} |{row_str}")


def verify_e2pm(table, n):
    """Verify E2PM properties."""
    # Absorbers
    for j in range(n):
        if table[0][j] != 0 or table[1][j] != 1:
            return False
    # No extra absorbers
    for x in range(2, n):
        if all(table[x][j] == x for j in range(n)):
            return False
    # Extensionality
    for x in range(n):
        for y in range(x + 1, n):
            if table[x] == table[y]:
                return False
    return True


def verify_has_retract_pair(table, n):
    """Check if any retraction pair exists."""
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            ok = True
            # ret(sec(x)) = x for core x
            for x in range(2, n):
                sx = table[sec_i][x]
                if sx < 0 or sx >= n or table[ret_i][sx] != x:
                    ok = False
                    break
            if not ok:
                continue
            # sec(ret(x)) = x for core x
            for x in range(2, n):
                rx = table[ret_i][x]
                if rx < 0 or rx >= n or table[sec_i][rx] != x:
                    ok = False
                    break
            if not ok:
                continue
            # anchor
            if table[ret_i][0] != 0:
                continue
            return True
    return False


def verify_has_dichotomy(table, n):
    """Check if HasDichotomy holds."""
    core = list(range(2, n))
    # P1: classifier exists
    has_cls = False
    for tau in core:
        if all(table[tau][j] in (0, 1) for j in range(n)):
            has_cls = True
            break
    if not has_cls:
        return False

    # P2: global dichotomy
    for y in core:
        core_vals = [table[y][x] for x in core]
        all_bool = all(v in (0, 1) for v in core_vals)
        all_nonbool = all(v >= 2 for v in core_vals)
        if not (all_bool or all_nonbool):
            return False

    # P3: non-degeneracy
    has_noncls = False
    for y in core:
        core_vals = [table[y][x] for x in core]
        if any(v >= 2 for v in core_vals):
            has_noncls = True
            break
    return has_noncls


def verify_has_icp(table, n):
    """Check if HasICP holds."""
    core = list(range(2, n))
    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                # b preserves core
                if not all(table[b][x] >= 2 for x in core):
                    continue
                # factorization
                if not all(table[a][x] == table[c][table[b][x]] for x in core):
                    continue
                # nontrivial
                vals = set(table[a][x] for x in core)
                if len(vals) < 2:
                    continue
                return True
    return False


# ═══════════════════════════════════════════════════════════════════
# Main search
# ═══════════════════════════════════════════════════════════════════

DIRECTIONS = [
    ("R_not_D", "R⇏D", 8),
    ("R_not_H", "R⇏H", 6),
    ("D_not_R", "D⇏R", 5),
    ("D_not_H", "D⇏H", 10),
    ("H_not_R", "H⇏R", 6),
    ("H_not_D", "H⇏D", 10),
]


def main():
    print("=" * 70)
    print("  MINIMAL SIZES FOR 6 NON-IMPLICATION DIRECTIONS")
    print("=" * 70)
    print()

    results = {}

    for direction, label, current_witness in DIRECTIONS:
        print(f"\n{'─'*70}")
        print(f"  {label} (current witness: N={current_witness})")
        print(f"{'─'*70}")

        found_n = None
        max_n = current_witness

        for n in range(3, max_n + 1):
            t0 = time.time()
            print(f"  N={n}: ", end="", flush=True)

            result, solver, dot = check_direction(direction, n)
            elapsed = time.time() - t0

            if result == "sat":
                table = extract_table(solver, dot, n)
                # Verify
                ok_e2pm = verify_e2pm(table, n)
                if direction.startswith("R"):
                    ok_pos = verify_has_retract_pair(table, n)
                elif direction.startswith("D"):
                    ok_pos = verify_has_dichotomy(table, n)
                else:
                    ok_pos = verify_has_icp(table, n)

                if direction.endswith("_D"):
                    ok_neg = not verify_has_dichotomy(table, n)
                elif direction.endswith("_R"):
                    ok_neg = not verify_has_retract_pair(table, n)
                else:
                    ok_neg = not verify_has_icp(table, n)

                verified = ok_e2pm and ok_pos and ok_neg
                print(f"SAT ({elapsed:.2f}s) verified={verified}")

                if verified:
                    found_n = n
                    print(f"\n  Witness table ({n}x{n}):")
                    print_table(table, n)
                    break
                else:
                    print(f"    WARNING: verification failed! e2pm={ok_e2pm} pos={ok_pos} neg={ok_neg}")
                    # Print table for debugging
                    print_table(table, n)
                    # Don't accept this, keep searching
            elif result == "unsat":
                print(f"UNSAT ({elapsed:.2f}s)")
            else:
                print(f"TIMEOUT ({elapsed:.2f}s)")

        if found_n is None:
            print(f"  No improvement found (minimum is at current witness N={max_n})")
            found_n = max_n

        results[label] = (current_witness, found_n)

    # Summary table
    print(f"\n\n{'='*70}")
    print(f"  SUMMARY")
    print(f"{'='*70}")
    print()
    print(f"  | {'Direction':<10} | {'Current':>7} | {'Minimum':>7} | {'Improvement':>11} |")
    print(f"  |{'-'*12}|{'-'*9}|{'-'*9}|{'-'*13}|")
    for label, (current, minimum) in results.items():
        improvement = current - minimum
        imp_str = f"-{improvement}" if improvement > 0 else "none"
        print(f"  | {label:<10} | {current:>7} | {minimum:>7} | {imp_str:>11} |")

    print()
    return results


if __name__ == "__main__":
    main()
