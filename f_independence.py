#!/usr/bin/env python3
"""
Independence of Faithful Encoding (F) relative to R, D, H.

F (Faithful Encoding): An E2PM with retraction pair (s, r) satisfies F if
  the s-orbit from z1=0 covers all N elements:
    rep(0) = 0, rep(1) = s·0, rep(2) = s·(s·0), ..., rep(N-1) = s^(N-1)(0)
  and all N values are pairwise distinct.

Note: F implies R (needs a retraction pair to define s).

Independence questions tested:
  1. R+D+H ⇏ F  (known: N=5 witness has non-injective rep)
  2. F ⇏ D       (F+R without D)
  3. F ⇏ H       (F+R without H)
  4. F+D ⇏ H
  5. F+H ⇏ D
  6. F+D+H        (coexistence)
  7. F+D+H + strict self-sim  (does t exist with dot(dot(t,rep(a)),rep(b))=dot(a,b)?)
"""

from __future__ import annotations
import sys
import time
from z3 import And, If, Int, Not, Or, Solver, sat, unsat


TIMEOUT_MS = 60000  # 60 seconds per query


# ═══════════════════════════════════════════════════════════════════════
# SAT Helpers
# ═══════════════════════════════════════════════════════════════════════

def make_dot(n):
    return [[Int(f"d_{i}_{j}") for j in range(n)] for i in range(n)]


def ite_lookup(dot, row, col_expr, n):
    """dot[row][col_expr] via nested If-Then-Else."""
    entry = dot[row][0]
    for c in range(1, n):
        entry = If(col_expr == c, dot[row][c], entry)
    return entry


def add_e2pm(s, dot, n):
    """E2PM constraints: domain, absorbers, no extra absorbers, extensionality."""
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


def add_has_retract_pair_enum(s, dot, n):
    """Assert HasRetractPair: at least one (sec, ret) pair works."""
    candidates = []
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            ret_sec_ok = And([
                ite_lookup(dot, ret_i, dot[sec_i][x], n) == x
                for x in range(2, n)
            ])
            sec_ret_ok = And([
                ite_lookup(dot, sec_i, dot[ret_i][x], n) == x
                for x in range(2, n)
            ])
            anchor = (dot[ret_i][0] == 0)
            candidates.append(And(ret_sec_ok, sec_ret_ok, anchor))
    s.add(Or(candidates))


def add_no_retract_pair(s, dot, n):
    """Assert NOT HasRetractPair."""
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            ret_sec_fails = [
                ite_lookup(dot, ret_i, dot[sec_i][x], n) != x
                for x in range(2, n)
            ]
            sec_ret_fails = [
                ite_lookup(dot, sec_i, dot[ret_i][x], n) != x
                for x in range(2, n)
            ]
            anchor_fails = (dot[ret_i][0] != 0)
            s.add(Or(ret_sec_fails + sec_ret_fails + [anchor_fails]))


def add_has_dichotomy(s, dot, n):
    """Assert HasDichotomy."""
    core = list(range(2, n))
    if len(core) < 1:
        s.add(False)
        return
    # P1: classifier exists
    cls_candidates = []
    for tau in core:
        is_cls = And([Or(dot[tau][j] == 0, dot[tau][j] == 1) for j in range(n)])
        cls_candidates.append(is_cls)
    s.add(Or(cls_candidates))
    # P2: global dichotomy
    for y in core:
        all_bool = And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        all_nonbool = And([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        s.add(Or(all_bool, all_nonbool))
    # P3: non-degeneracy
    noncls_candidates = []
    for y in core:
        has_nonbool = Or([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        noncls_candidates.append(has_nonbool)
    s.add(Or(noncls_candidates))


def add_no_dichotomy(s, dot, n):
    """Assert NOT HasDichotomy = NOT(P1 & P2 & P3)."""
    core = list(range(2, n))
    if len(core) < 1:
        return
    # NOT P1: no classifier
    no_classifier = And([
        Or([And(dot[tau][j] != 0, dot[tau][j] != 1) for j in range(n)])
        for tau in core
    ])
    # NOT P2: some element is mixed on core
    mixed_elements = []
    for y in core:
        has_bool = Or([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        has_nonbool = Or([And(dot[y][x] != 0, dot[y][x] != 1) for x in core])
        mixed_elements.append(And(has_bool, has_nonbool))
    some_mixed = Or(mixed_elements)
    # NOT P3: all core elements are classifiers
    all_classifiers = And([
        And([Or(dot[y][x] == 0, dot[y][x] == 1) for x in core])
        for y in core
    ])
    s.add(Or(no_classifier, some_mixed, all_classifiers))


def add_has_icp(s, dot, n):
    """Assert HasICP."""
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


def add_no_icp(s, dot, n):
    """Assert NOT HasICP."""
    core = list(range(2, n))
    if len(core) < 3:
        return
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


def add_faithful_encoding(s, dot, n):
    """Assert F: exists sec, ret forming retraction pair AND sec-orbit from 0 covers all N elements.

    We enumerate all (sec, ret) pairs. For each pair, compute rep values and require distinctness.
    At least one pair must work.
    """
    candidates = []
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            # Retraction pair conditions
            ret_sec_ok = And([
                ite_lookup(dot, ret_i, dot[sec_i][x], n) == x
                for x in range(2, n)
            ])
            sec_ret_ok = And([
                ite_lookup(dot, sec_i, dot[ret_i][x], n) == x
                for x in range(2, n)
            ])
            anchor = (dot[ret_i][0] == 0)

            # Compute rep values: rep[0]=0, rep[k+1]=sec·rep[k]
            rep = [None] * n
            rep[0] = 0  # concrete integer
            for k in range(1, n):
                if k == 1:
                    rep[k] = dot[sec_i][0]
                else:
                    rep[k] = ite_lookup(dot, sec_i, rep[k - 1], n)

            # All rep values pairwise distinct
            distinct_conds = []
            for i in range(n):
                for j in range(i + 1, n):
                    ri = rep[i]
                    rj = rep[j]
                    distinct_conds.append(ri != rj)

            candidates.append(And(ret_sec_ok, sec_ret_ok, anchor, And(distinct_conds)))

    s.add(Or(candidates))


def add_no_faithful_encoding(s, dot, n):
    """Assert NOT F: for every (sec, ret) retraction pair, the sec-orbit is NOT all-distinct.

    Either the pair is not a retraction pair, OR the orbit has a repeat.
    """
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            # Retraction pair conditions
            ret_sec_fails = [
                ite_lookup(dot, ret_i, dot[sec_i][x], n) != x
                for x in range(2, n)
            ]
            sec_ret_fails = [
                ite_lookup(dot, sec_i, dot[ret_i][x], n) != x
                for x in range(2, n)
            ]
            anchor_fails = (dot[ret_i][0] != 0)

            # Compute rep values
            rep = [None] * n
            rep[0] = 0
            for k in range(1, n):
                if k == 1:
                    rep[k] = dot[sec_i][0]
                else:
                    rep[k] = ite_lookup(dot, sec_i, rep[k - 1], n)

            # NOT all distinct = some pair equal
            some_equal = []
            for i in range(n):
                for j in range(i + 1, n):
                    some_equal.append(rep[i] == rep[j])

            # This (sec, ret) pair fails: not a retraction pair OR orbit not injective
            s.add(Or(ret_sec_fails + sec_ret_fails + [anchor_fails] + some_equal))


# ═══════════════════════════════════════════════════════════════════════
# Verification (independent of Z3)
# ═══════════════════════════════════════════════════════════════════════

def extract_table(s, dot, n):
    m = s.model()
    return [[m.evaluate(dot[i][j]).as_long() for j in range(n)] for i in range(n)]


def verify_e2pm(table, n):
    for j in range(n):
        if table[0][j] != 0 or table[1][j] != 1:
            return False
    for x in range(2, n):
        if all(table[x][j] == x for j in range(n)):
            return False
    for x in range(n):
        for y in range(x + 1, n):
            if table[x] == table[y]:
                return False
    return True


def find_retract_pairs(table, n):
    """Find all (sec, ret) retraction pairs."""
    pairs = []
    for sec_i in range(2, n):
        for ret_i in range(2, n):
            ok = True
            for x in range(2, n):
                sx = table[sec_i][x]
                if sx < 0 or sx >= n or table[ret_i][sx] != x:
                    ok = False
                    break
            if not ok:
                continue
            for x in range(2, n):
                rx = table[ret_i][x]
                if rx < 0 or rx >= n or table[sec_i][rx] != x:
                    ok = False
                    break
            if not ok:
                continue
            if table[ret_i][0] != 0:
                continue
            pairs.append((sec_i, ret_i))
    return pairs


def verify_faithful(table, n):
    """Check F: some retraction pair has injective s-orbit."""
    pairs = find_retract_pairs(table, n)
    for sec_i, ret_i in pairs:
        rep = [0]
        for k in range(1, n):
            rep.append(table[sec_i][rep[-1]])
        if len(set(rep)) == n:
            return True, sec_i, ret_i, rep
    return False, None, None, None


def verify_has_dichotomy(table, n):
    core = list(range(2, n))
    has_cls = any(all(table[tau][j] in (0, 1) for j in range(n)) for tau in core)
    if not has_cls:
        return False
    for y in core:
        core_vals = [table[y][x] for x in core]
        all_bool = all(v in (0, 1) for v in core_vals)
        all_nonbool = all(v >= 2 for v in core_vals)
        if not (all_bool or all_nonbool):
            return False
    has_noncls = any(any(table[y][x] >= 2 for x in core) for y in core)
    return has_noncls


def verify_has_icp(table, n):
    core = list(range(2, n))
    for a in core:
        for b in core:
            if b == a:
                continue
            for c in core:
                if c == a or c == b:
                    continue
                if not all(table[b][x] >= 2 for x in core):
                    continue
                if not all(table[a][x] == table[c][table[b][x]] for x in core):
                    continue
                vals = set(table[a][x] for x in core)
                if len(vals) >= 2:
                    return True
    return False


def check_strict_selfsim(table, n, rep):
    """Check if any t satisfies dot(dot(t, rep(a)), rep(b)) = dot(a,b) for all a,b."""
    for t in range(n):
        ok = True
        for a in range(n):
            if not ok:
                break
            for b in range(n):
                lhs = table[table[t][rep[a]]][rep[b]]
                rhs = table[a][b]
                if lhs != rhs:
                    ok = False
                    break
        if ok:
            return True, t
    return False, None


def print_table(table, n):
    header = "     " + "".join(f"{j:3d}" for j in range(n))
    print(header)
    print("     " + "---" * n)
    for i in range(n):
        row_str = "".join(f"{table[i][j]:3d}" for j in range(n))
        print(f"  {i:2d} |{row_str}")


# ═══════════════════════════════════════════════════════════════════════
# Test Definitions
# ═══════════════════════════════════════════════════════════════════════

TESTS = [
    {
        "id": "RDH_not_F",
        "label": "R+D+H => F?",
        "desc": "R+D+H + NOT F  (should be SAT: known N=5 witness)",
        "pos": ["R", "D", "H"],
        "neg": ["F"],
        "min_n": 5,
        "max_n": 8,
    },
    {
        "id": "F_not_D",
        "label": "F => D?",
        "desc": "F + NOT D  (F without dichotomy)",
        "pos": ["F"],
        "neg": ["D"],
        "min_n": 5,
        "max_n": 8,
    },
    {
        "id": "F_not_H",
        "label": "F => H?",
        "desc": "F + NOT H  (F without ICP)",
        "pos": ["F"],
        "neg": ["H"],
        "min_n": 5,
        "max_n": 8,
    },
    {
        "id": "FD_not_H",
        "label": "F+D => H?",
        "desc": "F + D + NOT H",
        "pos": ["F", "D"],
        "neg": ["H"],
        "min_n": 5,
        "max_n": 8,
    },
    {
        "id": "FH_not_D",
        "label": "F+H => D?",
        "desc": "F + H + NOT D",
        "pos": ["F", "H"],
        "neg": ["D"],
        "min_n": 5,
        "max_n": 8,
    },
    {
        "id": "FDH",
        "label": "F+D+H coexist?",
        "desc": "F + D + H  (all four properties)",
        "pos": ["F", "D", "H"],
        "neg": [],
        "min_n": 5,
        "max_n": 10,
    },
]


def build_solver(test, n):
    """Build Z3 solver for a test at size n."""
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    dot = make_dot(n)
    add_e2pm(s, dot, n)

    for prop in test["pos"]:
        if prop == "R":
            add_has_retract_pair_enum(s, dot, n)
        elif prop == "D":
            add_has_dichotomy(s, dot, n)
        elif prop == "H":
            add_has_icp(s, dot, n)
        elif prop == "F":
            add_faithful_encoding(s, dot, n)

    for prop in test["neg"]:
        if prop == "R":
            add_no_retract_pair(s, dot, n)
        elif prop == "D":
            add_no_dichotomy(s, dot, n)
        elif prop == "H":
            add_no_icp(s, dot, n)
        elif prop == "F":
            add_no_faithful_encoding(s, dot, n)

    return s, dot


def verify_witness(table, n, test):
    """Verify all properties on extracted table."""
    ok = True
    details = {}

    # Always verify E2PM
    e2pm = verify_e2pm(table, n)
    details["E2PM"] = e2pm
    if not e2pm:
        ok = False

    for prop in test["pos"]:
        if prop == "R":
            val = len(find_retract_pairs(table, n)) > 0
            details["R"] = val
            if not val:
                ok = False
        elif prop == "D":
            val = verify_has_dichotomy(table, n)
            details["D"] = val
            if not val:
                ok = False
        elif prop == "H":
            val = verify_has_icp(table, n)
            details["H"] = val
            if not val:
                ok = False
        elif prop == "F":
            val, sec, ret, rep = verify_faithful(table, n)
            details["F"] = val
            details["F_sec"] = sec
            details["F_ret"] = ret
            details["F_rep"] = rep
            if not val:
                ok = False

    for prop in test["neg"]:
        if prop == "R":
            val = len(find_retract_pairs(table, n)) > 0
            details["not_R"] = not val
            if val:
                ok = False
        elif prop == "D":
            val = verify_has_dichotomy(table, n)
            details["not_D"] = not val
            if val:
                ok = False
        elif prop == "H":
            val = verify_has_icp(table, n)
            details["not_H"] = not val
            if val:
                ok = False
        elif prop == "F":
            val, _, _, _ = verify_faithful(table, n)
            details["not_F"] = not val
            if val:
                ok = False

    return ok, details


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main():
    print("=" * 72)
    print("  INDEPENDENCE OF FAITHFUL ENCODING (F) RELATIVE TO R, D, H")
    print("=" * 72)
    print()
    print("  F = Faithful Encoding: s-orbit from 0 covers all N elements")
    print("  R = Retraction pair exists")
    print("  D = Classifier Dichotomy (Kripke)")
    print("  H = Internal Composition Property (ICP)")
    print()
    print("  Note: F implies R (needs retraction pair to define s).")
    print()

    results = {}
    fdh_witnesses = []  # Collect F+D+H witnesses for strict self-sim test

    for test in TESTS:
        print(f"\n{'─'*72}")
        print(f"  Test: {test['label']}")
        print(f"  Query: {test['desc']}")
        print(f"{'─'*72}")

        found = False
        for n in range(test["min_n"], test["max_n"] + 1):
            t0 = time.time()
            print(f"  N={n}: ", end="", flush=True)

            s, dot = build_solver(test, n)
            result = s.check()
            elapsed = time.time() - t0

            if result == sat:
                table = extract_table(s, dot, n)
                ok, details = verify_witness(table, n, test)

                if ok:
                    print(f"SAT ({elapsed:.1f}s) -- VERIFIED")
                    print(f"\n  Cayley table ({n}x{n}):")
                    print_table(table, n)

                    # Show retraction pair and rep if F holds
                    if "F" in details and details["F"]:
                        sec = details["F_sec"]
                        ret = details["F_ret"]
                        rep = details["F_rep"]
                        print(f"\n  s={sec}, r={ret}")
                        print(f"  rep = {rep}")

                    # Show which properties hold/fail
                    print(f"\n  Properties:")
                    for k, v in details.items():
                        if k.startswith("F_"):
                            continue
                        status = "HOLDS" if v else "FAILS"
                        print(f"    {k}: {status}")

                    results[test["id"]] = ("SAT", n, table, details)
                    found = True

                    # Collect F+D+H witnesses
                    if test["id"] == "FDH":
                        fdh_witnesses.append((n, table, details))

                    break
                else:
                    print(f"SAT ({elapsed:.1f}s) -- VERIFICATION FAILED")
                    for k, v in details.items():
                        if k.startswith("F_"):
                            continue
                        if not v:
                            print(f"    FAIL: {k}")
            elif result == unsat:
                print(f"UNSAT ({elapsed:.1f}s)")
            else:
                print(f"TIMEOUT ({elapsed:.1f}s)")

        if not found:
            results[test["id"]] = ("NOT_FOUND", test["max_n"], None, None)
            print(f"  ==> No witness found up to N={test['max_n']}")

    # ───────────────────────────────────────────────────────────────
    # Strict self-simulation test on F+D+H witnesses
    # ───────────────────────────────────────────────────────────────
    print(f"\n\n{'─'*72}")
    print(f"  STRICT SELF-SIMULATION TEST ON F+D+H WITNESSES")
    print(f"{'─'*72}")

    if not fdh_witnesses:
        print("  No F+D+H witness found; skipping strict self-sim test.")
        # Try building F+D+H at larger sizes specifically for this test
        print("  Searching for F+D+H witnesses at N=5..10 for self-sim check...")
        fdh_test = {
            "pos": ["F", "D", "H"],
            "neg": [],
        }
        for n in range(5, 11):
            t0 = time.time()
            print(f"  N={n}: ", end="", flush=True)
            s, dot = build_solver(fdh_test, n)
            result = s.check()
            elapsed = time.time() - t0
            if result == sat:
                table = extract_table(s, dot, n)
                ok, details = verify_witness(table, n, fdh_test)
                if ok:
                    print(f"SAT ({elapsed:.1f}s) -- checking self-sim")
                    fdh_witnesses.append((n, table, details))
                    break
                else:
                    print(f"SAT ({elapsed:.1f}s) -- verification failed")
            elif result == unsat:
                print(f"UNSAT ({elapsed:.1f}s)")
            else:
                print(f"TIMEOUT ({elapsed:.1f}s)")

    for (n, table, details) in fdh_witnesses:
        f_ok, sec, ret, rep = verify_faithful(table, n)
        if not f_ok:
            print(f"  N={n}: F does not hold (skipping)")
            continue

        print(f"\n  N={n}, s={sec}, r={ret}, rep={rep}")
        ss_ok, t_val = check_strict_selfsim(table, n, rep)
        if ss_ok:
            print(f"  STRICT SELF-SIM: YES (t={t_val})")
            print(f"  dot(dot({t_val}, rep(a)), rep(b)) = dot(a, b) for all a,b")
            # Verify a few
            print(f"  Spot checks:")
            for a in range(min(3, n)):
                for b in range(min(3, n)):
                    lhs = table[table[t_val][rep[a]]][rep[b]]
                    rhs = table[a][b]
                    print(f"    dot(dot({t_val},{rep[a]}),{rep[b]}) = {lhs}, dot({a},{b}) = {rhs}  {'OK' if lhs==rhs else 'FAIL'}")
        else:
            print(f"  STRICT SELF-SIM: NO (no t works)")
            # Show why: for each candidate t, show first failure
            print(f"  First failures per candidate t:")
            for t in range(n):
                for a in range(n):
                    found_fail = False
                    for b in range(n):
                        lhs = table[table[t][rep[a]]][rep[b]]
                        rhs = table[a][b]
                        if lhs != rhs:
                            print(f"    t={t}: fails at (a={a},b={b}): "
                                  f"dot(dot({t},{rep[a]}),{rep[b]})={lhs} != dot({a},{b})={rhs}")
                            found_fail = True
                            break
                    if found_fail:
                        break

    # ───────────────────────────────────────────────────────────────
    # Summary
    # ───────────────────────────────────────────────────────────────
    print(f"\n\n{'='*72}")
    print(f"  SUMMARY: INDEPENDENCE STRUCTURE OF F")
    print(f"{'='*72}")
    print()
    print(f"  {'Test':<20} {'Result':<12} {'Min N':<8} {'Interpretation'}")
    print(f"  {'─'*20} {'─'*12} {'─'*8} {'─'*30}")

    interpretations = {
        "RDH_not_F": ("R+D+H !=> F", "F is independent of R+D+H"),
        "F_not_D": ("F !=> D", "F does not imply D"),
        "F_not_H": ("F !=> H", "F does not imply H"),
        "FD_not_H": ("F+D !=> H", "F+D does not imply H"),
        "FH_not_D": ("F+H !=> D", "F+H does not imply D"),
        "FDH": ("F+D+H SAT", "All four coexist"),
    }

    for test_id, (short, interp) in interpretations.items():
        if test_id in results:
            status, n_val, _, _ = results[test_id]
            if status == "SAT":
                print(f"  {short:<20} {'SAT':<12} N={n_val:<5} {interp}")
            else:
                print(f"  {short:<20} {'OPEN':<12} {'>'}{test_id and TESTS[[t['id'] for t in TESTS].index(test_id)]['max_n']:<5} NOT confirmed")
        else:
            print(f"  {short:<20} {'SKIPPED':<12}")

    print()
    # Check if F is fully independent
    f_not_d = results.get("F_not_D", ("NOT_FOUND",))[0] == "SAT"
    f_not_h = results.get("F_not_H", ("NOT_FOUND",))[0] == "SAT"
    rdh_not_f = results.get("RDH_not_F", ("NOT_FOUND",))[0] == "SAT"
    fdh_sat = results.get("FDH", ("NOT_FOUND",))[0] == "SAT"

    if f_not_d and f_not_h and rdh_not_f:
        print("  F is FULLY INDEPENDENT of both D and H.")
    else:
        missing = []
        if not rdh_not_f:
            missing.append("R+D+H !=> F")
        if not f_not_d:
            missing.append("F !=> D")
        if not f_not_h:
            missing.append("F !=> H")
        print(f"  Independence PARTIALLY confirmed. Missing: {', '.join(missing)}")

    if fdh_sat:
        print("  F+D+H coexistence confirmed.")
    else:
        print("  F+D+H coexistence NOT confirmed in search range.")

    print()


if __name__ == "__main__":
    main()
