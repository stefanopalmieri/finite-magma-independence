#!/usr/bin/env python3
"""
R+D+H-Determined Self-Simulation Test
======================================

Tests whether R, D, H structure determines meaningful eval rules.

CRITICAL INSIGHT: Under R-eval, s is lazy, so rep(a) = s^a(z1) as a
TERM stays compound for a >= 1. This means:
  eval_R(rep(0)) = Atom(z1)
  eval_R(rep(1)) = App(Atom(s), Atom(z1))  -- COMPOUND
  eval_R(rep(2)) = App(Atom(s), App(Atom(s), Atom(z1)))  -- COMPOUND

The r-decode rule is what makes these compound reps useful:
  App(Atom(r), App(Atom(s), X)) -> X  (peel one s-layer)

So the sim term must use r to decode the compound rep arguments.
This is fundamentally different from standard eval where all reps
reduce to atoms.
"""

from __future__ import annotations
import json
import sys
from dataclasses import dataclass
from typing import Optional
from pathlib import Path
from itertools import product


# ===================================================================
# Term Algebra
# ===================================================================

@dataclass(frozen=True)
class Atom:
    val: int
    def __repr__(self):
        return f"{self.val}"

@dataclass(frozen=True)
class App:
    left: object
    right: object
    def __repr__(self):
        return f"({self.left} . {self.right})"

Term = Atom | App

def term_eq(t1, t2):
    if isinstance(t1, Atom) and isinstance(t2, Atom):
        return t1.val == t2.val
    if isinstance(t1, App) and isinstance(t2, App):
        return term_eq(t1.left, t2.left) and term_eq(t1.right, t2.right)
    return False

def term_str(t, depth=0):
    if depth > 20:
        return "..."
    if isinstance(t, Atom):
        return str(t.val)
    return f"({term_str(t.left, depth+1)}.{term_str(t.right, depth+1)})"

def term_size(t):
    if isinstance(t, Atom):
        return 1
    return 1 + term_size(t.left) + term_size(t.right)


# ===================================================================
# Rep Encoding (as TERMS, not ground values)
# ===================================================================

def make_rep_term(s, z1, a):
    """Build rep(a) = s^a(z1) as a TERM."""
    t = Atom(z1)
    for _ in range(a):
        t = App(Atom(s), t)
    return t


def compute_rep_ground(table, s, z1, N):
    """Compute s^a(z1) in ground algebra (for standard eval)."""
    vals = [0] * N
    vals[0] = z1
    for k in range(1, N):
        vals[k] = table[s][vals[k - 1]]
    return vals


# ===================================================================
# R-Determined Eval
# ===================================================================

MAX_DEPTH = 2000

def rdh_eval_r(term, table, s, r, depth=0):
    """
    R-determined eval:
      - atom(s) is LAZY (preserves encoding structure)
      - atom(r) DECODES s-layers: r . (s . X) -> X
      - All other atoms: ground apply
    """
    if depth > MAX_DEPTH:
        return None
    if isinstance(term, Atom):
        return term
    v1 = rdh_eval_r(term.left, table, s, r, depth + 1)
    if v1 is None:
        return None
    v2 = rdh_eval_r(term.right, table, s, r, depth + 1)
    if v2 is None:
        return None
    return rdh_apply_r(v1, v2, table, s, r)


def rdh_apply_r(v1, v2, table, s, r):
    N = len(table)
    # Ground apply: atom . atom
    if isinstance(v1, Atom) and isinstance(v2, Atom):
        a, b = v1.val, v2.val
        if 0 <= a < N and 0 <= b < N:
            return Atom(table[a][b])
        return App(v1, v2)
    # s is lazy: s . anything -> App(s, anything)
    if isinstance(v1, Atom) and v1.val == s:
        return App(Atom(s), v2)
    # r decodes s-layers: r . (s . X) -> X
    if isinstance(v1, Atom) and v1.val == r:
        if isinstance(v2, App) and isinstance(v2.left, Atom) and v2.left.val == s:
            return v2.right
        # r . atom(x) -> atom(table[r][x]) (ground apply)
        if isinstance(v2, Atom):
            return Atom(table[r][v2.val])
    # Stuck
    return App(v1, v2)


# ===================================================================
# R+H-Determined Eval
# ===================================================================

def rdh_eval_rh(term, table, s, r, icp_a, icp_b, icp_c, depth=0):
    if depth > MAX_DEPTH:
        return None
    if isinstance(term, Atom):
        return term
    v1 = rdh_eval_rh(term.left, table, s, r, icp_a, icp_b, icp_c, depth + 1)
    if v1 is None:
        return None
    v2 = rdh_eval_rh(term.right, table, s, r, icp_a, icp_b, icp_c, depth + 1)
    if v2 is None:
        return None
    return rdh_apply_rh(v1, v2, table, s, r, icp_a, icp_b, icp_c, depth)


def rdh_apply_rh(v1, v2, table, s, r, icp_a, icp_b, icp_c, depth=0):
    if depth > MAX_DEPTH:
        return None
    N = len(table)
    # Ground apply
    if isinstance(v1, Atom) and isinstance(v2, Atom):
        a, b = v1.val, v2.val
        if 0 <= a < N and 0 <= b < N:
            return Atom(table[a][b])
        return App(v1, v2)
    # s is lazy
    if isinstance(v1, Atom) and v1.val == s:
        return App(Atom(s), v2)
    # r decodes
    if isinstance(v1, Atom) and v1.val == r:
        if isinstance(v2, App) and isinstance(v2.left, Atom) and v2.left.val == s:
            return v2.right
        if isinstance(v2, Atom):
            return Atom(table[r][v2.val])
    # H: icp_a . X = icp_c . (icp_b . X)
    if isinstance(v1, Atom) and v1.val == icp_a:
        bv = rdh_apply_rh(Atom(icp_b), v2, table, s, r, icp_a, icp_b, icp_c, depth + 1)
        if bv is None:
            return None
        return rdh_apply_rh(Atom(icp_c), bv, table, s, r, icp_a, icp_b, icp_c, depth + 1)
    # Stuck
    return App(v1, v2)


# ===================================================================
# Standard Eval (baseline)
# ===================================================================

def std_eval(t, table):
    if isinstance(t, Atom):
        return t
    v1 = std_eval(t.left, table)
    v2 = std_eval(t.right, table)
    if isinstance(v1, Atom) and isinstance(v2, Atom):
        N = len(table)
        a, b = v1.val, v2.val
        if 0 <= a < N and 0 <= b < N:
            return Atom(table[a][b])
    return App(v1, v2)


# ===================================================================
# Property Checkers
# ===================================================================

def find_retraction_pairs(table, N):
    core = list(range(2, N))
    pairs = []
    for sv in core:
        for rv in core:
            ok = True
            for x in core:
                sx = table[sv][x]
                if sx < 0 or sx >= N or table[rv][sx] != x:
                    ok = False; break
                rx = table[rv][x]
                if rx < 0 or rx >= N or table[sv][rx] != x:
                    ok = False; break
            if ok:
                pairs.append((sv, rv))
    return pairs

def find_classifiers(table, N):
    return [tau for tau in range(2, N) if all(table[tau][j] in (0, 1) for j in range(N))]

def check_kripke(table, N):
    for x in range(2, N):
        cv = [table[x][j] for j in range(2, N)]
        if not (all(v in (0, 1) for v in cv) or all(v >= 2 for v in cv)):
            return False
    return True

def find_icp_triples(table, N):
    core = list(range(2, N))
    triples = []
    for b in core:
        if not all(table[b][x] >= 2 for x in core):
            continue
        for a in core:
            if a == b: continue
            if len(set(table[a][x] for x in core)) < 2: continue
            for c in core:
                if c == a or c == b: continue
                if all(table[a][x] == table[c][table[b][x]] for x in core):
                    triples.append((a, b, c))
    return triples


# ===================================================================
# Self-Simulation Test
# ===================================================================

def test_selfsim(eval_fn, table, N, s, z1, sim_term):
    """
    Check: eval(App(App(sim_term, rep(a)), rep(b))) == Atom(table[a][b])
    for all a, b.
    """
    total = N * N
    successes = 0
    failures = []
    for a in range(N):
        for b in range(N):
            term = App(App(sim_term, make_rep_term(s, z1, a)), make_rep_term(s, z1, b))
            result = eval_fn(term)
            expected = Atom(table[a][b])
            if result is not None and isinstance(result, Atom) and result.val == expected.val:
                successes += 1
            else:
                failures.append((a, b, result, expected))
                if len(failures) > 20:
                    # Early exit for hopeless cases
                    return successes, total, failures
    return successes, total, failures


# ===================================================================
# Test Tables
# ===================================================================

TABLE_5 = [
    [0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1],
    [0, 2, 2, 3, 4],
    [0, 0, 0, 1, 0],
    [0, 1, 0, 1, 0],
]

TABLE_6 = [
    [0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [3, 3, 4, 2, 5, 3],
    [0, 1, 3, 5, 2, 4],
    [0, 0, 1, 0, 1, 1],
    [2, 2, 5, 4, 3, 2],
]

TABLE_8_RnotD = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1],
    [3, 3, 7, 3, 4, 6, 5, 2],
    [0, 1, 7, 3, 4, 6, 5, 2],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [6, 2, 6, 2, 1, 1, 1, 1],
    [0, 0, 5, 2, 2, 2, 2, 2],
    [2, 2, 2, 1, 2, 2, 6, 3],
]

TABLE_6_RnotH = [
    [0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [0, 3, 3, 2, 5, 4],
    [2, 4, 5, 5, 1, 4],
    [5, 3, 0, 0, 3, 2],
    [4, 2, 2, 2, 2, 2],
]


def load_tables():
    tables = [
        ("N=5 R+D+H (Witness5)",   TABLE_5),
        ("N=6 R+D+H (Witness6)",   TABLE_6),
        ("N=8 R-not-D (Counter.)",  TABLE_8_RnotD),
        ("N=6 R-not-H (sNoH6)",    TABLE_6_RnotH),
    ]
    cex_path = Path(__file__).parent / "counterexamples.json"
    if cex_path.exists():
        with open(cex_path) as f:
            cex = json.load(f)
        for key, label in [("H_not_D", "N=10 H-not-D"),
                           ("D_not_H_compose", "N=10 D-not-H(comp)"),
                           ("D_not_H_inert", "N=10 D-not-H(inert)")]:
            if key in cex:
                tables.append((label, cex[key]))
    return tables


# ===================================================================
# Main Analysis
# ===================================================================

def analyze_table(name, table):
    N = len(table)
    print(f"\n{'='*72}")
    print(f"  {name} (N={N})")
    print(f"{'='*72}")

    # Print table
    hdr = "     " + "".join(f"{j:3d}" for j in range(N))
    print(hdr)
    print("     " + "---" * N)
    for i in range(N):
        print(f"  {i:2d} |" + "".join(f"{table[i][j]:3d}" for j in range(N)))

    # Properties
    ret_pairs = find_retraction_pairs(table, N)
    classifiers = find_classifiers(table, N)
    has_kripke = check_kripke(table, N)
    icp_trips = find_icp_triples(table, N)
    has_D = len(classifiers) > 0 and has_kripke
    has_H = len(icp_trips) > 0

    print(f"\n  Retraction pairs: {ret_pairs}")
    print(f"  D: classifiers={classifiers}, Kripke={has_kripke} => {has_D}")
    print(f"  H: ICP={icp_trips[:5]}{'...' if len(icp_trips)>5 else ''} => {has_H}")

    if not ret_pairs:
        print(f"  No retraction pair. Skipping.")
        return None

    # Pick a retraction pair
    s, r = ret_pairs[0]
    z1 = 0  # Start rep from absorber 0

    print(f"\n  Using s={s}, r={r}, z1={z1}")

    # Show what R-eval does to rep terms
    print(f"\n  --- What R-eval does to rep(a) ---")
    print(f"  Under STANDARD eval: eval(rep(a)) = atom(s^a(z1)) [ground]")
    print(f"  Under R-eval: s is LAZY, so rep(a) stays compound for a>=1")
    print()

    def eval_r(term):
        return rdh_eval_r(term, table, s, r)

    for a in range(min(N, 5)):
        rt = make_rep_term(s, z1, a)
        std_v = std_eval(rt, table)
        r_v = eval_r(rt)
        print(f"    rep({a}): std -> {std_v}, R-eval -> {term_str(r_v)}")

    # Show r-decode in action
    print(f"\n  --- r-decode examples ---")
    for a in range(1, min(N, 4)):
        # r . rep(a) should peel one s-layer
        rt = make_rep_term(s, z1, a)
        r_rt = App(Atom(r), rt)
        v = eval_r(r_rt)
        print(f"    r . rep({a}) = {term_str(v)}")

    # -------------------------------------------------------
    # TEST: R-eval self-simulation with atom sim terms
    # -------------------------------------------------------
    print(f"\n  --- R-eval self-simulation (atom sim terms) ---")
    print(f"  Need: eval_R(App(App(atom(c), rep(a)), rep(b))) = Atom(table[a][b])")

    # For atom(c) with c != s:
    #   eval_R(App(atom(c), rep(0))) = eval_R(App(atom(c), atom(z1))) = Atom(table[c][z1])
    #   eval_R(App(atom(c), rep(1))) = eval_R(App(atom(c), App(atom(s), atom(z1))))
    #     v1 = atom(c), v2 = App(atom(s), atom(z1))  [s is lazy]
    #     c != s, so this is STUCK: App(atom(c), App(atom(s), atom(z1)))
    # So atom(c) with c != s can only handle rep(0), not rep(a) for a >= 1.

    # For atom(s):
    #   eval_R(App(atom(s), rep(a))) = App(atom(s), rep(a))  [s is lazy]
    #   Then App(App(atom(s), rep(a)), rep(b)) is App of compound, STUCK.

    # For atom(r):
    #   eval_R(App(atom(r), rep(0))) = atom(table[r][z1])
    #   eval_R(App(atom(r), rep(1))) = eval_R(App(atom(r), App(atom(s), atom(z1))))
    #     = atom(z1)  [r peels s-layer, revealing z1]
    #   eval_R(App(atom(r), rep(2))) = eval_R(App(atom(r), App(atom(s), App(atom(s), atom(z1)))))
    #     = App(atom(s), atom(z1))  [r peels one s-layer, compound result]
    #   Then App(App(atom(s), atom(z1)), rep(b)) is App of compound, STUCK for b >= 1.

    print(f"\n  Detailed trace for each atom sim term c:")
    for c in range(N):
        # Check first few (a, b) pairs
        results_for_c = []
        any_fail = False
        for a in range(min(N, 4)):
            for b in range(min(N, 3)):
                term = App(App(Atom(c), make_rep_term(s, z1, a)), make_rep_term(s, z1, b))
                v = eval_r(term)
                expected = table[a][b]
                ok = isinstance(v, Atom) and v.val == expected
                results_for_c.append((a, b, v, expected, ok))
                if not ok:
                    any_fail = True

        # Summary for this c
        n_ok = sum(1 for _, _, _, _, ok in results_for_c if ok)
        n_tot = len(results_for_c)
        label = ""
        if c == s: label = " [s=lazy]"
        elif c == r: label = " [r=decode]"
        print(f"    c={c}{label}: {n_ok}/{n_tot} correct (of first {n_tot})")
        if any_fail:
            # Show first failure
            for a, b, v, exp, ok in results_for_c:
                if not ok:
                    print(f"      FAIL at ({a},{b}): got {term_str(v)}, expected {exp}")
                    break

    # -------------------------------------------------------
    # KEY ANALYSIS: What compound sim terms could work?
    # -------------------------------------------------------
    print(f"\n  --- Can COMPOUND sim terms work under R-eval? ---")
    print(f"  The problem: for a >= 1, rep(a) is compound under R-eval.")
    print(f"  App(atom(c), compound) is STUCK unless c == s or c == r.")
    print(f"  So the sim term must handle compound arguments.")
    print()

    # The only way to interact with compound rep(a):
    # 1. r . rep(a) = rep(a-1)  [peel one layer]
    # 2. s . rep(a) = rep(a+1)  [add one layer]
    #
    # To extract information from rep(a), we need to peel ALL a layers
    # using repeated r applications. But we don't know a in advance!
    # This requires a RECURSIVE sim term -- exactly the Y combinator.
    #
    # Without Y, we can peel a FIXED number of layers.
    # A sim term that peels k layers works for rep(k) but not rep(k+1).

    print(f"  To handle rep(a) for arbitrary a under R-eval:")
    print(f"  - Must peel a s-layers using r (one at a time)")
    print(f"  - But a varies! Need recursive peeling.")
    print(f"  - Fixed-depth sim terms can only handle fixed rep depths.")
    print()

    # Test: can any compound term of depth <= 3 work?
    # For small N, brute-force
    if N <= 6:
        print(f"  Brute-force compound sim term search (depth 1, N={N}):")
        found_any = False
        for c in range(N):
            for d in range(N):
                t = App(Atom(c), Atom(d))
                succ, total, fails = test_selfsim(eval_r, table, N, s, z1, t)
                if succ == total:
                    print(f"    FOUND: {term_str(t)} = {succ}/{total}")
                    found_any = True
                elif succ > N:  # Interesting partial match
                    print(f"    Partial: {term_str(t)} = {succ}/{total}")
        if not found_any:
            print(f"    No depth-1 compound sim term works.")
    else:
        print(f"  (Skipping brute-force for N={N}, too large)")

    # -------------------------------------------------------
    # ALTERNATIVE REP: identity encoding
    # -------------------------------------------------------
    # What if rep(a) = atom(a) (identity)? Then all reps are atoms
    # and the R-eval rules are invisible. This reduces to strict self-sim.
    print(f"\n  --- Alternative: identity rep (rep(a) = atom(a)) ---")
    print(f"  With identity rep, R-eval == standard eval (all atoms).")
    print(f"  Need: table[table[c][a]][b] = table[a][b] for all a,b.")

    id_sim_terms = []
    for c in range(N):
        ok = True
        for a in range(N):
            if not ok: break
            for b in range(N):
                if table[table[c][a]][b] != table[a][b]:
                    ok = False; break
        if ok:
            id_sim_terms.append(c)
    if id_sim_terms:
        print(f"  FOUND: identity-rep sim terms = {id_sim_terms}")
    else:
        print(f"  No identity-rep sim term exists (no strict self-sim).")

    # -------------------------------------------------------
    # Result
    # -------------------------------------------------------
    return {
        "name": name, "N": N, "has_D": has_D, "has_H": has_H,
        "id_sim": len(id_sim_terms) > 0,
        "s": s, "r": r,
    }


def main():
    print("=" * 72)
    print("  R+D+H-DETERMINED SELF-SIMULATION TEST")
    print("=" * 72)
    print()
    print("  HYPOTHESIS: R, D, H structure determines eval rules that")
    print("  make self-simulation non-vacuous.")
    print()
    print("  R-eval: s is LAZY (rep terms stay compound), r DECODES s-layers.")
    print("  This fundamentally changes how rep(a) behaves in the term algebra.")

    tables = load_tables()
    results = []

    for name, table in tables:
        r = analyze_table(name, table)
        if r is not None:
            results.append(r)

    # Summary
    print(f"\n{'='*72}")
    print(f"  SUMMARY")
    print(f"{'='*72}")
    print()
    print(f"  {'Table':<28} {'N':>2} {'D':>2} {'H':>2} {'id-sim':>7}")
    print(f"  {'-'*28} {'--':>2} {'--':>2} {'--':>2} {'-------':>7}")
    for r in results:
        d = "Y" if r["has_D"] else "N"
        h = "Y" if r["has_H"] else "N"
        ids = "Y" if r["id_sim"] else "N"
        print(f"  {r['name']:<28} {r['N']:>2} {d:>2} {h:>2} {ids:>7}")

    print(f"""
  ================================================================
  THEORETICAL ANALYSIS
  ================================================================

  CORRECTION: The s-lazy rule does NOT make rep terms compound!

  rep(a) = App(Atom(s), App(Atom(s), ... Atom(z1)))

  Under R-eval (bottom-up):
    eval(Atom(z1)) = Atom(z1)                         [atom]
    eval(App(Atom(s), Atom(z1))) :
      v1 = Atom(s), v2 = Atom(z1)                     [both atoms]
      -> Ground apply fires FIRST: Atom(table[s][z1])  [atom!]
    eval(App(Atom(s), atom_result)) :
      -> Ground apply again: Atom(table[s][...])       [atom!]

  Because evaluation is bottom-up and z1 is an atom, every
  intermediate result is an atom. The s-lazy rule only fires
  when v2 is compound, which never happens for rep terms.

  Therefore: eval_R(rep(a)) = eval_std(rep(a)) = atom(s^a(z1)).

  The s-lazy rule is STRUCTURALLY INERT for the rep encoding.
  It only fires when something ELSE produces a compound term
  and s is then applied to it. But in the self-simulation test
  App(App(t, rep(a)), rep(b)), the rep arguments always reduce
  to atoms first.

  CONSEQUENCE: For sim term atom(c) with c != s and c != r:
    eval_R(App(atom(c), atom(rep_ground(a)))) = atom(table[c][rep_ground(a)])
    Same as standard eval.

  For c == s:
    eval_R(App(atom(s), atom(rep_ground(a)))) = atom(table[s][rep_ground(a)])
    Ground apply fires (both atoms). Same as standard eval!
    The s-lazy rule does NOT fire because the argument is an atom.

  For c == r:
    eval_R(App(atom(r), atom(rep_ground(a)))) = atom(table[r][rep_ground(a)])
    Ground apply fires. The r-decode rule does NOT fire because
    the argument is an atom, not App(atom(s), ...).

  THEREFORE: R-determined eval == standard eval for the sim test.
  The R, D, H structure is INVISIBLE when rep terms reduce to atoms.

  The two R-specific rules (s-lazy and r-decode) can ONLY activate
  when intermediate computations produce compound terms. But the
  sim test App(App(t, rep(a)), rep(b)) reduces both rep args to
  atoms first, so neither rule ever fires.

  VERDICT: R+D+H-determined eval collapses to standard eval for
  the self-simulation test. The eval strategy does NOT matter
  when the representation maps elements to ground-reducible terms.

  To make R-structure VISIBLE, you would need EITHER:
    (a) A representation that produces irreducible compound terms
        (e.g., rep(a) = App(atom(tag), atom(a)) with tag lazy)
    (b) Simulation of compound terms (not just ground elements)
    (c) Recursive sim terms (Y-combinator) where intermediate
        steps produce compound terms that interact with R rules

  None of these apply to the standard rep(a) = s^a(z1) encoding.
""")


if __name__ == "__main__":
    main()
