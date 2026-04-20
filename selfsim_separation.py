#!/usr/bin/env python3
"""
Self-Simulation Separation Test
================================

Investigates whether R+D+H is sufficient for bounded self-simulation
under the s-always-lazy, R-determined eval.

Four phases:
  1. Enumerate Y-free terms up to depth d and test self-simulation
  2. Analyze WHY terms fail (partial application profiles)
  3. Test forced-eval variant for non-s,r atoms
  4. Separation analysis: what additional structure is needed?

Depth limits (to keep runtime feasible):
  N=5: depth 3 (~5*31^2 + 31*150 ~ 9000 terms at depth 3)
  N=6: depth 2 (~1770 terms; depth 3 would be ~3M)
"""

from __future__ import annotations
import sys
import time

# ===================================================================
# Term Algebra (tuple-based for hashability and speed)
# ===================================================================

ATOM = 'atom'
APP = 'app'

def make_atom(x):
    return (ATOM, x)

def make_app(t1, t2):
    return (APP, t1, t2)

def is_atom(t):
    return t[0] == ATOM

def is_app(t):
    return t[0] == APP

def term_depth(t):
    if is_atom(t):
        return 0
    return 1 + max(term_depth(t[1]), term_depth(t[2]))

def term_size(t):
    if is_atom(t):
        return 1
    return 1 + term_size(t[1]) + term_size(t[2])

def term_str(t, depth=0):
    if depth > 20:
        return "..."
    if is_atom(t):
        return str(t[1])
    return f"({term_str(t[1], depth+1)}.{term_str(t[2], depth+1)})"

# ===================================================================
# Rep Encoding (terms, not ground values)
# ===================================================================

def make_rep(k, s):
    """rep(k) = s^k(z1) as a TERM. s-lazy means these stay compound."""
    t = make_atom(0)  # z1 = 0 (absorber)
    for _ in range(k):
        t = make_app(make_atom(s), t)  # lazy: won't reduce
    return t

# ===================================================================
# Eval 1: s-always-lazy, R-determined (the main eval)
# ===================================================================

def rdh_eval(term, dot, s, r, fuel=100):
    """Evaluate with s-always-lazy and r-decode rules."""
    if fuel <= 0:
        return term
    if is_atom(term):
        return term
    t1, t2 = term[1], term[2]
    v1 = rdh_eval(t1, dot, s, r, fuel - 1)
    v2 = rdh_eval(t2, dot, s, r, fuel - 1)
    return rdh_apply(v1, v2, dot, s, r, fuel - 1)

def rdh_apply(v1, v2, dot, s, r, fuel):
    """Apply with R-determined rules."""
    if is_atom(v1) and is_atom(v2):
        return make_atom(dot[v1[1]][v2[1]])               # ground: always
    if is_atom(v1) and v1[1] == s:
        return make_app(make_atom(s), v2)                  # s is ALWAYS lazy
    if is_atom(v1) and v1[1] == r:
        if is_app(v2) and is_atom(v2[1]) and v2[1][1] == s:
            return v2[2]                                    # r decodes s: peel one layer
        if is_atom(v2):
            return make_atom(dot[r][v2[1]])
        return make_app(v1, v2)                            # stuck
    # Non-s, non-r atom applied to compound: stuck
    if is_atom(v1) and is_app(v2):
        return make_app(v1, v2)
    # Compound in function position: stuck
    return make_app(v1, v2)

# ===================================================================
# Eval 2: Force-eval variant (non-s,r atoms force compound args)
# ===================================================================

def force_ground(term, dot, s, r, fuel):
    """Force a compound term to its ground value by recursively evaluating s-towers."""
    if fuel <= 0:
        return term
    if is_atom(term):
        return term
    if is_app(term) and is_atom(term[1]) and term[1][1] == s:
        inner_ground = force_ground(term[2], dot, s, r, fuel - 1)
        if is_atom(inner_ground):
            return make_atom(dot[s][inner_ground[1]])
        return term
    return term

def rdh_eval_force(term, dot, s, r, fuel=100):
    """Evaluate with force-eval for non-s,r atoms."""
    if fuel <= 0:
        return term
    if is_atom(term):
        return term
    t1, t2 = term[1], term[2]
    v1 = rdh_eval_force(t1, dot, s, r, fuel - 1)
    v2 = rdh_eval_force(t2, dot, s, r, fuel - 1)
    return rdh_apply_force(v1, v2, dot, s, r, fuel - 1)

def rdh_apply_force(v1, v2, dot, s, r, fuel):
    """Apply with force-eval for non-s,r atoms."""
    if is_atom(v1) and is_atom(v2):
        return make_atom(dot[v1[1]][v2[1]])
    if is_atom(v1) and v1[1] == s:
        return make_app(make_atom(s), v2)
    if is_atom(v1) and v1[1] == r:
        if is_app(v2) and is_atom(v2[1]) and v2[1][1] == s:
            return v2[2]
        if is_atom(v2):
            return make_atom(dot[r][v2[1]])
        return make_app(v1, v2)
    # Non-s, non-r atom applied to compound: FORCE-EVAL the compound
    if is_atom(v1) and is_app(v2):
        ground_v2 = force_ground(v2, dot, s, r, fuel)
        if is_atom(ground_v2):
            return make_atom(dot[v1[1]][ground_v2[1]])
        return make_app(v1, v2)
    return make_app(v1, v2)

# ===================================================================
# Standard eval (for comparison / vacuous baseline)
# ===================================================================

def std_eval(term, dot, s=None, r=None, fuel=100):
    """Standard eval: atom*atom = dot lookup, everything else stuck.
    s and r params accepted but ignored (for uniform interface)."""
    if fuel <= 0:
        return term
    if is_atom(term):
        return term
    v1 = std_eval(term[1], dot, fuel=fuel - 1)
    v2 = std_eval(term[2], dot, fuel=fuel - 1)
    if is_atom(v1) and is_atom(v2):
        return make_atom(dot[v1[1]][v2[1]])
    return make_app(v1, v2)

# ===================================================================
# Term Enumeration
# ===================================================================

def enumerate_terms(N, max_depth):
    """Enumerate all Y-free terms up to given depth over {0,...,N-1}.
    Returns (by_depth, up_to) where up_to[d] is all terms of depth <= d."""
    by_depth = {}
    by_depth[0] = [make_atom(i) for i in range(N)]
    up_to = {0: list(by_depth[0])}

    for d in range(1, max_depth + 1):
        new_terms = set()
        all_prev = up_to[d - 1]
        exact_prev = by_depth[d - 1]
        below_prev = up_to.get(d - 2, [])

        # App(exact_d-1, any_up_to_d-1)
        for t1 in exact_prev:
            for t2 in all_prev:
                new_terms.add(make_app(t1, t2))
        # App(below_d-2, exact_d-1)
        for t1 in below_prev:
            for t2 in exact_prev:
                new_terms.add(make_app(t1, t2))

        by_depth[d] = list(new_terms)
        up_to[d] = up_to[d - 1] + by_depth[d]

    return by_depth, up_to

# ===================================================================
# Witnesses
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

WITNESSES = [
    ("Witness5 (N=5, R+D+H)", TABLE_5, 5, 2, 2),   # s=2, r=2
    ("Witness6 (N=6, R+D+H)", TABLE_6, 6, 2, 3),   # s=2, r=3
]

# ===================================================================
# Self-simulation test (with early exit)
# ===================================================================

def test_selfsim(term, dot, N, s, r, eval_fn, fuel=100):
    """Test: App(App(t, rep(a)), rep(b)) = atom(dot[a][b]) for all a,b.
    Returns (successes, total, failures_list)."""
    successes = 0
    failures = []
    total = N * N
    for a in range(N):
        for b in range(N):
            expr = make_app(make_app(term, make_rep(a, s)), make_rep(b, s))
            result = eval_fn(expr, dot, s, r, fuel)
            expected = make_atom(dot[a][b])
            if result == expected:
                successes += 1
            else:
                failures.append((a, b, result, expected))
    return successes, total, failures

def test_selfsim_fast(term, dot, N, s, r, eval_fn, fuel=100, min_to_beat=0):
    """Fast version: bail out early if we can't beat min_to_beat."""
    successes = 0
    total = N * N
    max_failures = total - min_to_beat - 1  # allowed failures to still beat
    n_failures = 0
    for a in range(N):
        for b in range(N):
            expr = make_app(make_app(term, make_rep(a, s)), make_rep(b, s))
            result = eval_fn(expr, dot, s, r, fuel)
            expected = make_atom(dot[a][b])
            if result == expected:
                successes += 1
            else:
                n_failures += 1
                if n_failures > max_failures:
                    return successes, False  # can't beat
    return successes, True

# ===================================================================
# Phase 1: Enumerate and test self-simulation
# ===================================================================

def phase1(name, dot, N, s, r, max_depth):
    """Phase 1: Enumerate Y-free terms, test self-sim under rdh_eval."""
    print(f"\n{'='*72}")
    print(f"  PHASE 1: Y-free term enumeration for {name}")
    print(f"  N={N}, s={s}, r={r}, max_depth={max_depth}")
    print(f"{'='*72}")

    print(f"\n  Table:")
    for i in range(N):
        print(f"    {i}: {dot[i]}")

    print(f"\n  Rep encodings under rdh_eval:")
    for a in range(N):
        rep = make_rep(a, s)
        evald = rdh_eval(rep, dot, s, r)
        print(f"    rep({a}) = {term_str(rep):30s} -> eval = {term_str(evald)}")

    t0 = time.time()
    by_depth, up_to = enumerate_terms(N, max_depth)

    for d in range(max_depth + 1):
        print(f"\n  Depth {d}: {len(by_depth[d])} new terms, cumulative {len(up_to[d])}")

    best_score = 0
    best_terms = []
    checked = 0

    for d in range(max_depth + 1):
        d_start = time.time()
        for term in by_depth[d]:
            score, could_beat = test_selfsim_fast(term, dot, N, s, r, rdh_eval, min_to_beat=best_score)
            checked += 1
            if score > best_score:
                best_score = score
                # get full failure list for best
                _, _, fails = test_selfsim(term, dot, N, s, r, rdh_eval)
                best_terms = [(term, fails)]
            elif score == best_score and score > 0 and len(best_terms) < 10:
                _, _, fails = test_selfsim(term, dot, N, s, r, rdh_eval)
                best_terms.append((term, fails))
            if score == N * N:
                print(f"\n  *** FOUND SELF-SIM TERM at depth {d}! ***")
                print(f"      t = {term_str(term)}")
                return term
        elapsed = time.time() - d_start
        print(f"    Depth {d} done: {len(by_depth[d])} terms in {elapsed:.1f}s, best so far = {best_score}/{N*N}")

    total_time = time.time() - t0
    print(f"\n  Total: {checked} terms checked in {total_time:.1f}s")
    print(f"\n  Best score: {best_score}/{N*N}")
    if best_terms:
        print(f"  Best terms ({len(best_terms)} shown):")
        for t, fails in best_terms[:5]:
            print(f"    {term_str(t)}  ({best_score}/{N*N})")
            if fails:
                for a, b, got, exp in fails[:3]:
                    print(f"      FAIL: ({a},{b}) -> {term_str(got)}, expected {term_str(exp)}")
                if len(fails) > 3:
                    print(f"      ... and {len(fails)-3} more failures")
    else:
        print(f"  No term scored above 0.")

    return None

# ===================================================================
# Phase 2: Partial Application Profiles
# ===================================================================

def phase2(name, dot, N, s, r, max_depth=2):
    """Phase 2: Analyze WHY terms fail via partial application profiles."""
    print(f"\n{'='*72}")
    print(f"  PHASE 2: Partial application profile analysis for {name}")
    print(f"  (up to depth {max_depth})")
    print(f"{'='*72}")

    by_depth, up_to = enumerate_terms(N, max_depth)
    all_terms = up_to[max_depth]

    interesting = []
    t0 = time.time()

    for term in all_terms:
        profile = []
        for a in range(N):
            pa = rdh_eval(make_app(term, make_rep(a, s)), dot, s, r)
            profile.append(pa)

        n_atoms = sum(1 for p in profile if is_atom(p))
        n_compound = N - n_atoms

        # Injectivity among all results
        all_strs = [term_str(p) for p in profile]
        n_distinct_all = len(set(all_strs))

        # Second application score
        second_ok = 0
        for a in range(N):
            pa = profile[a]
            for b in range(N):
                expr2 = make_app(pa, make_rep(b, s))
                result = rdh_eval(expr2, dot, s, r)
                expected = make_atom(dot[a][b])
                if result == expected:
                    second_ok += 1

        interesting.append((second_ok, n_atoms, n_compound, n_distinct_all, term, profile))

    interesting.sort(key=lambda x: -x[0])
    elapsed = time.time() - t0

    print(f"\n  Analyzed {len(all_terms)} terms in {elapsed:.1f}s")
    print(f"\n  Top 15 by second-application score:")
    print(f"  {'Score':>8} {'#Atom':>5} {'#Cmpd':>5} {'#Dist':>5}  Term")
    print(f"  {'-'*60}")

    for score, n_at, n_cmpd, n_dist, t, prof in interesting[:15]:
        print(f"  {score:>5}/{N*N} {n_at:>5} {n_cmpd:>5} {n_dist:>5}  {term_str(t)}")
        for a in range(N):
            pa = prof[a]
            print(f"           pa({a}) = {term_str(pa)}")
        print()

    max_score = interesting[0][0] if interesting else 0
    n_max = sum(1 for x in interesting if x[0] == max_score)
    print(f"  Maximum second-application score: {max_score}/{N*N} ({n_max} terms)")

    n_injective = sum(1 for x in interesting if x[3] == N)
    print(f"  Terms with all-distinct pa(): {n_injective}/{len(interesting)}")

    n_all_atom = sum(1 for x in interesting if x[1] == N)
    print(f"  Terms with all-atom pa(): {n_all_atom}/{len(interesting)}")

    return interesting

# ===================================================================
# Phase 3: Force-eval variant
# ===================================================================

def phase3(name, dot, N, s, r, max_depth):
    """Phase 3: Test force-eval variant."""
    print(f"\n{'='*72}")
    print(f"  PHASE 3: Force-eval variant for {name}")
    print(f"  max_depth={max_depth}")
    print(f"{'='*72}")

    print(f"\n  Rep encodings under force-eval:")
    for a in range(N):
        rep = make_rep(a, s)
        evald = rdh_eval_force(rep, dot, s, r)
        print(f"    rep({a}) = {term_str(rep):30s} -> eval = {term_str(evald)}")

    by_depth, up_to = enumerate_terms(N, max_depth)

    best_score = 0
    best_terms = []
    t0 = time.time()

    for d in range(max_depth + 1):
        for term in by_depth[d]:
            score, _ = test_selfsim_fast(term, dot, N, s, r, rdh_eval_force, min_to_beat=best_score)
            if score > best_score:
                best_score = score
                _, _, fails = test_selfsim(term, dot, N, s, r, rdh_eval_force)
                best_terms = [(term, fails)]
            elif score == best_score and score > 0 and len(best_terms) < 10:
                _, _, fails = test_selfsim(term, dot, N, s, r, rdh_eval_force)
                best_terms.append((term, fails))
            if score == N * N:
                print(f"\n  *** FOUND SELF-SIM TERM under force-eval at depth {d}! ***")
                print(f"      t = {term_str(term)}")
                return term
        print(f"    Depth {d}: best so far = {best_score}/{N*N}")

    elapsed = time.time() - t0
    print(f"\n  Total: {len(up_to[max_depth])} terms in {elapsed:.1f}s")
    print(f"  Best score under force-eval: {best_score}/{N*N}")
    if best_terms:
        print(f"  Best terms ({len(best_terms)} shown):")
        for t, fails in best_terms[:5]:
            print(f"    {term_str(t)}  ({best_score}/{N*N})")
            for a, b, got, exp in fails[:3]:
                print(f"      FAIL: ({a},{b}) -> {term_str(got)}, expected {term_str(exp)}")
            if len(fails) > 3:
                print(f"      ... and {len(fails)-3} more failures")

    return None

# ===================================================================
# Phase 4: Separation analysis (standard eval comparison)
# ===================================================================

def phase4(name, dot, N, s, r, max_depth=2):
    """Phase 4: Standard eval comparison + separation analysis."""
    print(f"\n{'='*72}")
    print(f"  PHASE 4: Separation analysis for {name}")
    print(f"{'='*72}")

    # Compute ground rep values: s^a(0) in the table
    rep_ground = [0] * N
    rep_ground[0] = 0
    for k in range(1, N):
        rep_ground[k] = dot[s][rep_ground[k - 1]]

    print(f"\n  Ground rep values (s^a(0) in table):")
    for a in range(N):
        print(f"    rep_ground({a}) = {rep_ground[a]}")

    rep_injective = len(set(rep_ground)) == N
    print(f"  Rep injective: {rep_injective}")
    if not rep_injective:
        print(f"  WARNING: Ground rep not injective -- standard self-sim impossible with this rep")

    # Atom-only sim terms under standard eval
    print(f"\n  --- Standard eval: atom sim terms ---")
    best_score_std = 0
    best_c_std = []
    for c in range(N):
        ok = 0
        for a in range(N):
            for b in range(N):
                if dot[dot[c][rep_ground[a]]][rep_ground[b]] == dot[a][b]:
                    ok += 1
        if ok > best_score_std:
            best_score_std = ok
            best_c_std = [c]
        elif ok == best_score_std:
            best_c_std.append(c)

    print(f"  Best score (atom terms): {best_score_std}/{N*N} via atoms {best_c_std}")

    # Compound terms under standard eval
    by_depth, up_to = enumerate_terms(N, max_depth)
    best_std_deep = 0
    best_std_deep_terms = []

    for term in up_to[max_depth]:
        score, _ = test_selfsim_fast(term, dot, N, s, r, std_eval, min_to_beat=best_std_deep)
        if score > best_std_deep:
            best_std_deep = score
            best_std_deep_terms = [term]
        elif score == best_std_deep and score > 0 and len(best_std_deep_terms) < 5:
            best_std_deep_terms.append(term)
        if score == N * N:
            print(f"\n  *** Standard eval self-sim found! ***")
            print(f"      t = {term_str(term)}")
            break

    print(f"  Best standard-eval score (depth {max_depth}): {best_std_deep}/{N*N}")
    if best_std_deep_terms:
        for t in best_std_deep_terms[:3]:
            print(f"    {term_str(t)}")

    return best_std_deep

# ===================================================================
# Phase 5: Failure mode analysis
# ===================================================================

def phase5(name, dot, N, s, r):
    """Analyze the fundamental obstacles to self-simulation."""
    print(f"\n{'='*72}")
    print(f"  PHASE 5: Failure mode analysis for {name}")
    print(f"{'='*72}")

    # Atom partial application: c . rep(a) under rdh_eval
    print(f"\n  --- Atom partial application: c . rep(a) under rdh_eval ---")
    for c in range(N):
        results = []
        atom_flags = []
        for a in range(N):
            pa = rdh_eval(make_app(make_atom(c), make_rep(a, s)), dot, s, r)
            results.append(term_str(pa))
            atom_flags.append(is_atom(pa))
        distinct = len(set(results))
        n_at = sum(atom_flags)
        tag = "  <-- s" if c == s else ("  <-- r" if c == r else "")
        print(f"    c={c}: {distinct} distinct, {n_at}/{N} atoms{tag}")
        for a in range(N):
            print(f"       c={c} . rep({a}) = {results[a]}")

    # r-decode chain
    print(f"\n  --- r-decode chain ---")
    for a in range(N):
        rep = make_rep(a, s)
        chain = [term_str(rep)]
        current = rep
        for step in range(a + 1):
            decoded = rdh_eval(make_app(make_atom(r), current), dot, s, r)
            chain.append(term_str(decoded))
            current = decoded
            if is_atom(current):
                break
        print(f"    rep({a}) -> {' -> '.join(chain)}")

    # The fundamental problem
    print(f"\n  --- Structural analysis ---")
    print(f"  rep(0) = atom(0)  [ground]")
    for a in range(1, min(N, 4)):
        print(f"  rep({a}) = {term_str(make_rep(a, s))}  [COMPOUND, depth {a}]")

    print(f"""
  KEY INSIGHT: Under rdh_eval with s-lazy:
  - rep(a) for a>=1 is a compound term of depth a
  - Only s (lazy wrap) and r (decode/peel) interact with compounds
  - All other atoms c get STUCK when applied to compound args

  For sim term t, we need:
    App(App(t, rep(a)), rep(b)) = atom(dot[a][b])

  But App(t, rep(a)) must produce an intermediate that:
    (1) encodes a (so we can select the right row)
    (2) can process rep(b) in the second application

  The problem: with only s and r as non-stuck atoms,
  the intermediate is either:
    - Another s-tower (rep(a+k) or rep(a-k)) -- encodes a but
      can't process rep(b) because s just wraps
    - An atom (if r fully decoded) -- loses structural info about a
      and just does ground dot lookup

  Neither option allows TABLE INDEXING: mapping (a,b) -> dot[a][b]
  for an ARBITRARY table. This is the separation.""")

# ===================================================================
# Main
# ===================================================================

def main():
    print("=" * 72)
    print("  SELF-SIMULATION SEPARATION TEST")
    print("  R+D+H under s-always-lazy, R-determined eval")
    print("=" * 72)

    results = {}

    for name, dot, N, s, r in WITNESSES:
        # Choose max_depth based on N
        if N <= 5:
            max_depth = 3
        else:
            max_depth = 2

        print(f"\n\n{'#'*72}")
        print(f"#  {name}")
        print(f"#  Using max_depth={max_depth}")
        print(f"{'#'*72}")

        # Phase 1
        found1 = phase1(name, dot, N, s, r, max_depth=max_depth)

        # Phase 2 (depth 2 always)
        phase2(name, dot, N, s, r, max_depth=min(max_depth, 2))

        # Phase 3
        found3 = phase3(name, dot, N, s, r, max_depth=max_depth)

        # Phase 4
        std_best = phase4(name, dot, N, s, r, max_depth=min(max_depth, 2))

        # Phase 5
        phase5(name, dot, N, s, r)

        results[name] = {
            'rdh_found': found1,
            'force_found': found3,
            'std_best': std_best,
        }

        print(f"\n{'='*72}")
        print(f"  VERDICT for {name}:")
        if found1:
            print(f"  rdh_eval: SELF-SIM FOUND: {term_str(found1)}")
        else:
            print(f"  rdh_eval: NO self-sim term found (depth <= {max_depth})")
        if found3:
            print(f"  force_eval: SELF-SIM FOUND: {term_str(found3)}")
        else:
            print(f"  force_eval: NO self-sim term found (depth <= {max_depth})")
        print(f"  std_eval best: {std_best}/{N*N}")
        print(f"{'='*72}")

    # ===================================================================
    # Final Separation Analysis
    # ===================================================================
    print(f"\n{'='*72}")
    print(f"  FINAL SEPARATION ANALYSIS")
    print(f"{'='*72}")

    any_rdh = any(v['rdh_found'] for v in results.values())
    any_force = any(v['force_found'] for v in results.values())

    print(f"\n  Results summary:")
    for name, v in results.items():
        rdh = "FOUND" if v['rdh_found'] else "NOT FOUND"
        force = "FOUND" if v['force_found'] else "NOT FOUND"
        print(f"    {name}: rdh={rdh}, force={force}, std_best={v['std_best']}")

    if not any_rdh and not any_force:
        print(f"""
  SEPARATION CONFIRMED (within search depth):
  No Y-free term achieves bounded self-simulation under EITHER
  the rdh_eval or the force-eval variant for ANY R+D+H witness.

  The s-always-lazy, R-determined eval creates a fundamental barrier:
  compound reps (rep(a>=1)) cannot be used for table indexing because
  the only operations available (s-wrap, r-peel) form a stack/unstack
  pair that preserves DEPTH but cannot perform arbitrary LOOKUP.

  Self-simulation requires either:
  (a) A richer eval (e.g., Y-combinator for unbounded recursion), or
  (b) Additional algebraic structure beyond R+D+H that enables
      a ground-level rep encoding (all reps are atoms), or
  (c) A fundamentally different simulation protocol.

  This is the SELFSIM SEPARATION: R+D+H constrains the algebra
  but does not determine the computation needed for self-simulation.
""")
    elif any_rdh:
        print(f"\n  Self-simulation IS achievable under rdh_eval!")
        print(f"  R+D+H may be sufficient.")
    elif any_force:
        print(f"\n  Self-simulation requires force-eval (not pure rdh_eval).")
        print(f"  This means non-s,r atoms need to force-reduce compound args.")

if __name__ == "__main__":
    main()
