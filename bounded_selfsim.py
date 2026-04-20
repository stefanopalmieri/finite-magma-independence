#!/usr/bin/env python3
"""
Bounded (Y-free) self-simulation test.

Tests whether bounded self-simulation is non-trivial by searching for
Y-free terms t such that under STANDARD reduction:
  eval(App(App(t, rep(a)), rep(b))) = atom(a · b)  for all a, b.

Standard reduction (deterministic, always terminates on finite terms):
  eval(atom(a)) = atom(a)
  eval(App(t1, t2)) = apply(eval(t1), eval(t2))
  apply(atom(a), atom(b)) = atom(dot(a, b))
  apply(atom(a), App(x,y)) = App(atom(a), App(x,y))   -- stuck
  apply(App(x,y), v) = App(App(x,y), v)                -- stuck

rep encoding: rep(a) = s^a(z1) as a TERM:
  rep(0) = atom(z1)
  rep(k) = App(atom(s), rep(k-1))

Under standard reduction, eval(rep(a)) = atom(rep_ground(a))
where rep_ground(a) = s^a(z1) computed in the ground algebra.
"""

import json
import itertools
from dataclasses import dataclass
from typing import Optional

# ═══════════════════════════════════════════════════════════════════
# Term Algebra
# ═══════════════════════════════════════════════════════════════════

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
        return f"({self.left} · {self.right})"

Term = Atom | App


def term_depth(t):
    if isinstance(t, Atom):
        return 0
    return 1 + max(term_depth(t.left), term_depth(t.right))


def term_size(t):
    if isinstance(t, Atom):
        return 1
    return 1 + term_size(t.left) + term_size(t.right)


# ═══════════════════════════════════════════════════════════════════
# Standard Reduction
# ═══════════════════════════════════════════════════════════════════

def std_apply(t1, t2):
    """Standard apply: only reduces atom·atom."""
    # This is part of standard reduction, not the table lookup itself
    return (t1, t2)  # placeholder, actual logic in std_eval


def std_eval(t, table):
    """
    Standard reduction.
    Returns a Term (either Atom or stuck App).
    """
    if isinstance(t, Atom):
        return t
    # App case
    v1 = std_eval(t.left, table)
    v2 = std_eval(t.right, table)
    if isinstance(v1, Atom) and isinstance(v2, Atom):
        return Atom(table[v1.val][v2.val])
    elif isinstance(v1, Atom):
        return App(v1, v2)  # stuck: atom applied to compound
    else:
        return App(v1, v2)  # stuck: compound applied to anything


# ═══════════════════════════════════════════════════════════════════
# Rep Encoding
# ═══════════════════════════════════════════════════════════════════

def compute_rep_ground(table, s, z1, N):
    """Compute rep_ground(a) = s^a(z1) in the ground algebra."""
    vals = [0] * N
    vals[0] = z1
    for k in range(1, N):
        vals[k] = table[s][vals[k - 1]]
    return vals


def make_rep_term(s, z1, a):
    """Build rep(a) as a term: s^a(z1)."""
    t = Atom(z1)
    for _ in range(a):
        t = App(Atom(s), t)
    return t


# ═══════════════════════════════════════════════════════════════════
# Term Enumeration (Y-free: only atoms and App)
# ═══════════════════════════════════════════════════════════════════

def enumerate_terms(N, max_depth):
    """
    Enumerate all Y-free terms up to a given depth over alphabet {0,...,N-1}.
    Returns dict: depth -> list of terms at exactly that depth.
    """
    by_depth = {}
    # Depth 0: atoms
    by_depth[0] = [Atom(i) for i in range(N)]

    # All terms up to depth d
    up_to = {0: list(by_depth[0])}

    for d in range(1, max_depth + 1):
        new_terms = []
        # App(t1, t2) where max(depth(t1), depth(t2)) == d-1
        # At least one must be at depth exactly d-1
        prev = up_to[d - 2] if d >= 2 else []
        exact = by_depth[d - 1]

        # (exact, anything_up_to_d-1) and (anything_up_to_d-2, exact)
        all_up_to_prev = up_to.get(d - 1, [])

        for t1 in exact:
            for t2 in all_up_to_prev:
                new_terms.append(App(t1, t2))
        for t1 in prev:
            for t2 in exact:
                new_terms.append(App(t1, t2))
        # Also (exact, exact)
        for t1 in exact:
            for t2 in exact:
                new_terms.append(App(t1, t2))

        # Deduplicate
        seen = set()
        deduped = []
        for t in new_terms:
            key = repr(t)
            if key not in seen:
                seen.add(key)
                deduped.append(t)
        by_depth[d] = deduped
        up_to[d] = up_to[d - 1] + deduped

    return by_depth, up_to


# ═══════════════════════════════════════════════════════════════════
# Bounded Self-Simulation Check
# ═══════════════════════════════════════════════════════════════════

def check_bounded_selfsim(table, N, s, r, z1, name, max_depth=3):
    """
    Check if a bounded (Y-free) self-simulation term exists.
    Returns the term if found, None otherwise.
    """
    print(f"\n{'='*70}")
    print(f"  {name}")
    print(f"  N={N}, s={s}, r={r}, z1={z1}")
    print(f"{'='*70}")

    # Print table
    for i in range(N):
        print(f"  {i}: {table[i]}")

    # Compute rep_ground values
    rep_ground = compute_rep_ground(table, s, z1, N)
    print(f"\n  rep_ground: {rep_ground}")

    # Check injectivity
    if len(set(rep_ground)) < N:
        collisions = {}
        for i, v in enumerate(rep_ground):
            collisions.setdefault(v, []).append(i)
        dupes = {v: ks for v, ks in collisions.items() if len(ks) > 1}
        print(f"  rep_ground NOT injective! Collisions: {dupes}")
        print(f"  => Bounded self-simulation IMPOSSIBLE (can't distinguish inputs)")
        return None

    print(f"  rep_ground is injective: OK")

    # Build rep terms
    rep_terms = [make_rep_term(s, z1, a) for a in range(N)]

    # Verify rep terms evaluate correctly
    for a in range(N):
        v = std_eval(rep_terms[a], table)
        if not isinstance(v, Atom) or v.val != rep_ground[a]:
            print(f"  ERROR: eval(rep({a})) = {v}, expected atom({rep_ground[a]})")
            return None

    # ─────────────────────────────────────────────────────────────
    # ANALYTICAL CHECK FIRST
    # ─────────────────────────────────────────────────────────────
    # For t = atom(c), the condition becomes:
    #   dot(dot(c, rep_ground(a)), rep_ground(b)) = dot(a, b) for all a,b
    # This is "strict self-simulation". Check all atoms first.
    print(f"\n  --- Checking atom terms (strict self-sim) ---")
    for c in range(N):
        ok = True
        for a in range(N):
            if not ok:
                break
            fa = table[c][rep_ground[a]]
            for b in range(N):
                lhs = table[fa][rep_ground[b]]
                rhs = table[a][b]
                if lhs != rhs:
                    ok = False
                    break
        if ok:
            print(f"  FOUND: t = atom({c}) is a strict self-simulation term!")
            print(f"    dot(dot({c}, rep(a)), rep(b)) = dot(a, b) for all a,b")
            return Atom(c)

    print(f"  No atom term works (no strict self-simulation).")

    # ─────────────────────────────────────────────────────────────
    # ANALYTICAL CHECK: can App(atom(c), atom(d)) work?
    # ─────────────────────────────────────────────────────────────
    # eval(App(App(App(atom(c), atom(d)), rep(a)), rep(b)))
    # = eval(App(App(atom(dot(c,d)), rep(a)), rep(b)))
    # = eval(App(atom(dot(dot(c,d), rep_ground(a))), rep(b)))
    # = atom(dot(dot(dot(c,d), rep_ground(a)), rep_ground(b)))
    # This reduces to: strict self-sim with t = dot(c,d). Already checked above.

    # ─────────────────────────────────────────────────────────────
    # DEEPER ANALYSIS: Why compound terms might not help
    # ─────────────────────────────────────────────────────────────
    # Key insight: eval(App(t, rep(a))) must produce an Atom for the
    # outer application to work. If it produces App(...), then
    # App(App(...), rep(b)) is stuck and can't equal atom(dot(a,b)).
    #
    # So we need: for all a, eval(App(t, rep(a))) = atom(f(a))
    # And then: dot(f(a), rep_ground(b)) = dot(a, b) for all a, b.
    #
    # For eval(App(t, rep(a))) to be an atom:
    #   eval(t) must be an atom, say atom(c)
    #   then result = atom(dot(c, rep_ground(a)))
    #   so f(a) = dot(c, rep_ground(a))
    #
    # OR eval(t) is compound (stuck), in which case
    #   App(stuck, atom(rep_ground(a))) is stuck => NOT an atom. FAIL.
    #
    # THEREFORE: eval(t) must be an atom.
    # If eval(t) = atom(c), then the condition is exactly:
    #   dot(dot(c, rep_ground(a)), rep_ground(b)) = dot(a, b) for all a,b
    # which is strict self-simulation with ground element c.
    #
    # CONCLUSION: For standard reduction, bounded self-simulation
    # is EXACTLY equivalent to strict self-simulation!

    print(f"\n  --- Analytical argument ---")
    print(f"  For eval(App(t, rep(a))) to produce an atom (required for outer apply),")
    print(f"  eval(t) must itself be an atom (compound · atom = stuck).")
    print(f"  If eval(t) = atom(c), the condition reduces to strict self-sim with t=c.")
    print(f"  Therefore bounded self-sim = strict self-sim for standard reduction.")

    # ─────────────────────────────────────────────────────────────
    # BRUTE FORCE VERIFICATION (depth 1 and 2, to confirm)
    # ─────────────────────────────────────────────────────────────
    print(f"\n  --- Brute-force verification up to depth {max_depth} ---")
    by_depth, up_to = enumerate_terms(N, max_depth)

    total_checked = 0
    for d in range(max_depth + 1):
        terms_at_d = by_depth[d]
        found_at_d = 0
        for t in terms_at_d:
            total_checked += 1
            # First check: does eval(t) produce an atom?
            tv = std_eval(t, table)
            if not isinstance(tv, Atom):
                continue  # eval(t) is stuck => can't work

            # eval(t) = atom(c), check strict self-sim with c
            c = tv.val
            ok = True
            for a in range(N):
                if not ok:
                    break
                fa = table[c][rep_ground[a]]
                for b in range(N):
                    lhs = table[fa][rep_ground[b]]
                    rhs = table[a][b]
                    if lhs != rhs:
                        ok = False
                        break
            if ok:
                print(f"  FOUND at depth {d}: t = {t} (evals to atom({c}))")
                found_at_d += 1
                return t

        count = len(terms_at_d)
        print(f"  Depth {d}: checked {count} terms, {found_at_d} solutions")

    print(f"  Total terms checked: {total_checked}")
    print(f"  No bounded self-simulation term found up to depth {max_depth}.")
    return None


# ═══════════════════════════════════════════════════════════════════
# Test Tables
# ═══════════════════════════════════════════════════════════════════

# N=5 coexistence witness (from self_sim_investigation.py / Witness5.lean)
TABLE_5 = [
    [0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1],
    [0, 2, 2, 3, 4],
    [0, 0, 0, 1, 0],
    [0, 1, 0, 1, 0],
]

# N=6 coexistence witness (from self_sim_investigation.py / Witness6.lean)
TABLE_6 = [
    [0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [3, 3, 4, 2, 5, 3],
    [0, 1, 3, 5, 2, 4],
    [0, 0, 1, 0, 1, 1],
    [2, 2, 5, 4, 3, 2],
]

# N=8 S-not-D counterexample (from counterexamples.json / Countermodel.lean)
TABLE_S_NOT_D = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1],
    [3, 3, 7, 3, 4, 6, 5, 2],
    [0, 1, 7, 3, 4, 6, 5, 2],
    [0, 0, 0, 0, 0, 0, 1, 0],
    [6, 2, 6, 2, 1, 1, 1, 1],
    [0, 0, 5, 2, 2, 2, 2, 2],
    [2, 2, 2, 1, 2, 2, 6, 3],
]


def find_retraction_pair(table, N):
    """Find s, r such that r(s(x)) = x and s(r(x)) = x for all x in core."""
    core = list(range(2, N))
    for s in core:
        for r in core:
            ok = True
            for x in core:
                sx = table[s][x]
                if sx < 0 or sx >= N:
                    ok = False
                    break
                if table[r][sx] != x:
                    ok = False
                    break
                rx = table[r][x]
                if rx < 0 or rx >= N:
                    ok = False
                    break
                if table[s][rx] != x:
                    ok = False
                    break
            if ok:
                return s, r
    return None, None


# ═══════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════

def main():
    print("╔══════════════════════════════════════════════════════════════════════╗")
    print("║  BOUNDED (Y-FREE) SELF-SIMULATION TEST                             ║")
    print("╚══════════════════════════════════════════════════════════════════════╝")

    # ─────────────────────────────────────────────────────────────
    # PHASE 1: Coexistence witnesses (N=5, N=6)
    # ─────────────────────────────────────────────────────────────
    print("\n" + "▓" * 70)
    print("  PHASE 1: Coexistence witnesses")
    print("▓" * 70)

    # N=5: s=2, r=2 (self-inverse), z1=0
    check_bounded_selfsim(TABLE_5, 5, s=2, r=2, z1=0,
                          name="N=5 coexistence witness (s=2, r=2)")

    # N=6: s=2, r=3, z1=0
    check_bounded_selfsim(TABLE_6, 6, s=2, r=3, z1=0,
                          name="N=6 coexistence witness (s=2, r=3)")

    # ─────────────────────────────────────────────────────────────
    # PHASE 2: Counterexamples (R without D or H)
    # ─────────────────────────────────────────────────────────────
    print("\n" + "▓" * 70)
    print("  PHASE 2: Counterexamples from counterexamples.json")
    print("▓" * 70)

    with open("/Users/spalmieri/Desktop/finite-magma-independence/counterexamples.json") as f:
        cex = json.load(f)

    # S_not_D (N=8): has R but not D
    table = cex["S_not_D"]
    N = len(table)
    s, r = find_retraction_pair(table, N)
    if s is not None:
        check_bounded_selfsim(table, N, s=s, r=r, z1=0,
                              name=f"S_not_D (N={N}, s={s}, r={r}): has R, lacks D")
    else:
        print(f"\n  S_not_D: no retraction pair found!")

    # D_not_H_compose (N=10)
    table = cex["D_not_H_compose"]
    N = len(table)
    s, r = find_retraction_pair(table, N)
    if s is not None:
        check_bounded_selfsim(table, N, s=s, r=r, z1=0,
                              name=f"D_not_H_compose (N={N}, s={s}, r={r}): has D, lacks H")
    else:
        print(f"\n  D_not_H_compose: no retraction pair found!")

    # D_not_H_inert (N=10)
    table = cex["D_not_H_inert"]
    N = len(table)
    s, r = find_retraction_pair(table, N)
    if s is not None:
        check_bounded_selfsim(table, N, s=s, r=r, z1=0,
                              name=f"D_not_H_inert (N={N}, s={s}, r={r}): has D, lacks H")
    else:
        print(f"\n  D_not_H_inert: no retraction pair found!")

    # H_not_D (N=10)
    table = cex["H_not_D"]
    N = len(table)
    s, r = find_retraction_pair(table, N)
    if s is not None:
        check_bounded_selfsim(table, N, s=s, r=r, z1=0,
                              name=f"H_not_D (N={N}, s={s}, r={r}): has H, lacks D")
    else:
        print(f"\n  H_not_D: no retraction pair found!")

    # Also check the N=8 counterexample from the hardcoded table
    s8, r8 = 2, 3
    check_bounded_selfsim(TABLE_S_NOT_D, 8, s=s8, r=r8, z1=0,
                          name="N=8 R-not-D (hardcoded, s=2, r=3)")

    # ─────────────────────────────────────────────────────────────
    # PHASE 3: Strict selfsim N=6 witness (from strict_selfsim_correct.py)
    # ─────────────────────────────────────────────────────────────
    print("\n" + "▓" * 70)
    print("  PHASE 3: Strict self-sim N=6 witness (from SAT search)")
    print("▓" * 70)

    # Run the SAT search to get the witness
    try:
        from z3 import Solver, Int, IntVal, If, And, Or, Not, sat
        found = search_strict_selfsim_witness()
        if found:
            table, s_val, r_val, t_val, N = found
            result = check_bounded_selfsim(table, N, s=s_val, r=r_val, z1=0,
                                           name=f"Strict self-sim witness (N={N}, s={s_val}, r={r_val}, t={t_val})")
        else:
            print("\n  No strict self-sim witness found by SAT search.")
    except ImportError:
        print("\n  z3 not available, skipping SAT search for Phase 3.")

    # ─────────────────────────────────────────────────────────────
    # SUMMARY
    # ─────────────────────────────────────────────────────────────
    print("\n" + "═" * 70)
    print("  THEORETICAL SUMMARY")
    print("═" * 70)
    print("""
  KEY RESULT: Under standard reduction, bounded self-simulation is
  EXACTLY equivalent to strict (ground-level) self-simulation.

  Proof sketch:
    For eval(App(App(t, rep(a)), rep(b))) = atom(dot(a,b)):
    1. The outer App needs eval(App(t, rep(a))) to be an Atom
       (otherwise the result is a stuck App, never an Atom).
    2. For eval(App(t, rep(a))) to be Atom, eval(t) must be Atom.
       (If eval(t) = App(...), then App(App(...), atom(rep_ground(a)))
       is stuck under standard reduction.)
    3. If eval(t) = atom(c), then eval(App(t, rep(a))) = atom(dot(c, rep_ground(a))).
    4. Then the condition becomes:
       dot(dot(c, rep_ground(a)), rep_ground(b)) = dot(a, b)
       which is strict self-simulation with ground element c.

  Consequence: The Y-free restriction does NOT create a new property.
  Bounded self-sim = strict self-sim = {exists c: row c encodes the table
  via the rep encoding}.

  The interesting question is whether UNBOUNDED (Y-containing) terms
  can do something strictly more --- that's where fixed-point combinators
  allow infinite unfolding and potentially richer computation.
""")


def search_strict_selfsim_witness():
    """Search for an N=6 strict self-sim witness using Z3."""
    try:
        from z3 import Solver, Int, IntVal, If, And, Or, Not, sat
    except ImportError:
        return None

    N = 6
    core = list(range(2, N))

    dot = [[Int(f"d_{y}_{x}") for x in range(N)] for y in range(N)]
    s_var = Int("s")
    r_var = Int("r")
    t_var = Int("t")

    solver = Solver()
    solver.set("timeout", 60000)

    # Domain
    for y in range(N):
        for x in range(N):
            solver.add(dot[y][x] >= 0, dot[y][x] < N)
    solver.add(s_var >= 2, s_var < N)
    solver.add(r_var >= 2, r_var < N)
    solver.add(t_var >= 0, t_var < N)

    # Left-absorbers
    for x in range(N):
        solver.add(dot[0][x] == 0)
        solver.add(dot[1][x] == 1)

    # No other absorbers
    for y in core:
        solver.add(Not(And([dot[y][x] == y for x in range(N)])))

    # Extensionality
    for y1 in range(N):
        for y2 in range(y1 + 1, N):
            solver.add(Or([dot[y1][x] != dot[y2][x] for x in range(N)]))

    # Symbolic dot lookup
    def dlookup(a, b):
        result = IntVal(0)
        for y in range(N - 1, -1, -1):
            for x in range(N - 1, -1, -1):
                result = If(And(a == y, b == x), dot[y][x], result)
        return result

    # Retraction pair
    for x in core:
        solver.add(dlookup(r_var, dlookup(s_var, IntVal(x))) == x)
        solver.add(dlookup(s_var, dlookup(r_var, IntVal(x))) == x)
    solver.add(dlookup(r_var, IntVal(0)) == 0)

    # rep values
    rep = [IntVal(0)]
    for k in range(1, N):
        rep.append(dlookup(s_var, rep[k - 1]))

    # Rep injectivity
    for i in range(N):
        for j in range(i + 1, N):
            solver.add(rep[i] != rep[j])

    # Strict self-simulation
    for a in range(N):
        for b in range(N):
            lhs = dlookup(dlookup(t_var, rep[a]), rep[b])
            rhs = dot[a][b]
            solver.add(lhs == rhs)

    print(f"\n  Searching for N={N} strict self-sim witness...")
    result = solver.check()
    print(f"  SAT result: {result}")

    if result == sat:
        m = solver.model()
        s_val = m.evaluate(s_var).as_long()
        r_val = m.evaluate(r_var).as_long()
        t_val = m.evaluate(t_var).as_long()

        table = []
        for y in range(N):
            row = [m.evaluate(dot[y][x]).as_long() for x in range(N)]
            table.append(row)

        rep_vals = [0]
        for k in range(1, N):
            rep_vals.append(table[s_val][rep_vals[k - 1]])

        print(f"  Found: s={s_val}, r={r_val}, t={t_val}")
        print(f"  rep = {rep_vals}")
        print(f"  Table:")
        for y in range(N):
            print(f"    {y}: {table[y]}")

        # Verify
        ok = True
        for a in range(N):
            for b in range(N):
                lhs = table[table[t_val][rep_vals[a]]][rep_vals[b]]
                rhs = table[a][b]
                if lhs != rhs:
                    print(f"  FAIL: dot(dot({t_val}, rep({a})), rep({b})) = {lhs} != {rhs}")
                    ok = False
        if ok:
            print(f"  Strict self-simulation VERIFIED for all {N*N} cells")

        return table, s_val, r_val, t_val, N

    return None


if __name__ == "__main__":
    main()
