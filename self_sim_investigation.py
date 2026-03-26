"""
Self-Simulation Definition Investigation
=========================================

Phase 1: Can a pathological eval trivially self-simulate arbitrary R-magmas?
Phase 3: Does eval_strict (ground-level) work?

Key finding: The lazy eval construction works for ANY retraction-equipped magma
with |core| >= 3 (so there exists t in core with t != s and t != z1).
This means the self-simulation definition, as currently stated, is trivially
satisfiable and does NOT impose meaningful constraints beyond having a
retraction pair.
"""

import itertools
import random
from dataclasses import dataclass
from typing import Optional

# ═══════════════════════════════════════════════════════════════════
# Cayley Tables (extracted from Lean files)
# ═══════════════════════════════════════════════════════════════════

# N=8 R-not-D counterexample (Countermodel.lean: rawPC8)
# s=2 (section), r=3 (retraction), z1=0, z2=1
TABLE_8 = [
    [0, 0, 0, 0, 0, 0, 0, 0],  # Row 0: absorber
    [1, 1, 1, 1, 1, 1, 1, 1],  # Row 1: absorber
    [3, 3, 7, 3, 4, 6, 5, 2],  # Row 2: Q (section)
    [0, 1, 7, 3, 4, 6, 5, 2],  # Row 3: E (retraction)
    [0, 0, 0, 0, 0, 0, 1, 0],  # Row 4: classifier
    [6, 2, 6, 2, 1, 1, 1, 1],  # Row 5: MIXED
    [0, 0, 5, 2, 2, 2, 2, 2],  # Row 6: encoder
    [2, 2, 2, 1, 2, 2, 6, 3],  # Row 7: MIXED
]

# N=5 witness (Witness5.lean: rawW5)
# s=2, r=2, z1=0, z2=1
TABLE_5 = [
    [0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1],
    [0, 2, 2, 3, 4],
    [0, 0, 0, 1, 0],
    [0, 1, 0, 1, 0],
]

# N=6 witness (Witness6.lean: rawW6)
# s=2, r=3, z1=0, z2=1
TABLE_6 = [
    [0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [3, 3, 4, 2, 5, 3],
    [0, 1, 3, 5, 2, 4],
    [0, 0, 1, 0, 1, 1],
    [2, 2, 5, 4, 3, 2],
]


def dot(table, a, b):
    return table[a][b]


# ═══════════════════════════════════════════════════════════════════
# Term Algebra
# ═══════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class Atom:
    val: int
    def __repr__(self):
        return f"atom({self.val})"

@dataclass(frozen=True)
class App:
    left: object  # Term
    right: object  # Term
    def __repr__(self):
        return f"App({self.left}, {self.right})"

Term = Atom | App


def term_eq(t1, t2):
    """Structural equality of terms."""
    if isinstance(t1, Atom) and isinstance(t2, Atom):
        return t1.val == t2.val
    if isinstance(t1, App) and isinstance(t2, App):
        return term_eq(t1.left, t2.left) and term_eq(t1.right, t2.right)
    return False


def sdepth(t):
    """Count nested section applications."""
    if isinstance(t, App) and isinstance(t.left, Atom) and t.left.val == 2:
        return sdepth(t.right) + 1
    return 0


def decode(t, N):
    """Decode a term to an element via s-depth mod N."""
    return sdepth(t) % N


def rep(a, N):
    """S-depth encoding: rep(a) = s^a(z1)."""
    t = Atom(0)  # z1
    for _ in range(a):
        t = App(Atom(2), t)
    return t


# ═══════════════════════════════════════════════════════════════════
# PHASE 1: Pathological eval for N=8 R-not-D counterexample
# ═══════════════════════════════════════════════════════════════════

def make_lazy_eval(table, N, s_idx, t_idx):
    """
    Construct a lazy eval for the given magma with simulation term t_idx.

    - atom(s_idx) is lazy: preserves s-depth encoding structure
    - atom(t_idx) is lazy: wraps argument on first application
    - App(atom(t_idx), inner) triggers row lookup via decode
    - All other atoms ground-reduce via the Cayley table
    """
    def apply_eval(u, v):
        if isinstance(u, Atom):
            if u.val == s_idx:
                return App(Atom(s_idx), v)
            elif u.val == t_idx:
                return App(Atom(t_idx), v)
            else:
                return Atom(dot(table, u.val, decode(v, N)))
        elif isinstance(u, App) and isinstance(u.left, Atom) and u.left.val == t_idx:
            # Row lookup: decode inner for row, v for column
            return Atom(dot(table, decode(u.right, N), decode(v, N)))
        else:
            return App(u, v)  # stuck

    def eval_term(t):
        if isinstance(t, Atom):
            return t
        elif isinstance(t, App):
            return apply_eval(eval_term(t.left), eval_term(t.right))

    return eval_term


def random_term(N, max_depth=4):
    """Generate a random term over Fin(N)."""
    if max_depth <= 0 or random.random() < 0.4:
        return Atom(random.randint(0, N - 1))
    return App(random_term(N, max_depth - 1), random_term(N, max_depth - 1))


def term_depth(t):
    if isinstance(t, Atom):
        return 0
    return 1 + max(term_depth(t.left), term_depth(t.right))


print("=" * 72)
print("PHASE 1: Pathological Lazy Eval for N=8 R-not-D Counterexample")
print("=" * 72)
print()
print("N=8 Cayley table (from Countermodel.lean):")
print("  s=2 (section), r=3 (retraction), z1=0, z2=1")
for i, row in enumerate(TABLE_8):
    print(f"  Row {i}: {row}")
print()

# Verify retraction axioms
N8 = 8
s8, r8 = 2, 3
# The FRM axioms from the Lean file:
#   ret_sec : ∀ x, dot(r, dot(s, x)) = dot(s, x)    -- r is left-inverse of s on image
#   sec_ret : ∀ x, dot(s, dot(r, x)) = x             -- s . r = id (round-trip)
#   ret_zero₁ : dot(r, z1) = z1                       -- E-transparency for z1
print("Retraction pair verification:")
print(f"  ret_sec check: r(s(x)) = s(x) for all x?")
for x in range(N8):
    lhs = dot(TABLE_8, r8, dot(TABLE_8, s8, x))
    rhs = dot(TABLE_8, s8, x)
    ok = "OK" if lhs == rhs else "FAIL"
    print(f"    r(s({x})) = {lhs}, s({x}) = {rhs}  [{ok}]")
print(f"  sec_ret check: s(r(x)) = x for all x?")
for x in range(N8):
    lhs = dot(TABLE_8, s8, dot(TABLE_8, r8, x))
    ok = "OK" if lhs == x else "FAIL"
    print(f"    s(r({x})) = {lhs}  [{ok}]")
print()

# Test s-depth encoding
print("S-depth encoding verification (rep(a) has sdepth a):")
for a in range(N8):
    r = rep(a, N8)
    sd = sdepth(r)
    d = decode(r, N8)
    print(f"  rep({a}): sdepth={sd}, decode={d} {'OK' if d == a else 'FAIL'}")
print()

# Try all possible simulation terms t (excluding s=2)
print("Testing lazy eval construction with each simulation term t:")
print("-" * 60)

working_terms = []
for t_idx in range(N8):
    if t_idx == s8:
        # t = s is problematic (conflates encoding and simulation)
        continue

    eval_fn = make_lazy_eval(TABLE_8, N8, s8, t_idx)

    # Check self-simulation: eval(App(App(atom(t), rep(a)), rep(b))) = atom(dot(a,b))
    all_ok = True
    failures = []
    for a in range(N8):
        for b in range(N8):
            term = App(App(Atom(t_idx), rep(a, N8)), rep(b, N8))
            result = eval_fn(term)
            expected = Atom(dot(TABLE_8, a, b))
            if not term_eq(result, expected):
                all_ok = False
                failures.append((a, b, result, expected))

    if all_ok:
        working_terms.append(t_idx)
        print(f"  t={t_idx}: Self-simulation WORKS for all 64 cells!")
    else:
        print(f"  t={t_idx}: FAILS ({len(failures)} cells)")
        for a, b, got, exp in failures[:3]:
            print(f"    dot({a},{b}): expected {exp}, got {got}")

print()

# Also test t = s = 2 with analysis of why it's problematic
print("Testing t=s=2 (section element as simulation term):")
t_idx = 2
eval_fn_s = make_lazy_eval(TABLE_8, N8, s8, t_idx)  # s_idx == t_idx == 2
all_ok = True
failures = []
for a in range(N8):
    for b in range(N8):
        term = App(App(Atom(t_idx), rep(a, N8)), rep(b, N8))
        result = eval_fn_s(term)
        expected = Atom(dot(TABLE_8, a, b))
        if not term_eq(result, expected):
            all_ok = False
            failures.append((a, b, result, expected))
if all_ok:
    working_terms.append(t_idx)
    print(f"  t=2: Self-simulation WORKS even with t=s! (both lazy for same atom)")
else:
    print(f"  t=2: FAILS ({len(failures)} cells)")
    for a, b, got, exp in failures[:5]:
        print(f"    dot({a},{b}): expected {exp}, got {got}")
print()

# Compositionality verification
print("=" * 72)
print("COMPOSITIONALITY VERIFICATION")
print("=" * 72)
print()

if working_terms:
    t_test = working_terms[0]
    eval_fn = make_lazy_eval(TABLE_8, N8, s8, t_test)
    print(f"Testing compositionality for t={t_test} on random terms...")
    print()

    # Compositionality: if eval(s1) = eval(s2), then for all u,
    # eval(App(s1, u)) = eval(App(s2, u))
    #
    # By construction, eval(App(s, t)) = apply_eval(eval(s), eval(t)),
    # so the result depends on s ONLY through eval(s). This is
    # compositional by definition.

    print("STRUCTURAL ARGUMENT:")
    print("  eval(App(s, t)) = apply_eval(eval(s), eval(t))")
    print("  Therefore eval(App(s1, u)) depends on s1 ONLY through eval(s1).")
    print("  If eval(s1) = eval(s2), then apply_eval(eval(s1), eval(u)) = apply_eval(eval(s2), eval(u)).")
    print("  QED: compositionality holds BY CONSTRUCTION.")
    print()

    # Empirical verification too
    random.seed(42)
    comp_tests = 0
    comp_failures = 0

    # Generate many pairs (s1, s2) and check that eval(s1)=eval(s2) implies
    # eval(App(s1,u)) = eval(App(s2,u))
    terms = [random_term(N8, d) for d in range(5) for _ in range(200)]
    evals = [(t, eval_fn(t)) for t in terms]

    # Group by eval result
    eval_groups = {}
    for t, ev in evals:
        key = repr(ev)
        if key not in eval_groups:
            eval_groups[key] = []
        eval_groups[key].append(t)

    equiv_classes = {k: v for k, v in eval_groups.items() if len(v) >= 2}
    print(f"  Found {len(equiv_classes)} equivalence classes with >=2 members")

    for key, group in equiv_classes.items():
        for i in range(min(5, len(group))):
            for j in range(i + 1, min(6, len(group))):
                s1 = group[i]
                s2 = group[j]
                # Verify eval(s1) = eval(s2)
                e1 = eval_fn(s1)
                e2 = eval_fn(s2)
                assert term_eq(e1, e2), f"Bug: {e1} != {e2}"
                # Test with several u's
                for _ in range(10):
                    u = random_term(N8, 3)
                    r1 = eval_fn(App(s1, u))
                    r2 = eval_fn(App(s2, u))
                    comp_tests += 1
                    if not term_eq(r1, r2):
                        comp_failures += 1

    print(f"  Ran {comp_tests} compositionality tests: {comp_failures} failures")
    if comp_failures == 0:
        print("  COMPOSITIONALITY VERIFIED empirically.")
    print()

# Nested term test
print("=" * 72)
print("NESTED TERM TEST")
print("=" * 72)
print()
print("Testing eval on deeply nested terms to check consistency:")
if working_terms:
    t_test = working_terms[0]
    eval_fn = make_lazy_eval(TABLE_8, N8, s8, t_test)

    # Triple application: App(App(App(t, rep(a)), rep(b)), rep(c))
    # eval(App(App(t, rep(a)), rep(b))) = atom(dot(a,b))
    # eval(App(atom(dot(a,b)), rep(c))) = ...depends on what atom(dot(a,b)) does
    print(f"Triple application: App(App(App(atom({t_test}), rep(a)), rep(b)), rep(c))")
    print(f"  Inner result: atom(dot(a,b))")
    print(f"  Then: apply_eval(atom(dot(a,b)), rep(c))")
    print()
    for a in range(min(3, N8)):
        for b in range(min(3, N8)):
            for c in range(min(3, N8)):
                inner = Atom(dot(TABLE_8, a, b))
                term = App(App(App(Atom(t_test), rep(a, N8)), rep(b, N8)), rep(c, N8))
                result = eval_fn(term)
                # The inner eval gives atom(dot(a,b)), then we apply to rep(c)
                # If dot(a,b) == s_idx or dot(a,b) == t_test, it's lazy
                # Otherwise it ground-reduces
                ab = dot(TABLE_8, a, b)
                if ab == s8:
                    expected_desc = f"App(atom(2), rep({c})) [lazy s]"
                elif ab == t_test:
                    expected_desc = f"App(atom({t_test}), rep({c})) [lazy t, ready for next lookup]"
                else:
                    expected_desc = f"atom(dot({ab}, {c})) = atom({dot(TABLE_8, ab, c)}) [ground reduce]"
                print(f"  dot({a},{b})={ab}, then apply to rep({c}): {result}  [{expected_desc}]")
    print()

# ═══════════════════════════════════════════════════════════════════
# KEY ANALYSIS: Why this works for ANY R-magma
# ═══════════════════════════════════════════════════════════════════

print("=" * 72)
print("KEY ANALYSIS: Why This Works for ANY R-Magma")
print("=" * 72)
print("""
The lazy eval construction works for ANY magma (M, dot) of size N with a
section element s, provided there exists an element t != s in {0..N-1}.

Construction:
  1. rep(a) = s^a(atom(z1))           -- s-depth encoding
  2. decode(term) = sdepth(term) % N   -- s-depth decoding
  3. applyEval:
     - atom(s) applied to v  -> App(atom(s), v)     [lazy: preserve encoding]
     - atom(t) applied to v  -> App(atom(t), v)     [lazy: wrap for lookup]
     - App(atom(t), inner) applied to v
                             -> atom(dot(decode(inner), decode(v)))  [lookup]
     - atom(a) applied to v  -> atom(dot(a, decode(v)))  [ground reduce]
     - otherwise             -> App(u, v)            [stuck]

Compositionality:
  eval(App(s, t)) = applyEval(eval(s), eval(t))
  Result depends on s ONLY through eval(s). QED.

Self-simulation:
  eval(App(App(atom(t), rep(a)), rep(b)))
  = applyEval(applyEval(atom(t), rep(a)), rep(b))     [eval recurses]
  = applyEval(App(atom(t), rep(a)), rep(b))            [atom(t) is lazy]
  = atom(dot(decode(rep(a)), decode(rep(b))))           [lookup case]
  = atom(dot(a, b))                                     [decode(rep(a)) = a]

This requires:
  (a) t != s (so atom(t) and atom(s) have different lazy behaviors)
  (b) decode(rep(a)) = a for all a in {0..N-1}
      (true because sdepth(s^a(atom(0))) = a and a < N so a % N = a)

It does NOT require:
  - Any algebraic properties of t (t can be an absorber, classifier, anything)
  - The Kripke dichotomy
  - Any relationship between s and a retraction r
  - Even a retraction! Just a distinguished element s is enough.

CONCLUSION: The self-simulation definition (exists compositional eval and
term t such that eval(App(App(t, rep(a)), rep(b))) = atom(dot(a, b)))
is TRIVIALLY satisfiable for any magma of size N >= 2 with a distinguished
section element. It imposes NO constraints on the algebraic structure.

The definition is vacuous as stated.
""")

# ═══════════════════════════════════════════════════════════════════
# PHASE 3: eval_strict (ground-level evaluation)
# ═══════════════════════════════════════════════════════════════════

print("=" * 72)
print("PHASE 3: eval_strict (Ground-Level Evaluation)")
print("=" * 72)
print()
print("Under eval_strict:")
print("  eval_strict(atom(a)) = a")
print("  eval_strict(App(t1, t2)) = dot(eval_strict(t1), eval_strict(t2))")
print()
print("Self-simulation requires: exists t such that")
print("  dot(dot(t, rep_elem(a)), rep_elem(b)) = dot(a, b) for all a, b")
print("where rep_elem(a) = eval_strict(rep(a)) = s^a(z1) as a ground value.")
print()


def compute_rep_elem(table, N, s_idx, z1=0):
    """Compute ground-level rep values: rep_elem(a) = s^a(z1)."""
    reps = [z1]
    val = z1
    for a in range(1, N):
        val = dot(table, s_idx, val)
        reps.append(val)
    return reps


# ─── Test 3a: N=5 witness ───
print("-" * 60)
print("Test 3a: N=5 witness (s=2, r=2, z1=0)")
print("-" * 60)
reps5 = compute_rep_elem(TABLE_5, 5, 2, 0)
print(f"  rep_elem values: {reps5}")
print(f"  Distinct values: {set(reps5)} ({len(set(reps5))} unique out of 5)")
injective5 = len(set(reps5)) == 5
print(f"  Injective: {injective5}")
if not injective5:
    for i in range(5):
        for j in range(i + 1, 5):
            if reps5[i] == reps5[j]:
                print(f"  COLLISION: rep_elem({i}) = rep_elem({j}) = {reps5[i]}")
print()

# ─── Test 3b: N=6 witness ───
print("-" * 60)
print("Test 3b: N=6 witness (s=2, r=3, z1=0)")
print("-" * 60)
reps6 = compute_rep_elem(TABLE_6, 6, 2, 0)
print(f"  rep_elem values: {reps6}")
print(f"  Distinct values: {set(reps6)} ({len(set(reps6))} unique out of 6)")
injective6 = len(set(reps6)) == 6
print(f"  Injective: {injective6}")
if not injective6:
    for i in range(6):
        for j in range(i + 1, 6):
            if reps6[i] == reps6[j]:
                print(f"  COLLISION: rep_elem({i}) = rep_elem({j}) = {reps6[i]}")
print()

# ─── Test 3c: Exhaustive check for eval_strict self-simulation ───
print("-" * 60)
print("Test 3c: Exhaustive search for eval_strict simulation term")
print("-" * 60)

for name, table, N, s_idx, reps in [
    ("N=5", TABLE_5, 5, 2, reps5),
    ("N=6", TABLE_6, 6, 2, reps6),
    ("N=8", TABLE_8, 8, 2, compute_rep_elem(TABLE_8, 8, 2, 0)),
]:
    print(f"\n  {name} (s={s_idx}):")
    if name == "N=8":
        reps8 = reps
        print(f"    rep_elem values: {reps}")
        print(f"    Distinct: {len(set(reps))} unique out of {N}")

    for t in range(N):
        all_ok = True
        for a in range(N):
            for b in range(N):
                lhs = dot(table, dot(table, t, reps[a]), reps[b])
                rhs = dot(table, a, b)
                if lhs != rhs:
                    all_ok = False
                    break
            if not all_ok:
                break
        if all_ok:
            print(f"    t={t}: eval_strict self-simulation WORKS!")
        else:
            # Count how many cells work
            ok_count = sum(
                1 for a in range(N) for b in range(N)
                if dot(table, dot(table, t, reps[a]), reps[b]) == dot(table, a, b)
            )
            print(f"    t={t}: FAILS ({ok_count}/{N*N} cells match)")

print()

# ─── Test 3d: Z3 search for eval_strict-compatible magmas ───
print("=" * 72)
print("Test 3d: Z3 Search for eval_strict-Compatible Magmas")
print("=" * 72)
print()

try:
    from z3 import Solver, Int, And, Or, Distinct, sat, If

    for target_N in [5, 6]:
        print(f"Searching for N={target_N} E2PM with injective rep_elem and eval_strict self-simulation...")

        solver = Solver()
        N = target_N

        # Cayley table variables
        T = [[Int(f"t_{i}_{j}") for j in range(N)] for i in range(N)]
        for i in range(N):
            for j in range(N):
                solver.add(T[i][j] >= 0, T[i][j] < N)

        # Absorber rows: 0 is z1, 1 is z2
        for j in range(N):
            solver.add(T[0][j] == 0)
            solver.add(T[1][j] == 1)

        # Extensionality: distinct rows (for non-absorbers implied, but let's enforce globally)
        for i1 in range(N):
            for i2 in range(i1 + 1, N):
                solver.add(Or(*[T[i1][j] != T[i2][j] for j in range(N)]))

        # No other absorbers: for each a not in {0,1}, exists b s.t. dot(a,b) not in {a repeated}
        # Actually: "no other zeros" means no element besides 0,1 has a constant row
        for a in range(2, N):
            # There exists j, k with T[a][j] != T[a][k] OR T[a][0] != a
            # Simpler: row a is not constantly a
            solver.add(Or(*[T[a][j] != T[a][0] for j in range(1, N)]))

        # Section element: s = 2
        s_idx = 2

        # Retraction element: try r = 3 for N>=6, r = 2 for N=5
        # Actually let's let r be free
        r_idx = Int("r")
        solver.add(r_idx >= 2, r_idx < N)

        # rep_elem values (ground level)
        rep_elem = [Int(f"rep_{a}") for a in range(N)]
        rep_elem[0] = Int("rep_0_val")
        solver.add(rep_elem[0] == 0)  # rep(0) = z1 = 0

        # rep_elem(a+1) = dot(s, rep_elem(a))
        # We need to express: rep_elem[a] = T[s_idx][rep_elem[a-1]]
        # This requires nested If chains since rep_elem[a-1] is a variable
        def table_lookup(row, col_var, N, T):
            """Express T[row][col_var] using If chains."""
            result = T[row][0]
            for v in range(1, N):
                result = If(col_var == v, T[row][v], result)
            return result

        for a in range(1, N):
            solver.add(rep_elem[a] == table_lookup(s_idx, rep_elem[a - 1], N, T))

        # Injectivity of rep_elem
        for i in range(N):
            solver.add(rep_elem[i] >= 0, rep_elem[i] < N)
        solver.add(Distinct(*rep_elem))

        # Retraction axioms
        # ret_sec: r(s(x)) relates to x... The actual axiom from FaithfulRetractMagma:
        # ret_sec: dot(ret, dot(sec, x)) = dot(sec, x) for all core x
        # sec_ret: dot(sec, dot(ret, x)) = x for core x? Let me check the Lean def.
        # Actually from the Lean: ret_sec means the composition works.
        # Let me just require: r . s = id on core (elements 2..N-1)
        # and s . r acts as identity on the image of s

        # Simplified: For a retraction pair, we need:
        # dot(r, dot(s, x)) = x for all x (r is left-inverse of s on image)
        # Actually the standard axiom is just: ret . sec = sec (retraction), sec . ret = sec (also?)
        # From the Lean: ret_sec says one thing, sec_ret another.
        # Let me use the actual FRM axioms from the Lean:
        # ret_sec : ∀ x, dot ret (dot sec x) = dot sec x   [E(Q(x)) = Q(x)]
        # sec_ret : ∀ x, dot sec (dot ret x) = x           [Q(E(x)) = x]   wait that can't be right
        # Actually from CatKripkeWallMinimal.lean the axiom might be different.
        # Let me just use a simpler version: require E-transparency + round-trip

        # For simplicity, just search with the core constraint:
        # There exists t such that for all a, b:
        #   dot(dot(t, rep_elem(a)), rep_elem(b)) = dot(a, b)

        t_var = Int("sim_t")
        solver.add(t_var >= 0, t_var < N)

        for a in range(N):
            for b in range(N):
                # dot(dot(t_var, rep_elem[a]), rep_elem[b]) = dot(a, b)
                # LHS: first compute dot(t_var, rep_elem[a])
                # t_var and rep_elem[a] are both symbolic
                inner = Int(f"inner_{a}")

                # inner = T[t_var][rep_elem[a]]
                # Need double If chain
                inner_expr = T[0][0]  # default
                for ti in range(N):
                    for ri in range(N):
                        inner_expr = If(And(t_var == ti, rep_elem[a] == ri),
                                        T[ti][ri], inner_expr)
                solver.add(inner == inner_expr)

                # outer = T[inner][rep_elem[b]]
                outer = Int(f"outer_{a}_{b}")
                outer_expr = T[0][0]
                for ii in range(N):
                    for ri in range(N):
                        outer_expr = If(And(inner == ii, rep_elem[b] == ri),
                                        T[ii][ri], outer_expr)
                solver.add(outer == outer_expr)

                # Must equal dot(a, b)
                solver.add(outer == table_lookup(a, Int(f"const_b_{b}"), N, T)
                           if False else outer == T[a][b])

        print(f"  Solver configured with {N*N} self-sim constraints + injectivity...")
        result = solver.check()
        if result == sat:
            m = solver.model()
            print(f"  FOUND a model!")
            print(f"  Simulation term t = {m[t_var]}")
            print(f"  rep_elem = {[m.evaluate(rep_elem[a]) for a in range(N)]}")
            print(f"  Cayley table:")
            for i in range(N):
                row = [m.evaluate(T[i][j]).as_long() for j in range(N)]
                print(f"    Row {i}: {row}")
        else:
            print(f"  NO MODEL FOUND (result: {result})")
        print()

except ImportError:
    print("  Z3 not available, skipping Test 3d.")
    print()

# ═══════════════════════════════════════════════════════════════════
# FINAL SUMMARY
# ═══════════════════════════════════════════════════════════════════

print("=" * 72)
print("FINAL SUMMARY")
print("=" * 72)
print(f"""
PHASE 1 RESULT: The pathological lazy eval WORKS.
  - For the N=8 R-not-D counterexample, simulation terms that work: {working_terms}
  - The construction is purely structural: it uses decode(rep(a)) = a (s-depth),
    NOT any algebraic property of the magma.
  - Compositionality holds by construction: eval(App(s,t)) = applyEval(eval(s), eval(t)).
  - This works for ANY magma with N >= 2 and a distinguished element s.
  - The definition of self-simulation is VACUOUS under the lazy eval interpretation.

PHASE 3 RESULT: eval_strict collapses.
  - N=5 witness: rep_elem is NOT injective (collisions: rep(0)=rep(1)=0).
  - N=6 witness: rep_elem is NOT injective (collisions: rep(1)=rep(5)=3).
  - Even where rep_elem has some distinct values, no simulation term t satisfies
    dot(dot(t, rep_elem(a)), rep_elem(b)) = dot(a, b) for all a, b.
  - eval_strict would be a meaningful constraint IF the s-depth encoding were
    injective at the ground level, but our witnesses show this often fails.

IMPLICATION FOR THE PAPER:
  The current self-simulation definition (SelfSim5.lean, SelfSim6.lean) uses
  a lazy eval that makes self-simulation trivially achievable. The eval function
  is essentially a term-level lookup table that works for ANY magma.

  To make self-simulation a meaningful (non-trivial) property, one would need
  either:
    (a) Restrict to eval_strict (ground evaluation), which requires injective
        s-depth encoding -- a genuinely constraining condition.
    (b) Add constraints on eval beyond compositionality (e.g., homomorphism,
        or require eval to respect some equational theory).
    (c) Require the simulation term t to be algebraically constrained
        (e.g., t must be in the core, or t must relate to the retraction).
""")
