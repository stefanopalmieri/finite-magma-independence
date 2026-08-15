"""A4 ablation for the intrinsic kernel (CoreCanonical.lean): does
canonicity need the ICP axiom?

CoreCanonical's `core_canonical` derives the artifact's full core block
from an intrinsic axiom set: retraction (H1), quote involution (H2),
quote core-valuedness (H3), the three quoted-classifier row axioms —
A1: `⌜quote⌝` recognizes exactly the operators, A3: `⌜shift⌝`
recognizes exactly {shift, itself}, A4: `⌜eval⌝` complements `⌜quote⌝`
(the ICP law in complement form) — each with a two-valuedness typing
half (K2/J2/C2), and A2: shift's six cells.

This script prices each recognition axiom by ablation, in the style of
n8_enumerate_lexmin.py. WLOG labels: z1=0, z2=1, s=2, r=3, gamma=4;
the quoted operators K=s.s, C=s.r, J=s.gamma land somewhere in
{5,6,7} — a 3! relabeling freedom the bridge's `g` absorbs, pinned
here to (K,C,J)=(5,6,7) for clean counts (raw counts = 6x).

RESULTS (2026-08-14, this script's asserts):
  full intrinsic system, placement pinned:   1 model  (= dotA8 core)
  drop A4  (keep C2):                       64 models (= 2^6: exactly
      the free {0,1}-choices of ⌜eval⌝'s six core cells; nothing else
      in the system touches that row — A4 IS those six bits)
  drop A1  (keep K2):                       64 models (same, for
      ⌜quote⌝'s row)
  drop A3  (keep J2):                       64 models (same, for
      ⌜shift⌝'s row)

Reading: the intrinsic kernel is a three-row specification plus glue —
each classifier row is pinned by exactly one recognition axiom, each
irreducible (its removal opens an independent 2^6 moduli space), and
the other 18 core cells (the three operator rows) are forced by
H1+H2+H3+A2 alone. ICP's place in the intrinsic presentation is
therefore: ONE OF EXACTLY THREE recognition axioms, on par with
"⌜quote⌝ recognizes operators" — needed there, derived in the
law-set presentation (judge-closure at t = kappa forces it;
n8_enumerate_lexmin.py). Two presentations, one law.
"""
import z3

n = 8
core = [2, 3, 4, 5, 6, 7]

# The artifact's core block (rawA8 restricted to rows/cols 2..7).
RAW_A8 = [
    [0, 0, 0, 0, 0, 0, 0, 0],
    [1, 1, 1, 1, 1, 1, 1, 1],
    [0, 0, 5, 6, 7, 2, 3, 4],
    [0, 1, 5, 6, 7, 2, 3, 4],
    [0, 0, 5, 7, 6, 2, 4, 3],
    [0, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 0, 1, 0, 0, 1],
]


def system(a1=True, a3=True, a4=True, pin_placement=True):
    """The core_canonical hypothesis list at pinned labels.

    a1/a3/a4 toggle the recognition axioms hK/hJ/hC; their
    two-valuedness halves hK2/hJ2/hC2 always stay."""
    T = [[z3.Int(f"t{i}_{j}") for j in range(n)] for i in range(n)]
    S = z3.Solver()
    for i in range(n):
        for j in range(n):
            S.add(T[i][j] >= 0, T[i][j] < n)
    s, r, g = 2, 3, 4
    # H3: quote core-valued on core
    for x in core:
        S.add(T[s][x] >= 2)
    # H1 retraction + H2 involution (case split on the quote value)
    for x in core:
        for v in core:
            S.add(z3.Implies(T[s][x] == v, T[r][v] == x))
            S.add(z3.Implies(T[s][x] == v, T[s][v] == x))
    K, C, J = T[s][s], T[s][r], T[s][g]
    if pin_placement:
        S.add(K == 5, C == 6, J == 7)
    # Row axioms for the three quoted classifiers. Each is guarded on
    # the placement value so the encoding is faithful when unpinned.
    for q in core:
        for x in core:
            # K2 + A1: ⌜quote⌝ two-valued; recognizes exactly {s,r,γ}
            S.add(z3.Implies(K == q,
                             z3.Or(T[q][x] == 0, T[q][x] == 1)))
            if a1:
                want = (x in (s, r, g))
                S.add(z3.Implies(K == q,
                                 T[q][x] == 1 if want else T[q][x] != 1))
            # C2 + A4: ⌜eval⌝ two-valued; complements ⌜quote⌝ (ICP)
            S.add(z3.Implies(C == q,
                             z3.Or(T[q][x] == 0, T[q][x] == 1)))
            if a4:
                for k in core:
                    S.add(z3.Implies(z3.And(C == q, K == k),
                                     (T[q][x] == 1) == (T[k][x] == 0)))
            # J2 + A3: ⌜shift⌝ two-valued; recognizes exactly {γ, ⌜γ⌝}
            S.add(z3.Implies(J == q,
                             z3.Or(T[q][x] == 0, T[q][x] == 1)))
            if a3:
                S.add(z3.Implies(J == q,
                                 T[q][x] == 1 if x == g else
                                 z3.If(z3.IntVal(x) == J,
                                       T[q][x] == 1, T[q][x] != 1)))
    # A2: shift's six cells
    S.add(T[g][s] == K, T[g][r] == J, T[g][g] == C)
    for q in core:
        S.add(z3.Implies(K == q, T[g][q] == s))
        S.add(z3.Implies(C == q, T[g][q] == g))
        S.add(z3.Implies(J == q, T[g][q] == r))
    return S, T


def count_core_tables(cap=500, **kw):
    S, T = system(**kw)
    models, count = [], 0
    while S.check() == z3.sat and count < cap:
        m = S.model()
        tbl = [[m.evaluate(T[i][j]).as_long() for j in core] for i in core]
        models.append(tbl)
        S.add(z3.Or([T[i][j] != m.evaluate(T[i][j]).as_long()
                     for i in core for j in core]))
        count += 1
    return count, models


if __name__ == "__main__":
    a8core = [[RAW_A8[i][j] for j in core] for i in core]

    cnt, models = count_core_tables()
    print(f"full intrinsic system (placement pinned): {cnt} core table(s)")
    assert cnt == 1, f"expected the unique canonical core block, got {cnt}"
    assert models[0] == a8core, "the unique model is not dotA8's core block!"
    print("  = dotA8's core block exactly (core_canonical, re-derived)")

    cnt6, _ = count_core_tables(pin_placement=False)
    print(f"full system, placement free: {cnt6} core tables")
    assert cnt6 == 6, f"expected 3! placement relabelings, got {cnt6}"

    for name, kw in (("A4 (⌜eval⌝ complements ⌜quote⌝ — the ICP)",
                      dict(a4=False)),
                     ("A1 (⌜quote⌝ recognizes the operators)",
                      dict(a1=False)),
                     ("A3 (⌜shift⌝ recognizes the shift pair)",
                      dict(a3=False))):
        cnt, models = count_core_tables(**kw)
        print(f"drop {name}: {cnt} core tables")
        assert cnt == 64, f"expected 2^6 = 64, got {cnt}"
        assert sum(1 for t in models if t == a8core) == 1, \
            "dotA8's core block should appear exactly once"
    print("IRREDUCIBLE x3: each recognition axiom is exactly the six free "
          "bits of its classifier row; canonicity fails 63/64 ways without "
          "any one of them")
