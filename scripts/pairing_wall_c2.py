"""The pairing wall's c = 2 edge case, settled by exhaustive search.

The abstract pairing wall (Magma/DataWalls.lean, `pairing_wall`) is
pure pigeonhole: internal curried pairing with both projections forces
(n-2)^2 <= n, impossible for n >= 5 (three or more core elements).
The c = 2 edge (n = 4) squeaks past counting: 4 <= 4. MACHINE.md's
prose claimed the wall for |core| >= 2; this script is the referee.

Question: does a 4-element magma with two left-absorbers admit
P, fst, snd with

    fst . ((P . a) . b) = a   and   snd . ((P . a) . b) = b

for all a, b in core = {2, 3}?  Tested both with and without
extensionality (distinct rows).

RESULT (asserted below): UNSAT in both cases — the wall holds at
c = 2 as well, but by case analysis rather than counting: with only
two core elements the projections are forced to coincide with the
partial applications, and their row constraints clash. So the
|core| >= 2 claim is TRUE, with a two-part proof: pigeonhole for
c >= 3 (the Lean theorem), exhaustion for c = 2 (this script).
"""
import z3

n = 4
core = [2, 3]

def solve(extensional):
    T = [[z3.Int(f"t{i}_{j}") for j in range(n)] for i in range(n)]
    S = z3.Solver()
    for i in range(n):
        for j in range(n):
            S.add(T[i][j] >= 0, T[i][j] < n)
    # two left-absorbers
    for j in range(n):
        S.add(T[0][j] == 0, T[1][j] == 1)
    if extensional:
        for a in range(n):
            for b in range(a + 1, n):
                S.add(z3.Or([T[a][x] != T[b][x] for x in range(n)]))
    P, fst, snd = z3.Ints("P fst snd")
    for v in (P, fst, snd):
        S.add(v >= 0, v < n)
    # fst . ((P . a) . b) = a  and  snd . ((P . a) . b) = b  on core:
    # case-split every table lookup through explicit value guards
    for a in core:
        for pa in range(n):          # pa = P . a
            for pab in range(n):     # pab = pa . b
                for b in core:
                    S.add(z3.Implies(
                        z3.And(*[z3.Implies(P == p, T[p][a] == pa)
                                 for p in range(n)],
                               T[pa][b] == pab),
                        z3.And(*[z3.Implies(fst == f, T[f][pab] == a)
                                 for f in range(n)],
                               *[z3.Implies(snd == s, T[s][pab] == b)
                                 for s in range(n)])))
    return S.check()

for ext in (False, True):
    r = solve(ext)
    label = "with extensionality" if ext else "without extensionality"
    print(f"c = 2 pairing {label}: {r}")
    assert r == z3.unsat, (
        f"pairing found at c = 2 ({label}) — the |core| >= 2 claim "
        "would need weakening to >= 3!")
print("WALL HOLDS AT c = 2: no internal pairing even where pigeonhole "
      "is silent")
