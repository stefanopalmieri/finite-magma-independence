"""Clone-theory experiment: unary polynomial clone closure of D-magmas.

Computes the unary part of the polynomial clone (closure of {id, constants}
under composition and pointwise product f(x)*g(x)) and tests functional
(polynomial) completeness via the Slupecki criterion (|A| >= 3: a clone
containing all unary operations and an essentially binary surjective
operation is all of O_A).

Findings (frozen):
  * dNoS4 (the tight D=/=>S witness, E2PM.lean): unary clone = 256/256,
    essentially binary surjective => FUNCTIONALLY COMPLETE and satisfies D.
  * comp5 below: N=5 E2PM satisfying D, no retraction pair, unary clone
    = 3125/3125 => functionally complete and satisfies D.
  * witness5 (270/3125), rdNoH5 (629/3125), kernel6 (302/46656): far from
    complete -- external expressive power is a free dial inside D-magmas.

Together with the completeness wall (CompletenessWall.lean: combinatory
completeness excludes D at every cardinality), this separates *internal*
(combinatory: operations named by elements as rows) from *external*
(clone/polynomial: operations expressible) completeness: D is consistent
with a Sheffer-complete function space, but never with an algebra that can
NAME that completeness.
"""
def unary_poly_closure(T, n, cap=None):
    full = n ** n
    if cap is None: cap = full
    U = {tuple(range(n))} | {tuple(a for _ in range(n)) for a in range(n)}
    changed = True
    while changed and len(U) < cap:
        changed = False
        for f in list(U):
            for g in list(U):
                for h in (tuple(f[g[x]] for x in range(n)),
                          tuple(T[f[x]][g[x]] for x in range(n))):
                    if h not in U:
                        U.add(h); changed = True
            if len(U) >= cap: break
    return U

dNoS4 = [[0,0,0,0],[1,1,1,1],[0,1,1,1],[2,3,2,2]]
comp5 = [[0,0,0,0,0],[1,1,1,1,1],[1,0,0,1,0],[0,3,3,2,2],[4,0,4,3,3]]

if __name__ == "__main__":
    for name, T in [("dNoS4", dNoS4), ("comp5", comp5)]:
        n = len(T)
        U = unary_poly_closure(T, n)
        print(name, len(U), "of", n ** n)
