"""The 18 orbits' true coordinates: role placement relative to the
quote-cycle structure — and the self-location characterization."""
import sys
sys.path.insert(0, 'scripts/canonicality')
from census_frame_n8 import (B, G, CHI, inv, is_invol, act_N, act_C,
                             comp, f3_families, ART_N, ART_C)

combos = f3_families()

def canon(cfg):
    tn, tc = cfg
    return min((act_N(g, tn), act_C(g, tc)) for g in G)

def placement(cfg):
    """Invariant coordinates: for a valid (s,r,gamma / chi,notchi,j)
    role assignment, locate each role holder's s-cycle: P (source of
    the judge swap), Q (target/judged), O (off).  Returns the pattern
    (gamma_holder_cycle, chi_cycle, notchi_cycle, j_cycle)."""
    tn, tc = cfg
    NOTCHI = tuple(1 - x for x in CHI)
    pats = set()
    for i in range(3):          # s position
        for j in range(3):      # r position
            if i == j or tn[j] != inv(tn[i]) or not is_invol(tn[i]):
                continue
            k = 3 - i - j       # gamma position
            s, g = tn[i], tn[k]
            # find the ordered cycle pair (P,Q): g = swap(P,Q) o s
            cyc = [(x, s[x]) for x in range(3)]   # (n-elt, c-elt)
            for P in cyc:
                for Q in cyc:
                    if P == Q:
                        continue
                    t = list(range(6))
                    t[P[0]], t[Q[0]] = Q[0], P[0]
                    t[P[1]], t[Q[1]] = Q[1], P[1]
                    if tuple(t[s[x]] for x in range(6)) != g:
                        continue
                    O = next(c for c in cyc if c not in (P, Q))
                    def cycname(elt):
                        for nm, c in (("P", P), ("Q", Q), ("O", O)):
                            if elt in c:
                                return nm
                        return "?"
                    # j row position and content
                    for jj in range(3):
                        if tc[jj] == tuple(1 if x in Q else 0
                                           for x in range(6)):
                            jcy = cycname(3 + jj)
                            break
                    else:
                        continue
                    chicy = next(cycname(3 + a) for a in range(3)
                                 if tc[a] == CHI)
                    ncy = next(cycname(3 + a) for a in range(3)
                               if tc[a] == NOTCHI)
                    pats.add((cycname(k), chicy, ncy, jcy))
    return frozenset(pats)

orbits = {}
for cfg in combos:
    orbits.setdefault(canon(cfg), cfg)
art_key = canon((ART_N, ART_C))

print("orbit placement patterns (gamma@, chi@, notchi@, judge-row@):")
selfloc = []
for idx, (key, rep) in enumerate(sorted(orbits.items())):
    pats = placement(rep)
    mark = "  <-- ARTIFACT" if key == art_key else ""
    print(f"orbit {idx:2d}: {sorted(pats)}{mark}")
    # self-location: gamma on Q, judge row on Q, chi on O
    if any(p == ("Q", "O", "P", "Q") for p in pats):
        selfloc.append(idx)
print(f"\nself-locating orbits (gamma@Q, chi@O, notchi@P, j@Q): {selfloc}")
