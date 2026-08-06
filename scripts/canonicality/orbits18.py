"""Classify the 18 F3 orbits; hunt the separating axiom.

Candidates, from StackAForced.lean's residue list and the artifact's
decoded structure:
  (C1) commutation hygiene: gamma o s = s o gamma on the core
  (C2) judge orientation: judge row indicates the IMAGE cycle Q
       (already imposed) vs source P — variant check
  (C3) role multiplicity: r-row = s-row as maps (forced by involution
       + retraction; sanity)
  (C4) gamma fixes the OFF-judge cycle pointwise (artifact: gamma
       fixes {2,5} = the cycle not in the swapped pair)
"""
import sys
sys.path.insert(0, 'scripts/canonicality')
from census_frame_n8 import (B, G, CHI, inv, is_invol, act_N, act_C,
                             comp, cycles_of_invol, cycle_swap,
                             indicator, f3_families, ART_N, ART_C,
                             NPART, CPART)
from itertools import permutations

combos = f3_families()
print(f"F3 raw: {len(combos)}")

def canon(cfg):
    tn, tc = cfg
    return min((act_N(g, tn), act_C(g, tc)) for g in G)

orbits = {}
for cfg in combos:
    orbits.setdefault(canon(cfg), []).append(cfg)
print(f"orbits: {len(orbits)}")
art_key = canon((ART_N, ART_C))

def commutes(tn):
    """C1 on a representative: exists assignment s,r,gamma with s
    involutive, r-row = s-row-inverse, gamma the third, and
    gamma o s = s o gamma."""
    for i in range(3):
        for j in range(3):
            if i == j or tn[j] != inv(tn[i]) or not is_invol(tn[i]):
                continue
            k = 3 - i - j
            if comp(tn[k], tn[i]) == comp(tn[i], tn[k]):
                return True
    return False

def gamma_fixes_offcycle(tn):
    """C4: gamma pointwise-fixes... artifact gamma maps 2->5,5->2 on
    the off cycle {2,5} — i.e., gamma AGREES WITH s on the off-cycle
    (not fixes pointwise: gamma(2)=5=s(2)). Test: exists roles with
    gamma = s on exactly one s-cycle and = cycle-swap o s elsewhere
    (that's judge-closure already). Refine: gamma agrees with s on
    the off cycle."""
    for i in range(3):
        for j in range(3):
            if i == j or tn[j] != inv(tn[i]) or not is_invol(tn[i]):
                continue
            k = 3 - i - j
            s, g = tn[i], tn[k]
            agree = [x for x in range(6) if g[x] == s[x]]
            # exactly one s-cycle (2 elements) of agreement
            if len(agree) == 2 and s[agree[0]] == agree[1]:
                return True
    return False

print("\norbit survey (representative = canonical form):")
for idx, (key, members) in enumerate(sorted(orbits.items())):
    tn, tc = key
    c1 = commutes(tn)
    c4 = gamma_fixes_offcycle(tn)
    mark = "  <-- ARTIFACT" if key == art_key else ""
    print(f"orbit {idx:2d}: size {len(members):3d}  C1(commute)={int(c1)} "
          f"C4(off-cycle-agree)={int(c4)}{mark}")

n_c1 = sum(1 for key in orbits if commutes(key[0]))
n_c4 = sum(1 for key in orbits if gamma_fixes_offcycle(key[0]))
n_both = sum(1 for key in orbits
             if commutes(key[0]) and gamma_fixes_offcycle(key[0]))
print(f"\norbits with C1: {n_c1}; with C4: {n_c4}; with both: {n_both}")
print(f"artifact: C1={int(commutes(art_key[0]))} "
      f"C4={int(gamma_fixes_offcycle(art_key[0]))}")
