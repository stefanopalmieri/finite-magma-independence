"""Was lex-min luck?  Compute the lexicographic minimum over the 648
labeled F3 configurations and check which orbit it lands in."""
import sys
sys.path.insert(0, 'scripts/canonicality')
from census_frame_n8 import (G, CHI, inv, is_invol, act_N, act_C,
                             f3_families, ART_N, ART_C)

combos = f3_families()

def full_block(cfg):
    """6x6 core block, row-major, N-rows as core element labels (+2),
    C-rows as absorber labels 0/1."""
    tn, tc = cfg
    rows = []
    for b in tn:
        rows.append(tuple(b[x] + 2 for x in range(6)))
    for v in tc:
        rows.append(tuple(v))
    return tuple(rows)

def canon(cfg):
    tn, tc = cfg
    return min((act_N(g, tn), act_C(g, tc)) for g in G)

art_key = canon((ART_N, ART_C))

def is_selfloc(key):
    return key == art_key

# lex-min over all 648 labeled configs (roles pinned: rows 2,3 = quote
# copies at positions 0,1... in F3 the s-copies and gamma occupy the
# three N positions in all arrangements; the artifact convention is
# quote=pos0, eval=pos1, shift=pos2 with kappa at C-pos0)
best = min(combos, key=full_block)
print("global lex-min over all 648 labeled configs:")
print("  block:", full_block(best))
print("  in artifact's (self-locating) orbit:", canon(best) == art_key)
print("  equals artifact's exact labeled block:",
      full_block(best) == full_block((ART_N, ART_C)))

# variant: kappa pinned to classifier position 0 (the law-set pins the
# introspector's label), as the artifact's law set did
pinned = [c for c in combos if c[1][0] == CHI]
bestp = min(pinned, key=full_block)
print(f"\nwith kappa law-pinned to label 5 ({len(pinned)} configs):")
print("  lex-min in self-locating orbit:", canon(bestp) == art_key)
print("  equals artifact's labeled block:",
      full_block(bestp) == full_block((ART_N, ART_C)))

# how special is this?  count how many of the 18 orbits could win
# lex-min under SOME labeling within their own orbit
from collections import defaultdict
orbit_best = {}
for c in combos:
    k = canon(c)
    fb = full_block(c)
    if k not in orbit_best or fb < orbit_best[k]:
        orbit_best[k] = fb
ranking = sorted(orbit_best.items(), key=lambda kv: kv[1])
print("\norbit ranking by each orbit's own lex-min representative:")
for i, (k, fb) in enumerate(ranking[:3]):
    tag = "  <-- ARTIFACT (self-locating)" if k == art_key else ""
    print(f"  rank {i}: row4-core={fb[2][:3]}..., row6-start={fb[5][:3]}{tag}")
