import sys, itertools, json
sys.path.insert(0, 'scripts')
sys.path.insert(0, 'scripts/canonicality')
import z3
from n8_enumerate_lexmin import law_set, core, n
from probe_dispatch import check_W_concrete

S, T = law_set()
tables = []
while S.check() == z3.sat:
    m = S.model()
    tbl = [[m.evaluate(T[i][j]).as_long() for j in range(n)] for i in range(n)]
    tables.append(tbl)
    S.add(z3.Or([T[i][j] != m.evaluate(T[i][j]).as_long()
                 for i in core for j in core]))
print(f"enumerated: {len(tables)} models")
hits = [(t, check_W_concrete(t, 8)) for t in tables]
withW = [(t, w) for t, w in hits if w is not None]
print(f"models satisfying W: {len(withW)} / {len(tables)}")
if withW:
    lex = min(withW, key=lambda tw: tuple(tuple(r) for r in tw[0]))
    print("lex-min W-satisfying model:")
    for r in lex[0]:
        print(" ", r)
    print("witness:", lex[1])
    json.dump({"count_total": len(tables), "count_W": len(withW),
               "lexmin_W_table": lex[0], "witness": lex[1]},
              open('scripts/canonicality/w_over_228_result.json', 'w'), indent=1)
