"""The ablation ledger: every chosen law of the N=8 law set, priced.

The derivation ledger (MACHINE.md §2, paper §ledger) sorts the
canonical model's law set into derived and chosen. The ICP episode
showed that unpriced "chosen" laws can hide surprises in both
directions — a law can be secretly redundant, or secretly load-bearing
through a label. This script completes the practice started by the ¬W
and ICP records in `n8_enumerate_lexmin.py`: every remaining chosen
law gets a drop-experiment with committed asserts. One shared law-set
definition (`n8_enumerate_lexmin.law_set`) is the single source of
truth; this script only toggles its switches.

RESULTS (2026-08-15, all asserts below; ~10 minutes of Z3):

  law dropped              models   lex-min
  ------------------------ -------  ------------------------------
  (baseline)                  168   rawA8
  quote-commutation           168   unchanged   <- REDUNDANT
  shift involution            264   unchanged   (tie-break-inert)
  shift action-distinctness   216   unchanged   (tie-break-inert)
  faithful shift              168   unchanged   <- subsumed by involution
  comm + involution           264   unchanged   (comm still implied)
  comm + ¬W                   228   unchanged   (comm implied pre-¬W too)
  faithful + involution      1344   row 4 -> [0,0,5,5,5,2,2,2]
  all four shift laws        1584   row 4 -> [0,0,5,5,5,2,2,2]

  measurement: quote involution (not a law) holds in 144 of the 168
  models — the order-minimum tie-break prices at 24 models.

READINGS:

* Quote-commutation — the ledger's "definition of hygienic" — is
  IMPLIED by the remaining laws at every margin probed (adopted set,
  involution-free set, pre-¬W set). It has selective content only
  when faithfulness AND involution are both absent (1344 -> 1584).
  As an enumeration constraint it is redundant; it remains the
  definitional characterization used by the frame theorems
  (StackAForced.lean, QuoteOrbit.lean).
* Faithfulness is subsumed by the involution (an involution is a
  bijection), and the involution is tie-break-inert on its own — but
  drop BOTH and the lex-min degenerates: shift collapses to the
  cheapest block-swap map and the artifact loses its hygiene
  operator. One shift-injectivity law is load-bearing for row 4;
  which of the two supplies it is a presentation choice.
* Distinctness and the involution are individually real constraints
  (216, 264 models) that the lex-min tie-break never feels.

THE COMPRESSED LEDGER: with the frame derived (StackAForced), the
eval side free (EvalSideFree), ICP a consequence of judge-closure,
¬W inert, and the above, the artifact's chosen-and-load-bearing
residue is exactly TWO laws — judge-closure (buys row 7, the shift?
recognizer) and one shift-injectivity law (buys row 4, the hygiene
operator) — plus naming conventions, with the representative itself
characterized by self-location (CoreCanonical.lean) rather than by
lex-min.
"""
import importlib.util
import pathlib

import z3

_here = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location(
    "n8_enumerate_lexmin", _here / "n8_enumerate_lexmin.py")
lexmin = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lexmin)

core = lexmin.core
RAW_A8 = lexmin.RAW_A8

DEGENERATE_SHIFT = [0, 0, 5, 5, 5, 2, 2, 2]


def count_models(cap=20000, **kw):
    """Exact model count (asserts the cap is never hit — no silent caps)."""
    S, T = lexmin.law_set(**kw)
    n = 0
    while S.check() == z3.sat and n < cap:
        m = S.model()
        S.add(z3.Or([T[i][j] != m.evaluate(T[i][j]).as_long()
                     for i in core for j in core]))
        n += 1
    assert n < cap, f"model count hit the cap ({cap}) — raise it"
    return n


def run(name, expect_count, expect_rows, **kw):
    n = count_models(**kw)
    tbl = lexmin.lex_min_table(**kw)
    diff = {k: tbl[k] for k in range(8) if tbl[k] != RAW_A8[k]}
    print(f"{name}: {n} models | "
          f"lex-min {'unchanged' if not diff else 'changed ' + str(diff)}")
    assert n == expect_count, f"{name}: expected {expect_count}, got {n}"
    assert diff == expect_rows, f"{name}: lex-min diff {diff}"


if __name__ == "__main__":
    run("baseline", 168, {})
    # single drops
    run("drop quote-commutation", 168, {}, quote_comm=False)
    run("drop shift involution", 264, {}, shift_inv=False)
    run("drop shift distinctness", 216, {}, shift_distinct=False)
    run("drop faithful shift", 168, {}, faithful=False)
    print("REDUNDANT: quote-commutation and faithfulness add no "
          "constraint over the rest of the adopted law set")
    print("INERT: involution and distinctness are real constraints "
          "the tie-break never feels")
    # locating probes
    run("drop commutation + involution", 264, {},
        quote_comm=False, shift_inv=False)
    run("drop commutation + ¬W", 228, {},
        quote_comm=False, no_dispatch=False)
    run("drop faithfulness + involution", 1344,
        {4: DEGENERATE_SHIFT}, faithful=False, shift_inv=False)
    run("drop all four shift laws", 1584,
        {4: DEGENERATE_SHIFT},
        quote_comm=False, shift_inv=False, shift_distinct=False,
        faithful=False)
    print("LOAD-BEARING: one shift-injectivity law buys row 4 — drop "
          "both injectivity sources and the hygiene operator degenerates")
    # measurement: quote involution inside the adopted space
    S, T = lexmin.law_set()
    inv = tot = 0
    while S.check() == z3.sat:
        m = S.model()
        vals = {(i, j): m.evaluate(T[i][j]).as_long()
                for i in range(8) for j in range(8)}
        tot += 1
        if all(vals[(2, vals[(2, x)])] == x for x in core):
            inv += 1
        S.add(z3.Or([T[i][j] != vals[(i, j)]
                     for i in core for j in core]))
    print(f"measurement: quote involution holds in {inv}/{tot} models")
    assert (inv, tot) == (144, 168), f"expected 144/168, got {inv}/{tot}"
    print("TIE-BREAK PRICED: the order-minimum convention (quote "
          "involutive) excludes 24 of the 168 — bought by lex-min, "
          "retired by self-location")
    print("ALL LEDGER ASSERTS PASS")
