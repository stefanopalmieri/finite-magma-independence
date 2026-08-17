"""The self-location probe: judge-closure retires — for a price named
in full.

The ICP episode's move, one level up. Within the adopted law set, ICP
turned out to be a THEOREM of judge-closure + frame (the 306-model
UNSAT record in `n8_enumerate_lexmin.py`). The canonicity work then
showed the final 18 -> 1 selection is *self-location* — "the
classifiers are the quotations of the operators", certified
intrinsically as `CoreCanonical.lean`'s H1-H3 + A1-A4. That left the
ledger's last asymmetry: judge-closure justified operationally
(metacircularity spends it: KernelConsumption) but not derived, while
self-location is conceptually prior. The probe (2026-08-17): over the
closure-free law set, does self-location force judge-closure?

RESULTS (all asserts below; a few minutes of Z3):

  space (all over laws - closure)          models  closure forced?
  ---------------------------------------- ------  ---------------
  (baseline)                                1,860   no (lex-min
                                                    drifts at row 7)
  + SL (= A1/A3/A4: classifier content)         5   NO — SAT, and the
                                                    countermodels are
                                                    exactly the two
                                                    quote 6-cycles
  + H2 (quote involution) alone             1,116   NO — SAT
  + SL + H2 (the CoreCanonical package)         3   YES — UNSAT

  measurements: SL holds in 3/168 of the adopted models; the 5 SL
  models split 3 involutive (closure holds) + 2 six-cycles (closure
  fails); lex-min is rawA8 in every SL space probed.

READINGS:

* **Judge-closure is a theorem of the self-location package** —
  content (A1: [quote] answers yes exactly on the operators; A4:
  [eval] answers the complement; A3: [shift] answers yes exactly on
  shift and itself) PLUS form (H2: quote is an involution on the
  core). Over the frame, SL + H2 forces every judge's composite with
  quote to be named: kappa . quote and complement . quote land on
  each other via the pinned rows, and recognizer . quote is the
  recognizer itself precisely because the involution closes the
  shift pair.
* **Both halves are necessary.** Content without form: quote can act
  as a 6-cycle through the correctly-placed classifiers, and the
  recognizer's composite (indicator of {shift, [eval-of-shift]}) is
  a judgment no judge names — closure fails exactly at the
  recognizer. Form without content: 1,116 involutive-quote models
  with closure failing elsewhere.
* **The quote involution changes status.** The ablation ledger
  priced it as tie-break trivia (144/168, 24 models). It is not
  trivia: it is the *form half of self-description* — quotation that
  un-quotes is what lets the system's judgment of its own hygiene
  operator be one of its own judges.
* **The swap is a re-axiomatization, not a conservative rewrite.**
  SL is strictly sharper than closure (3/168 adopted models satisfy
  it; closure does not imply SL and SL alone does not imply
  closure). Its legitimacy is the certified canonicity theorem: the
  package characterizes the artifact up to core-isomorphism
  (CoreCanonical.lean), and the lex-min is unchanged in every space
  probed here.

THE RE-COMPRESSED LEDGER: adopt the self-location package (H2 +
A1/A3/A4) and judge-closure retires from axiom to consequence. The
chosen-and-load-bearing residue is then ONE definitional law (a
shift-injectivity source: hygiene means renaming) plus ONE
self-description principle (self-location, involution included) plus
naming — the universal-property conjecture (paper OP5) in executable
form, answered for the closure axiom.
"""
import importlib.util
import itertools
import pathlib

import z3

_here = pathlib.Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location(
    "n8_enumerate_lexmin", _here / "n8_enumerate_lexmin.py")
lexmin = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(lexmin)

n = lexmin.n
Nblk, Cblk = lexmin.Nblk, lexmin.Cblk
core = lexmin.core
RAW_A8 = lexmin.RAW_A8

RECOGNIZER_DRIFT = [0, 0, 0, 0, 0, 0, 0, 1]  # closure-free lex-min row 7


def selfloc(T):
    """CoreCanonical's A1/A3/A4 in the law-set world: quote sends the
    three operators to three classifier positions whose rows carry,
    on the core, the certified recognition content. Existential over
    placement — no naming presupposed (the kernel's row-5/row-6
    pinnings then leave [shift] nowhere to live but position 7)."""
    opts = []
    for cs, cr, cg in itertools.permutations(Cblk):
        conj = [T[2][2] == cs, T[2][3] == cr, T[2][4] == cg]
        for x in core:
            conj.append(T[cs][x] == (1 if x in Nblk else 0))     # A1
            conj.append(T[cr][x] == (0 if x in Nblk else 1))     # A4
            conj.append(T[cg][x] == (1 if x in (4, cg) else 0))  # A3
        opts.append(z3.And(conj))
    return z3.Or(opts)


def h2(T):
    """CoreCanonical's H2: quote is an involution on the core."""
    return z3.And([z3.Implies(T[2][x] == v, T[2][v] == x)
                   for x in core for v in core])


def closure_formula(T):
    """The judge-closure law as a formula (negatable): for every
    judge t, t . quote is a named judge."""
    con = []
    for t in Cblk:
        opts = []
        for t2 in Cblk:
            conj = []
            for x in core:
                for v in core:
                    conj.append(
                        z3.Implies(T[2][x] == v, T[t2][x] == T[t][v]))
            opts.append(z3.And(conj))
        con.append(z3.Or(opts))
    return z3.And(con)


def solver(extras=(), **kw):
    S, T = lexmin.law_set(**kw)
    for e in extras:
        S.add(e(T))
    return S, T


def count_models(extras=(), cap=20000, **kw):
    S, T = solver(extras, **kw)
    m_count = 0
    while S.check() == z3.sat and m_count < cap:
        m = S.model()
        S.add(z3.Or([T[i][j] != m.evaluate(T[i][j]).as_long()
                     for i in core for j in core]))
        m_count += 1
    assert m_count < cap, f"model count hit the cap ({cap})"
    return m_count


def lex_min(extras=(), **kw):
    S, T = solver(extras, **kw)
    fixed = []
    for i in range(n):
        row = []
        for j in range(n):
            for val in range(n):
                S.push()
                S.add(T[i][j] == val)
                if S.check() == z3.sat:
                    S.pop()
                    S.add(T[i][j] == val)
                    row.append(val)
                    break
                S.pop()
            else:
                raise RuntimeError(f"unsat at cell ({i},{j})")
        fixed.append(row)
    return fixed


def lexmin_diff(tbl):
    return {k: tbl[k] for k in range(8) if tbl[k] != RAW_A8[k]}


if __name__ == "__main__":
    # 1. closure-free baseline (re-verify the known record)
    base = count_models(closure=False)
    bdiff = lexmin_diff(lex_min(closure=False))
    print(f"closure-free: {base} models | lex-min drift {bdiff}")
    assert base == 1860
    assert bdiff == {7: RECOGNIZER_DRIFT}

    # 2. content alone does NOT force closure — and the certificate is
    #    the quote 6-cycle
    S, T = solver((selfloc,), closure=False)
    S.add(z3.Not(closure_formula(T)))
    assert S.check() == z3.sat
    m = S.model()
    q = [m.evaluate(T[2][x]).as_long() for x in core]
    invol = all(m.evaluate(T[2][m.evaluate(T[2][x]).as_long()]).as_long() == x
                for x in core)
    print(f"SL + NOT closure: sat | countermodel quote core action {q} "
          f"(involution={invol})")
    assert not invol, "countermodel must break the involution"

    # 3. the SL space: 5 models, lex-min unchanged, and the exact
    #    decomposition — involutive iff closure
    S, T = solver((selfloc,), closure=False)
    kinds = []
    while S.check() == z3.sat:
        m = S.model()
        vals = {(i, j): m.evaluate(T[i][j]).as_long()
                for i in range(8) for j in range(8)}
        iv = all(vals[(2, vals[(2, x)])] == x for x in core)
        cl = all(
            any([vals[(t2, x)] for x in core] ==
                [vals[(t, vals[(2, x)])] for x in core] for t2 in Cblk)
            for t in Cblk)
        kinds.append((iv, cl))
        S.add(z3.Or([T[i][j] != vals[(i, j)] for i in core for j in core]))
    print(f"SL space: {len(kinds)} models | "
          f"involutive+closed {kinds.count((True, True))}, "
          f"six-cycle+open {kinds.count((False, False))}")
    assert len(kinds) == 5
    assert kinds.count((True, True)) == 3
    assert kinds.count((False, False)) == 2
    assert lexmin_diff(lex_min((selfloc,), closure=False)) == {}

    # 4. form alone does NOT force closure
    S, T = solver((h2,), closure=False)
    S.add(z3.Not(closure_formula(T)))
    assert S.check() == z3.sat
    h2n = count_models((h2,), closure=False)
    print(f"H2 + NOT closure: sat | H2 space: {h2n} models")
    assert h2n == 1116

    # 5. THE THEOREM: the package forces closure
    S, T = solver((selfloc, h2), closure=False)
    S.add(z3.Not(closure_formula(T)))
    verdict = S.check()
    print(f"SL + H2 + NOT closure: {verdict}")
    assert verdict == z3.unsat, "the self-location package must force closure"
    pkg = count_models((selfloc, h2), closure=False)
    pdiff = lexmin_diff(lex_min((selfloc, h2), closure=False))
    print(f"SL + H2 space: {pkg} models | lex-min drift {pdiff}")
    assert pkg == 3
    assert pdiff == {}

    # 6. strictness: closure does not imply SL; the measurement
    S, T = solver((lambda t: z3.Not(selfloc(t)),))
    assert S.check() == z3.sat
    S, T = solver()
    sl_yes = tot = 0
    while S.check() == z3.sat:
        m = S.model()
        vals = {(i, j): m.evaluate(T[i][j]).as_long()
                for i in range(8) for j in range(8)}
        ok = False
        for cs, cr, cg in itertools.permutations(Cblk):
            if (vals[(2, 2)], vals[(2, 3)], vals[(2, 4)]) != (cs, cr, cg):
                continue
            if all(vals[(cs, x)] == (1 if x in Nblk else 0)
                   and vals[(cr, x)] == (0 if x in Nblk else 1)
                   and vals[(cg, x)] == (1 if x in (4, cg) else 0)
                   for x in core):
                ok = True
                break
        tot += 1
        sl_yes += ok
        S.add(z3.Or([T[i][j] != vals[(i, j)] for i in core for j in core]))
    print(f"measurement: SL holds in {sl_yes}/{tot} adopted models")
    assert (sl_yes, tot) == (3, 168)

    print("CLOSURE RETIRED: judge-closure is a theorem of self-location "
          "(A1/A3/A4) + quote involution (H2) over the frame — both "
          "halves necessary, certificates above")
    print("ALL SELFLOC ASSERTS PASS")
