#!/usr/bin/env python3
"""
σ-equivariant program-equivalence prover for Ψ∗/N=9.

The honest test of whether the canonical-witness substrate's σ does
real work at the proof level.

Setup:
  An "equivalence prover" reduces both terms to normal form via
  psi_eval and reports equality. Step count = the size of the proof
  (number of evaluator steps to reach normal form).

The σ-equivariance question:
  If σ is a symmetry of programs as well as of the algebra, then proofs
  should σ-conjugate. Specifically, for every term t:

    (P1)  nf(σ(t)) = σ(nf(t))           -- evaluation commutes with σ
    (P2)  steps(σ(t)) = steps(t)        -- proof length is σ-invariant

  Together, (P1) ∧ (P2) means: a proof of t₁ ≡ t₂ in k steps gives a
  proof of σ(t₁) ≡ σ(t₂) in k steps for free, by σ-conjugation. That's
  practical proof reuse.

  If either (P1) or (P2) fails, σ doesn't conjugate proofs. σ-equivalence
  is then a structural fact about the algebra, not a useful operation
  on the proof system.

What I expect (predicted before running):
  σ-equivariance should hold for the *atomic* fragment of the evaluator
  (everything that bottoms out in dot(), since the N=9 table is σ-
  equivariant by construction). It should fail for the *structural*
  fragment — Q is lazy, E is eager (non-symmetric eval rules); f
  projects fst, η projects snd (σ swaps them but the meaning of the
  projection is absolute, not σ-permutable); the Q-rule produces a
  Closure when body has Vars, the E-rule reduces eagerly.

  If that prediction holds, σ-equivariance is a property of the algebra
  (the Cayley table) but not of the calculus (the term language + eval
  rules). The substrate's symmetry doesn't ride up to the toolchain.
"""

from __future__ import annotations

import os
import sys
from dataclasses import dataclass

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from psi_star_n9_sigma import (
    Var, Prim, App, Closure, lam, app, pair_t, sigma_image,
    psi_eval, term_str, has_vars,
)
from psi_star_n9 import (
    nat, to_nat, Q, E, F_ENC, G_ENC, ETA, RHO, TAU, TOP, BOT,
    NAMES, SIGMA,
)


# ═══════════════════════════════════════════════════════════════════════
# Equivalence prover
# ═══════════════════════════════════════════════════════════════════════

@dataclass(frozen=True)
class EvalResult:
    ok: bool                    # did evaluation complete?
    value: object               # normal form (or error message)
    steps: int                  # number of psi_eval invocations


def evaluate(t) -> EvalResult:
    """Reduce t to normal form. Return value + step count."""
    steps = [0]
    try:
        nf = psi_eval(t, env=(), _steps=steps)
        return EvalResult(True, nf, steps[0])
    except Exception as e:
        return EvalResult(False, f"{type(e).__name__}: {e}", steps[0])


def equivalent(t1, t2) -> tuple[bool, EvalResult, EvalResult]:
    """Prove t1 ≡ t2 by reducing both to normal form and comparing."""
    r1 = evaluate(t1)
    r2 = evaluate(t2)
    if not (r1.ok and r2.ok):
        return (False, r1, r2)
    return (_terms_equal(r1.value, r2.value), r1, r2)


def _terms_equal(a, b) -> bool:
    """Structural equality, treating Closures by content."""
    if type(a) != type(b):
        return False
    if isinstance(a, int):
        return a == b
    if isinstance(a, App):
        return _terms_equal(a.fun, b.fun) and _terms_equal(a.arg, b.arg)
    if isinstance(a, Closure):
        return _terms_equal(a.body, b.body) and len(a.env) == len(b.env) \
               and all(_terms_equal(x, y) for x, y in zip(a.env, b.env))
    if isinstance(a, Var):
        return a.index == b.index
    if isinstance(a, Prim):
        return a.name == b.name and len(a.args) == len(b.args) \
               and all(_terms_equal(x, y) for x, y in zip(a.args, b.args))
    return a == b


# ═══════════════════════════════════════════════════════════════════════
# σ-equivariance test
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class SigmaCheck:
    label: str
    eq_orig: bool
    eq_sigma: bool
    steps_orig: tuple[int, int]      # (steps for t1, steps for t2)
    steps_sigma: tuple[int, int]     # (steps for σ(t1), steps for σ(t2))
    nf_commutes_t1: bool             # σ(nf(t1)) == nf(σ(t1)) ?
    nf_commutes_t2: bool
    note: str = ""


def sigma_check(label: str, t1, t2, note: str = "") -> SigmaCheck:
    """Run the equivalence prover on (t1, t2) and on (σ(t1), σ(t2));
    report whether σ-equivariance holds for this pair."""
    eq_orig, r1, r2 = equivalent(t1, t2)
    s1, s2 = sigma_image(t1), sigma_image(t2)
    eq_sigma, sr1, sr2 = equivalent(s1, s2)

    # Evaluation-commutes-with-σ check
    nf_commutes_1 = False
    nf_commutes_2 = False
    if r1.ok and sr1.ok:
        try:
            nf_commutes_1 = _terms_equal(sigma_image(r1.value), sr1.value)
        except Exception:
            nf_commutes_1 = False
    if r2.ok and sr2.ok:
        try:
            nf_commutes_2 = _terms_equal(sigma_image(r2.value), sr2.value)
        except Exception:
            nf_commutes_2 = False

    return SigmaCheck(
        label=label,
        eq_orig=eq_orig,
        eq_sigma=eq_sigma,
        steps_orig=(r1.steps, r2.steps),
        steps_sigma=(sr1.steps, sr2.steps),
        nf_commutes_t1=nf_commutes_1,
        nf_commutes_t2=nf_commutes_2,
        note=note,
    )


def render(check: SigmaCheck) -> str:
    """One-line summary."""
    eq_match = "EQ-MATCH" if check.eq_orig == check.eq_sigma else "EQ-DIFFER"
    step_match = ("STEPS-MATCH" if check.steps_orig == check.steps_sigma
                  else "STEPS-DIFFER")
    nf_match = "NF-COMMUTES" if (check.nf_commutes_t1 and check.nf_commutes_t2) \
               else "NF-FAILS"
    σ_safe = (check.eq_orig == check.eq_sigma
              and check.steps_orig == check.steps_sigma
              and check.nf_commutes_t1 and check.nf_commutes_t2)
    badge = "✓ σ-safe" if σ_safe else "✗ σ-breaks"
    return (f"  [{badge}] {check.label}\n"
            f"    orig:  ≡={check.eq_orig!s:<5}  steps={check.steps_orig}\n"
            f"    σ-img: ≡={check.eq_sigma!s:<5}  steps={check.steps_sigma}    "
            f"{eq_match}, {step_match}, {nf_match}"
            + (f"\n    note: {check.note}" if check.note else ""))


# ═══════════════════════════════════════════════════════════════════════
# Test battery
# ═══════════════════════════════════════════════════════════════════════

def battery():
    """Run the σ-equivariance test battery on terms of increasing
    structural complexity."""
    checks: list[SigmaCheck] = []

    # ── Class A: Pure atom·atom dot expressions ──────────────────────
    # Predicted σ-safe: the table is σ-equivariant by construction.
    checks.append(sigma_check(
        "A1. dot(f, z₂) ≡ τ              (pure atom·atom → table)",
        App(F_ENC, TOP), TAU,
        "single dot lookup; both sides atomic"))
    checks.append(sigma_check(
        "A2. dot(τ, dot(f, z₂)) ≡ z₁     (chained atom·atom dots)",
        App(TAU, App(F_ENC, TOP)), BOT))
    checks.append(sigma_check(
        "A3. dot(g, z₁) ≡ App(g, z₁)     (g is a constructor)",
        App(G_ENC, BOT), App(G_ENC, BOT)))

    # ── Class B: Q/E asymmetry ───────────────────────────────────────
    # Q is lazy (eval rule returns App(Q, _) unchanged) but E is eager
    # (eval rule reduces arg first). σ swaps them, but eval rules don't σ-match.
    checks.append(sigma_check(
        "B1. App(Q, z₂) ≡ App(Q, z₂)     (Q-frozen value)",
        App(Q, TOP), App(Q, TOP),
        "Q is lazy → 0 reduction; σ-image is App(E, z₂) which DOT-folds"))
    checks.append(sigma_check(
        "B2. nat(2) ≡ nat(2)             (Q-chain of length 2)",
        nat(2), nat(2),
        "σ-image is E-chain, which forces the chain via dot folds"))
    checks.append(sigma_check(
        "B3. eval(App(E, App(Q, z₂))) ≡ z₂   (E unwraps Q)",
        App(E, App(Q, TOP)), TOP,
        "E·Q is the QE retraction; σ-image is App(Q, App(E, z₂)) → frozen"))

    # ── Class C: f/η pair-projection asymmetry ───────────────────────
    # f extracts fst, η extracts snd. σ swaps them — but fst-vs-snd
    # is an absolute asymmetry of pairs, not σ-permutable.
    p = pair_t(TOP, BOT)
    checks.append(sigma_check(
        "C1. App(f, pair(T, NIL)) ≡ T    (fst of a pair)",
        App(F_ENC, p), TOP,
        "σ-image is App(η, pair(T, NIL)) → η extracts snd → NIL ≠ T"))
    checks.append(sigma_check(
        "C2. App(η, pair(T, NIL)) ≡ NIL  (snd of a pair)",
        App(ETA, p), BOT,
        "σ-image is App(f, pair(T, NIL)) → f extracts fst → T ≠ NIL"))

    # ── Class D: ρ-branch ────────────────────────────────────────────
    # ρ is σ-fixed at the algebra level, but its eval rule dispatches on
    # atom-vs-compound — and what counts as atom-vs-compound is not
    # itself σ-permutable.
    checks.append(sigma_check(
        "D1. ρ on atom → f-path           (ρ structural branch)",
        App(RHO, TOP), App(F_ENC, TOP)))

    # ── Class E: λ-calculus programs ─────────────────────────────────
    Id = lam(Var(0))
    checks.append(sigma_check(
        "E1. (id z₂) ≡ z₂                 (β-reduction of identity)",
        app(Id, TOP), TOP,
        "σ-image breaks: σ(λ.body) = App(E, body) → unbound Var(0)"))

    K = lam(lam(Var(1)))
    checks.append(sigma_check(
        "E2. (K T NIL) ≡ T                (K combinator)",
        app(app(K, TOP), BOT), TOP))

    # ── Class F: Self-equivalences (sanity check) ────────────────────
    # t ≡ t is always true; the question is whether step counts match.
    checks.append(sigma_check(
        "F1. nat(3) ≡ nat(3)              (syntactic identity)",
        nat(3), nat(3)))
    checks.append(sigma_check(
        "F2. (id z₁) ≡ (id z₁)            (identity applied to NIL)",
        app(Id, BOT), app(Id, BOT)))

    return checks


# ═══════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════

def main() -> int:
    print("σ-equivariant program-equivalence prover for Ψ∗/N=9")
    print("=" * 78)
    print()
    print("For each test pair (t₁, t₂) we check three properties:")
    print("  • equivalence answer matches between original and σ-image")
    print("  • step counts match")
    print("  • normal forms commute with σ:  σ(nf(t)) == nf(σ(t))")
    print("All three must hold for σ to give automatic proof reuse on this pair.")
    print()

    by_class: dict[str, list[SigmaCheck]] = {}
    for check in battery():
        cls = check.label[0]
        by_class.setdefault(cls, []).append(check)

    class_names = {
        "A": "Class A — pure atom·atom (table-only)",
        "B": "Class B — Q/E asymmetry (lazy vs eager)",
        "C": "Class C — f/η pair projection",
        "D": "Class D — ρ structural branch",
        "E": "Class E — λ-calculus programs",
        "F": "Class F — self-equivalences (sanity)",
    }

    summary_safe: dict[str, int] = {}
    summary_total: dict[str, int] = {}

    for cls, checks in by_class.items():
        print(f"  {class_names[cls]}")
        print("  " + "-" * 70)
        for c in checks:
            print(render(c))
            σ_safe = (c.eq_orig == c.eq_sigma
                      and c.steps_orig == c.steps_sigma
                      and c.nf_commutes_t1 and c.nf_commutes_t2)
            summary_safe[cls] = summary_safe.get(cls, 0) + (1 if σ_safe else 0)
            summary_total[cls] = summary_total.get(cls, 0) + 1
        print()

    print("=" * 78)
    print("TALLY")
    print("=" * 78)
    for cls in sorted(by_class):
        s, t = summary_safe.get(cls, 0), summary_total.get(cls, 0)
        verdict = ("σ-safe across the board" if s == t
                   else "σ-breaks" if s == 0
                   else f"mixed ({s}/{t} σ-safe)")
        print(f"  {class_names[cls]:55s}  {verdict}")

    print()
    print("=" * 78)
    print("INTERPRETATION")
    print("=" * 78)
    print("""
  Class A (pure atom·atom, table-only) is σ-safe by construction:
  the N=9 Cayley table satisfies σ(TABLE[a][b]) = TABLE[σ(a)][σ(b)],
  and the evaluator's atom·atom rule is just dot(). So any equivalence
  proven by table folding alone σ-conjugates exactly.

  Classes B, C, D break σ-equivariance for a structural reason: the
  evaluator's reduction rules for Q, E, f, η, ρ are NOT σ-equivariant
  even though σ permutes the atoms involved.

    • Q is lazy (eval(App(Q, _)) = App(Q, _), no reduction).
    • E is eager (eval(App(E, t)) reduces t and may collapse).
      σ swaps Q with E, but lazy ≠ eager. σ-conjugating a Q-step
      gives an E-step — different evaluator behavior, different result.

    • f extracts fst from a g-pair; η extracts snd. σ swaps f with η.
      But "fst" and "snd" are absolute positions in a pair, not σ-
      permutable concepts. σ-conjugating "extract fst" gives "extract
      snd" — a different operation on the same data structure.

    • ρ is σ-fixed. Its eval rule dispatches on atom-vs-compound;
      that classification is not preserved by σ on terms with structure.

  Class E (λ-calculus) breaks completely — σ-image of a closed
  λ-program has unbound Vars (Vars have no σ-dual; the previous
  experiment).

  Class F shows the deeper issue: even t ≡ t (syntactic identity!) has
  σ-step-count ≠ orig-step-count when the term goes through structural
  rules. The "proof" of t ≡ t is 0 reductions on the original side
  but multiple reductions on the σ-image side, because σ-image isn't
  syntactically equal to itself in fewer steps — it has to reduce
  through E-chains where the original was a Q-frozen value.

  CONCLUSION: σ-equivariance is a property of the *algebra* (the table
  is σ-equivariant by construction). It is NOT a property of the
  *evaluator* (the eval rules add structural reductions that break σ).
  Therefore σ-equivalence does NOT give automatic proof reuse for
  programs with structure. The substrate's symmetry is real but stays
  inside the algebra; it does not propagate up to the toolchain.

  WHERE σ-EQUIVALENCE STILL DOES SOMETHING USEFUL:

    • As a structural invariant of the algebra (used by the SAT search
      that found the substrate in the first place).
    • For atom-only sub-expressions during partial evaluation —
      table-fold opportunities are σ-symmetric.
    • As a diagnostic: a calculus whose reduction rules WERE σ-
      equivariant would automatically give proof reuse. Our evaluator
      isn't that calculus, and modifying it to be one would mean
      giving up the lazy/eager distinction (which is load-bearing).

  HONEST VERDICT for the toolchain question: σ-equivalence is decorative
  at the proof level for any program that uses Q/E/f/η/ρ structurally
  — i.e., essentially any program. For a substrate intended as a Lisp
  ground, that's everything we care about. The N=9 algebra remains
  the smallest canonical-witness Lisp substrate, but σ does not earn
  its keep at the proof level — only at the algebra-search level.""")

    return 0


if __name__ == "__main__":
    sys.exit(main())
