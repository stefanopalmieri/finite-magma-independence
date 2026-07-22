import Magma.FactorizationEnv

/-!
# Factorization with Closures: β, and the Fuel It Forces

The second extension rung of `MACHINE.md` §9: the factorization theorem
carried through **closures**. Programs gain the de Bruijn binder `lam`,
values gain closures (code + captured environment), and application of a
closure is β — at which point evaluation is genuinely partial:
K-infinity put universality in an external driver loop, and this file
is where that loop's non-termination becomes real. `run` is therefore
**fuel-indexed**: `none` means the loop was cut short, in-band errors
still cut to the halt channel, and the headline law holds **uniformly
in fuel**:

    evalD fuel ρ (quoteD p) = run fuel ρ p        (for every fuel, ρ, p)

So `eval (quote p)` and `p` converge together, diverge together, and
agree on every value — R7RS §6.12's law at the precision partiality
demands. The induction's base case is still `eatom_qatom`, the
artifact's certified retraction.

What is certified around the headline:

* **β through quotation** (`run_beta`), and the table still the only
  semantic step on instructions (`run_app_atom`).
* **Fuel is operational, not semantic** (`run_mono`, `run_mono_le`):
  a produced value is stable under more fuel; `none` only ever means
  "not yet".
* **Divergence is real** (`Omega_diverges`, `eval_quote_Omega`):
  Ω = (λx. x x)(λx. x x) runs to `none` at every fuel, and so does the
  eval of its quotation — the driver loop provably cannot be internal,
  K-infinity's operational shadow.
* **Conservativity** (`run_embed`, `eval_quote_embed`): a λ-free
  program of depth d, under any fuel ≥ d, computes exactly the
  environment rung's total value. Fuel changes nothing it does not
  mention.
* **The duality reached metacircularly** (`eval_quote_duality_demo`):
  (λx. x·x) applied to the quote instruction, run through eval∘quote,
  computes `data?` — the artifact's duality pairing arrived at by β.

Representation: the third compound syntax class gets the remaining
natural tag — quote (element 2) marks λ-bodies, eval (3) applications,
shift (4) variables. The mnemonic is exact: abstraction *suspends* its
body precisely as quotation does (`run_lam` builds a closure without
evaluating under the binder). Tag values remain engineering
(`MACHINE.md` §8); the necessity of tags is not. Closures are runtime
values only — `decodeD` rejects them, so quotations never mention
environments and representation adequacy stays static.

Scope note: this is the C and E of CESK with β only — control
*operators* (μ / `call/cc`) and the store are the remaining rungs.
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationClos

open Factorization (qatom eatom eatom_qatom)

/-- Programs: instructions, de Bruijn variables, abstraction,
    application. -/
inductive Prog where
  | atom : Fin 8 → Prog
  | var  : Nat → Prog
  | lam  : Prog → Prog
  | app  : Prog → Prog → Prog
deriving DecidableEq

/-- Tape values: machine elements, inert heap cells, and closures —
    code plus its captured environment. Closures are runtime values
    only; they are never quotations. -/
inductive Val where
  | elem : Fin 8 → Val
  | cell : Val → Val → Val
  | clos : Prog → List Val → Val

/-- Environments: the machine's E component. -/
abbrev Env := List Val

/-- The fuel-indexed evaluator. The only semantic step on instructions
    is still one table lookup; `lam` suspends its body as a closure;
    applying a closure is β; `none` is exhausted fuel, while in-band
    errors (unbound variable, applying heap data) still cut to the halt
    channel. -/
def run : Nat → Env → Prog → Option Val
  | 0, _, _ => none
  | _ + 1, _, .atom a => some (.elem a)
  | _ + 1, ρ, .var n => some (ρ.getD n (.elem 0))
  | _ + 1, ρ, .lam b => some (.clos b ρ)
  | fuel + 1, ρ, .app f x =>
    match run fuel ρ f, run fuel ρ x with
    | some (.elem a), some (.elem b) => some (.elem (dotA8 a b))
    | some (.clos b ρ'), some v => run fuel (v :: ρ') b
    | some _, some _ => some (.elem 0)
    | _, _ => none

/-- De Bruijn indices on the tape: unary shift-cell numerals, as in the
    environment rung. -/
def natToVal : Nat → Val
  | 0 => .elem 0
  | n + 1 => .cell (.elem 4) (natToVal n)

def valToNat : Val → Option Nat
  | .elem b => if b = (0 : Fin 8) then some 0 else none
  | .cell (.elem h) t => if h = (4 : Fin 8) then (valToNat t).map (· + 1) else none
  | _ => none

theorem valToNat_natToVal : ∀ n : Nat, valToNat (natToVal n) = some n := by
  intro n
  induction n with
  | zero => simp [natToVal, valToNat]
  | succ n ih => simp [natToVal, valToNat, ih]

/-- Driver-level quote. Atoms go through the table's duality; the three
    compound syntax classes carry heap tags — quote (2) for λ-bodies,
    eval (3) for applications, shift (4) for variables. -/
def quoteD : Prog → Val
  | .atom a => .elem (qatom a)
  | .var n => .cell (.elem 4) (natToVal n)
  | .lam b => .cell (.elem 2) (quoteD b)
  | .app f x => .cell (.elem 3) (.cell (quoteD f) (quoteD x))

mutual
  /-- Driver-level decode: the reading half of user-level eval.
      Closures are rejected — representations never mention
      environments. -/
  def decodeD : Val → Option Prog
    | .elem b => some (.atom (eatom b))
    | .cell (.elem h) rest =>
      if h = (2 : Fin 8) then (decodeD rest).map .lam
      else if h = (3 : Fin 8) then decodeApp rest
      else if h = (4 : Fin 8) then (valToNat rest).map .var
      else none
    | _ => none

  /-- Reading the payload of an application quotation. -/
  def decodeApp : Val → Option Prog
    | .cell u v =>
      match decodeD u, decodeD v with
      | some f, some x => some (.app f x)
      | _, _ => none
    | _ => none
end

/-- User-level eval: R7RS's two-argument signature, now fuel-indexed.
    A non-code value is an in-band error (halt channel); `none` is
    exhausted fuel only. -/
def evalD (fuel : Nat) (ρ : Env) (v : Val) : Option Val :=
  match decodeD v with
  | some p => run fuel ρ p
  | none => some (.elem 0)

/-- The only semantic step on instructions is still the table. -/
theorem run_app_atom (fuel : Nat) (ρ : Env) (a b : Fin 8) :
    run (fuel + 1 + 1) ρ (.app (.atom a) (.atom b)) =
      some (.elem (dotA8 a b)) := rfl

/-- Abstraction suspends its body — a closure is built, nothing under
    the binder is evaluated. This is the λ/quote analogy made exact. -/
theorem run_lam (fuel : Nat) (ρ : Env) (b : Prog) :
    run (fuel + 1) ρ (.lam b) = some (.clos b ρ) := rfl

/-- **β**: applying an abstraction binds the argument's value and runs
    the body in the extended captured environment. -/
theorem run_beta (fuel : Nat) (ρ : Env) (b x : Prog) (v : Val)
    (hx : run (fuel + 1) ρ x = some v) :
    run (fuel + 1 + 1) ρ (.app (.lam b) x) = run (fuel + 1) (v :: ρ) b := by
  simp [run, hx]

set_option linter.unusedSimpArgs false in
/-- **Representation adequacy, still static**: decoding a quotation
    recovers the program exactly — no environment, no fuel. Base case:
    the certified table law `eatom_qatom`. -/
theorem decode_quote (p : Prog) : decodeD (quoteD p) = some p := by
  induction p with
  | atom a => simp [quoteD, decodeD, eatom_qatom]
  | var n => simp [quoteD, decodeD, valToNat_natToVal]
  | lam b ih => simp [quoteD, decodeD, ih]
  | app f x ihf ihx => simp [quoteD, decodeD, decodeApp, ihf, ihx]

/-- **The factorization theorem with closures**: uniformly in fuel,
    `eval fuel ρ (quote p) = run fuel ρ p` — eval of a quotation and
    the program itself converge together, diverge together, and agree
    on every value. -/
theorem eval_quote (fuel : Nat) (ρ : Env) (p : Prog) :
    evalD fuel ρ (quoteD p) = run fuel ρ p := by
  simp [evalD, decode_quote]

/-- **Fuel is operational, not semantic**: a produced value is stable
    under one more unit of fuel. -/
theorem run_mono : ∀ {fuel : Nat} {ρ : Env} {p : Prog} {v : Val},
    run fuel ρ p = some v → run (fuel + 1) ρ p = some v := by
  intro fuel
  induction fuel with
  | zero => intro ρ p v h; simp [run] at h
  | succ k ih =>
    intro ρ p v h
    cases p with
    | atom a => exact h
    | var n => exact h
    | lam b => exact h
    | app f x =>
      simp only [run] at h ⊢
      cases hf : run k ρ f with
      | none => rw [hf] at h; simp at h
      | some w =>
        rw [hf] at h
        cases hx : run k ρ x with
        | none => rw [hx] at h; cases w <;> simp at h
        | some u =>
          rw [hx] at h
          rw [ih hf, ih hx]
          cases w with
          | elem a => cases u <;> exact h
          | cell w₁ w₂ => cases u <;> exact h
          | clos b ρ' => exact ih h

/-- `none` only ever means "not yet": values persist to every larger
    fuel. -/
theorem run_mono_le {fuel fuel' : Nat} (hle : fuel ≤ fuel') {ρ : Env}
    {p : Prog} {v : Val} (h : run fuel ρ p = some v) :
    run fuel' ρ p = some v := by
  induction hle with
  | refl => exact h
  | step _ ih => exact run_mono ih

/-- The environment rung embeds: its programs are the λ-free ones. -/
def embed : FactorizationEnv.Prog → Prog
  | .atom a => .atom a
  | .var n => .var n
  | .app f x => .app (embed f) (embed x)

/-- Its values embed too (no closures ever arise from them). -/
def embedVal : Factorization.Val → Val
  | .elem a => .elem a
  | .cell u v => .cell (embedVal u) (embedVal v)

/-- Sufficient fuel for a λ-free program: its depth. -/
def depth : FactorizationEnv.Prog → Nat
  | .atom _ => 1
  | .var _ => 1
  | .app f x => max (depth f) (depth x) + 1

/-- **Conservativity**: a λ-free program of depth d, under any fuel
    ≥ d and any embedded environment, computes exactly the environment
    rung's total value. β and fuel change nothing they do not
    mention. -/
theorem run_embed (p : FactorizationEnv.Prog) :
    ∀ fuel : Nat, depth p ≤ fuel → ∀ ρ : FactorizationEnv.Env,
      run fuel (ρ.map embedVal) (embed p) =
        some (embedVal (FactorizationEnv.run ρ p)) := by
  induction p with
  | atom a =>
    intro fuel hf ρ
    simp only [depth] at hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | var n =>
    intro fuel hf ρ
    simp only [depth] at hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    simp only [run, embed, FactorizationEnv.run, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases ρ[n]? <;> simp [embedVal]
  | app f x ihf ihx =>
    intro fuel hf ρ
    simp only [depth] at hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have hkf : depth f ≤ k := by omega
    have hkx : depth x ≤ k := by omega
    simp only [embed, run, FactorizationEnv.run, ihf k hkf ρ, ihx k hkx ρ]
    cases FactorizationEnv.run ρ f <;> cases FactorizationEnv.run ρ x <;>
      simp [embedVal]

/-- Corollary: the closure-rung eval, on the quotation of a λ-free
    program with sufficient fuel, returns the environment rung's value
    — the whole ladder is conservative, rung over rung. -/
theorem eval_quote_embed (p : FactorizationEnv.Prog) (fuel : Nat)
    (hf : depth p ≤ fuel) (ρ : FactorizationEnv.Env) :
    evalD fuel (ρ.map embedVal) (quoteD (embed p)) =
      some (embedVal (FactorizationEnv.run ρ p)) := by
  rw [eval_quote]; exact run_embed p fuel hf ρ

/-- ((λx. x) a) through eval∘quote: β through quotation. -/
theorem eval_quote_identity (a : Fin 8) :
    evalD 3 [] (quoteD (.app (.lam (.var 0)) (.atom a))) =
      some (.elem a) := by
  rw [eval_quote]; rfl

/-- (λx. x·x) applied to the quote instruction, through eval∘quote:
    self-application of quote computes `data?` — the artifact's duality
    pairing (`artifactA8_duality_pairing`), reached metacircularly
    by β. -/
theorem eval_quote_duality_demo :
    evalD 4 [] (quoteD (.app (.lam (.app (.var 0) (.var 0))) (.atom 2))) =
      some (.elem 5) := by
  rw [eval_quote]; rfl

/-- δ = λx. x x. -/
def deltaP : Prog := .lam (.app (.var 0) (.var 0))

/-- Ω = δ δ. -/
def OmegaP : Prog := .app deltaP deltaP

theorem run_delta_body_none :
    ∀ fuel (ρ₁ ρ₂ : Env),
      run fuel (.clos (.app (.var 0) (.var 0)) ρ₁ :: ρ₂)
        (.app (.var 0) (.var 0)) = none := by
  intro fuel
  induction fuel with
  | zero => intro ρ₁ ρ₂; rfl
  | succ k ih =>
    intro ρ₁ ρ₂
    cases k with
    | zero => rfl
    | succ m => exact ih ρ₁ ρ₁

/-- **Divergence is real**: Ω runs to `none` at every fuel — the driver
    loop provably cannot terminate on it. K-infinity's operational
    shadow: iteration lives outside the table, and outside is where it
    can fail to halt. -/
theorem Omega_diverges (fuel : Nat) (ρ : Env) : run fuel ρ OmegaP = none := by
  cases fuel with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ m => exact run_delta_body_none (m + 1) ρ ρ

/-- Eval of the quotation of Ω diverges at every fuel: user-level eval
    inherits the driver's partiality exactly. -/
theorem eval_quote_Omega (fuel : Nat) (ρ : Env) :
    evalD fuel ρ (quoteD OmegaP) = none := by
  rw [eval_quote]; exact Omega_diverges fuel ρ

end FactorizationClos
end Dichotomic
