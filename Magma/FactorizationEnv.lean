import Magma.Factorization

/-!
# Factorization with Environments: the E Component

The first extension rung promised in `MACHINE.md` §9: the factorization
theorem of `Magma/Factorization.lean` carried through **environments**
(the E of CESK, §4). Programs gain de Bruijn variable references, the
driver's `run` and the user-level `eval` gain an environment argument —
R7RS §6.12's *actual* two-argument signature, `(eval expr env)` — and
the same induction proves, for **every** environment ρ and program p,

    evalD ρ (quoteD p) = run ρ p

The base case is unchanged: `eatom_qatom`, the artifact's certified
retraction law. The environment threads through untouched because
**representation adequacy is static** — `decode_quote` mentions no ρ;
quotation and decoding never consult the environment, only the semantic
step does.

Two design points, each forced or certified rather than chosen:

* **A second compound syntax class forces heap tags.** With one compound
  constructor, cells could be untagged (the minimal file); with two
  (application, variable), representations must be discriminated — and
  per the recognizer wall, recognition of representation classes lives
  in heap tags on the tape, never in instruction identity. The tag
  *values* are engineering (`MACHINE.md` §8); the *necessity* of tags is
  not. Applications are tagged by eval (element 3), variables by shift
  (element 4).
* **The shift instruction is the variable tag, made literal.** Quoted
  de Bruijn indices are unary shift-cell numerals, so one more shift
  cell on the representation *is* one more de Bruijn lift
  (`quote_var_succ`), and evaluation peels it by skipping one binding
  (`shift_cell_skips_binding`) — the table's certified renaming operator
  (`artifactA8_shift_*`) marking exactly the things renaming acts on.

Conservativity is proved, not presumed: variable-free programs embed,
and under every environment the extended driver computes exactly the
minimal driver's value (`run_embed`, `eval_quote_embed`).

Scope note: environments here bind values to indices; there is still no
binding *form* — closures (λ) arrive with the control step, where β
demands fuel or a step relation. That is the next rung (`MACHINE.md`
§§4–6), and this file's statically-adequate-representation shape is
what it must preserve.
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationEnv

open Factorization (Val qatom eatom eatom_qatom)

/-- Programs with variables: artifact instructions, de Bruijn variable
    references, and application. -/
inductive Prog where
  | atom : Fin 8 → Prog
  | var  : Nat → Prog
  | app  : Prog → Prog → Prog
deriving DecidableEq

/-- Environments: the machine's E component — a de Bruijn value stack. -/
abbrev Env := List Val

/-- The evaluator with environments. The only semantic step is still one
    table lookup; a variable is an environment lookup; an unbound
    variable is an error and cuts to the halt channel (R7RS: "it is an
    error"). -/
def run (ρ : Env) : Prog → Val
  | .atom a => .elem a
  | .var n => ρ.getD n (.elem 0)
  | .app f x =>
    match run ρ f, run ρ x with
    | .elem a, .elem b => .elem (dotA8 a b)
    | _, _ => .elem 0

/-- De Bruijn indices on the tape: unary shift-cell numerals. -/
def natToVal : Nat → Val
  | 0 => .elem 0
  | n + 1 => .cell (.elem 4) (natToVal n)

/-- Reading a shift-cell numeral back. -/
def valToNat : Val → Option Nat
  | .elem b => if b = (0 : Fin 8) then some 0 else none
  | .cell (.elem h) t => if h = (4 : Fin 8) then (valToNat t).map (· + 1) else none
  | _ => none

theorem valToNat_natToVal : ∀ n : Nat, valToNat (natToVal n) = some n := by
  intro n
  induction n with
  | zero => simp [natToVal, valToNat]
  | succ n ih => simp [natToVal, valToNat, ih]

/-- Driver-level quote. Atoms go through the table's duality exactly as
    in the minimal file; the two compound syntax classes carry heap
    tags — eval (3) for applications, shift (4) for variables. -/
def quoteD : Prog → Val
  | .atom a => .elem (qatom a)
  | .var n => .cell (.elem 4) (natToVal n)
  | .app f x => .cell (.elem 3) (.cell (quoteD f) (quoteD x))

/-- Driver-level decode: the reading half of user-level eval. -/
def decodeD : Val → Option Prog
  | .elem b => some (.atom (eatom b))
  | .cell (.elem h) (.elem b) =>
    if h = (4 : Fin 8) then (valToNat (.elem b)).map .var else none
  | .cell (.elem h) (.cell u v) =>
    if h = (3 : Fin 8) then
      match decodeD u, decodeD v with
      | some f, some x => some (.app f x)
      | _, _ => none
    else if h = (4 : Fin 8) then
      (valToNat (.cell u v)).map .var
    else none
  | .cell (.cell _ _) _ => none

/-- User-level eval with its environment argument — R7RS §6.12's
    two-argument signature. Decoding is static; only `run` consults ρ. -/
def evalD (ρ : Env) (v : Val) : Val :=
  match decodeD v with
  | some p => run ρ p
  | none => .elem 0

/-- The driver's only semantic step is still the table. -/
theorem run_app_atom (ρ : Env) (a b : Fin 8) :
    run ρ (.app (.atom a) (.atom b)) = .elem (dotA8 a b) := rfl

/-- Variables are environment lookups. -/
theorem run_var (ρ : Env) (n : Nat) :
    run ρ (.var n) = ρ.getD n (.elem 0) := rfl

/-- One more shift cell on the representation is one more de Bruijn
    lift: the successor structure of quoted variables **is** the shift
    tag. -/
theorem quote_var_succ (n : Nat) :
    quoteD (.var (n + 1)) = .cell (.elem 4) (quoteD (.var n)) := rfl

set_option linter.unusedSimpArgs false in
/-- **Representation adequacy, environment-free**: decoding a quotation
    recovers the program exactly, before any environment is supplied.
    Base case: the certified table law `eatom_qatom`. -/
theorem decode_quote (p : Prog) : decodeD (quoteD p) = some p := by
  induction p with
  | atom a => simp [quoteD, decodeD, eatom_qatom]
  | var n => cases n <;> simp [quoteD, natToVal, decodeD, valToNat, valToNat_natToVal]
  | app f x ihf ihx => simp [quoteD, decodeD, ihf, ihx]

/-- **The factorization theorem with environments**: for every
    environment ρ and every program p, `eval ρ (quote p) = run ρ p`.
    R7RS's two-argument `eval` law, derived; the environment threads
    through untouched because representation adequacy is static. -/
theorem eval_quote (ρ : Env) (p : Prog) : evalD ρ (quoteD p) = run ρ p := by
  simp [evalD, decode_quote]

/-- Eval of a quoted variable is exactly environment lookup: the
    freshest binding is retrieved through the representation. -/
theorem eval_quote_var_zero (ρ : Env) (v : Val) :
    evalD (v :: ρ) (quoteD (.var 0)) = v := by
  simp [eval_quote, run]

/-- The de Bruijn adjunction at the driver level: one more shift cell
    on the representation (`quote_var_succ`) is one more binding skipped
    in the environment. -/
theorem shift_cell_skips_binding (ρ : Env) (v : Val) (n : Nat) :
    evalD (v :: ρ) (quoteD (.var (n + 1))) = evalD ρ (quoteD (.var n)) := by
  simp [eval_quote, run]

/-- The minimal calculus embeds: atoms and applications, no variables. -/
def embed : Factorization.Prog → Prog
  | .atom a => .atom a
  | .app f x => .app (embed f) (embed x)

/-- **Conservativity**: on variable-free programs, every environment
    computes exactly the minimal driver's value — the extension changes
    nothing it does not mention. -/
theorem run_embed (ρ : Env) (p : Factorization.Prog) :
    run ρ (embed p) = Factorization.run p := by
  induction p with
  | atom a => rfl
  | app f x ihf ihx =>
    simp only [embed, run, Factorization.run, ihf, ihx]
    cases Factorization.run f <;> cases Factorization.run x <;> rfl

/-- Corollary: the environment-extended eval, on the quotation of a
    variable-free program, returns the minimal theorem's value under
    every environment. -/
theorem eval_quote_embed (ρ : Env) (p : Factorization.Prog) :
    evalD ρ (quoteD (embed p)) = Factorization.run p := by
  rw [eval_quote, run_embed]

end FactorizationEnv
end Dichotomic
