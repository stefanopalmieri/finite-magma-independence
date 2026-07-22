import Magma.FactorizationClos

/-!
# Factorization with Control: the Machine Becomes System L

The third extension rung of `MACHINE.md` §9: **control operators**. The
big-step driver of the closure rung is replaced by a machine in the
CEK/System L family, and here §3's correspondence table stops being an
analogy and becomes the definitions:

* machine states are **commands** ⟨focus ‖ continuation⟩ — `State.eval`
  focuses a producer (a program), `State.ret` cuts a value against a
  consumer (a continuation);
* halting **is** cutting against the toplevel co-constant
  (`step_halt`);
* `callcc` **is** binder-form μ: it binds the current consumer at de
  Bruijn index 0 and runs its body against that same consumer
  (`step_mu`);
* invoking a captured continuation is a cut against the captured
  consumer, *discarding* the current one (`step_throw`);
* proper tail calls are machine shape, not optimization: β re-enters
  the body under the **same** continuation (`step_beta`) — the stack
  never grows in tail position.

The factorization theorem survives the restructure untouched:

    evalD fuel ρ (quoteD p) = runM fuel ρ p       (uniformly in fuel)

with base case still `eatom_qatom`. Fuel now counts machine steps.

Two design facts, both theorem-shaped rather than chosen:

* **Continuations are first-class but not data.** `decodeD` rejects
  closures and reified continuations: quotations never mention
  environments or consumers, so representation adequacy stays static —
  R7RS's unwritable procedures (a continuation cannot be `write`n or
  re-`read`) as a structural property of the driver.
* **Conservativity is a simulation theorem** (`machine_sim`): whatever
  the closure rung's big-step driver computes, the machine computes —
  proved continuation-polymorphically, with machine fuel existential —
  and by machine determinism (`loop_det`) it computes nothing else
  (`machine_embed_unique`). Ω still diverges, now by entering a
  provable five-state machine cycle (`machine_delta_cycle`).

Tags: the fourth compound syntax class takes judge? (element 6) —
continuations are consumers, and the μ-form's tag is the consumer
block's own judge. Values: quote (2) = λ, eval (3) = app, shift (4) =
var, judge? (6) = callcc. Tag values are engineering (`MACHINE.md`
§8); the necessity of tags is not.

Remaining rung: the store (S of CESK), then outward to R7RS.
-/

set_option autoImplicit false

namespace Dichotomic
namespace FactorizationCtrl

open Factorization (qatom eatom eatom_qatom)

/-- Programs: instructions, de Bruijn variables, abstraction,
    application, and μ (`callcc` — binds the current continuation at
    index 0). -/
inductive Prog where
  | atom   : Fin 8 → Prog
  | var    : Nat → Prog
  | lam    : Prog → Prog
  | app    : Prog → Prog → Prog
  | callcc : Prog → Prog
deriving DecidableEq

mutual
  /-- Tape values: elements, heap cells, closures, and reified
      continuations (the μ-variable's value). -/
  inductive Val where
    | elem : Fin 8 → Val
    | cell : Val → Val → Val
    | clos : Prog → List Val → Val
    | cont : Kont → Val

  /-- Continuations — the machine's consumers: the toplevel
      co-constant, an argument-pending frame, and an apply frame. -/
  inductive Kont where
    | halt : Kont
    | appL : Prog → List Val → Kont → Kont
    | appR : Val → Kont → Kont
end

/-- Environments: the machine's E component. -/
abbrev Env := List Val

/-- Machine states are commands ⟨focus ‖ continuation⟩: either a
    program focused for evaluation, or a value being cut against a
    consumer. -/
inductive State where
  | eval : Prog → Env → Kont → State
  | ret  : Val → Kont → State

/-- One machine step. The only semantic step on instructions is still
    one table lookup; everything else is focus movement. -/
def step : State → State ⊕ Val
  | .eval (.atom a) _ k => .inl (.ret (.elem a) k)
  | .eval (.var n) ρ k => .inl (.ret (ρ.getD n (.elem 0)) k)
  | .eval (.lam b) ρ k => .inl (.ret (.clos b ρ) k)
  | .eval (.app f x) ρ k => .inl (.eval f ρ (.appL x ρ k))
  | .eval (.callcc b) ρ k => .inl (.eval b (.cont k :: ρ) k)
  | .ret v .halt => .inr v
  | .ret v (.appL x ρ k) => .inl (.eval x ρ (.appR v k))
  | .ret v (.appR (.clos b ρ') k) => .inl (.eval b (v :: ρ') k)
  | .ret v (.appR (.cont k') _) => .inl (.ret v k')
  | .ret (.elem b) (.appR (.elem a) k) => .inl (.ret (.elem (dotA8 a b)) k)
  | .ret (.cell _ _) (.appR (.elem _) k) => .inl (.ret (.elem 0) k)
  | .ret (.clos _ _) (.appR (.elem _) k) => .inl (.ret (.elem 0) k)
  | .ret (.cont _) (.appR (.elem _) k) => .inl (.ret (.elem 0) k)
  | .ret _ (.appR (.cell _ _) k) => .inl (.ret (.elem 0) k)

/-- Halting is a cut against the toplevel co-constant. -/
theorem step_halt (v : Val) : step (.ret v .halt) = .inr v := rfl

/-- **μ**: `callcc` binds the current consumer at index 0 and runs its
    body against that same consumer. -/
theorem step_mu (b : Prog) (ρ : Env) (k : Kont) :
    step (.eval (.callcc b) ρ k) = .inl (.eval b (.cont k :: ρ) k) := rfl

/-- **Throw**: invoking a captured continuation cuts the value against
    the captured consumer — the current one is discarded. -/
theorem step_throw (v : Val) (k' k : Kont) :
    step (.ret v (.appR (.cont k') k)) = .inl (.ret v k') := rfl

/-- **Proper tail calls are machine shape**: β re-enters the body under
    the *same* continuation — the stack does not grow. -/
theorem step_beta (v : Val) (b : Prog) (ρ' : List Val) (k : Kont) :
    step (.ret v (.appR (.clos b ρ') k)) = .inl (.eval b (v :: ρ') k) := rfl

/-- The driver loop: iterate `step` under fuel. External by K-infinity;
    partial because it must be. -/
def loop : Nat → State → Option Val
  | 0, _ => none
  | fuel + 1, s =>
    match step s with
    | .inl s' => loop fuel s'
    | .inr v => some v

/-- Run a program: focus it against the toplevel consumer. -/
def runM (fuel : Nat) (ρ : Env) (p : Prog) : Option Val :=
  loop fuel (.eval p ρ .halt)

theorem loop_mono {n : Nat} {s : State} {w : Val} (h : loop n s = some w) :
    loop (n + 1) s = some w := by
  induction n generalizing s with
  | zero => simp [loop] at h
  | succ m ih =>
    simp only [loop] at h ⊢
    cases hs : step s with
    | inl s' => rw [hs] at h; exact ih h
    | inr v => rw [hs] at h; exact h

theorem loop_mono_le {n n' : Nat} (hle : n ≤ n') {s : State} {w : Val}
    (h : loop n s = some w) : loop n' s = some w := by
  induction hle with
  | refl => exact h
  | step _ ih => exact loop_mono ih

/-- The machine is deterministic: any two convergent runs from the same
    state agree. -/
theorem loop_det {n n' : Nat} {s : State} {w w' : Val}
    (h : loop n s = some w) (h' : loop n' s = some w') : w = w' := by
  rcases Nat.le_total n n' with hle | hle
  · rw [loop_mono_le hle h] at h'
    exact Option.some.inj h'
  · rw [loop_mono_le hle h'] at h
    exact (Option.some.inj h).symm

/-- De Bruijn indices on the tape: unary shift-cell numerals. -/
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

/-- Driver-level quote. Atoms go through the table's duality; compound
    classes carry heap tags — quote (2) λ, eval (3) app, shift (4)
    var, judge? (6) μ. -/
def quoteD : Prog → Val
  | .atom a => .elem (qatom a)
  | .var n => .cell (.elem 4) (natToVal n)
  | .lam b => .cell (.elem 2) (quoteD b)
  | .app f x => .cell (.elem 3) (.cell (quoteD f) (quoteD x))
  | .callcc b => .cell (.elem 6) (quoteD b)

mutual
  /-- Driver-level decode. Closures and reified continuations are
      rejected: procedures and consumers are first-class values but
      never data. -/
  def decodeD : Val → Option Prog
    | .elem b => some (.atom (eatom b))
    | .cell (.elem h) rest =>
      if h = (2 : Fin 8) then (decodeD rest).map .lam
      else if h = (3 : Fin 8) then decodeApp rest
      else if h = (4 : Fin 8) then (valToNat rest).map .var
      else if h = (6 : Fin 8) then (decodeD rest).map .callcc
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

/-- User-level eval: R7RS's two-argument signature over the machine. -/
def evalD (fuel : Nat) (ρ : Env) (v : Val) : Option Val :=
  match decodeD v with
  | some p => runM fuel ρ p
  | none => some (.elem 0)

set_option linter.unusedSimpArgs false in
/-- **Representation adequacy, still static**: no environment, no fuel,
    no continuation. Base case: the certified table law
    `eatom_qatom`. -/
theorem decode_quote (p : Prog) : decodeD (quoteD p) = some p := by
  induction p with
  | atom a => simp [quoteD, decodeD, eatom_qatom]
  | var n => simp [quoteD, decodeD, valToNat_natToVal]
  | lam b ih => simp [quoteD, decodeD, ih]
  | app f x ihf ihx => simp [quoteD, decodeD, decodeApp, ihf, ihx]
  | callcc b ih => simp [quoteD, decodeD, ih]

/-- **The factorization theorem over the machine**: uniformly in fuel,
    `eval fuel ρ (quote p) = runM fuel ρ p` — the metacircular law
    survives the restructure to a System L machine unchanged. -/
theorem eval_quote (fuel : Nat) (ρ : Env) (p : Prog) :
    evalD fuel ρ (quoteD p) = runM fuel ρ p := by
  simp [evalD, decode_quote]

/-- μ with a vacuous binding: `(callcc (λk. a))`-style — the body never
    invokes its continuation and returns normally. -/
theorem eval_quote_callcc_unused (a : Fin 8) :
    evalD 4 [] (quoteD (.callcc (.atom a))) = some (.elem a) := by
  rw [eval_quote]; rfl

/-- **The escape**: eval · (callcc k. ((k data?) judge?)). The captured
    continuation is invoked with `data?` (element 5) *before* the outer
    application to judge? can happen — that pending frame is discarded
    (`step_throw`), and 5 returns straight to the eval-instruction
    frame: dotA8 3 5 = 2. Control transfer through quotation, certified
    against the table. -/
theorem eval_quote_callcc_escape :
    evalD 16 []
      (quoteD (.app (.atom 3)
        (.callcc (.app (.app (.var 0) (.atom 5)) (.atom 6))))) =
      some (.elem 2) := by
  rw [eval_quote]; rfl

/-- The closure rung embeds: its programs are the μ-free ones. -/
def embed : FactorizationClos.Prog → Prog
  | .atom a => .atom a
  | .var n => .var n
  | .lam b => .lam (embed b)
  | .app f x => .app (embed f) (embed x)

mutual
  /-- Its values embed too — no continuations ever arise from them. -/
  def embedVal : FactorizationClos.Val → Val
    | .elem a => .elem a
    | .cell u v => .cell (embedVal u) (embedVal v)
    | .clos b ρ => .clos (embed b) (embedEnv ρ)

  def embedEnv : List FactorizationClos.Val → List Val
    | [] => []
    | v :: ρ => embedVal v :: embedEnv ρ
end

theorem getD_embedEnv (ρ : FactorizationClos.Env) (n : Nat) :
    (embedEnv ρ).getD n (.elem 0) = embedVal (ρ.getD n (.elem 0)) := by
  induction ρ generalizing n with
  | nil => simp [embedEnv, embedVal]
  | cons u ρ ih =>
    cases n with
    | zero => simp [embedEnv]
    | succ m => simpa [embedEnv] using ih m

/-- **The simulation theorem**: whatever the closure rung's big-step
    driver computes, the machine computes — stated
    continuation-polymorphically (if returning the embedded value to k
    eventually answers w, then evaluating the program in k eventually
    answers w), with machine fuel existential. -/
theorem machine_sim :
    ∀ {fuel : Nat} {ρ : FactorizationClos.Env} {p : FactorizationClos.Prog}
      {v : FactorizationClos.Val},
      FactorizationClos.run fuel ρ p = some v →
      ∀ (k : Kont) (n : Nat) (w : Val),
        loop n (.ret (embedVal v) k) = some w →
        ∃ m, loop m (.eval (embed p) (embedEnv ρ) k) = some w := by
  intro fuel
  induction fuel with
  | zero => intro ρ p v h; simp [FactorizationClos.run] at h
  | succ fu ih =>
    intro ρ p v h k n w hn
    cases p with
    | atom a =>
      obtain rfl : FactorizationClos.Val.elem a = v := by
        simpa [FactorizationClos.run] using h
      refine ⟨n + 1, ?_⟩
      simp only [embed, loop, step]
      simpa only [embedVal] using hn
    | var i =>
      obtain rfl : ρ.getD i (.elem 0) = v := by
        simpa [FactorizationClos.run] using h
      refine ⟨n + 1, ?_⟩
      simp only [embed, loop, step, getD_embedEnv]
      exact hn
    | lam b =>
      obtain rfl : FactorizationClos.Val.clos b ρ = v := by
        simpa [FactorizationClos.run] using h
      refine ⟨n + 1, ?_⟩
      simp only [embed, loop, step]
      simpa only [embedVal] using hn
    | app f x =>
      simp only [FactorizationClos.run] at h
      cases hf : FactorizationClos.run fu ρ f with
      | none => rw [hf] at h; simp at h
      | some vf =>
        rw [hf] at h
        cases hx : FactorizationClos.run fu ρ x with
        | none => rw [hx] at h; cases vf <;> simp at h
        | some vx =>
          rw [hx] at h
          cases vf with
          | elem a =>
            cases vx with
            | elem b =>
              obtain rfl : FactorizationClos.Val.elem (dotA8 a b) = v := by
                simpa using h
              have h₂ : loop (n + 1)
                  (.ret (embedVal (.elem b)) (.appR (.elem a) k)) = some w := by
                simp only [embedVal, loop, step]
                simpa only [embedVal] using hn
              obtain ⟨m₂, hm₂⟩ := ih hx (.appR (.elem a) k) (n + 1) w h₂
              have h₁ : loop (m₂ + 1)
                  (.ret (embedVal (.elem a))
                    (.appL (embed x) (embedEnv ρ) k)) = some w := by
                simp only [embedVal, loop, step]
                exact hm₂
              obtain ⟨m₁, hm₁⟩ :=
                ih hf (.appL (embed x) (embedEnv ρ) k) (m₂ + 1) w h₁
              refine ⟨m₁ + 1, ?_⟩
              simp only [embed, loop, step]
              exact hm₁
            | cell u₁ u₂ =>
              obtain rfl : FactorizationClos.Val.elem 0 = v := by
                simpa using h
              have h₂ : loop (n + 1)
                  (.ret (embedVal (.cell u₁ u₂))
                    (.appR (.elem a) k)) = some w := by
                simp only [embedVal, loop, step]
                simpa only [embedVal] using hn
              obtain ⟨m₂, hm₂⟩ := ih hx (.appR (.elem a) k) (n + 1) w h₂
              have h₁ : loop (m₂ + 1)
                  (.ret (embedVal (.elem a))
                    (.appL (embed x) (embedEnv ρ) k)) = some w := by
                simp only [embedVal, loop, step]
                exact hm₂
              obtain ⟨m₁, hm₁⟩ :=
                ih hf (.appL (embed x) (embedEnv ρ) k) (m₂ + 1) w h₁
              refine ⟨m₁ + 1, ?_⟩
              simp only [embed, loop, step]
              exact hm₁
            | clos b' ρ' =>
              obtain rfl : FactorizationClos.Val.elem 0 = v := by
                simpa using h
              have h₂ : loop (n + 1)
                  (.ret (embedVal (.clos b' ρ'))
                    (.appR (.elem a) k)) = some w := by
                simp only [embedVal, loop, step]
                simpa only [embedVal] using hn
              obtain ⟨m₂, hm₂⟩ := ih hx (.appR (.elem a) k) (n + 1) w h₂
              have h₁ : loop (m₂ + 1)
                  (.ret (embedVal (.elem a))
                    (.appL (embed x) (embedEnv ρ) k)) = some w := by
                simp only [embedVal, loop, step]
                exact hm₂
              obtain ⟨m₁, hm₁⟩ :=
                ih hf (.appL (embed x) (embedEnv ρ) k) (m₂ + 1) w h₁
              refine ⟨m₁ + 1, ?_⟩
              simp only [embed, loop, step]
              exact hm₁
          | cell w₁ w₂ =>
            obtain rfl : FactorizationClos.Val.elem 0 = v := by
              cases vx <;> simpa using h
            have h₂ : loop (n + 1)
                (.ret (embedVal vx)
                  (.appR (.cell (embedVal w₁) (embedVal w₂)) k)) = some w := by
              simp only [loop, step]
              simpa only [embedVal] using hn
            obtain ⟨m₂, hm₂⟩ :=
              ih hx (.appR (.cell (embedVal w₁) (embedVal w₂)) k) (n + 1) w h₂
            have h₁ : loop (m₂ + 1)
                (.ret (embedVal (.cell w₁ w₂))
                  (.appL (embed x) (embedEnv ρ) k)) = some w := by
              simp only [embedVal, loop, step]
              exact hm₂
            obtain ⟨m₁, hm₁⟩ :=
              ih hf (.appL (embed x) (embedEnv ρ) k) (m₂ + 1) w h₁
            refine ⟨m₁ + 1, ?_⟩
            simp only [embed, loop, step]
            exact hm₁
          | clos b ρ'' =>
            replace h : FactorizationClos.run fu (vx :: ρ'') b = some v := h
            obtain ⟨m₃, hm₃⟩ := ih h k n w hn
            have h₂ : loop (m₃ + 1)
                (.ret (embedVal vx)
                  (.appR (.clos (embed b) (embedEnv ρ'')) k)) = some w := by
              simp only [loop, step]
              simpa only [embedEnv] using hm₃
            obtain ⟨m₂, hm₂⟩ :=
              ih hx (.appR (.clos (embed b) (embedEnv ρ'')) k) (m₃ + 1) w h₂
            have h₁ : loop (m₂ + 1)
                (.ret (embedVal (.clos b ρ''))
                  (.appL (embed x) (embedEnv ρ) k)) = some w := by
              simp only [embedVal, loop, step]
              exact hm₂
            obtain ⟨m₁, hm₁⟩ :=
              ih hf (.appL (embed x) (embedEnv ρ) k) (m₂ + 1) w h₁
            refine ⟨m₁ + 1, ?_⟩
            simp only [embed, loop, step]
            exact hm₁

/-- **Conservativity**: the machine computes everything the closure
    rung's big-step driver does. -/
theorem machine_embed {fuel : Nat} {ρ : FactorizationClos.Env}
    {p : FactorizationClos.Prog} {v : FactorizationClos.Val}
    (h : FactorizationClos.run fuel ρ p = some v) :
    ∃ m, runM m (embedEnv ρ) (embed p) = some (embedVal v) :=
  machine_sim h .halt 1 (embedVal v) rfl

/-- …and by determinism, nothing else: any machine answer on a μ-free
    program is the big-step answer. -/
theorem machine_embed_unique {fuel n : Nat} {ρ : FactorizationClos.Env}
    {p : FactorizationClos.Prog} {v : FactorizationClos.Val} {w : Val}
    (h : FactorizationClos.run fuel ρ p = some v)
    (hw : runM n (embedEnv ρ) (embed p) = some w) : w = embedVal v := by
  obtain ⟨m, hm⟩ := machine_embed h
  exact loop_det hw hm

/-- Corollary through quotation: eval of the quotation of a μ-free
    program machine-computes the closure rung's value. -/
theorem eval_quote_embed {fuel : Nat} {ρ : FactorizationClos.Env}
    {p : FactorizationClos.Prog} {v : FactorizationClos.Val}
    (h : FactorizationClos.run fuel ρ p = some v) :
    ∃ m, evalD m (embedEnv ρ) (quoteD (embed p)) = some (embedVal v) := by
  simpa only [eval_quote] using machine_embed h

/-- δ = λx. x x. -/
def deltaM : Prog := .lam (.app (.var 0) (.var 0))

/-- Ω = δ δ. -/
def OmegaM : Prog := .app deltaM deltaM

/-- The Ω cycle: from ⟨δ-closure ‖ apply-δ-closure⟩ the machine returns
    to the same command in five steps — divergence as a certified
    finite cycle. -/
theorem machine_delta_cycle (ρ : Env) :
    ∀ m, loop m (.ret (.clos (.app (.var 0) (.var 0)) ρ)
      (.appR (.clos (.app (.var 0) (.var 0)) ρ) .halt)) = none := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | _ | _ | _ | m
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact ih m (by omega)

/-- Ω diverges on the machine at every fuel. -/
theorem machine_Omega_diverges (fuel : Nat) (ρ : Env) :
    runM fuel ρ OmegaM = none := by
  rcases fuel with _ | _ | _ | _ | fuel
  · rfl
  · rfl
  · rfl
  · rfl
  · exact machine_delta_cycle ρ fuel

/-- Eval of the quotation of Ω diverges at every fuel: user-level eval
    inherits the machine's partiality exactly. -/
theorem eval_quote_Omega (fuel : Nat) (ρ : Env) :
    evalD fuel ρ (quoteD OmegaM) = none := by
  rw [eval_quote]; exact machine_Omega_diverges fuel ρ

end FactorizationCtrl
end Dichotomic
