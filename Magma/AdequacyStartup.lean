import Magma.MetaImage
import Magma.AdequacyRep

/-!
# Adequacy campaign, rung 3b (i): the startup lemma

The first **symbolic** theorem about the running image: for *every*
environment `ρ` and continuation `κ`, running the frozen image from
an empty store performs exactly `startupSteps = 1275` machine steps
of letrec-knot setup — allocating the 14 knot cells, building and
backpatching the dispatch closures — and arrives at the canonical
post-startup state: the `meval` closure returned to `κ`, over the
knot store. Neither `ρ` nor `κ` is touched (the image is closed and
the store starts empty), which is what lets one concrete computation
stand for all contexts.

The post-startup artifacts (`knotStore`, `metaBody`,
`metaEnvPrefix`) are **self-computing definitions** — extracted by
running the machine inside the definition, not pasted as generated
text — so the startup theorem is a single defeq check between the
symbolic run and the computed one (`rfl`), and nothing can drift.

`knot_length` pins the rung-2 parameter to reality: `K₀ = 14` stops
being a documented count and becomes a theorem about the image.

`meval_entry` packages startup for consumers: from the canonical
initial state `metaState p` (META applied to a quotation entering
through the environment), the machine reaches the `meval` entry
state — body focused, quotation bound, knot store in place — in
exactly `entrySteps = startupSteps + 4` steps, for every program
`p`. Later rungs start their symbolic case analyses from
`mevalEntry p`, never re-crossing the knot.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyStartup

open FactorizationEqv MetaImage

/-! ## Step-iteration machinery -/

/-- Iterate `step`, staying at `.inl` states; a produced value is
    final and absorbing. -/
def stepIter : Nat → State → State ⊕ Val
  | 0, s => .inl s
  | n + 1, s =>
    match step s with
    | .inl s' => stepIter n s'
    | .inr v => .inr v

/-- Chaining: a completed `stepIter` segment prepends to any
    further iteration. -/
theorem stepIter_append {a : Nat} {s s' : State}
    (h : stepIter a s = .inl s') (b : Nat) :
    stepIter (a + b) s = stepIter b s' := by
  induction a generalizing s with
  | zero =>
    simp only [stepIter] at h
    cases h
    simp [Nat.zero_add]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [stepIter] at h ⊢
    cases hs : step s with
    | inl s₁ => rw [hs] at h; exact ih h
    | inr v => rw [hs] at h; exact absurd h (by simp)

/-- Fuel transfer into the certified `loop`: a completed `stepIter`
    segment is a fuel prefix. -/
theorem loop_stepIter {n : Nat} {s s' : State}
    (h : stepIter n s = .inl s') (m : Nat) :
    loop (m + n) s = loop m s' := by
  induction n generalizing s with
  | zero =>
    simp only [stepIter] at h
    cases h
    rfl
  | succ n ih =>
    simp only [stepIter] at h
    rw [show m + (n + 1) = (m + n) + 1 by omega]
    simp only [loop]
    cases hs : step s with
    | inl s₁ => rw [hs] at h; exact ih h
    | inr v => rw [hs] at h; exact absurd h (by simp)

/-! ## The post-startup artifacts, self-computing -/

/-- The knot takes exactly this many steps (probe-discovered; the
    theorems below fail if it drifts). -/
def startupSteps : Nat := 1275

/-- A startup run over an arbitrary initial environment. The knot's
    closures **capture `ρ` inside themselves** (every dispatch
    closure's environment ends in the initial environment), so the
    post-startup artifacts are parametric in `ρ` — extracted by
    running the machine inside the definition, per environment. -/
def startupRun (ρ : Env) : State ⊕ Val :=
  stepIter startupSteps (.eval META ρ [] .halt)

/-- The 14-cell knot store over `ρ`: the image's letrec cells,
    holding the backpatched dispatch closures (whose environments
    end in `ρ`). Written once at startup, never again. -/
def knotStoreF (ρ : Env) : Store :=
  match startupRun ρ with
  | .inl (.ret _ σ _) => σ
  | _ => []

/-- The body of the `meval` closure (the `(lambda (q) (meval q tt))`
    at the image's core) — a program subterm, environment-free. -/
def metaBody : Prog :=
  match startupRun [] with
  | .inl (.ret (.clos b _) _ _) => b
  | _ => .atom 0

/-- The environment captured by the `meval` closure at startup over
    `ρ`: locs, forwarders, and backpatched closures — the knot's
    three layers (42 entries), over `ρ`. -/
def metaEnvF (ρ : Env) : Env :=
  match startupRun ρ with
  | .inl (.ret (.clos _ e) _ _) => e
  | _ => []

/-- Sanity: the empty-context probe run really ends at a returned
    closure over the original continuation. -/
theorem startup_shape :
    (match startupRun [] with
     | .inl (.ret (.clos _ _) _ .halt) => true
     | _ => false) = true := by
  native_decide

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`K₀ = 14`, as a theorem about the image — for every initial
    environment**: the knot allocates exactly the 14 letrec cells,
    and the store's *spine* is concrete even though its entries
    carry `ρ`, so this holds symbolically by reduction. Rung 2's
    offset parameter, pinned. -/
theorem knot_length (ρ : Env) : (knotStoreF ρ).length = 14 :=
  rfl

/-! ## The startup lemma -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **Startup, symbolically.** For every environment and every
    continuation, the image's first `startupSteps` steps from an
    empty store are the knot setup, landing at the `meval` closure
    returned to `κ` over the knot store. One defeq check: the
    symbolic run reduces to the computed artifacts. -/
theorem meta_startup (ρ : Env) (κ : Kont) :
    stepIter startupSteps (.eval META ρ [] κ) =
      .inl (.ret (.clos metaBody (metaEnvF ρ)) (knotStoreF ρ) κ) :=
  rfl

/-! ## The entry theorem -/

/-- The canonical initial state (as in `AdequacyInstances`): META
    applied to a quotation entering through the environment. -/
def metaState (p : Prog) : State :=
  .eval (.app META (.var 0)) [quoteD p] [] .halt

/-- Steps from `metaState` to the `meval` entry: unfold the
    application (1), the knot (`startupSteps`), then argument lookup
    and β (3). -/
def entrySteps : Nat := startupSteps + 4

/-- The `meval` entry state: body focused, the quotation bound at
    index 0 over the captured environment, knot store in place.
    Every later rung's symbolic case analysis starts here. -/
def mevalEntry (p : Prog) : State :=
  .eval metaBody
    (quoteD p :: metaEnvF [quoteD p]) (knotStoreF [quoteD p]) .halt

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **The entry theorem**: every adequacy run reaches the `meval`
    entry state in exactly `entrySteps` steps — the knot is crossed
    once, uniformly in the program. -/
theorem meval_entry (p : Prog) :
    stepIter entrySteps (metaState p) = .inl (mevalEntry p) := by
  have h1 : stepIter 1 (metaState p) =
      .inl (.eval META [quoteD p] []
        (.appL (.var 0) [quoteD p] .halt)) := rfl
  have h2 := stepIter_append h1 (startupSteps + 3)
  rw [show (1 : Nat) + (startupSteps + 3) = entrySteps by
    simp [entrySteps]; omega] at h2
  rw [h2]
  have h3 := stepIter_append
    (meta_startup [quoteD p] (.appL (.var 0) [quoteD p] .halt)) 3
  rw [show startupSteps + 3 = startupSteps + 3 from rfl] at h3
  rw [h3]
  rfl

/-- Startup packaged for `loop`: fuel prefixes transfer. -/
theorem loop_meval_entry (p : Prog) (m : Nat) :
    loop (m + entrySteps) (metaState p) = loop m (mevalEntry p) :=
  loop_stepIter (meval_entry p) m

end AdequacyStartup
end Dichotomic
