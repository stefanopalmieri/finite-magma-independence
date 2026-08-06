import Magma.AdequacyStore

/-!
# Adequacy campaign, rung 5½: completeness and well-formedness

The converse direction, for the 12-form fragment: a **terminating
machine run is a derivation**. Until now every theorem consumed an
`EvS` derivation; this rung manufactures one from a run, which
upgrades the master theorem from "derivations transport" to **"the
interpreted world converges whenever the direct world does"**
(`meta_inherits_convergence`) — no derivation hypothesis, just the
run.

Two pieces:

* **Store well-formedness** (`WfV`/`WfVs`/`WfSt`): every location in
  every reachable value is under the store's length, closure bodies
  stay in the control-free fragment (`Ctl0`), and continuation
  values do not occur. `evS_wf` proves preservation: stores only
  grow, and well-formedness rides through all 22 clauses. This
  discharges rung 5's honest boundary — the in-bounds premise on
  `derefLoc` — for every run from a closed program: **out-of-bounds
  reads are provably unreachable**, not merely excluded.
* **Completeness** (`evS_complete`): by induction on fuel, a
  terminating run of a `Ctl0` program from well-formed state has an
  `EvS` derivation, with the returned value pinned at `halt`
  (`evS_complete_halt`). The fuel bookkeeping runs on two small
  tools: `loop_through` (a completed prefix strictly consumes fuel)
  and the ladder's `loop_mono_le`.

Corollary and headline: `meta_inherits_convergence` — for every
control-free closed program whose direct run terminates, META's run
terminates with a representing value. Composed with `evS_steps` the
other way, convergence for the 12-form fragment transfers from the
machine to the interpreted world unconditionally. (The reverse
transfer, and with it two-sided divergence agreement, is rung 7's,
via the small-step layer rung 6 introduces.)

An honest re-scoping, discovered here: the tower corollary cannot
land at this rung. META's own image contains a `callcc` form (the
absorption arm of its dispatch — dead code on 12-form inputs, but
syntactically present), so `Ctl0 META` is false and completeness
does not apply to META's own runs. The evaluated-positions
refinement that would fix this is exactly rung 6's small-step
simulation, where `callcc` joins the relation and META becomes
fully in-fragment — the tower moves there, with the machinery of
this rung as its engine.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyComplete

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep
  AdequacyLeaf AdequacySim AdequacyData AdequacyStoreKit AdequacyStore

/-! ## The control-free fragment -/

/-- The 12-form fragment: no `callcc`, no `eqv`, anywhere. -/
def Ctl0 : Prog → Prop
  | .atom _ => True
  | .var _ => True
  | .lam b => Ctl0 b
  | .app f x => Ctl0 f ∧ Ctl0 x
  | .callcc _ => False
  | .ref e => Ctl0 e
  | .deref e => Ctl0 e
  | .setref l e => Ctl0 l ∧ Ctl0 e
  | .cons a b => Ctl0 a ∧ Ctl0 b
  | .car e => Ctl0 e
  | .cdr e => Ctl0 e
  | .pairp e => Ctl0 e
  | .ite c t e => Ctl0 c ∧ Ctl0 t ∧ Ctl0 e
  | .eqv _ _ => False

/-! ## Well-formed values

Locations bounded by `m`, closure bodies control-free, closure
environments well-formed, and no continuation values (first-order
control — rung 6 lifts this). -/

mutual
  def WfV (m : Nat) : Val → Prop
    | .elem _ => True
    | .cell a d => WfV m a ∧ WfV m d
    | .clos b ρ => Ctl0 b ∧ WfVs m ρ
    | .cont _ => False
    | .loc i => i < m

  def WfVs (m : Nat) : List Val → Prop
    | [] => True
    | v :: vs => WfV m v ∧ WfVs m vs
end

/-- A well-formed store: every cell well-formed at the store's own
    length. -/
def WfSt (σ : Store) : Prop := WfVs σ.length σ

/-! ### Monotonicity (stores only grow) -/

mutual
  theorem wfV_mono {m m' : Nat} (h : m ≤ m') :
      ∀ v, WfV m v → WfV m' v
    | .elem _, _ => trivial
    | .cell a d, ⟨ha, hd⟩ => ⟨wfV_mono h a ha, wfV_mono h d hd⟩
    | .clos _ ρ, ⟨hb, hρ⟩ => ⟨hb, wfVs_mono h ρ hρ⟩
    | .cont _, hf => hf.elim
    | .loc _, hi => Nat.lt_of_lt_of_le hi h

  theorem wfVs_mono {m m' : Nat} (h : m ≤ m') :
      ∀ ρ, WfVs m ρ → WfVs m' ρ
    | [], _ => trivial
    | v :: vs, ⟨hv, hvs⟩ => ⟨wfV_mono h v hv, wfVs_mono h vs hvs⟩
end

/-! ### List plumbing -/

theorem wfVs_getD {m : Nat} :
    ∀ {ρ : List Val}, WfVs m ρ → ∀ n, WfV m (ρ.getD n (.elem 0))
  | [], _, _ => trivial
  | _ :: _, ⟨hv, _⟩, 0 => hv
  | _ :: vs, ⟨_, hvs⟩, n + 1 => wfVs_getD (ρ := vs) hvs n

theorem wfVs_set {m : Nat} {w : Val} (hw : WfV m w) :
    ∀ {ρ : List Val}, WfVs m ρ → ∀ n, WfVs m (ρ.set n w)
  | [], _, _ => trivial
  | _ :: _, ⟨_, hvs⟩, 0 => ⟨hw, hvs⟩
  | _ :: vs, ⟨hv, hvs⟩, n + 1 => ⟨hv, wfVs_set hw (ρ := vs) hvs n⟩

theorem wfVs_append {m : Nat} {w : Val} (hw : WfV m w) :
    ∀ {ρ : List Val}, WfVs m ρ → WfVs m (ρ ++ [w])
  | [], _ => ⟨hw, trivial⟩
  | _ :: vs, ⟨hv, hvs⟩ => ⟨hv, wfVs_append hw (ρ := vs) hvs⟩

/-- Allocation preserves store well-formedness. -/
theorem wfSt_append {σ : Store} {v : Val} (hσ : WfSt σ)
    (hv : WfV σ.length v) : WfSt (σ ++ [v]) := by
  unfold WfSt
  rw [List.length_append]
  exact wfVs_append (wfV_mono (by omega) v hv)
    (wfVs_mono (by omega) σ hσ)

/-- Writes preserve store well-formedness. -/
theorem wfSt_set {σ : Store} {w : Val} {n : Nat} (hσ : WfSt σ)
    (hw : WfV σ.length w) : WfSt (σ.set n w) := by
  unfold WfSt
  rw [List.length_set]
  exact wfVs_set hw hσ n

/-! ## Preservation

Well-formedness rides through every clause; stores only grow. -/

theorem evS_wf {p : Prog} {ρ : Env} {σ : Store} {v : Val} {σ₂ : Store}
    (h : EvS p ρ σ v σ₂) : Ctl0 p → WfVs σ.length ρ → WfSt σ →
    WfV σ₂.length v ∧ WfSt σ₂ ∧ σ.length ≤ σ₂.length := by
  induction h with
  | atom a ρ σ => exact fun _ _ hσ => ⟨trivial, hσ, Nat.le_refl _⟩
  | var n ρ σ => exact fun _ hρ hσ => ⟨wfVs_getD hρ n, hσ, Nat.le_refl _⟩
  | lam b ρ σ => exact fun hp hρ hσ => ⟨⟨hp, hρ⟩, hσ, Nat.le_refl _⟩
  | @appClos f x b ρ ρ' σ σ₁ σ₂ σ₃ vx v _ _ _ ihf ihx ihb =>
    intro hp hρ hσ
    obtain ⟨⟨hb, hρ'⟩, hσ₁, hl₁⟩ := ihf hp.1 hρ hσ
    obtain ⟨hvx, hσ₂, hl₂⟩ := ihx hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    obtain ⟨hv, hσ₃, hl₃⟩ := ihb hb
      ⟨hvx, wfVs_mono hl₂ ρ' hρ'⟩ hσ₂
    exact ⟨hv, hσ₃, Nat.le_trans hl₁ (Nat.le_trans hl₂ hl₃)⟩
  | @appElem f x ρ σ σ₁ σ₂ a b _ _ ihf ihx =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihf hp.1 hρ hσ
    obtain ⟨_, hσ₂, hl₂⟩ := ihx hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨trivial, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @appElemErr f x ρ σ σ₁ σ₂ a w _ _ hw ihf ihx =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihf hp.1 hρ hσ
    obtain ⟨_, hσ₂, hl₂⟩ := ihx hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨trivial, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @appCellErr f x ρ σ σ₁ σ₂ a d w _ _ ihf ihx =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihf hp.1 hρ hσ
    obtain ⟨_, hσ₂, hl₂⟩ := ihx hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨trivial, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @appLocErr f x ρ σ σ₁ σ₂ l w _ _ ihf ihx =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihf hp.1 hρ hσ
    obtain ⟨_, hσ₂, hl₂⟩ := ihx hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨trivial, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @cons a b ρ σ σ₁ σ₂ va vb _ _ iha ihb =>
    intro hp hρ hσ
    obtain ⟨hva, hσ₁, hl₁⟩ := iha hp.1 hρ hσ
    obtain ⟨hvb, hσ₂, hl₂⟩ := ihb hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨⟨wfV_mono hl₂ va hva, hvb⟩, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @carCell e ρ σ σ₁ u w _ ihe =>
    intro hp hρ hσ
    obtain ⟨⟨hu, _⟩, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨hu, hσ₁, hl₁⟩
  | @carErr e ρ σ σ₁ w _ _ ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨trivial, hσ₁, hl₁⟩
  | @cdrCell e ρ σ σ₁ u w _ ihe =>
    intro hp hρ hσ
    obtain ⟨⟨_, hw⟩, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨hw, hσ₁, hl₁⟩
  | @cdrErr e ρ σ σ₁ w _ _ ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨trivial, hσ₁, hl₁⟩
  | @pairpYes e ρ σ σ₁ u w _ ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨trivial, hσ₁, hl₁⟩
  | @pairpNo e ρ σ σ₁ w _ _ ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨trivial, hσ₁, hl₁⟩
  | @iteFf c t e ρ σ σ₁ σ₂ v _ _ ihc ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihc hp.1 hρ hσ
    obtain ⟨hv, hσ₂, hl₂⟩ := ihe hp.2.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨hv, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @iteElem c t e ρ σ σ₁ σ₂ b v _ _ _ ihc iht =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihc hp.1 hρ hσ
    obtain ⟨hv, hσ₂, hl₂⟩ := iht hp.2.1 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨hv, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @iteVal c t e ρ σ σ₁ σ₂ w v _ _ _ ihc iht =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihc hp.1 hρ hσ
    obtain ⟨hv, hσ₂, hl₂⟩ := iht hp.2.1 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨hv, hσ₂, Nat.le_trans hl₁ hl₂⟩
  | @ref e ρ σ σ₁ v _ ihe =>
    intro hp hρ hσ
    obtain ⟨hv, hσ₁, hl₁⟩ := ihe hp hρ hσ
    refine ⟨?_, wfSt_append hσ₁ hv, ?_⟩
    · rw [List.length_append]; exact Nat.lt_succ_self _
    · rw [List.length_append]; omega
  | @derefLoc e ρ σ σ₁ n _ hn ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨wfVs_getD hσ₁ n, hσ₁, hl₁⟩
  | @derefErr e ρ σ σ₁ w _ _ ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihe hp hρ hσ
    exact ⟨trivial, hσ₁, hl₁⟩
  | @setLoc l e ρ σ σ₁ σ₂ n w _ _ ihl ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihl hp.1 hρ hσ
    obtain ⟨hw, hσ₂, hl₂⟩ := ihe hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    refine ⟨?_, wfSt_set hσ₂ hw, ?_⟩
    · rw [List.length_set]; exact hw
    · rw [List.length_set]; exact Nat.le_trans hl₁ hl₂
  | @setErr l e ρ σ σ₁ σ₂ vl w _ _ _ ihl ihe =>
    intro hp hρ hσ
    obtain ⟨_, hσ₁, hl₁⟩ := ihl hp.1 hρ hσ
    obtain ⟨_, hσ₂, hl₂⟩ := ihe hp.2 (wfVs_mono hl₁ ρ hρ) hσ₁
    exact ⟨trivial, hσ₂, Nat.le_trans hl₁ hl₂⟩

/-! ## Fuel bookkeeping -/

/-- A completed prefix strictly consumes fuel: if the run finishes
    within `n` but is still going at `m`, then `m < n` and the rest
    finishes on the remainder. -/
theorem loop_through {m : Nat} {s s' : State}
    (h : stepIter m s = .inl s') :
    ∀ {n : Nat} {w : Val}, loop n s = some w →
      m < n ∧ loop (n - m) s' = some w := by
  induction m generalizing s with
  | zero =>
    intro n w hl
    simp only [stepIter] at h
    cases h
    cases n with
    | zero => simp [loop] at hl
    | succ n => exact ⟨Nat.succ_pos n, hl⟩
  | succ m ih =>
    intro n w hl
    simp only [stepIter] at h
    cases hs : step s with
    | inl s₁ =>
      rw [hs] at h
      cases n with
      | zero => simp [loop] at hl
      | succ n =>
        have hl₁ : loop n s₁ = some w := by
          simpa only [loop, hs] using hl
        obtain ⟨hlt, hrest⟩ := ih h hl₁
        exact ⟨Nat.succ_lt_succ hlt, by simpa [Nat.succ_sub_succ] using hrest⟩
    | inr v => rw [hs] at h; exact absurd h (by simp)

/-! ## Completeness

A terminating run of a control-free program from well-formed state
is a derivation. Induction on fuel; sub-runs re-fueled via
`loop_mono_le`; the deref case discharges its in-bounds premise
from well-formedness. -/

theorem evS_complete :
    ∀ (n : Nat) {p : Prog} {ρ : Env} {σ : Store} {κ : Kont} {w : Val},
      loop n (.eval p ρ σ κ) = some w → Ctl0 p →
      WfVs σ.length ρ → WfSt σ →
      ∃ (v : Val) (σ' : Store), EvS p ρ σ v σ' := by
  intro n
  induction n with
  | zero => intro p ρ σ κ w h; simp [loop] at h
  | succ n IH =>
    intro p ρ σ κ w h hp hρ hσ
    -- one helper used in every compound case: run a sub-derivation's
    -- segment through the remaining fuel
    cases p with
    | atom a => exact ⟨.elem a, σ, .atom a ρ σ⟩
    | var i => exact ⟨_, σ, .var i ρ σ⟩
    | lam b => exact ⟨_, σ, .lam b ρ σ⟩
    | callcc b => exact hp.elim
    | eqv a b => exact hp.elim
    | app f x =>
      have hf : loop n (.eval f ρ σ (.appL x ρ κ)) = some w := h
      obtain ⟨vf, σ₁, hEf⟩ := IH hf hp.1 hρ hσ
      obtain ⟨hvf, hσ₁, hl₁⟩ := evS_wf hEf hp.1 hρ hσ
      obtain ⟨mf, hSf⟩ := evS_steps hEf (.appL x ρ κ)
      obtain ⟨hmf, hrest⟩ := loop_through hSf hf
      cases hnm : n - mf with
      | zero => rw [hnm] at hrest; simp [loop] at hrest
      | succ k =>
        rw [hnm] at hrest
        have hx : loop k (.eval x ρ σ₁ (.appR vf κ)) = some w := hrest
        obtain ⟨vx, σ₂, hEx⟩ := IH (loop_mono_le (by omega) hx) hp.2
          (wfVs_mono hl₁ ρ hρ) hσ₁
        obtain ⟨hvx, hσ₂, hl₂⟩ := evS_wf hEx hp.2
          (wfVs_mono hl₁ ρ hρ) hσ₁
        obtain ⟨mx, hSx⟩ := evS_steps hEx (.appR vf κ)
        obtain ⟨hmx, hrest₂⟩ := loop_through hSx hx
        cases vf with
        | clos b ρ' =>
          cases hkm : k - mx with
          | zero => rw [hkm] at hrest₂; simp [loop] at hrest₂
          | succ k₂ =>
            rw [hkm] at hrest₂
            have hb : loop k₂ (.eval b (vx :: ρ') σ₂ κ) = some w :=
              hrest₂
            obtain ⟨hCb, hρ'⟩ := hvf
            obtain ⟨v, σ₃, hEb⟩ := IH (loop_mono_le (by omega) hb) hCb
              ⟨hvx, wfVs_mono hl₂ ρ' hρ'⟩ hσ₂
            exact ⟨v, σ₃, .appClos hEf hEx hEb⟩
        | elem a =>
          cases vx with
          | elem b => exact ⟨_, σ₂, .appElem hEf hEx⟩
          | cell _ _ =>
            exact ⟨_, σ₂, .appElemErr hEf hEx (by intro b hb; cases hb)⟩
          | clos _ _ =>
            exact ⟨_, σ₂, .appElemErr hEf hEx (by intro b hb; cases hb)⟩
          | loc _ =>
            exact ⟨_, σ₂, .appElemErr hEf hEx (by intro b hb; cases hb)⟩
          | cont _ => exact hvx.elim
        | cell a d => exact ⟨_, σ₂, .appCellErr hEf hEx⟩
        | loc l => exact ⟨_, σ₂, .appLocErr hEf hEx⟩
        | cont _ => exact hvf.elim
    | cons a b =>
      have ha : loop n (.eval a ρ σ (.consL b ρ κ)) = some w := h
      obtain ⟨va, σ₁, hEa⟩ := IH ha hp.1 hρ hσ
      obtain ⟨hva, hσ₁, hl₁⟩ := evS_wf hEa hp.1 hρ hσ
      obtain ⟨ma, hSa⟩ := evS_steps hEa (.consL b ρ κ)
      obtain ⟨hma, hrest⟩ := loop_through hSa ha
      cases hnm : n - ma with
      | zero => rw [hnm] at hrest; simp [loop] at hrest
      | succ k =>
        rw [hnm] at hrest
        have hb : loop k (.eval b ρ σ₁ (.consR va κ)) = some w := hrest
        obtain ⟨vb, σ₂, hEb⟩ := IH (loop_mono_le (by omega) hb) hp.2
          (wfVs_mono hl₁ ρ hρ) hσ₁
        exact ⟨_, σ₂, .cons hEa hEb⟩
    | car e =>
      have he : loop n (.eval e ρ σ (.carK κ)) = some w := h
      obtain ⟨ve, σ₁, hEe⟩ := IH he hp hρ hσ
      obtain ⟨hve, _, _⟩ := evS_wf hEe hp hρ hσ
      cases ve with
      | cell u d => exact ⟨u, σ₁, .carCell hEe⟩
      | elem _ => exact ⟨_, σ₁, .carErr hEe (by intro u v hc; cases hc)⟩
      | clos _ _ => exact ⟨_, σ₁, .carErr hEe (by intro u v hc; cases hc)⟩
      | loc _ => exact ⟨_, σ₁, .carErr hEe (by intro u v hc; cases hc)⟩
      | cont _ => exact hve.elim
    | cdr e =>
      have he : loop n (.eval e ρ σ (.cdrK κ)) = some w := h
      obtain ⟨ve, σ₁, hEe⟩ := IH he hp hρ hσ
      obtain ⟨hve, _, _⟩ := evS_wf hEe hp hρ hσ
      cases ve with
      | cell u d => exact ⟨d, σ₁, .cdrCell hEe⟩
      | elem _ => exact ⟨_, σ₁, .cdrErr hEe (by intro u v hc; cases hc)⟩
      | clos _ _ => exact ⟨_, σ₁, .cdrErr hEe (by intro u v hc; cases hc)⟩
      | loc _ => exact ⟨_, σ₁, .cdrErr hEe (by intro u v hc; cases hc)⟩
      | cont _ => exact hve.elim
    | pairp e =>
      have he : loop n (.eval e ρ σ (.pairK κ)) = some w := h
      obtain ⟨ve, σ₁, hEe⟩ := IH he hp hρ hσ
      obtain ⟨hve, _, _⟩ := evS_wf hEe hp hρ hσ
      cases ve with
      | cell u d => exact ⟨_, σ₁, .pairpYes hEe⟩
      | elem _ => exact ⟨_, σ₁, .pairpNo hEe (by intro u v hc; cases hc)⟩
      | clos _ _ => exact ⟨_, σ₁, .pairpNo hEe (by intro u v hc; cases hc)⟩
      | loc _ => exact ⟨_, σ₁, .pairpNo hEe (by intro u v hc; cases hc)⟩
      | cont _ => exact hve.elim
    | ite c t e =>
      have hc : loop n (.eval c ρ σ (.iteK t e ρ κ)) = some w := h
      obtain ⟨vc, σ₁, hEc⟩ := IH hc hp.1 hρ hσ
      obtain ⟨hvc, hσ₁, hl₁⟩ := evS_wf hEc hp.1 hρ hσ
      obtain ⟨mc, hSc⟩ := evS_steps hEc (.iteK t e ρ κ)
      obtain ⟨hmc, hrest⟩ := loop_through hSc hc
      cases vc with
      | elem b =>
        by_cases hb : b = 1
        · subst hb
          cases hnm : n - mc with
          | zero => rw [hnm] at hrest; simp [loop] at hrest
          | succ k =>
            rw [hnm] at hrest
            have he : loop k (.eval e ρ σ₁ κ) = some w := by
              simpa only [loop, step, if_pos rfl] using hrest
            obtain ⟨v, σ₂, hEe⟩ := IH (loop_mono_le (by omega) he)
              hp.2.2 (wfVs_mono hl₁ ρ hρ) hσ₁
            exact ⟨v, σ₂, .iteFf hEc hEe⟩
        · cases hnm : n - mc with
          | zero => rw [hnm] at hrest; simp [loop] at hrest
          | succ k =>
            rw [hnm] at hrest
            have ht : loop k (.eval t ρ σ₁ κ) = some w := by
              simpa only [loop, step, if_neg hb] using hrest
            obtain ⟨v, σ₂, hEt⟩ := IH (loop_mono_le (by omega) ht)
              hp.2.1 (wfVs_mono hl₁ ρ hρ) hσ₁
            exact ⟨v, σ₂, .iteElem hEc hb hEt⟩
      | cont _ => exact hvc.elim
      | cell a d =>
        cases hnm : n - mc with
        | zero => rw [hnm] at hrest; simp [loop] at hrest
        | succ k =>
          rw [hnm] at hrest
          have ht : loop k (.eval t ρ σ₁ κ) = some w := hrest
          obtain ⟨v, σ₂, hEt⟩ := IH (loop_mono_le (by omega) ht)
            hp.2.1 (wfVs_mono hl₁ ρ hρ) hσ₁
          exact ⟨v, σ₂, .iteVal hEc (by intro b hb; cases hb) hEt⟩
      | clos _ _ =>
        cases hnm : n - mc with
        | zero => rw [hnm] at hrest; simp [loop] at hrest
        | succ k =>
          rw [hnm] at hrest
          have ht : loop k (.eval t ρ σ₁ κ) = some w := hrest
          obtain ⟨v, σ₂, hEt⟩ := IH (loop_mono_le (by omega) ht)
            hp.2.1 (wfVs_mono hl₁ ρ hρ) hσ₁
          exact ⟨v, σ₂, .iteVal hEc (by intro b hb; cases hb) hEt⟩
      | loc _ =>
        cases hnm : n - mc with
        | zero => rw [hnm] at hrest; simp [loop] at hrest
        | succ k =>
          rw [hnm] at hrest
          have ht : loop k (.eval t ρ σ₁ κ) = some w := hrest
          obtain ⟨v, σ₂, hEt⟩ := IH (loop_mono_le (by omega) ht)
            hp.2.1 (wfVs_mono hl₁ ρ hρ) hσ₁
          exact ⟨v, σ₂, .iteVal hEc (by intro b hb; cases hb) hEt⟩
    | ref e =>
      have he : loop n (.eval e ρ σ (.refK κ)) = some w := h
      obtain ⟨ve, σ₁, hEe⟩ := IH he hp hρ hσ
      exact ⟨_, _, .ref hEe⟩
    | deref e =>
      have he : loop n (.eval e ρ σ (.derefK κ)) = some w := h
      obtain ⟨ve, σ₁, hEe⟩ := IH he hp hρ hσ
      obtain ⟨hve, hσ₁, _⟩ := evS_wf hEe hp hρ hσ
      cases ve with
      | loc i => exact ⟨_, σ₁, .derefLoc hEe hve⟩
      | elem _ => exact ⟨_, σ₁, .derefErr hEe (by intro i hi; cases hi)⟩
      | clos _ _ => exact ⟨_, σ₁, .derefErr hEe (by intro i hi; cases hi)⟩
      | cell _ _ => exact ⟨_, σ₁, .derefErr hEe (by intro i hi; cases hi)⟩
      | cont _ => exact hve.elim
    | setref l e =>
      have hl : loop n (.eval l ρ σ (.setL e ρ κ)) = some w := h
      obtain ⟨vl, σ₁, hEl⟩ := IH hl hp.1 hρ hσ
      obtain ⟨hvl, hσ₁, hl₁⟩ := evS_wf hEl hp.1 hρ hσ
      obtain ⟨ml, hSl⟩ := evS_steps hEl (.setL e ρ κ)
      obtain ⟨hml, hrest⟩ := loop_through hSl hl
      cases hnm : n - ml with
      | zero => rw [hnm] at hrest; simp [loop] at hrest
      | succ k =>
        rw [hnm] at hrest
        have he : loop k (.eval e ρ σ₁ (.setR vl κ)) = some w := hrest
        obtain ⟨ve, σ₂, hEe⟩ := IH (loop_mono_le (by omega) he) hp.2
          (wfVs_mono hl₁ ρ hρ) hσ₁
        cases vl with
        | loc i => exact ⟨_, _, .setLoc hEl hEe⟩
        | elem _ => exact ⟨_, σ₂, .setErr hEl (by intro i hi; cases hi) hEe⟩
        | clos _ _ => exact ⟨_, σ₂, .setErr hEl (by intro i hi; cases hi) hEe⟩
        | cell _ _ => exact ⟨_, σ₂, .setErr hEl (by intro i hi; cases hi) hEe⟩
        | cont _ => exact hvl.elim

/-- Completeness at `halt` pins the value: the derivation's result
    *is* the run's result. -/
theorem evS_complete_halt {p : Prog} {n : Nat} {w : Val}
    (h : runM n [] [] p = some w) (hp : Ctl0 p) :
    ∃ σ', EvS p [] [] w σ' := by
  obtain ⟨v, σ', hE⟩ := evS_complete n h hp trivial trivial
  obtain ⟨m, hS⟩ := evS_steps hE .halt
  obtain ⟨hm, hrest⟩ := loop_through hS h
  cases hnm : n - m with
  | zero => rw [hnm] at hrest; simp [loop] at hrest
  | succ k =>
    rw [hnm] at hrest
    have : some v = some w := by simpa [loop, step] using hrest
    cases this
    exact ⟨σ', hE⟩

/-! ## The headline: convergence transfers from the run -/

/-- **The interpreted world converges whenever the direct world
    does** — for every control-free closed program, from the run
    itself: no derivation hypothesis. The machine's terminating run
    is converted into a derivation (`evS_complete`), and the
    derivation drives the simulation (`adequacy_store`). Together
    with `evS_steps`, convergence for the 12-form fragment is now a
    property transported by the theorem, not an assumption fed to
    it. -/
theorem meta_inherits_convergence {p : Prog} (hp : Ctl0 p) {n : Nat}
    {v : Val} (h : runM n [] [] p = some v) :
    ∃ (m : Nat) (vT : Val), RepV 14 KRempty vT v ∧
      loop m (metaState p) = some vT := by
  obtain ⟨σ', hE⟩ := evS_complete_halt h hp
  obtain ⟨m, vT, σT, _, rep, hloop, _⟩ := adequacy_store hE
  exact ⟨m, vT, rep, hloop⟩

end AdequacyComplete
end Dichotomic
