import Magma.AdequacyCtlKit
import Magma.AdequacyEntry
import Magma.AdequacyStore

/-!
# Adequacy campaign, rung 6: the simulation — control joins, and
# the tower

The small-step simulation over state pairs, covering the **full
13-form domain** (`EqvFree` — exactly META v1's): `SRel` relates a
direct machine state to its META image, `sim_step` proves every
direct step is matched by a nonempty META segment preserving the
relation, and the corollaries are the campaign's remaining prizes:

* `sim_run` / `sim_diverge` — **two-sided behavior transfer**: the
  META run converges exactly when the direct run does, with
  representing values (`adequacy_ctl`, `meta_diverges_iff`).
* `tower_step` — **one interpretation layer, as a theorem**: for
  every eqv-free closed program with a terminating run, the closed
  program `META ⬝ ⌜p⌝` also terminates, with a representing value.
  Its input conditions are re-established by its own conclusion, so
  it composes with itself:
* `tower` — **the tower collapses at every height**: every finite
  iterate `META ⬝ ⌜META ⬝ ⌜⋯ ⌜p⌝⋯⌝⌝` terminates, each level's value
  representing the one below. The two-level demo of the machine
  rung becomes the `k = 2` instance of an induction.

The relations: `KRel` pairs each direct continuation frame with the
corresponding certified transformer applied at related pieces —
continuation representation *is* the dispatch architecture; there
is nothing else to say about a continuation than which certified
segment rebuilds it. `RepVc` is rung 2's relation with `KRel` at
the `kont` clause and interpretability (`EqvFree`) carried on
closure bodies. `callcc`'s case hands the `KRel` evidence over
directly — the kit proved capture is *literally* the base
continuation — and the throw case is the machine's cont-application
arm one level up.

Well-formedness (`WfV6`/`WfK6`, now covering continuations) rides
along only to discharge the in-bounds obligation at the read — the
same honest boundary as rungs 5/5½, closed the same way.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyControl

open FactorizationEqv MetaImage AdequacyStartup AdequacyRep AdequacyLeaf
  AdequacySim AdequacyData AdequacyStoreKit AdequacyStore AdequacyCtlKit
  AdequacyEntry

/-! ## The relations -/

mutual
  /-- Tagged value represents direct value — rung 2's clauses, with
      interpretability on closure bodies and `KRel` at `kont`. -/
  inductive RepVc (ρ₀ : Env) : Val → Val → Prop where
    | elem (k : Fin 8) : RepVc ρ₀ (.cell (.elem 2) (.elem k)) (.elem k)
    | clos {ρT : Val} {ρ : Env} (b : Prog) :
        EqvFree b → RepEnvc ρ₀ ρT ρ →
        RepVc ρ₀ (.cell (.elem 3) (.cell (quoteD b) ρT)) (.clos b ρ)
    | kont {κm κ : Kont} : KRel ρ₀ κm κ →
        RepVc ρ₀ (.cell (.elem 4) (.cont κm)) (.cont κ)
    | loc (i : Nat) :
        RepVc ρ₀ (.cell (.elem 5) (.loc (14 + i))) (.loc i)
    | cell {aT dT a d : Val} : RepVc ρ₀ aT a → RepVc ρ₀ dT d →
        RepVc ρ₀ (.cell (.elem 6) (.cell aT dT)) (.cell a d)

  /-- Tagged environments: cons chains ending in `tt`. -/
  inductive RepEnvc (ρ₀ : Env) : Val → Env → Prop where
    | nil : RepEnvc ρ₀ (.elem 0) []
    | cons {vT ρT : Val} {v : Val} {ρ : Env} :
        RepVc ρ₀ vT v → RepEnvc ρ₀ ρT ρ →
        RepEnvc ρ₀ (.cell vT ρT) (v :: ρ)

  /-- **The continuation relation**: each direct frame paired with
      the certified transformer applied at related pieces. Dead
      transformer parameters are constructor arguments. -/
  inductive KRel (ρ₀ : Env) : Kont → Kont → Prop where
    | halt : KRel ρ₀ .halt .halt
    | appL {x : Prog} {ρ : Env} {ρT qf : Val} {κm κ : Kont} :
        EqvFree x → RepEnvc ρ₀ ρT ρ → KRel ρ₀ κm κ →
        KRel ρ₀ (appKf ρ₀ qf (quoteD x) ρT κm) (.appL x ρ κ)
    | appR {vf qf qx ρT vfT : Val} {κm κ : Kont} :
        RepVc ρ₀ vfT vf → KRel ρ₀ κm κ →
        KRel ρ₀ (appKx ρ₀ qf qx ρT vfT κm) (.appR vf κ)
    | refK {κm κ : Kont} : KRel ρ₀ κm κ →
        KRel ρ₀ (.refK (.consR (.elem 5) κm)) (.refK κ)
    | derefK {qe ρT : Val} {κm κ : Kont} : KRel ρ₀ κm κ →
        KRel ρ₀ (derefKf ρ₀ qe ρT κm) (.derefK κ)
    | setL {e : Prog} {ρ : Env} {ql ρT : Val} {κm κ : Kont} :
        EqvFree e → RepEnvc ρ₀ ρT ρ → KRel ρ₀ κm κ →
        KRel ρ₀ (setKl ρ₀ ql (quoteD e) ρT κm) (.setL e ρ κ)
    | setR {vl ql qe ρT vlT : Val} {κm κ : Kont} :
        RepVc ρ₀ vlT vl → KRel ρ₀ κm κ →
        KRel ρ₀ (setKx ρ₀ ql qe ρT vlT κm) (.setR vl κ)
    | consL {b : Prog} {ρ : Env} {qa ρT : Val} {κm κ : Kont} :
        EqvFree b → RepEnvc ρ₀ ρT ρ → KRel ρ₀ κm κ →
        KRel ρ₀ (consKf ρ₀ qa (quoteD b) ρT κm) (.consL b ρ κ)
    | consR {va qa qb ρT vaT : Val} {κm κ : Kont} :
        RepVc ρ₀ vaT va → KRel ρ₀ κm κ →
        KRel ρ₀ (consKx ρ₀ qa qb ρT vaT κm) (.consR va κ)
    | carK {qe ρT : Val} {κm κ : Kont} : KRel ρ₀ κm κ →
        KRel ρ₀ (carKf ρ₀ qe ρT κm) (.carK κ)
    | cdrK {qe ρT : Val} {κm κ : Kont} : KRel ρ₀ κm κ →
        KRel ρ₀ (cdrKf ρ₀ qe ρT κm) (.cdrK κ)
    | pairK {qe ρT : Val} {κm κ : Kont} : KRel ρ₀ κm κ →
        KRel ρ₀ (pairKf ρ₀ qe ρT κm) (.pairK κ)
    | iteK {t e : Prog} {ρ : Env} {qc ρT : Val} {κm κ : Kont} :
        EqvFree t → EqvFree e → RepEnvc ρ₀ ρT ρ → KRel ρ₀ κm κ →
        KRel ρ₀ (iteKf ρ₀ qc (quoteD t) (quoteD e) ρT κm)
          (.iteK t e ρ κ)
end

/-- The state relation: a direct state and its META image. -/
inductive SRel (ρ₀ : Env) : State → State → Prop where
  | eval {p : Prog} {ρ : Env} {σ : Store} {κ : Kont}
      {ρT : Val} {σT : Store} {κm : Kont} :
      EqvFree p → RepEnvc ρ₀ ρT ρ →
      List.Forall₂ (RepVc ρ₀) σT σ → KRel ρ₀ κm κ →
      SRel ρ₀ (mevalCallS ρ₀ σT (quoteD p) ρT κm) (.eval p ρ σ κ)
  | ret {v : Val} {σ : Store} {κ : Kont}
      {vT : Val} {σT : Store} {κm : Kont} :
      RepVc ρ₀ vT v → List.Forall₂ (RepVc ρ₀) σT σ → KRel ρ₀ κm κ →
      SRel ρ₀ (.ret vT (knotStoreF ρ₀ ++ σT) κm) (.ret v σ κ)

/-! ### Right-side inversions -/

theorem elemRc {ρ₀ : Env} {vT : Val} {k : Fin 8}
    (h : RepVc ρ₀ vT (.elem k)) :
    vT = .cell (.elem 2) (.elem k) := by
  cases h; rfl

theorem closRc {ρ₀ : Env} {vT : Val} {b : Prog} {ρ : Env}
    (h : RepVc ρ₀ vT (.clos b ρ)) :
    ∃ ρT, vT = .cell (.elem 3) (.cell (quoteD b) ρT) ∧
      EqvFree b ∧ RepEnvc ρ₀ ρT ρ := by
  cases h with | clos _ hb hρ => exact ⟨_, rfl, hb, hρ⟩

theorem kontRc {ρ₀ : Env} {vT : Val} {κ : Kont}
    (h : RepVc ρ₀ vT (.cont κ)) :
    ∃ κm, vT = .cell (.elem 4) (.cont κm) ∧ KRel ρ₀ κm κ := by
  cases h with | kont hκ => exact ⟨_, rfl, hκ⟩

theorem locRc {ρ₀ : Env} {vT : Val} {l : Nat}
    (h : RepVc ρ₀ vT (.loc l)) :
    vT = .cell (.elem 5) (.loc (14 + l)) := by
  cases h; rfl

theorem cellRc {ρ₀ : Env} {vT a d : Val}
    (h : RepVc ρ₀ vT (.cell a d)) :
    ∃ aT dT, vT = .cell (.elem 6) (.cell aT dT) ∧
      RepVc ρ₀ aT a ∧ RepVc ρ₀ dT d := by
  cases h with | cell ha hd => exact ⟨_, _, rfl, ha, hd⟩

/-! ### Environment lookup and store plumbing -/

theorem chainNthc {ρ₀ : Env} :
    ∀ {ρT : Val} {ρ : Env}, RepEnvc ρ₀ ρT ρ →
      ∀ n, RepVc ρ₀ (chainNth ρT n) (ρ.getD n (.elem 0))
  | _, _, .nil, n => by
    simp only [chainNth, List.getD]
    exact .elem 0
  | _, _, .cons hv hρ, 0 => by simpa [chainNth] using hv
  | _, _, .cons hv hρ, n + 1 => by
    simpa [chainNth] using chainNthc hρ n

theorem forall₂_getDc {ρ₀ : Env} {σT σ : Store}
    (hF : List.Forall₂ (RepVc ρ₀) σT σ)
    {n : Nat} (hn : n < σ.length) (d d' : Val) :
    RepVc ρ₀ (σT.getD n d) (σ.getD n d') := by
  have h : σ[n]? = some σ[n] := List.getElem?_eq_getElem hn
  obtain ⟨vT', hvT', hR⟩ := forall₂_getElem? hF h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h, hvT']
  exact hR

/-- `mnth` simulates `chainNth` against `RepEnvc` (the kit's
    segments are representation-agnostic). -/
theorem mnth_simc (ρ₀ : Env) (σ' : Store) :
    ∀ (n : Nat) {ρT : Val} {ρ : Env}, RepEnvc ρ₀ ρT ρ →
      ∀ κ : Kont,
      ∃ m, stepIter m (mnthCallS ρ₀ σ' ρT (natToVal n) κ) =
        .inl (.ret (chainNth ρT n) (knotStoreF ρ₀ ++ σ') κ) := by
  intro n
  induction n with
  | zero =>
    intro ρT ρ hρ κ
    cases hρ with
    | nil => exact ⟨10, mnth_nil_S ρ₀ σ' _ κ⟩
    | cons hv hρ' => exact ⟨13, mnth_zero_S ρ₀ σ' _ _ κ⟩
  | succ n ih =>
    intro ρT ρ hρ κ
    cases hρ with
    | nil => exact ⟨10, mnth_nil_S ρ₀ σ' _ κ⟩
    | cons hv hρ' =>
      obtain ⟨m, hm⟩ := ih hρ' κ
      exact ⟨31 + m, stepIter_chain (mnth_succ_S ρ₀ σ' _ _ _ κ) hm⟩

theorem atomSteps_pos (a : Fin 8) : 0 < atomSteps a := by
  fin_cases a <;> decide

/-! ## Well-formedness, continuations included -/

mutual
  def WfV6 (m : Nat) : Val → Prop
    | .elem _ => True
    | .cell a d => WfV6 m a ∧ WfV6 m d
    | .clos _ ρ => WfVs6 m ρ
    | .cont κ => WfK6 m κ
    | .loc i => i < m

  def WfVs6 (m : Nat) : List Val → Prop
    | [] => True
    | v :: vs => WfV6 m v ∧ WfVs6 m vs

  def WfK6 (m : Nat) : Kont → Prop
    | .halt => True
    | .appL _ ρ k => WfVs6 m ρ ∧ WfK6 m k
    | .appR v k => WfV6 m v ∧ WfK6 m k
    | .refK k => WfK6 m k
    | .derefK k => WfK6 m k
    | .setL _ ρ k => WfVs6 m ρ ∧ WfK6 m k
    | .setR v k => WfV6 m v ∧ WfK6 m k
    | .consL _ ρ k => WfVs6 m ρ ∧ WfK6 m k
    | .consR v k => WfV6 m v ∧ WfK6 m k
    | .carK k => WfK6 m k
    | .cdrK k => WfK6 m k
    | .pairK k => WfK6 m k
    | .iteK _ _ ρ k => WfVs6 m ρ ∧ WfK6 m k
    | .eqvL _ ρ k => WfVs6 m ρ ∧ WfK6 m k
    | .eqvR v k => WfV6 m v ∧ WfK6 m k
end

mutual
  theorem wfV6_mono {m m' : Nat} (h : m ≤ m') :
      ∀ v, WfV6 m v → WfV6 m' v
    | .elem _, _ => trivial
    | .cell a d, ⟨ha, hd⟩ => ⟨wfV6_mono h a ha, wfV6_mono h d hd⟩
    | .clos _ ρ, hρ => wfVs6_mono h ρ hρ
    | .cont κ, hκ => wfK6_mono h κ hκ
    | .loc _, hi => Nat.lt_of_lt_of_le hi h

  theorem wfVs6_mono {m m' : Nat} (h : m ≤ m') :
      ∀ ρ, WfVs6 m ρ → WfVs6 m' ρ
    | [], _ => trivial
    | v :: vs, ⟨hv, hvs⟩ => ⟨wfV6_mono h v hv, wfVs6_mono h vs hvs⟩

  theorem wfK6_mono {m m' : Nat} (h : m ≤ m') :
      ∀ κ, WfK6 m κ → WfK6 m' κ
    | .halt, _ => trivial
    | .appL _ ρ k, ⟨hρ, hk⟩ => ⟨wfVs6_mono h ρ hρ, wfK6_mono h k hk⟩
    | .appR v k, ⟨hv, hk⟩ => ⟨wfV6_mono h v hv, wfK6_mono h k hk⟩
    | .refK k, hk => wfK6_mono h k hk
    | .derefK k, hk => wfK6_mono h k hk
    | .setL _ ρ k, ⟨hρ, hk⟩ => ⟨wfVs6_mono h ρ hρ, wfK6_mono h k hk⟩
    | .setR v k, ⟨hv, hk⟩ => ⟨wfV6_mono h v hv, wfK6_mono h k hk⟩
    | .consL _ ρ k, ⟨hρ, hk⟩ => ⟨wfVs6_mono h ρ hρ, wfK6_mono h k hk⟩
    | .consR v k, ⟨hv, hk⟩ => ⟨wfV6_mono h v hv, wfK6_mono h k hk⟩
    | .carK k, hk => wfK6_mono h k hk
    | .cdrK k, hk => wfK6_mono h k hk
    | .pairK k, hk => wfK6_mono h k hk
    | .iteK _ _ ρ k, ⟨hρ, hk⟩ => ⟨wfVs6_mono h ρ hρ, wfK6_mono h k hk⟩
    | .eqvL _ ρ k, ⟨hρ, hk⟩ => ⟨wfVs6_mono h ρ hρ, wfK6_mono h k hk⟩
    | .eqvR v k, ⟨hv, hk⟩ => ⟨wfV6_mono h v hv, wfK6_mono h k hk⟩
end

theorem wfVs6_getD {m : Nat} :
    ∀ {ρ : List Val}, WfVs6 m ρ → ∀ n, WfV6 m (ρ.getD n (.elem 0))
  | [], _, _ => trivial
  | _ :: _, ⟨hv, _⟩, 0 => hv
  | _ :: vs, ⟨_, hvs⟩, n + 1 => wfVs6_getD (ρ := vs) hvs n

theorem wfVs6_set {m : Nat} {w : Val} (hw : WfV6 m w) :
    ∀ {ρ : List Val}, WfVs6 m ρ → ∀ n, WfVs6 m (ρ.set n w)
  | [], _, _ => trivial
  | _ :: _, ⟨_, hvs⟩, 0 => ⟨hw, hvs⟩
  | _ :: vs, ⟨hv, hvs⟩, n + 1 => ⟨hv, wfVs6_set hw (ρ := vs) hvs n⟩

theorem wfVs6_append {m : Nat} {w : Val} (hw : WfV6 m w) :
    ∀ {ρ : List Val}, WfVs6 m ρ → WfVs6 m (ρ ++ [w])
  | [], _ => ⟨hw, trivial⟩
  | _ :: vs, ⟨hv, hvs⟩ => ⟨hv, wfVs6_append hw (ρ := vs) hvs⟩

/-- Well-formed machine states. -/
def WfStat : State → Prop
  | .eval _ ρ σ κ => WfVs6 σ.length ρ ∧ WfVs6 σ.length σ ∧ WfK6 σ.length κ
  | .ret v σ κ => WfV6 σ.length v ∧ WfVs6 σ.length σ ∧ WfK6 σ.length κ

/-- One machine step preserves well-formedness. -/
theorem step_wf : ∀ {s s' : State}, step s = .inl s' → WfStat s → WfStat s' := by
  intro s s' hs hw
  cases s with
  | eval p ρ σ κ =>
    obtain ⟨hρ, hσ, hκ⟩ := hw
    cases p with
    | atom a => cases hs; exact ⟨trivial, hσ, hκ⟩
    | var n => cases hs; exact ⟨wfVs6_getD hρ n, hσ, hκ⟩
    | lam b => cases hs; exact ⟨hρ, hσ, hκ⟩
    | app f x => cases hs; exact ⟨hρ, hσ, hρ, hκ⟩
    | callcc b => cases hs; exact ⟨⟨hκ, hρ⟩, hσ, hκ⟩
    | ref e => cases hs; exact ⟨hρ, hσ, hκ⟩
    | deref e => cases hs; exact ⟨hρ, hσ, hκ⟩
    | setref l e => cases hs; exact ⟨hρ, hσ, hρ, hκ⟩
    | cons a b => cases hs; exact ⟨hρ, hσ, hρ, hκ⟩
    | car e => cases hs; exact ⟨hρ, hσ, hκ⟩
    | cdr e => cases hs; exact ⟨hρ, hσ, hκ⟩
    | pairp e => cases hs; exact ⟨hρ, hσ, hκ⟩
    | ite c t e => cases hs; exact ⟨hρ, hσ, hρ, hκ⟩
    | eqv a b => cases hs; exact ⟨hρ, hσ, hρ, hκ⟩
  | ret v σ κ =>
    obtain ⟨hv, hσ, hκ⟩ := hw
    cases κ with
    | halt => simp [step] at hs
    | appL x ρ' k =>
      cases hs
      obtain ⟨hρ', hk⟩ := hκ
      exact ⟨hρ', hσ, hv, hk⟩
    | appR f k =>
      obtain ⟨hf, hk⟩ := hκ
      cases f with
      | clos b ρ' => cases hs; exact ⟨⟨hv, hf⟩, hσ, hk⟩
      | cont k' => cases hs; exact ⟨hv, hσ, hf⟩
      | elem a =>
        cases v <;> cases hs <;> exact ⟨trivial, hσ, hk⟩
      | cell a d => cases v <;> cases hs <;> exact ⟨trivial, hσ, hk⟩
      | loc l => cases v <;> cases hs <;> exact ⟨trivial, hσ, hk⟩
    | refK k =>
      cases hs
      refine ⟨?_, ?_, ?_⟩
      · rw [List.length_append]
        exact Nat.lt_succ_self _
      · rw [List.length_append]
        exact wfVs6_append (wfV6_mono (by simp) v hv)
          (wfVs6_mono (by simp) σ hσ)
      · rw [List.length_append]
        exact wfK6_mono (by simp) _ hκ
    | derefK k =>
      cases v with
      | loc n => cases hs; exact ⟨wfVs6_getD hσ n, hσ, hκ⟩
      | elem k' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | cell a d => cases hs; exact ⟨trivial, hσ, hκ⟩
      | clos b ρ' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | cont k' => cases hs; exact ⟨trivial, hσ, hκ⟩
    | setL e ρ' k =>
      cases hs
      obtain ⟨hρ', hk⟩ := hκ
      exact ⟨hρ', hσ, hv, hk⟩
    | setR l k =>
      obtain ⟨hl, hk⟩ := hκ
      cases l with
      | loc n =>
        cases hs
        refine ⟨?_, ?_, ?_⟩
        · rw [List.length_set]; exact hv
        · rw [List.length_set]; exact wfVs6_set hv hσ n
        · rw [List.length_set]; exact hk
      | elem a => cases hs; exact ⟨trivial, hσ, hk⟩
      | cell a d => cases hs; exact ⟨trivial, hσ, hk⟩
      | clos b ρ' => cases hs; exact ⟨trivial, hσ, hk⟩
      | cont k' => cases hs; exact ⟨trivial, hσ, hk⟩
    | consL b ρ' k =>
      cases hs
      obtain ⟨hρ', hk⟩ := hκ
      exact ⟨hρ', hσ, hv, hk⟩
    | consR a k =>
      cases hs
      obtain ⟨ha, hk⟩ := hκ
      exact ⟨⟨ha, hv⟩, hσ, hk⟩
    | carK k =>
      cases v with
      | cell a d => cases hs; exact ⟨hv.1, hσ, hκ⟩
      | elem k' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | clos b ρ' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | cont k' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | loc n => cases hs; exact ⟨trivial, hσ, hκ⟩
    | cdrK k =>
      cases v with
      | cell a d => cases hs; exact ⟨hv.2, hσ, hκ⟩
      | elem k' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | clos b ρ' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | cont k' => cases hs; exact ⟨trivial, hσ, hκ⟩
      | loc n => cases hs; exact ⟨trivial, hσ, hκ⟩
    | pairK k =>
      cases v <;> cases hs <;> exact ⟨trivial, hσ, hκ⟩
    | iteK t e ρ' k =>
      obtain ⟨hρ', hk⟩ := hκ
      cases v <;> cases hs <;> exact ⟨hρ', hσ, hk⟩
    | eqvL b ρ' k =>
      cases hs
      obtain ⟨hρ', hk⟩ := hκ
      exact ⟨hρ', hσ, hv, hk⟩
    | eqvR u k =>
      cases hs
      obtain ⟨hu, hk⟩ := hκ
      refine ⟨?_, hσ, hk⟩
      unfold eqvVal
      cases u <;> cases v <;> simp <;> try trivial
      all_goals split <;> trivial

/-! ## The simulation -/

/-- **One direct step, one META segment.** Every machine step from
    a related, well-formed state is matched by a nonempty META
    segment landing in the relation again. The dispatch kit
    provides every segment; the relation's constructors provide
    every frame. -/
theorem sim_step {ρ₀ : Env} {sm sd sd' : State}
    (hR : SRel ρ₀ sm sd) (hw : WfStat sd)
    (hs : step sd = .inl sd') :
    ∃ n sm', 0 < n ∧ stepIter n sm = .inl sm' ∧ SRel ρ₀ sm' sd' := by
  cases hR with
  | @eval p ρ σ κ ρT σT κm hp hρ hσ hκ =>
    cases p with
    | atom a =>
      cases hs
      exact ⟨atomSteps a, _, atomSteps_pos a,
        meval_atom_S ρ₀ σT a ρT κm, .ret (.elem a) hσ hκ⟩
    | var n =>
      cases hs
      obtain ⟨m, hm⟩ := mnth_simc ρ₀ σT n hρ κm
      exact ⟨116 + m, _, by omega,
        stepIter_chain (meval_var_dispatch_S ρ₀ σT (natToVal n) ρT κm) hm,
        .ret (chainNthc hρ n) hσ hκ⟩
    | lam b =>
      cases hs
      exact ⟨115, _, by omega, meval_lam_S ρ₀ σT (quoteD b) ρT κm,
        .ret (.clos b hp hρ) hσ hκ⟩
    | app f x =>
      cases hs
      exact ⟨129, _, by omega,
        meval_app_f_S ρ₀ σT (quoteD f) (quoteD x) ρT κm,
        .eval hp.1 hρ hσ (.appL hp.2 hρ hκ)⟩
    | callcc b =>
      cases hs
      exact ⟨132, _, by omega, meval_callcc_S ρ₀ σT (quoteD b) ρT κm,
        .eval hp (.cons (.kont hκ) hρ) hσ hκ⟩
    | ref e =>
      cases hs
      exact ⟨194, _, by omega, meval_ref_e_S ρ₀ σT (quoteD e) ρT κm,
        .eval hp hρ hσ (.refK hκ)⟩
    | deref e =>
      cases hs
      exact ⟨193, _, by omega, meval_deref_e_S ρ₀ σT (quoteD e) ρT κm,
        .eval hp hρ hσ (.derefK hκ)⟩
    | setref l e =>
      cases hs
      exact ⟨188, _, by omega,
        meval_set_l_S ρ₀ σT (quoteD l) (quoteD e) ρT κm,
        .eval hp.1 hρ hσ (.setL hp.2 hρ hκ)⟩
    | cons a b =>
      cases hs
      exact ⟨223, _, by omega,
        meval_cons_a_S ρ₀ σT (quoteD a) (quoteD b) ρT κm,
        .eval hp.1 hρ hσ (.consL hp.2 hρ hκ)⟩
    | car e =>
      cases hs
      exact ⟨220, _, by omega, meval_car_e_S ρ₀ σT (quoteD e) ρT κm,
        .eval hp hρ hσ (.carK hκ)⟩
    | cdr e =>
      cases hs
      exact ⟨213, _, by omega, meval_cdr_e_S ρ₀ σT (quoteD e) ρT κm,
        .eval hp hρ hσ (.cdrK hκ)⟩
    | pairp e =>
      cases hs
      exact ⟨186, _, by omega, meval_pairp_e_S ρ₀ σT (quoteD e) ρT κm,
        .eval hp hρ hσ (.pairK hκ)⟩
    | ite c t e =>
      cases hs
      exact ⟨188, _, by omega,
        meval_ite_c_S ρ₀ σT (quoteD c) (quoteD t) (quoteD e) ρT κm,
        .eval hp.1 hρ hσ (.iteK hp.2.1 hp.2.2 hρ hκ)⟩
    | eqv a b => exact hp.elim
  | @ret v σ κ vT σT κm hv hσ hκ =>
    cases hκ with
    | halt => simp [step] at hs
    | @appL x ρ' ρT' qf κm' κ' hx hρ' hκ' =>
      cases hs
      exact ⟨29, _, by omega,
        meval_app_x_S ρ₀ σT qf (quoteD x) ρT' vT κm',
        .eval hx hρ' hσ (.appR hv hκ')⟩
    | @appR vf qf qx ρT' vfT κm' κ' hvf hκ' =>
      cases vf with
      | clos b ρ'' =>
        cases hs
        obtain ⟨ρTf, rfl, hb, hρ''⟩ := closRc hvf
        exact ⟨214, _, by omega,
          mapply_clos_S ρ₀ σT qf qx ρT' (quoteD b) ρTf vT κm',
          .eval hb (.cons hv hρ'') hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, hκ''⟩ := kontRc hvf
        exact ⟨260, _, by omega,
          mapply_shf_S ρ₀ σT qf qx ρT' vT κm'' κm',
          .ret hv hσ hκ''⟩
      | elem a =>
        obtain rfl := elemRc hvf
        cases v with
        | elem b =>
          cases hs
          obtain rfl := elemRc hv
          exact ⟨198, _, by omega,
            mapply_elem_elem_S ρ₀ σT qf qx ρT' a b κm',
            .ret (.elem (dotA8 a b)) hσ hκ'⟩
        | clos b' ρ'' =>
          cases hs
          obtain ⟨ρTx, rfl, _, _⟩ := closRc hv
          exact ⟨190, _, by omega,
            mapply_elem_clos_S ρ₀ σT qf qx ρT' (quoteD b') ρTx a κm',
            .ret (.elem 0) hσ hκ'⟩
        | cell a' d' =>
          cases hs
          obtain ⟨aT, dT, rfl, _, _⟩ := cellRc hv
          exact ⟨149, _, by omega,
            mapply_elem_cell_S ρ₀ σT qf qx ρT' aT dT a κm',
            .ret (.elem 0) hσ hκ'⟩
        | loc l' =>
          cases hs
          obtain rfl := locRc hv
          exact ⟨149, _, by omega,
            mapply_elem_loc_S ρ₀ σT qf qx ρT' a (14 + l') κm',
            .ret (.elem 0) hσ hκ'⟩
        | cont κ'' =>
          cases hs
          obtain ⟨κm'', rfl, _⟩ := kontRc hv
          exact ⟨183, _, by omega,
            mapply_elem_shf_S ρ₀ σT qf qx ρT' a κm'' κm',
            .ret (.elem 0) hσ hκ'⟩
      | cell a' d' =>
        cases hs
        obtain ⟨aT, dT, rfl, _, _⟩ := cellRc hvf
        exact ⟨159, _, by omega,
          mapply_cellf_S ρ₀ σT qf qx ρT' aT dT vT κm',
          .ret (.elem 0) hσ hκ'⟩
      | loc l' =>
        cases hs
        obtain rfl := locRc hvf
        exact ⟨159, _, by omega,
          mapply_locf_S ρ₀ σT qf qx ρT' vT (14 + l') κm',
          .ret (.elem 0) hσ hκ'⟩
    | @refK κm' κ' hκ' =>
      cases hs
      have hlen : (knotStoreF ρ₀ ++ σT).length = 14 + σ.length := by
        rw [List.length_append, knot_length ρ₀, hσ.length_eq]
      have run2 := ref_alloc (knotStoreF ρ₀ ++ σT) vT κm'
      rw [hlen, List.append_assoc] at run2
      exact ⟨2, _, by omega, run2,
        .ret (.loc σ.length)
          (forall₂_append hσ (List.Forall₂.cons hv List.Forall₂.nil))
          hκ'⟩
    | @derefK qe ρT' κm' κ' hκ' =>
      cases v with
      | loc n =>
        cases hs
        obtain rfl := locRc hv
        have hn : n < σ.length := hw.1
        have hget : (knotStoreF ρ₀ ++ σT).getD (14 + n) (.elem 0) =
            σT.getD n (.elem 0) := by
          have h := getD_append_right' (knotStoreF ρ₀) σT n (.elem 0)
          rwa [knot_length ρ₀] at h
        have run2 := stepIter_chain
          (deref_pre_S ρ₀ σT qe ρT' (14 + n) κm')
          (deref_read (knotStoreF ρ₀ ++ σT) (14 + n) κm')
        rw [hget] at run2
        exact ⟨63 + 1, _, by omega, run2,
          .ret (forall₂_getDc hσ hn _ _) hσ hκ'⟩
      | elem k =>
        cases hs
        obtain rfl := elemRc hv
        exact ⟨57, _, by omega, mderef_elem_S ρ₀ σT qe ρT' k κm',
          .ret (.elem 0) hσ hκ'⟩
      | clos b' ρ'' =>
        cases hs
        obtain ⟨ρTx, rfl, _, _⟩ := closRc hv
        exact ⟨57, _, by omega,
          mderef_clos_S ρ₀ σT qe ρT' (quoteD b') ρTx κm',
          .ret (.elem 0) hσ hκ'⟩
      | cell a' d' =>
        cases hs
        obtain ⟨aT, dT, rfl, _, _⟩ := cellRc hv
        exact ⟨64, _, by omega, mderef_cell_S ρ₀ σT qe ρT' aT dT κm',
          .ret (.elem 0) hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, _⟩ := kontRc hv
        exact ⟨57, _, by omega, mderef_shf_S ρ₀ σT qe ρT' κm'' κm',
          .ret (.elem 0) hσ hκ'⟩
    | @setL e ρ' ql ρT' κm' κ' he hρ' hκ' =>
      cases hs
      exact ⟨23, _, by omega,
        meval_set_x_S ρ₀ σT ql (quoteD e) ρT' vT κm',
        .eval he hρ' hσ (.setR hv hκ')⟩
    | @setR vl ql qe ρT' vlT κm' κ' hvl hκ' =>
      cases vl with
      | loc n =>
        cases hs
        obtain rfl := locRc hvl
        have hset : (knotStoreF ρ₀ ++ σT).set (14 + n) vT =
            knotStoreF ρ₀ ++ σT.set n vT := by
          have h := set_append_right' (knotStoreF ρ₀) σT n vT
          rwa [knot_length ρ₀] at h
        have run2 := stepIter_chain
          (set_pre_S ρ₀ σT ql qe ρT' vT (14 + n) κm')
          (stepIter_chain
            (set_fire (knotStoreF ρ₀ ++ σT) vT (14 + n)
              (setKp ρ₀ ql qe ρT' vT (14 + n) κm'))
            (set_post_S ρ₀ ((knotStoreF ρ₀ ++ σT).set (14 + n) vT)
              ql qe ρT' vT (14 + n) κm'))
        rw [hset] at run2
        exact ⟨68 + (1 + 2), _, by omega, run2,
          .ret hv (forall₂_set hσ hv) hκ'⟩
      | elem k =>
        cases hs
        obtain rfl := elemRc hvl
        exact ⟨57, _, by omega, mset_elem_S ρ₀ σT ql qe ρT' vT k κm',
          .ret (.elem 0) hσ hκ'⟩
      | clos b' ρ'' =>
        cases hs
        obtain ⟨ρTx, rfl, _, _⟩ := closRc hvl
        exact ⟨57, _, by omega,
          mset_clos_S ρ₀ σT ql qe ρT' (quoteD b') ρTx vT κm',
          .ret (.elem 0) hσ hκ'⟩
      | cell a' d' =>
        cases hs
        obtain ⟨aT, dT, rfl, _, _⟩ := cellRc hvl
        exact ⟨64, _, by omega,
          mset_cell_S ρ₀ σT ql qe ρT' aT dT vT κm',
          .ret (.elem 0) hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, _⟩ := kontRc hvl
        exact ⟨57, _, by omega,
          mset_shf_S ρ₀ σT ql qe ρT' vT κm'' κm',
          .ret (.elem 0) hσ hκ'⟩
    | @consL b ρ' qa ρT' κm' κ' hb hρ' hκ' =>
      cases hs
      exact ⟨20, _, by omega,
        meval_cons_b_S ρ₀ σT qa (quoteD b) ρT' vT κm',
        .eval hb hρ' hσ (.consR hv hκ')⟩
    | @consR va qa qb ρT' vaT κm' κ' hva hκ' =>
      cases hs
      exact ⟨2, _, by omega, cons_pack_S ρ₀ σT qa qb ρT' vaT vT κm',
        .ret (.cell hva hv) hσ hκ'⟩
    | @carK qe ρT' κm' κ' hκ' =>
      cases v with
      | cell u d =>
        cases hs
        obtain ⟨aT, dT, rfl, ha, hd⟩ := cellRc hv
        exact ⟨64, _, by omega, mcar_cell_S ρ₀ σT qe ρT' aT dT κm',
          .ret ha hσ hκ'⟩
      | elem k =>
        cases hs
        obtain rfl := elemRc hv
        exact ⟨57, _, by omega, mcar_elem_S ρ₀ σT qe ρT' k κm',
          .ret (.elem 0) hσ hκ'⟩
      | clos b' ρ'' =>
        cases hs
        obtain ⟨ρTx, rfl, _, _⟩ := closRc hv
        exact ⟨57, _, by omega,
          mcar_clos_S ρ₀ σT qe ρT' (quoteD b') ρTx κm',
          .ret (.elem 0) hσ hκ'⟩
      | loc l' =>
        cases hs
        obtain rfl := locRc hv
        exact ⟨64, _, by omega, mcar_loc_S ρ₀ σT qe ρT' (14 + l') κm',
          .ret (.elem 0) hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, _⟩ := kontRc hv
        exact ⟨57, _, by omega, mcar_shf_S ρ₀ σT qe ρT' κm'' κm',
          .ret (.elem 0) hσ hκ'⟩
    | @cdrK qe ρT' κm' κ' hκ' =>
      cases v with
      | cell u d =>
        cases hs
        obtain ⟨aT, dT, rfl, ha, hd⟩ := cellRc hv
        exact ⟨64, _, by omega, mcdr_cell_S ρ₀ σT qe ρT' aT dT κm',
          .ret hd hσ hκ'⟩
      | elem k =>
        cases hs
        obtain rfl := elemRc hv
        exact ⟨57, _, by omega, mcdr_elem_S ρ₀ σT qe ρT' k κm',
          .ret (.elem 0) hσ hκ'⟩
      | clos b' ρ'' =>
        cases hs
        obtain ⟨ρTx, rfl, _, _⟩ := closRc hv
        exact ⟨57, _, by omega,
          mcdr_clos_S ρ₀ σT qe ρT' (quoteD b') ρTx κm',
          .ret (.elem 0) hσ hκ'⟩
      | loc l' =>
        cases hs
        obtain rfl := locRc hv
        exact ⟨64, _, by omega, mcdr_loc_S ρ₀ σT qe ρT' (14 + l') κm',
          .ret (.elem 0) hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, _⟩ := kontRc hv
        exact ⟨57, _, by omega, mcdr_shf_S ρ₀ σT qe ρT' κm'' κm',
          .ret (.elem 0) hσ hκ'⟩
    | @pairK qe ρT' κm' κ' hκ' =>
      cases v with
      | cell u d =>
        cases hs
        obtain ⟨aT, dT, rfl, _, _⟩ := cellRc hv
        exact ⟨64, _, by omega, mpairp_cell_S ρ₀ σT qe ρT' aT dT κm',
          .ret (.elem 0) hσ hκ'⟩
      | elem k =>
        cases hs
        obtain rfl := elemRc hv
        exact ⟨57, _, by omega, mpairp_elem_S ρ₀ σT qe ρT' k κm',
          .ret (.elem 1) hσ hκ'⟩
      | clos b' ρ'' =>
        cases hs
        obtain ⟨ρTx, rfl, _, _⟩ := closRc hv
        exact ⟨57, _, by omega,
          mpairp_clos_S ρ₀ σT qe ρT' (quoteD b') ρTx κm',
          .ret (.elem 1) hσ hκ'⟩
      | loc l' =>
        cases hs
        obtain rfl := locRc hv
        exact ⟨64, _, by omega, mpairp_loc_S ρ₀ σT qe ρT' (14 + l') κm',
          .ret (.elem 1) hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, _⟩ := kontRc hv
        exact ⟨57, _, by omega, mpairp_shf_S ρ₀ σT qe ρT' κm'' κm',
          .ret (.elem 1) hσ hκ'⟩
    | @iteK t e ρ' qc ρT' κm' κ' ht he hρ' hκ' =>
      cases v with
      | elem b =>
        obtain rfl := elemRc hv
        by_cases hb : b = 1
        · subst hb
          cases hs
          exact ⟨119, _, by omega,
            mite_ff_S ρ₀ σT qc (quoteD t) (quoteD e) ρT' κm',
            .eval he hρ' hσ hκ'⟩
        · cases hs
          rw [if_neg hb]
          exact ⟨119, _, by omega,
            mite_elem_tt_S ρ₀ σT qc (quoteD t) (quoteD e) ρT' b hb κm',
            .eval ht hρ' hσ hκ'⟩
      | clos b' ρ'' =>
        cases hs
        obtain ⟨ρTx, rfl, _, _⟩ := closRc hv
        exact ⟨114, _, by omega,
          mite_clos_S ρ₀ σT qc (quoteD t) (quoteD e) ρT'
            (quoteD b') ρTx κm',
          .eval ht hρ' hσ hκ'⟩
      | cell a' d' =>
        cases hs
        obtain ⟨aT, dT, rfl, _, _⟩ := cellRc hv
        exact ⟨73, _, by omega,
          mite_cell_S ρ₀ σT qc (quoteD t) (quoteD e) ρT' aT dT κm',
          .eval ht hρ' hσ hκ'⟩
      | loc l' =>
        cases hs
        obtain rfl := locRc hv
        exact ⟨73, _, by omega,
          mite_loc_S ρ₀ σT qc (quoteD t) (quoteD e) ρT' (14 + l') κm',
          .eval ht hρ' hσ hκ'⟩
      | cont κ'' =>
        cases hs
        obtain ⟨κm'', rfl, _⟩ := kontRc hv
        exact ⟨107, _, by omega,
          mite_shf_S ρ₀ σT qc (quoteD t) (quoteD e) ρT' κm'' κm',
          .eval ht hρ' hσ hκ'⟩

/-! ## Behavior transfer -/

theorem stepIter_prefix {n : Nat} {s s' : State}
    (h : stepIter n s = .inl s') :
    ∀ {m : Nat}, m ≤ n → ∃ s'', stepIter m s = .inl s'' := by
  induction n generalizing s with
  | zero =>
    intro m hm
    cases Nat.le_zero.mp hm
    exact ⟨s, rfl⟩
  | succ n ih =>
    intro m hm
    cases m with
    | zero => exact ⟨s, rfl⟩
    | succ m =>
      simp only [stepIter] at h ⊢
      cases hstep : step s with
      | inl s₁ =>
        rw [hstep] at h
        exact ih h (Nat.succ_le_succ_iff.mp hm)
      | inr v => rw [hstep] at h; exact absurd h (by simp)

theorem loop_none_of_stepIter_inl {n : Nat} {s s' : State}
    (h : stepIter n s = .inl s') : loop n s = none := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [stepIter] at h
    simp only [loop]
    cases hstep : step s with
    | inl s₁ => rw [hstep] at h; exact ih h
    | inr v => rw [hstep] at h; exact absurd h (by simp)

theorem loop_none_down {m n : Nat} (hle : m ≤ n) {s : State}
    (h : loop n s = none) : loop m s = none := by
  cases hm : loop m s with
  | none => rfl
  | some w => rw [loop_mono_le hle hm] at h; exact absurd h (by simp)

/-- **Convergence transfers**: from a related, well-formed pair, a
    terminating direct run yields a terminating META run with a
    representing value. -/
theorem sim_run {ρ₀ : Env} :
    ∀ {n : Nat} {sm sd : State} {v : Val}, SRel ρ₀ sm sd →
      WfStat sd → loop n sd = some v →
      ∃ (m : Nat) (vT : Val), RepVc ρ₀ vT v ∧ loop m sm = some vT := by
  intro n
  induction n with
  | zero => intro sm sd v _ _ h; exact absurd h (by simp [loop])
  | succ n ih =>
    intro sm sd v hR hw h
    cases hstep : step sd with
    | inr w =>
      have hv : v = w := by
        simp only [loop, hstep] at h
        exact (Option.some.inj h).symm
      subst hv
      cases hR with
      | eval hp hρ hσ hκ =>
        rename_i p _ _ _ _ _ _
        cases p <;> simp [step] at hstep
      | @ret v' σ κ vT σT κm hv' hσ hκ =>
        cases hκ with
        | halt =>
          have : v' = v := by
            simpa [step] using hstep
          subst this
          exact ⟨1, vT, hv', by simp [loop, step]⟩
        | appL hx hρ' hκ' => simp [step] at hstep
        | appR hvf hκ' =>
          rename_i vf _ _ _ _ _ _
          cases vf <;> cases v' <;> simp [step] at hstep
        | refK hκ' => simp [step] at hstep
        | derefK hκ' => cases v' <;> simp [step] at hstep
        | setL he hρ' hκ' => simp [step] at hstep
        | setR hvl hκ' =>
          rename_i vl _ _ _ _ _ _
          cases vl <;> simp [step] at hstep
        | consL hb hρ' hκ' => simp [step] at hstep
        | consR hva hκ' => simp [step] at hstep
        | carK hκ' => cases v' <;> simp [step] at hstep
        | cdrK hκ' => cases v' <;> simp [step] at hstep
        | pairK hκ' => cases v' <;> simp [step] at hstep
        | iteK ht he hρ' hκ' => cases v' <;> simp [step] at hstep
    | inl sd' =>
      obtain ⟨k, sm', hk, hseg, hR'⟩ := sim_step hR hw hstep
      have hw' := step_wf hstep hw
      have h' : loop n sd' = some v := by
        simpa only [loop, hstep] using h
      obtain ⟨m, vT, rep, hm⟩ := ih hR' hw' h'
      exact ⟨m + k, vT, rep, by rw [loop_stepIter hseg]; exact hm⟩

/-- **Divergence transfers**: if the direct run never terminates,
    neither does the META run. -/
theorem sim_diverge {ρ₀ : Env} :
    ∀ (m : Nat) {sm sd : State}, SRel ρ₀ sm sd → WfStat sd →
      (∀ n, loop n sd = none) → loop m sm = none := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro sm sd hR hw hdiv
    cases m with
    | zero => rfl
    | succ m' =>
      cases hstep : step sd with
      | inr w =>
        have : loop 1 sd = some w := by simp [loop, hstep]
        rw [hdiv 1] at this
        exact absurd this (by simp)
      | inl sd' =>
        obtain ⟨k, sm', hk, hseg, hR'⟩ := sim_step hR hw hstep
        have hw' := step_wf hstep hw
        have hdiv' : ∀ n, loop n sd' = none := by
          intro n
          have := hdiv (n + 1)
          simpa only [loop, hstep] using this
        by_cases hmk : m' + 1 ≤ k
        · obtain ⟨s'', hpre⟩ := stepIter_prefix hseg hmk
          exact loop_none_of_stepIter_inl hpre
        · push_neg at hmk
          have hrest : loop (m' + 1 - k) sm' = none :=
            IH (m' + 1 - k) (by omega) hR' hw' hdiv'
          have : loop ((m' + 1 - k) + k) sm = loop (m' + 1 - k) sm' :=
            loop_stepIter hseg _
          rw [show m' + 1 = (m' + 1 - k) + k by omega, this]
          exact hrest

/-! ## Adequacy for the 13-form domain -/

/-- From the canonical initial state, the calling convention is
    reached in `entrySteps + 17` steps. -/
theorem entry_all (p : Prog) :
    stepIter (entrySteps + 17) (metaState p) =
      .inl (mevalCallS [quoteD p] [] (quoteD p) (.elem 0) .halt) :=
  stepIter_chain (meval_entry p) (call_entry_S p)

/-- **Adequacy for the full 13-form domain**: every eqv-free closed
    program with a terminating run has a terminating META run with
    a representing value — `callcc` included. -/
theorem adequacy_ctl {p : Prog} (hp : EqvFree p) {n : Nat} {v : Val}
    (h : runM n [] [] p = some v) :
    ∃ (m : Nat) (vT : Val), RepVc [quoteD p] vT v ∧
      loop m (metaState p) = some vT := by
  have hR : SRel [quoteD p]
      (mevalCallS [quoteD p] [] (quoteD p) (.elem 0) .halt)
      (.eval p [] [] .halt) :=
    .eval hp .nil List.Forall₂.nil .halt
  obtain ⟨m, vT, rep, hm⟩ :=
    sim_run (ρ₀ := [quoteD p]) hR ⟨trivial, trivial, trivial⟩ h
  refine ⟨m + (entrySteps + 17), vT, rep, ?_⟩
  rw [loop_stepIter (entry_all p)]
  exact hm

/-- **Divergence transfers to the interpreted world**: if the
    direct run diverges, META's run diverges. With `adequacy_ctl`,
    the two runs' behaviors agree in both directions. -/
theorem meta_diverges {p : Prog} (hp : EqvFree p)
    (hdiv : ∀ n, runM n [] [] p = none) :
    ∀ m, loop m (metaState p) = none := by
  intro m
  have hR : SRel [quoteD p]
      (mevalCallS [quoteD p] [] (quoteD p) (.elem 0) .halt)
      (.eval p [] [] .halt) :=
    .eval hp .nil List.Forall₂.nil .halt
  by_cases hme : m ≤ entrySteps + 17
  · obtain ⟨s'', hpre⟩ := stepIter_prefix (entry_all p) hme
    exact loop_none_of_stepIter_inl hpre
  · push_neg at hme
    have hrest : loop (m - (entrySteps + 17))
        (mevalCallS [quoteD p] [] (quoteD p) (.elem 0) .halt) = none :=
      sim_diverge _ hR ⟨trivial, trivial, trivial⟩ hdiv
    rw [show m = (m - (entrySteps + 17)) + (entrySteps + 17) by omega,
      loop_stepIter (entry_all p)]
    exact hrest

/-! ## The tower -/

/-- Quotation-shaped values: what `quoteD` produces. -/
inductive QShape : Val → Prop where
  | elem (k : Fin 8) : QShape (.elem k)
  | cell {a d : Val} : QShape a → QShape d → QShape (.cell a d)

theorem qshape_natToVal (n : Nat) : QShape (natToVal n) := by
  induction n with
  | zero => exact .elem 0
  | succ n ih => exact .cell (.elem 4) ih

theorem qshape_quoteD (p : Prog) : QShape (quoteD p) := by
  induction p with
  | atom a => exact .elem _
  | var n => exact .cell (.elem 4) (qshape_natToVal n)
  | lam b ih => exact .cell (.elem 2) ih
  | app f x ihf ihx => exact .cell (.elem 3) (.cell ihf ihx)
  | callcc b ih => exact .cell (.elem 6) ih
  | ref e ih => exact .cell (.elem 5) (.cell (.elem 2) ih)
  | deref e ih => exact .cell (.elem 5) (.cell (.elem 3) ih)
  | setref l e ihl ihe =>
    exact .cell (.elem 5) (.cell (.elem 4) (.cell ihl ihe))
  | cons a b iha ihb =>
    exact .cell (.elem 7) (.cell (.elem 2) (.cell iha ihb))
  | car e ih => exact .cell (.elem 7) (.cell (.elem 3) ih)
  | cdr e ih => exact .cell (.elem 7) (.cell (.elem 4) ih)
  | pairp e ih => exact .cell (.elem 7) (.cell (.elem 5) ih)
  | ite c t e ihc iht ihe =>
    exact .cell (.elem 7) (.cell (.elem 6) (.cell ihc (.cell iht ihe)))
  | eqv a b iha ihb =>
    exact .cell (.elem 7) (.cell (.elem 7) (.cell iha ihb))

/-- A quotation-shaped value as the program that rebuilds it. -/
def valProg : Val → Prog
  | .elem k => .atom k
  | .cell a d => .cons (valProg a) (valProg d)
  | _ => .atom 0

theorem valProg_eqvFree {v : Val} (h : QShape v) : EqvFree (valProg v) := by
  induction h with
  | elem k => trivial
  | cell _ _ iha ihd => exact ⟨iha, ihd⟩

theorem valProg_evs {v : Val} (h : QShape v) :
    ∀ (ρ : Env) (σ : Store), EvS (valProg v) ρ σ v σ := by
  induction h with
  | elem k => exact fun ρ σ => .atom k ρ σ
  | cell _ _ iha ihd => exact fun ρ σ => .cons (iha ρ σ) (ihd ρ σ)

/-- The tower program: META applied to the program that rebuilds
    `⌜q⌝` — a *closed* program, one interpretation layer up. -/
def towerP (q : Prog) : Prog := .app META (valProg (quoteD q))

theorem towerP_eqvFree (q : Prog) : EqvFree (towerP q) :=
  ⟨meta_eqvFree, valProg_eqvFree (qshape_quoteD q)⟩

/-- **One interpretation layer, as a theorem**: if an eqv-free
    closed program's run terminates, the closed program
    `META ⬝ ⌜p⌝` also terminates, with a value representing the
    original's. The hypotheses of this theorem are re-established
    by its conclusion, so it composes with itself. -/
theorem tower_step {q : Prog} (hq : EqvFree q) {n : Nat} {w : Val}
    (h : runM n [] [] q = some w) :
    ∃ (m : Nat) (wT : Val), RepVc [] wT w ∧
      runM m [] [] (towerP q) = some wT := by
  -- the direct run of the tower program, constructed in segments
  have h1 : stepIter 1 (.eval (towerP q) [] [] .halt) =
      .inl (.eval META [] []
        (.appL (valProg (quoteD q)) [] .halt)) := rfl
  have h2 := meta_startup [] (.appL (valProg (quoteD q)) [] .halt)
  have h3 : stepIter 1 (.ret (.clos metaBody (metaEnvF []))
      (knotStoreF []) (.appL (valProg (quoteD q)) [] .halt)) =
      .inl (.eval (valProg (quoteD q)) [] (knotStoreF [])
        (.appR (.clos metaBody (metaEnvF [])) .halt)) := rfl
  obtain ⟨nv, h4⟩ := evS_steps (valProg_evs (qshape_quoteD q) []
    (knotStoreF [])) (.appR (.clos metaBody (metaEnvF [])) .halt)
  have h5 : stepIter 1 (.ret (quoteD q) (knotStoreF [])
      (.appR (.clos metaBody (metaEnvF [])) .halt)) =
      .inl (.eval metaBody (quoteD q :: metaEnvF [])
        (knotStoreF []) .halt) := rfl
  have h6 := entry17 [] (quoteD q) .halt
  -- the simulated run of q at ρ₀ = []
  have hR : SRel [] (mevalCallS [] [] (quoteD q) (.elem 0) .halt)
      (.eval q [] [] .halt) :=
    .eval hq .nil List.Forall₂.nil .halt
  obtain ⟨m', wT, rep, hm'⟩ :=
    sim_run (ρ₀ := []) hR ⟨trivial, trivial, trivial⟩ h
  -- assemble
  have chain := stepIter_chain h1 (stepIter_chain h2
    (stepIter_chain h3 (stepIter_chain h4
      (stepIter_chain h5 h6))))
  refine ⟨m' + (1 + (startupSteps + (1 + (nv + (1 + 17))))), wT, rep, ?_⟩
  unfold runM
  rw [loop_stepIter chain]
  exact hm'

/-- The tower at height `k`: `META ⬝ ⌜META ⬝ ⌜⋯⌜p⌝⋯⌝⌝`. -/
def towerIter : Nat → Prog → Prog
  | 0, q => q
  | k + 1, q => towerP (towerIter k q)

theorem towerIter_eqvFree (k : Nat) {q : Prog} (hq : EqvFree q) :
    EqvFree (towerIter k q) := by
  induction k with
  | zero => exact hq
  | succ k ih => exact towerP_eqvFree _

/-- **The tower collapses at every height**: every finite iterate of
    interpretation terminates, each level's value representing the
    one below (adjacent levels related by `tower_step`). The
    two-level demonstration of the machine rung is the `k = 2`
    instance. -/
theorem tower (k : Nat) {q : Prog} (hq : EqvFree q) {n : Nat}
    {w : Val} (h : runM n [] [] q = some w) :
    ∃ (m : Nat) (wk : Val), runM m [] [] (towerIter k q) = some wk := by
  induction k generalizing n w with
  | zero => exact ⟨n, w, h⟩
  | succ k ih =>
    obtain ⟨m, wk, hm⟩ := ih h
    obtain ⟨m', wT, _, hm'⟩ :=
      tower_step (towerIter_eqvFree k hq) hm
    exact ⟨m', wT, hm'⟩

end AdequacyControl
end Dichotomic
