import Magma.AdequacyData

/-!
# Adequacy campaign, rung 5 (kit): the dispatch kit over live stores

Every dispatch lemma of rungs 3b(iv) and 4, restated over a store
with a **symbolic suffix** — `knotStoreF ρ₀ ++ σ'` — plus the new
segments for `ref`/`deref`/`setref`. The knot prefix's spine is
concrete, so kernel reduction walks it exactly as before while the
suffix rides as a passenger; each `rfl` below *certifies* that its
segment never touches the suffix. The committed continuation
transformers (`appKf`, `consKf`, …) are reused unchanged — they were
extracted at the bare knot store, and the `rfl`s here verify they
are suffix-independent.

The store forms' own segments, probe-discovered:

* **`ref`**: 194 dispatch steps to the operand's call under the
  *concrete* frames `refK · consR[quo-tag]` — no projection needed —
  then `ref_alloc`: the machine's own `refK` arm allocates at
  `σ.length` and one `consR` tags it, **at any store whatsoever**:
  the canonical location map `i ↦ K₀ + i` is the machine's
  allocation rule meeting the knot prefix, not a bookkeeping device.
* **`deref`**: 193 dispatch steps; then 63 steps from the tagged
  location's return to the *naked read* — the `derefK` frame sits
  directly on the caller's continuation (tail position), and
  `deref_read` is the machine's read arm with the index and store
  fully symbolic. Error arms (element/closure 57, cell 64) agree
  with the machine's default.
* **`setref`**: 188 steps to the location operand's call, 23 to the
  value operand's (the location value a passenger), then 68 steps
  to the *naked write*, the machine's `setR` arm with index, value,
  and store symbolic (`set_fire`), and a 2-step unwind over the
  (now symbolic) written store. Error arms agree.

This file is pure kit — the relation and the master induction live
in `AdequacyStore.lean`.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyStoreKit

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep
  AdequacyLeaf AdequacySim AdequacyData

/-! ## List helper -/

theorem getD_append_right' {α : Type*} (P l : List α) (i : Nat) (d : α) :
    (P ++ l).getD (P.length + i) d = l.getD i d := by
  induction P with
  | nil => simp
  | cons x P ih =>
    simpa [List.getD, Nat.succ_add] using ih

/-! ## Call states over live stores -/

/-- The `meval` calling convention over a suffixed store. -/
def mevalCallS (ρ₀ : Env) (σ' : Store) (q ρT : Val) (κ : Kont) : State :=
  match (knotStoreF ρ₀).getD 9 (.elem 0) with
  | .clos (.lam b) e => .eval b (ρT :: q :: e) (knotStoreF ρ₀ ++ σ') κ
  | _ => .ret (.elem 0) [] .halt

/-- The `mnth` calling convention over a suffixed store. -/
def mnthCallS (ρ₀ : Env) (σ' : Store) (ρT num : Val) (κ : Kont) : State :=
  match (knotStoreF ρ₀).getD 8 (.elem 0) with
  | .clos (.lam b) e => .eval b (num :: ρT :: e) (knotStoreF ρ₀ ++ σ') κ
  | _ => .ret (.elem 0) [] .halt

/-! ## The pure kit, suffixed -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
theorem meval_atom_S (ρ₀ : Env) (σ' : Store) (a : Fin 8) (ρT : Val)
    (κ : Kont) :
    stepIter (atomSteps a) (mevalCallS ρ₀ σ' (quoteD (.atom a)) ρT κ) =
      .inl (.ret (.cell (.elem 2) (.elem a)) (knotStoreF ρ₀ ++ σ') κ) := by
  fin_cases a <;> rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_lam_S (ρ₀ : Env) (σ' : Store) (qb ρT : Val) (κ : Kont) :
    stepIter 115 (mevalCallS ρ₀ σ' (.cell (.elem 2) qb) ρT κ) =
      .inl (.ret (.cell (.elem 3) (.cell qb ρT))
        (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_var_dispatch_S (ρ₀ : Env) (σ' : Store) (num ρT : Val)
    (κ : Kont) :
    stepIter 116 (mevalCallS ρ₀ σ' (.cell (.elem 4) num) ρT κ) =
      .inl (mnthCallS ρ₀ σ' ρT num κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mnth_nil_S (ρ₀ : Env) (σ' : Store) (num : Val) (κ : Kont) :
    stepIter 10 (mnthCallS ρ₀ σ' (.elem 0) num κ) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mnth_zero_S (ρ₀ : Env) (σ' : Store) (vT ρT' : Val) (κ : Kont) :
    stepIter 13 (mnthCallS ρ₀ σ' (.cell vT ρT') (.elem 0) κ) =
      .inl (.ret vT (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mnth_succ_S (ρ₀ : Env) (σ' : Store) (vT ρT' num : Val)
    (κ : Kont) :
    stepIter 31 (mnthCallS ρ₀ σ' (.cell vT ρT')
        (.cell (.elem 4) num) κ) =
      .inl (mnthCallS ρ₀ σ' ρT' num κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- `mnth` simulates `chainNth` over any live store. -/
theorem mnth_sim_S (ρ₀ : Env) (σ' : Store) :
    ∀ (n : Nat) {ρT : Val} {ρ : Env}, RepEnv 14 KRempty ρT ρ →
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

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_app_f_S (ρ₀ : Env) (σ' : Store) (qf qx ρT : Val)
    (κ : Kont) :
    stepIter 129 (mevalCallS ρ₀ σ'
        (.cell (.elem 3) (.cell qf qx)) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qf ρT (appKf ρ₀ qf qx ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_app_x_S (ρ₀ : Env) (σ' : Store) (qf qx ρT vfT : Val)
    (κ : Kont) :
    stepIter 29 (.ret vfT (knotStoreF ρ₀ ++ σ')
        (appKf ρ₀ qf qx ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qx ρT (appKx ρ₀ qf qx ρT vfT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_clos_S (ρ₀ : Env) (σ' : Store) (qf qx ρT qb ρT' vxT : Val)
    (κ : Kont) :
    stepIter 214 (.ret vxT (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 3) (.cell qb ρT')) κ)) =
      .inl (mevalCallS ρ₀ σ' qb (.cell vxT ρT') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_elem_pre_S (ρ₀ : Env) (σ' : Store) (qf qx ρT : Val)
    (a b : Fin 8) (κ : Kont) :
    stepIter 196 (.ret (.cell (.elem 2) (.elem b))
        (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.elem b) (knotStoreF ρ₀ ++ σ')
        (.appR (.elem a) (.consR (.elem 2) κ))) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- All 64 products over any live store (`elem_fire` was already
    store-generic). -/
theorem mapply_elem_elem_S (ρ₀ : Env) (σ' : Store) (qf qx ρT : Val)
    (a b : Fin 8) (κ : Kont) :
    stepIter 198 (.ret (.cell (.elem 2) (.elem b))
        (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem (dotA8 a b)))
        (knotStoreF ρ₀ ++ σ') κ) :=
  stepIter_chain (mapply_elem_pre_S ρ₀ σ' qf qx ρT a b κ)
    (elem_fire (knotStoreF ρ₀ ++ σ') a b κ)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_elem_clos_S (ρ₀ : Env) (σ' : Store) (qf qx ρT q' ρT' : Val)
    (a : Fin 8) (κ : Kont) :
    stepIter 190 (.ret (.cell (.elem 3) (.cell q' ρT'))
        (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_elem_cell_S (ρ₀ : Env) (σ' : Store) (qf qx ρT aT dT : Val)
    (a : Fin 8) (κ : Kont) :
    stepIter 149 (.ret (.cell (.elem 6) (.cell aT dT))
        (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_elem_loc_S (ρ₀ : Env) (σ' : Store) (qf qx ρT : Val)
    (a : Fin 8) (l : Nat) (κ : Kont) :
    stepIter 149 (.ret (.cell (.elem 5) (.loc l))
        (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 2) (.elem a)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_cellf_S (ρ₀ : Env) (σ' : Store) (qf qx ρT aT dT vxT : Val)
    (κ : Kont) :
    stepIter 159 (.ret vxT (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 6) (.cell aT dT)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mapply_locf_S (ρ₀ : Env) (σ' : Store) (qf qx ρT vxT : Val)
    (l : Nat) (κ : Kont) :
    stepIter 159 (.ret vxT (knotStoreF ρ₀ ++ σ')
        (appKx ρ₀ qf qx ρT (.cell (.elem 5) (.loc l)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

/-! ## The data kit, suffixed -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_cons_a_S (ρ₀ : Env) (σ' : Store) (qa qb ρT : Val)
    (κ : Kont) :
    stepIter 223 (mevalCallS ρ₀ σ'
        (.cell (.elem 7) (.cell (.elem 2) (.cell qa qb))) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qa ρT (consKf ρ₀ qa qb ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_cons_b_S (ρ₀ : Env) (σ' : Store) (qa qb ρT vaT : Val)
    (κ : Kont) :
    stepIter 20 (.ret vaT (knotStoreF ρ₀ ++ σ')
        (consKf ρ₀ qa qb ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qb ρT (consKx ρ₀ qa qb ρT vaT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem cons_pack_S (ρ₀ : Env) (σ' : Store) (qa qb ρT vaT vbT : Val)
    (κ : Kont) :
    stepIter 2 (.ret vbT (knotStoreF ρ₀ ++ σ')
        (consKx ρ₀ qa qb ρT vaT κ)) =
      .inl (.ret (.cell (.elem 6) (.cell vaT vbT))
        (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_car_e_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (κ : Kont) :
    stepIter 220 (mevalCallS ρ₀ σ'
        (.cell (.elem 7) (.cell (.elem 3) qe)) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qe ρT (carKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcar_cell_S (ρ₀ : Env) (σ' : Store) (qe ρT aT dT : Val)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT))
        (knotStoreF ρ₀ ++ σ') (carKf ρ₀ qe ρT κ)) =
      .inl (.ret aT (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcar_elem_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (k : Fin 8)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k))
        (knotStoreF ρ₀ ++ σ') (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcar_clos_S (ρ₀ : Env) (σ' : Store) (qe ρT q' ρT' : Val)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT'))
        (knotStoreF ρ₀ ++ σ') (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcar_loc_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (l : Nat)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 5) (.loc l))
        (knotStoreF ρ₀ ++ σ') (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_cdr_e_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (κ : Kont) :
    stepIter 213 (mevalCallS ρ₀ σ'
        (.cell (.elem 7) (.cell (.elem 4) qe)) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qe ρT (cdrKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcdr_cell_S (ρ₀ : Env) (σ' : Store) (qe ρT aT dT : Val)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT))
        (knotStoreF ρ₀ ++ σ') (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret dT (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcdr_elem_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (k : Fin 8)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k))
        (knotStoreF ρ₀ ++ σ') (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcdr_clos_S (ρ₀ : Env) (σ' : Store) (qe ρT q' ρT' : Val)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT'))
        (knotStoreF ρ₀ ++ σ') (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mcdr_loc_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (l : Nat)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 5) (.loc l))
        (knotStoreF ρ₀ ++ σ') (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_pairp_e_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val)
    (κ : Kont) :
    stepIter 186 (mevalCallS ρ₀ σ'
        (.cell (.elem 7) (.cell (.elem 5) qe)) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qe ρT (pairKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mpairp_cell_S (ρ₀ : Env) (σ' : Store) (qe ρT aT dT : Val)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT))
        (knotStoreF ρ₀ ++ σ') (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mpairp_elem_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (k : Fin 8)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k))
        (knotStoreF ρ₀ ++ σ') (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mpairp_clos_S (ρ₀ : Env) (σ' : Store) (qe ρT q' ρT' : Val)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT'))
        (knotStoreF ρ₀ ++ σ') (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mpairp_loc_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (l : Nat)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 5) (.loc l))
        (knotStoreF ρ₀ ++ σ') (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem meval_ite_c_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT : Val)
    (κ : Kont) :
    stepIter 188 (mevalCallS ρ₀ σ'
        (.cell (.elem 7) (.cell (.elem 6)
          (.cell qc (.cell qt qe)))) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qc ρT (iteKf ρ₀ qc qt qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mite_ff_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT : Val)
    (κ : Kont) :
    stepIter 119 (.ret (.cell (.elem 2) (.elem 1))
        (knotStoreF ρ₀ ++ σ') (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qe ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
theorem mite_elem_tt_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT : Val)
    (b : Fin 8) (hb : b ≠ 1) (κ : Kont) :
    stepIter 119 (.ret (.cell (.elem 2) (.elem b))
        (knotStoreF ρ₀ ++ σ') (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qt ρT κ) := by
  fin_cases b <;> first | exact absurd rfl hb | rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mite_clos_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT q' ρT' : Val)
    (κ : Kont) :
    stepIter 114 (.ret (.cell (.elem 3) (.cell q' ρT'))
        (knotStoreF ρ₀ ++ σ') (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qt ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mite_cell_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT aT dT : Val)
    (κ : Kont) :
    stepIter 73 (.ret (.cell (.elem 6) (.cell aT dT))
        (knotStoreF ρ₀ ++ σ') (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qt ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
theorem mite_loc_S (ρ₀ : Env) (σ' : Store) (qc qt qe ρT : Val)
    (l : Nat) (κ : Kont) :
    stepIter 73 (.ret (.cell (.elem 5) (.loc l))
        (knotStoreF ρ₀ ++ σ') (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qt ρT κ) :=
  rfl

/-! ## The store forms

Quotation sub-tags under the store tag `5`: ref `2`, deref `3`,
setref `4`. -/

/-- The continuation of `deref`'s sub-evaluation. -/
def derefKf (ρ₀ : Env) (qe ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 193 (mevalCallS ρ₀ []
    (.cell (.elem 5) (.cell (.elem 3) qe)) ρT κ))

/-- The continuation of `setref`'s location sub-evaluation. -/
def setKl (ρ₀ : Env) (ql qe ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 188 (mevalCallS ρ₀ []
    (.cell (.elem 5) (.cell (.elem 4) (.cell ql qe))) ρT κ))

/-- The continuation of `setref`'s value sub-evaluation. -/
def setKx (ρ₀ : Env) (ql qe ρT vlT : Val) (κ : Kont) : Kont :=
  projK (stepIter 23 (.ret vlT (knotStoreF ρ₀)
    (setKl ρ₀ ql qe ρT κ)))

/-- Projection under a `setR` frame (for the write's post-frames). -/
def projSetR : State ⊕ Val → Kont
  | .inl (.ret _ _ (.setR _ k)) => k
  | _ => .halt

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ref` dispatch**: 194 steps to the operand's recursive call,
    under *concrete* frames — the machine's `refK` with the tagging
    `consR` already installed. -/
theorem meval_ref_e_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (κ : Kont) :
    stepIter 194 (mevalCallS ρ₀ σ'
        (.cell (.elem 5) (.cell (.elem 2) qe)) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qe ρT (.refK (.consR (.elem 5) κ))) :=
  rfl

/-- **The allocation, at any store**: the machine's own `refK` arm
    allocates at `σ.length` and `consR` tags the location. The
    canonical map `i ↦ K₀ + i` is this arm meeting the knot prefix —
    allocation lockstep is the machine's rule, not bookkeeping. -/
theorem ref_alloc (σ : Store) (vT : Val) (κ : Kont) :
    stepIter 2 (.ret vT σ (.refK (.consR (.elem 5) κ))) =
      .inl (.ret (.cell (.elem 5) (.loc σ.length)) (σ ++ [vT]) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`deref` dispatch**: 193 steps to the operand's recursive
    call. -/
theorem meval_deref_e_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val)
    (κ : Kont) :
    stepIter 193 (mevalCallS ρ₀ σ'
        (.cell (.elem 5) (.cell (.elem 3) qe)) ρT κ) =
      .inl (mevalCallS ρ₀ σ' qe ρT (derefKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`deref` of a location, approach**: 63 steps from the tagged
    location's return to the naked read — the `derefK` frame lands
    *directly on the caller's continuation* (tail position), index
    a passenger. -/
theorem deref_pre_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (j : Nat)
    (κ : Kont) :
    stepIter 63 (.ret (.cell (.elem 5) (.loc j))
        (knotStoreF ρ₀ ++ σ') (derefKf ρ₀ qe ρT κ)) =
      .inl (.ret (.loc j) (knotStoreF ρ₀ ++ σ') (.derefK κ)) :=
  rfl

/-- **The read, at any store**: the machine's own `derefK` arm,
    index and store symbolic. -/
theorem deref_read (σ : Store) (j : Nat) (κ : Kont) :
    stepIter 1 (.ret (.loc j) σ (.derefK κ)) =
      .inl (.ret (σ.getD j (.elem 0)) σ κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`deref` of an element**: default agreement. -/
theorem mderef_elem_S (ρ₀ : Env) (σ' : Store) (qe ρT : Val) (k : Fin 8)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k))
        (knotStoreF ρ₀ ++ σ') (derefKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`deref` of a closure**: default agreement. -/
theorem mderef_clos_S (ρ₀ : Env) (σ' : Store) (qe ρT q' ρT' : Val)
    (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT'))
        (knotStoreF ρ₀ ++ σ') (derefKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`deref` of a pair**: default agreement. -/
theorem mderef_cell_S (ρ₀ : Env) (σ' : Store) (qe ρT aT dT : Val)
    (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT))
        (knotStoreF ρ₀ ++ σ') (derefKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`setref` dispatch**: 188 steps to the location operand's
    recursive call. -/
theorem meval_set_l_S (ρ₀ : Env) (σ' : Store) (ql qe ρT : Val)
    (κ : Kont) :
    stepIter 188 (mevalCallS ρ₀ σ'
        (.cell (.elem 5) (.cell (.elem 4) (.cell ql qe))) ρT κ) =
      .inl (mevalCallS ρ₀ σ' ql ρT (setKl ρ₀ ql qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`setref`, phase 2**: 23 steps from the location value's return
    to the value operand's recursive call — the location a
    passenger. -/
theorem meval_set_x_S (ρ₀ : Env) (σ' : Store) (ql qe ρT vlT : Val)
    (κ : Kont) :
    stepIter 23 (.ret vlT (knotStoreF ρ₀ ++ σ')
        (setKl ρ₀ ql qe ρT κ)) =
      .inl (mevalCallS ρ₀ σ' qe ρT (setKx ρ₀ ql qe ρT vlT κ)) :=
  rfl

/-- **The write, at any store**: the machine's own `setR` arm —
    index, value, and store symbolic. -/
theorem set_fire (σ : Store) (wT : Val) (j : Nat) (κ : Kont) :
    stepIter 1 (.ret wT σ (.setR (.loc j) κ)) =
      .inl (.ret wT (σ.set j wT) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`setref` on an element**: default agreement, store
    untouched. -/
theorem mset_elem_S (ρ₀ : Env) (σ' : Store) (ql qe ρT wT : Val)
    (k : Fin 8) (κ : Kont) :
    stepIter 57 (.ret wT (knotStoreF ρ₀ ++ σ')
        (setKx ρ₀ ql qe ρT (.cell (.elem 2) (.elem k)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`setref` on a closure**: default agreement, store untouched. -/
theorem mset_clos_S (ρ₀ : Env) (σ' : Store) (ql qe ρT q' ρT' wT : Val)
    (κ : Kont) :
    stepIter 57 (.ret wT (knotStoreF ρ₀ ++ σ')
        (setKx ρ₀ ql qe ρT (.cell (.elem 3) (.cell q' ρT')) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`setref` on a pair**: default agreement, store untouched. -/
theorem mset_cell_S (ρ₀ : Env) (σ' : Store) (ql qe ρT aT dT wT : Val)
    (κ : Kont) :
    stepIter 64 (.ret wT (knotStoreF ρ₀ ++ σ')
        (setKx ρ₀ ql qe ρT (.cell (.elem 6) (.cell aT dT)) κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀ ++ σ') κ) :=
  rfl

/-! ## Entry over the live store -/

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- The startup entry lands in the suffixed calling convention with
    the empty suffix. -/
theorem call_entry_S (p : Prog) :
    stepIter 17 (mevalEntry p) =
      .inl (mevalCallS [quoteD p] [] (quoteD p) (.elem 0) .halt) :=
  rfl

end AdequacyStoreKit
end Dichotomic
