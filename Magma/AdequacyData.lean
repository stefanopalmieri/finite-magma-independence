import Magma.AdequacySim

/-!
# Adequacy campaign, rung 4: the data forms

The simulation induction of rung 3b(iv), extended to `mdata`'s arms:
`cons`, `car`, `cdr`, `pairp`, `ite`. The relation `EvD` grows nine
new clauses mirroring the machine arm for arm — including the three
`ite` arms (ff takes the else-branch; every other element and every
non-element value takes the then-branch) and the `car`/`cdr`/`pairp`
error arms. The master theorem `meval_simD` re-proves nothing from
3b(iv): its eight pure cases invoke the imported dispatch kit
verbatim, and only the data forms bring new kernel reductions.

Probe-discovered, `rfl`-certified, as before:

* **`cons` is the application pattern in miniature**: two dispatch
  segments (223/20 steps) through two self-computing continuation
  transformers, then a 2-step *pack* — the machine's own `consR`
  arms build the tagged pair, both components symbolic
  (`cons_pack`, the `elem_fire` of this rung).
* **`car`/`cdr`/`pairp` dispatch on the result tag** (64 steps for
  cells and locations — the discriminating path; 57 for elements
  and closures), payloads passengers throughout; the error and
  negative answers agree with the machine's defaults exactly.
* **`ite` branches where the machine branches**: ff (119 steps) to
  the else-quotation, non-ff elements (119) and closures (114) and
  cells/locations (73) to the then-quotation — all tail calls at
  the original continuation, so `KRempty` still suffices.
* **The store still never moves**: cells are immediate values on
  this machine (`cons` allocates nothing), so the whole 10-form
  fragment runs over the unchanged knot store. `ref`/`deref`/
  `setref` (rung 5) is where the store alignment finally engages.

Corollaries: `adequacy_data` (closed programs of the 10-form
fragment, one derivation ⇒ both runs + the relation);
`adequacy_list` — adequacy for *every* quoted list, an infinite
family in data structure (`cons`-chains of arbitrary length, the
tagged result representing the direct list componentwise); and
`adequacy_car_cons` (the constructor/projector roundtrip through
the interpreter, all 64 element pairs, zero kernel cost).
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyData

open FactorizationEqv MetaImage AdequacyStartup AdequacyInstances AdequacyRep
  AdequacyLeaf AdequacySim

/-! ## The big-step relation, extended

`EvD` = `EvP`'s eight clauses + nine data clauses, mirroring the
machine (`evd_steps`). `evP_evD` embeds the rung-3b(iv) relation. -/

/-- Big-step evaluation for the 10-form fragment (pure + data),
    matching the machine arm for arm. -/
inductive EvD : Prog → Env → Val → Prop where
  | atom (a : Fin 8) (ρ : Env) : EvD (.atom a) ρ (.elem a)
  | var (n : Nat) (ρ : Env) : EvD (.var n) ρ (ρ.getD n (.elem 0))
  | lam (b : Prog) (ρ : Env) : EvD (.lam b) ρ (.clos b ρ)
  | appClos {f x b : Prog} {ρ ρ' : Env} {vx v : Val} :
      EvD f ρ (.clos b ρ') → EvD x ρ vx → EvD b (vx :: ρ') v →
      EvD (.app f x) ρ v
  | appElem {f x : Prog} {ρ : Env} {a b : Fin 8} :
      EvD f ρ (.elem a) → EvD x ρ (.elem b) →
      EvD (.app f x) ρ (.elem (dotA8 a b))
  | appElemErr {f x : Prog} {ρ : Env} {a : Fin 8} {w : Val} :
      EvD f ρ (.elem a) → EvD x ρ w → (∀ b : Fin 8, w ≠ .elem b) →
      EvD (.app f x) ρ (.elem 0)
  | appCellErr {f x : Prog} {ρ : Env} {a d w : Val} :
      EvD f ρ (.cell a d) → EvD x ρ w → EvD (.app f x) ρ (.elem 0)
  | appLocErr {f x : Prog} {ρ : Env} {l : Nat} {w : Val} :
      EvD f ρ (.loc l) → EvD x ρ w → EvD (.app f x) ρ (.elem 0)
  | cons {a b : Prog} {ρ : Env} {va vb : Val} :
      EvD a ρ va → EvD b ρ vb → EvD (.cons a b) ρ (.cell va vb)
  | carCell {e : Prog} {ρ : Env} {u w : Val} :
      EvD e ρ (.cell u w) → EvD (.car e) ρ u
  | carErr {e : Prog} {ρ : Env} {w : Val} :
      EvD e ρ w → (∀ u v, w ≠ .cell u v) → EvD (.car e) ρ (.elem 0)
  | cdrCell {e : Prog} {ρ : Env} {u w : Val} :
      EvD e ρ (.cell u w) → EvD (.cdr e) ρ w
  | cdrErr {e : Prog} {ρ : Env} {w : Val} :
      EvD e ρ w → (∀ u v, w ≠ .cell u v) → EvD (.cdr e) ρ (.elem 0)
  | pairpYes {e : Prog} {ρ : Env} {u w : Val} :
      EvD e ρ (.cell u w) → EvD (.pairp e) ρ (.elem 0)
  | pairpNo {e : Prog} {ρ : Env} {w : Val} :
      EvD e ρ w → (∀ u v, w ≠ .cell u v) → EvD (.pairp e) ρ (.elem 1)
  | iteFf {c t e : Prog} {ρ : Env} {v : Val} :
      EvD c ρ (.elem 1) → EvD e ρ v → EvD (.ite c t e) ρ v
  | iteElem {c t e : Prog} {ρ : Env} {b : Fin 8} {v : Val} :
      EvD c ρ (.elem b) → b ≠ 1 → EvD t ρ v → EvD (.ite c t e) ρ v
  | iteVal {c t e : Prog} {ρ : Env} {w v : Val} :
      EvD c ρ w → (∀ b : Fin 8, w ≠ .elem b) → EvD t ρ v →
      EvD (.ite c t e) ρ v

/-- The rung-3b(iv) relation embeds: `EvD` conservatively extends
    `EvP`. -/
theorem evP_evD {p : Prog} {ρ : Env} {v : Val} (h : EvP p ρ v) :
    EvD p ρ v := by
  induction h with
  | atom a ρ => exact .atom a ρ
  | var n ρ => exact .var n ρ
  | lam b ρ => exact .lam b ρ
  | appClos _ _ _ ihf ihx ihb => exact .appClos ihf ihx ihb
  | appElem _ _ ihf ihx => exact .appElem ihf ihx
  | appElemErr _ _ hw ihf ihx => exact .appElemErr ihf ihx hw
  | appCellErr _ _ ihf ihx => exact .appCellErr ihf ihx
  | appLocErr _ _ ihf ihx => exact .appLocErr ihf ihx

/-- `EvD` is sound for the machine: a derivation is a terminating
    run, at every store and continuation (the fragment still never
    touches the store — cells are immediate values). -/
theorem evd_steps {p : Prog} {ρ : Env} {v : Val} (h : EvD p ρ v) :
    ∀ (σ : Store) (κ : Kont),
      ∃ n, stepIter n (.eval p ρ σ κ) = .inl (.ret v σ κ) := by
  induction h with
  | atom a ρ => exact fun σ κ => ⟨1, rfl⟩
  | var n ρ => exact fun σ κ => ⟨1, rfl⟩
  | lam b ρ => exact fun σ κ => ⟨1, rfl⟩
  | @appClos f x b ρ ρ' vx v _ _ _ ihf ihx ihb =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.clos b ρ') κ)
    obtain ⟨nb, hb⟩ := ihb σ κ
    exact ⟨1 + (nf + (1 + (nx + (1 + nb)))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx (stepIter_chain rfl hb))))⟩
  | @appElem f x ρ a b _ _ ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.elem a) κ)
    exact ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx rfl)))⟩
  | @appElemErr f x ρ a w _ _ hw ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.elem a) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @appCellErr f x ρ a d w _ _ ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.cell a d) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w <;> rfl
  | @appLocErr f x ρ l w _ _ ihf ihx =>
    intro σ κ
    obtain ⟨nf, hf⟩ := ihf σ (.appL x ρ κ)
    obtain ⟨nx, hx⟩ := ihx σ (.appR (.loc l) κ)
    refine ⟨1 + (nf + (1 + (nx + 1))),
      stepIter_chain rfl (stepIter_chain hf (stepIter_chain rfl
        (stepIter_chain hx ?_)))⟩
    cases w <;> rfl
  | @cons a b ρ va vb _ _ iha ihb =>
    intro σ κ
    obtain ⟨na, ha⟩ := iha σ (.consL b ρ κ)
    obtain ⟨nb, hb⟩ := ihb σ (.consR va κ)
    exact ⟨1 + (na + (1 + (nb + 1))),
      stepIter_chain rfl (stepIter_chain ha (stepIter_chain rfl
        (stepIter_chain hb rfl)))⟩
  | @carCell e ρ u w _ ihe =>
    intro σ κ
    obtain ⟨ne, he⟩ := ihe σ (.carK κ)
    exact ⟨1 + (ne + 1),
      stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @carErr e ρ w _ hw ihe =>
    intro σ κ
    obtain ⟨ne, he⟩ := ihe σ (.carK κ)
    refine ⟨1 + (ne + 1),
      stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | elem _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @cdrCell e ρ u w _ ihe =>
    intro σ κ
    obtain ⟨ne, he⟩ := ihe σ (.cdrK κ)
    exact ⟨1 + (ne + 1),
      stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @cdrErr e ρ w _ hw ihe =>
    intro σ κ
    obtain ⟨ne, he⟩ := ihe σ (.cdrK κ)
    refine ⟨1 + (ne + 1),
      stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | elem _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @pairpYes e ρ u w _ ihe =>
    intro σ κ
    obtain ⟨ne, he⟩ := ihe σ (.pairK κ)
    exact ⟨1 + (ne + 1),
      stepIter_chain rfl (stepIter_chain he rfl)⟩
  | @pairpNo e ρ w _ hw ihe =>
    intro σ κ
    obtain ⟨ne, he⟩ := ihe σ (.pairK κ)
    refine ⟨1 + (ne + 1),
      stepIter_chain rfl (stepIter_chain he ?_)⟩
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | elem _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl
  | @iteFf c t e ρ v _ _ ihc ihe =>
    intro σ κ
    obtain ⟨nc, hc⟩ := ihc σ (.iteK t e ρ κ)
    obtain ⟨ne, he⟩ := ihe σ κ
    exact ⟨1 + (nc + (1 + ne)),
      stepIter_chain rfl (stepIter_chain hc (stepIter_chain rfl he))⟩
  | @iteElem c t e ρ b v _ hb _ ihc iht =>
    intro σ κ
    obtain ⟨nc, hc⟩ := ihc σ (.iteK t e ρ κ)
    obtain ⟨nt, ht⟩ := iht σ κ
    have h1 : stepIter 1 (.ret (.elem b) σ (.iteK t e ρ κ)) =
        .inl (.eval (if b = 1 then e else t) ρ σ κ) := rfl
    rw [if_neg hb] at h1
    exact ⟨1 + (nc + (1 + nt)),
      stepIter_chain rfl (stepIter_chain hc (stepIter_chain h1 ht))⟩
  | @iteVal c t e ρ w v _ hw _ ihc iht =>
    intro σ κ
    obtain ⟨nc, hc⟩ := ihc σ (.iteK t e ρ κ)
    obtain ⟨nt, ht⟩ := iht σ κ
    refine ⟨1 + (nc + (1 + nt)),
      stepIter_chain rfl (stepIter_chain hc (stepIter_chain ?_ ht))⟩
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cell _ _ => rfl
    | clos _ _ => rfl
    | cont _ => rfl
    | loc _ => rfl

/-- The cell inversion, carrying the component representations
    (rung 3b(iv)'s `cellR_inv` gave only the shape; `car`/`cdr`
    need the parts). -/
theorem cellR_inv' {vT u w : Val}
    (h : RepV 14 KRempty vT (.cell u w)) :
    ∃ aT dT, vT = .cell (.elem 6) (.cell aT dT) ∧
      RepV 14 KRempty aT u ∧ RepV 14 KRempty dT w := by
  cases h with | cell ha hd => exact ⟨_, _, rfl, ha, hd⟩

/-! ## The dispatch kit for the data forms

Quotation sub-tags under the data tag `7`: cons `2`, car `3`,
cdr `4`, pairp `5`, ite `6`. Counts probe-discovered; every payload
the count does not depend on is universally quantified. -/

/-- The continuation of `cons`'s first sub-evaluation. -/
def consKf (ρ₀ : Env) (qa qb ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 223 (mevalCall ρ₀
    (.cell (.elem 7) (.cell (.elem 2) (.cell qa qb))) ρT κ))

/-- The continuation of `cons`'s second sub-evaluation. -/
def consKx (ρ₀ : Env) (qa qb ρT vaT : Val) (κ : Kont) : Kont :=
  projK (stepIter 20 (.ret vaT (knotStoreF ρ₀) (consKf ρ₀ qa qb ρT κ)))

/-- The continuation of `car`'s sub-evaluation. -/
def carKf (ρ₀ : Env) (qe ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 220 (mevalCall ρ₀
    (.cell (.elem 7) (.cell (.elem 3) qe)) ρT κ))

/-- The continuation of `cdr`'s sub-evaluation. -/
def cdrKf (ρ₀ : Env) (qe ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 213 (mevalCall ρ₀
    (.cell (.elem 7) (.cell (.elem 4) qe)) ρT κ))

/-- The continuation of `pairp`'s sub-evaluation. -/
def pairKf (ρ₀ : Env) (qe ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 186 (mevalCall ρ₀
    (.cell (.elem 7) (.cell (.elem 5) qe)) ρT κ))

/-- The continuation of `ite`'s condition sub-evaluation. -/
def iteKf (ρ₀ : Env) (qc qt qe ρT : Val) (κ : Kont) : Kont :=
  projK (stepIter 188 (mevalCall ρ₀
    (.cell (.elem 7) (.cell (.elem 6) (.cell qc (.cell qt qe)))) ρT κ))

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cons`, phase 1**: 223 steps to the first component's
    recursive call. -/
theorem meval_cons_a (ρ₀ : Env) (qa qb ρT : Val) (κ : Kont) :
    stepIter 223 (mevalCall ρ₀
        (.cell (.elem 7) (.cell (.elem 2) (.cell qa qb))) ρT κ) =
      .inl (mevalCall ρ₀ qa ρT (consKf ρ₀ qa qb ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cons`, phase 2**: 20 steps from the first value's return to
    the second component's recursive call — the value a passenger. -/
theorem meval_cons_b (ρ₀ : Env) (qa qb ρT vaT : Val) (κ : Kont) :
    stepIter 20 (.ret vaT (knotStoreF ρ₀) (consKf ρ₀ qa qb ρT κ)) =
      .inl (mevalCall ρ₀ qb ρT (consKx ρ₀ qa qb ρT vaT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **The pack**: the machine's own `consR` arms build the tagged
    pair in 2 steps, both components symbolic — this rung's
    `elem_fire`. -/
theorem cons_pack (ρ₀ : Env) (qa qb ρT vaT vbT : Val) (κ : Kont) :
    stepIter 2 (.ret vbT (knotStoreF ρ₀)
        (consKx ρ₀ qa qb ρT vaT κ)) =
      .inl (.ret (.cell (.elem 6) (.cell vaT vbT))
        (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`car` dispatch**: 220 steps to the operand's recursive call. -/
theorem meval_car_e (ρ₀ : Env) (qe ρT : Val) (κ : Kont) :
    stepIter 220 (mevalCall ρ₀
        (.cell (.elem 7) (.cell (.elem 3) qe)) ρT κ) =
      .inl (mevalCall ρ₀ qe ρT (carKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`car` of a pair**: the head, payloads passengers. -/
theorem mcar_cell (ρ₀ : Env) (qe ρT aT dT : Val) (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT)) (knotStoreF ρ₀)
        (carKf ρ₀ qe ρT κ)) =
      .inl (.ret aT (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`car` of an element**: default agreement. -/
theorem mcar_elem (ρ₀ : Env) (qe ρT : Val) (k : Fin 8) (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k)) (knotStoreF ρ₀)
        (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`car` of a closure**: default agreement. -/
theorem mcar_clos (ρ₀ : Env) (qe ρT q' ρT' : Val) (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT')) (knotStoreF ρ₀)
        (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`car` of a location**: default agreement (the discriminating
    64-step path — the loc tag shares `data?`'s first probe). -/
theorem mcar_loc (ρ₀ : Env) (qe ρT : Val) (l : Nat) (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 5) (.loc l)) (knotStoreF ρ₀)
        (carKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cdr` dispatch**: 213 steps to the operand's recursive call. -/
theorem meval_cdr_e (ρ₀ : Env) (qe ρT : Val) (κ : Kont) :
    stepIter 213 (mevalCall ρ₀
        (.cell (.elem 7) (.cell (.elem 4) qe)) ρT κ) =
      .inl (mevalCall ρ₀ qe ρT (cdrKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cdr` of a pair**: the tail. -/
theorem mcdr_cell (ρ₀ : Env) (qe ρT aT dT : Val) (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT)) (knotStoreF ρ₀)
        (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret dT (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cdr` of an element**: default agreement. -/
theorem mcdr_elem (ρ₀ : Env) (qe ρT : Val) (k : Fin 8) (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k)) (knotStoreF ρ₀)
        (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cdr` of a closure**: default agreement. -/
theorem mcdr_clos (ρ₀ : Env) (qe ρT q' ρT' : Val) (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT')) (knotStoreF ρ₀)
        (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`cdr` of a location**: default agreement. -/
theorem mcdr_loc (ρ₀ : Env) (qe ρT : Val) (l : Nat) (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 5) (.loc l)) (knotStoreF ρ₀)
        (cdrKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`pairp` dispatch**: 186 steps to the operand's recursive
    call. -/
theorem meval_pairp_e (ρ₀ : Env) (qe ρT : Val) (κ : Kont) :
    stepIter 186 (mevalCall ρ₀
        (.cell (.elem 7) (.cell (.elem 5) qe)) ρT κ) =
      .inl (mevalCall ρ₀ qe ρT (pairKf ρ₀ qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`pairp` of a pair**: yes (`tt`), payloads passengers. -/
theorem mpairp_cell (ρ₀ : Env) (qe ρT aT dT : Val) (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 6) (.cell aT dT)) (knotStoreF ρ₀)
        (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 0)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`pairp` of an element**: no (`ff`). -/
theorem mpairp_elem (ρ₀ : Env) (qe ρT : Val) (k : Fin 8) (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 2) (.elem k)) (knotStoreF ρ₀)
        (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`pairp` of a closure**: no. -/
theorem mpairp_clos (ρ₀ : Env) (qe ρT q' ρT' : Val) (κ : Kont) :
    stepIter 57 (.ret (.cell (.elem 3) (.cell q' ρT')) (knotStoreF ρ₀)
        (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`pairp` of a location**: no — the discriminating path: a
    location shares the data probe's first answer, and META's
    second test tells them apart, agreeing with the machine. -/
theorem mpairp_loc (ρ₀ : Env) (qe ρT : Val) (l : Nat) (κ : Kont) :
    stepIter 64 (.ret (.cell (.elem 5) (.loc l)) (knotStoreF ρ₀)
        (pairKf ρ₀ qe ρT κ)) =
      .inl (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀) κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ite` dispatch**: 188 steps to the condition's recursive
    call — all three quotations passengers. -/
theorem meval_ite_c (ρ₀ : Env) (qc qt qe ρT : Val) (κ : Kont) :
    stepIter 188 (mevalCall ρ₀
        (.cell (.elem 7) (.cell (.elem 6)
          (.cell qc (.cell qt qe)))) ρT κ) =
      .inl (mevalCall ρ₀ qc ρT (iteKf ρ₀ qc qt qe ρT κ)) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ite` on `ff`**: the else-branch, as a tail call at the
    original continuation. -/
theorem mite_ff (ρ₀ : Env) (qc qt qe ρT : Val) (κ : Kont) :
    stepIter 119 (.ret (.cell (.elem 2) (.elem 1)) (knotStoreF ρ₀)
        (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCall ρ₀ qe ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 40000000 in
/-- **`ite` on a non-`ff` element**: the then-branch, tail call —
    seven cases, each its own reduction (the truthiness probe's
    outcome depends on the element), so this one theorem carries
    eight kernel reductions and a ten-fold heartbeat budget. -/
theorem mite_elem_tt (ρ₀ : Env) (qc qt qe ρT : Val) (b : Fin 8)
    (hb : b ≠ 1) (κ : Kont) :
    stepIter 119 (.ret (.cell (.elem 2) (.elem b)) (knotStoreF ρ₀)
        (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCall ρ₀ qt ρT κ) := by
  fin_cases b <;> first | exact absurd rfl hb | rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ite` on a closure**: truthy — the then-branch (the machine's
    non-element arm), tail call. -/
theorem mite_clos (ρ₀ : Env) (qc qt qe ρT q' ρT' : Val) (κ : Kont) :
    stepIter 114 (.ret (.cell (.elem 3) (.cell q' ρT')) (knotStoreF ρ₀)
        (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCall ρ₀ qt ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ite` on a pair**: truthy — the then-branch, tail call. -/
theorem mite_cell (ρ₀ : Env) (qc qt qe ρT aT dT : Val) (κ : Kont) :
    stepIter 73 (.ret (.cell (.elem 6) (.cell aT dT)) (knotStoreF ρ₀)
        (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCall ρ₀ qt ρT κ) :=
  rfl

set_option maxRecDepth 400000 in
set_option maxHeartbeats 4000000 in
/-- **`ite` on a location**: truthy — the then-branch, tail call. -/
theorem mite_loc (ρ₀ : Env) (qc qt qe ρT : Val) (l : Nat) (κ : Kont) :
    stepIter 73 (.ret (.cell (.elem 5) (.loc l)) (knotStoreF ρ₀)
        (iteKf ρ₀ qc qt qe ρT κ)) =
      .inl (mevalCall ρ₀ qt ρT κ) :=
  rfl

/-! ## The master theorem, extended -/

/-- **The simulation induction over the 10-form fragment.** The
    eight pure cases are rung 3b(iv)'s, invoking the imported kit;
    the nine data cases glue the new dispatch lemmas. Still over
    the unchanged knot store, still with the empty continuation
    relation — every branch call is a tail call. -/
theorem meval_simD {p : Prog} {ρ : Env} {v : Val} (h : EvD p ρ v) :
    ∀ (ρ₀ : Env) {ρT : Val}, RepEnv 14 KRempty ρT ρ → ∀ κ : Kont,
      ∃ (n : Nat) (vT : Val), RepV 14 KRempty vT v ∧
        stepIter n (mevalCall ρ₀ (quoteD p) ρT κ) =
          .inl (.ret vT (knotStoreF ρ₀) κ) := by
  induction h with
  | atom a ρ =>
    intro ρ₀ ρT hρ κ
    exact ⟨atomSteps a, _, .elem a, meval_atom ρ₀ a ρT κ⟩
  | var n ρ =>
    intro ρ₀ ρT hρ κ
    obtain ⟨m, hm⟩ := mnth_sim ρ₀ n hρ κ
    exact ⟨116 + m, _, hρ.chainNth n,
      stepIter_chain (meval_var_dispatch ρ₀ (natToVal n) ρT κ) hm⟩
  | lam b ρ =>
    intro ρ₀ ρT hρ κ
    exact ⟨115, _, .clos b hρ, meval_lam ρ₀ (quoteD b) ρT κ⟩
  | @appClos f x b ρ ρ' vx v _ _ _ ihf ihx ihb =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain ⟨ρTf, rfl, hρ'⟩ := closR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 3) (.cell (quoteD b) ρTf)) κ)
    obtain ⟨nb, vT, repB, runB⟩ := ihb ρ₀ (.cons repX hρ') κ
    exact ⟨129 + (nf + (29 + (nx + (214 + nb)))), vT, repB,
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 3) (.cell (quoteD b) ρTf)) κ)
            (stepIter_chain runX
              (stepIter_chain
                (mapply_clos ρ₀ (quoteD f) (quoteD x) ρT
                  (quoteD b) ρTf vxT κ) runB))))⟩
  | @appElem f x ρ a b _ _ ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := elemR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 2) (.elem a)) κ)
    obtain rfl := elemR_inv repX
    exact ⟨129 + (nf + (29 + (nx + 198))), _, .elem (dotA8 a b),
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 2) (.elem a)) κ)
            (stepIter_chain runX
              (mapply_elem_elem ρ₀ (quoteD f) (quoteD x) ρT a b κ))))⟩
  | @appElemErr f x ρ a w _ _ hw ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := elemR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 2) (.elem a)) κ)
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cont κ' => exact (kontR_inv repX).elim
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 190))), _, .elem 0,
        stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_clos ρ₀ (quoteD f) (quoteD x) ρT
                  (quoteD b') ρTx a κ))))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 149))), _, .elem 0,
        stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_cell ρ₀ (quoteD f) (quoteD x) ρT
                  aT dT a κ))))⟩
    | loc l' =>
      obtain rfl := locR_inv repX
      exact ⟨129 + (nf + (29 + (nx + 149))), _, .elem 0,
        stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
          (stepIter_chain runF
            (stepIter_chain
              (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
                (.cell (.elem 2) (.elem a)) κ)
              (stepIter_chain runX
                (mapply_elem_loc ρ₀ (quoteD f) (quoteD x) ρT
                  a (14 + l') κ))))⟩
  | @appCellErr f x ρ a d w _ _ ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain ⟨aT, dT, rfl⟩ := cellR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 6) (.cell aT dT)) κ)
    exact ⟨129 + (nf + (29 + (nx + 159))), _, .elem 0,
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 6) (.cell aT dT)) κ)
            (stepIter_chain runX
              (mapply_cellf ρ₀ (quoteD f) (quoteD x) ρT aT dT vxT κ))))⟩
  | @appLocErr f x ρ l w _ _ ihf ihx =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nf, vfT, repF, runF⟩ :=
      ihf ρ₀ hρ (appKf ρ₀ (quoteD f) (quoteD x) ρT κ)
    obtain rfl := locR_inv repF
    obtain ⟨nx, vxT, repX, runX⟩ :=
      ihx ρ₀ hρ (appKx ρ₀ (quoteD f) (quoteD x) ρT
        (.cell (.elem 5) (.loc (14 + l))) κ)
    exact ⟨129 + (nf + (29 + (nx + 159))), _, .elem 0,
      stepIter_chain (meval_app_f ρ₀ (quoteD f) (quoteD x) ρT κ)
        (stepIter_chain runF
          (stepIter_chain
            (meval_app_x ρ₀ (quoteD f) (quoteD x) ρT
              (.cell (.elem 5) (.loc (14 + l))) κ)
            (stepIter_chain runX
              (mapply_locf ρ₀ (quoteD f) (quoteD x) ρT vxT (14 + l) κ))))⟩
  | @cons a b ρ va vb _ _ iha ihb =>
    intro ρ₀ ρT hρ κ
    obtain ⟨na, vaT, repA, runA⟩ :=
      iha ρ₀ hρ (consKf ρ₀ (quoteD a) (quoteD b) ρT κ)
    obtain ⟨nb, vbT, repB, runB⟩ :=
      ihb ρ₀ hρ (consKx ρ₀ (quoteD a) (quoteD b) ρT vaT κ)
    exact ⟨223 + (na + (20 + (nb + 2))), _, .cell repA repB,
      stepIter_chain (meval_cons_a ρ₀ (quoteD a) (quoteD b) ρT κ)
        (stepIter_chain runA
          (stepIter_chain
            (meval_cons_b ρ₀ (quoteD a) (quoteD b) ρT vaT κ)
            (stepIter_chain runB
              (cons_pack ρ₀ (quoteD a) (quoteD b) ρT vaT vbT κ))))⟩
  | @carCell e ρ u w _ ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨ne, veT, repE, runE⟩ :=
      ihe ρ₀ hρ (carKf ρ₀ (quoteD e) ρT κ)
    obtain ⟨aT, dT, rfl, ha, hd⟩ := cellR_inv' repE
    exact ⟨220 + (ne + 64), aT, ha,
      stepIter_chain (meval_car_e ρ₀ (quoteD e) ρT κ)
        (stepIter_chain runE (mcar_cell ρ₀ (quoteD e) ρT aT dT κ))⟩
  | @carErr e ρ w _ hw ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨ne, veT, repE, runE⟩ :=
      ihe ρ₀ hρ (carKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨220 + (ne + 57), _, .elem 0,
        stepIter_chain (meval_car_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE (mcar_elem ρ₀ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨220 + (ne + 57), _, .elem 0,
        stepIter_chain (meval_car_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcar_clos ρ₀ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | loc l' =>
      obtain rfl := locR_inv repE
      exact ⟨220 + (ne + 64), _, .elem 0,
        stepIter_chain (meval_car_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcar_loc ρ₀ (quoteD e) ρT (14 + l') κ))⟩
  | @cdrCell e ρ u w _ ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨ne, veT, repE, runE⟩ :=
      ihe ρ₀ hρ (cdrKf ρ₀ (quoteD e) ρT κ)
    obtain ⟨aT, dT, rfl, ha, hd⟩ := cellR_inv' repE
    exact ⟨213 + (ne + 64), dT, hd,
      stepIter_chain (meval_cdr_e ρ₀ (quoteD e) ρT κ)
        (stepIter_chain runE (mcdr_cell ρ₀ (quoteD e) ρT aT dT κ))⟩
  | @cdrErr e ρ w _ hw ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨ne, veT, repE, runE⟩ :=
      ihe ρ₀ hρ (cdrKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨213 + (ne + 57), _, .elem 0,
        stepIter_chain (meval_cdr_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE (mcdr_elem ρ₀ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨213 + (ne + 57), _, .elem 0,
        stepIter_chain (meval_cdr_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcdr_clos ρ₀ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | loc l' =>
      obtain rfl := locR_inv repE
      exact ⟨213 + (ne + 64), _, .elem 0,
        stepIter_chain (meval_cdr_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE
            (mcdr_loc ρ₀ (quoteD e) ρT (14 + l') κ))⟩
  | @pairpYes e ρ u w _ ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨ne, veT, repE, runE⟩ :=
      ihe ρ₀ hρ (pairKf ρ₀ (quoteD e) ρT κ)
    obtain ⟨aT, dT, rfl, _, _⟩ := cellR_inv' repE
    exact ⟨186 + (ne + 64), _, .elem 0,
      stepIter_chain (meval_pairp_e ρ₀ (quoteD e) ρT κ)
        (stepIter_chain runE (mpairp_cell ρ₀ (quoteD e) ρT aT dT κ))⟩
  | @pairpNo e ρ w _ hw ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨ne, veT, repE, runE⟩ :=
      ihe ρ₀ hρ (pairKf ρ₀ (quoteD e) ρT κ)
    cases w with
    | cell u v => exact absurd rfl (hw u v)
    | cont κ' => exact (kontR_inv repE).elim
    | elem k =>
      obtain rfl := elemR_inv repE
      exact ⟨186 + (ne + 57), _, .elem 1,
        stepIter_chain (meval_pairp_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE (mpairp_elem ρ₀ (quoteD e) ρT k κ))⟩
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repE
      exact ⟨186 + (ne + 57), _, .elem 1,
        stepIter_chain (meval_pairp_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE
            (mpairp_clos ρ₀ (quoteD e) ρT (quoteD b') ρTx κ))⟩
    | loc l' =>
      obtain rfl := locR_inv repE
      exact ⟨186 + (ne + 64), _, .elem 1,
        stepIter_chain (meval_pairp_e ρ₀ (quoteD e) ρT κ)
          (stepIter_chain runE
            (mpairp_loc ρ₀ (quoteD e) ρT (14 + l') κ))⟩
  | @iteFf c t e ρ v _ _ ihc ihe =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nc, vcT, repC, runC⟩ :=
      ihc ρ₀ hρ (iteKf ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
    obtain rfl := elemR_inv repC
    obtain ⟨ne, veT, repE, runE⟩ := ihe ρ₀ hρ κ
    exact ⟨188 + (nc + (119 + ne)), veT, repE,
      stepIter_chain
        (meval_ite_c ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
        (stepIter_chain runC
          (stepIter_chain
            (mite_ff ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ) runE))⟩
  | @iteElem c t e ρ b v _ hb _ ihc iht =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nc, vcT, repC, runC⟩ :=
      ihc ρ₀ hρ (iteKf ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
    obtain rfl := elemR_inv repC
    obtain ⟨nt, vtT, repT, runT⟩ := iht ρ₀ hρ κ
    exact ⟨188 + (nc + (119 + nt)), vtT, repT,
      stepIter_chain
        (meval_ite_c ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
        (stepIter_chain runC
          (stepIter_chain
            (mite_elem_tt ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT
              b hb κ) runT))⟩
  | @iteVal c t e ρ w v _ hw _ ihc iht =>
    intro ρ₀ ρT hρ κ
    obtain ⟨nc, vcT, repC, runC⟩ :=
      ihc ρ₀ hρ (iteKf ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
    obtain ⟨nt, vtT, repT, runT⟩ := iht ρ₀ hρ κ
    cases w with
    | elem b => exact absurd rfl (hw b)
    | cont κ' => exact (kontR_inv repC).elim
    | clos b' ρ'' =>
      obtain ⟨ρTx, rfl, _⟩ := closR_inv repC
      exact ⟨188 + (nc + (114 + nt)), vtT, repT,
        stepIter_chain
          (meval_ite_c ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
          (stepIter_chain runC
            (stepIter_chain
              (mite_clos ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT
                (quoteD b') ρTx κ) runT))⟩
    | cell a' d' =>
      obtain ⟨aT, dT, rfl⟩ := cellR_inv repC
      exact ⟨188 + (nc + (73 + nt)), vtT, repT,
        stepIter_chain
          (meval_ite_c ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
          (stepIter_chain runC
            (stepIter_chain
              (mite_cell ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT
                aT dT κ) runT))⟩
    | loc l' =>
      obtain rfl := locR_inv repC
      exact ⟨188 + (nc + (73 + nt)), vtT, repT,
        stepIter_chain
          (meval_ite_c ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT κ)
          (stepIter_chain runC
            (stepIter_chain
              (mite_loc ρ₀ (quoteD c) (quoteD t) (quoteD e) ρT
                (14 + l') κ) runT))⟩

/-! ## Top-level adequacy for the 10-form fragment -/

/-- **Adequacy for the pure + data fragment**: from one big-step
    derivation of a closed program — the meta run converges, the
    direct run converges, and the values stand in the relation. -/
theorem adequacy_data {p : Prog} {v : Val} (h : EvD p [] v) :
    ∃ (n : Nat) (vT : Val), RepV 14 KRempty vT v ∧
      loop n (metaState p) = some vT ∧
      ∃ m, runM m [] [] p = some v := by
  obtain ⟨n, vT, rep, run⟩ := meval_simD h [quoteD p] .nil .halt
  obtain ⟨m, hm⟩ := evd_steps h [] .halt
  have lastM : stepIter 1 (.ret vT (knotStoreF [quoteD p]) .halt) =
      .inr vT := rfl
  have lastD : stepIter 1 (.ret v [] .halt) = .inr v := rfl
  exact ⟨entrySteps + (17 + (n + 1)), vT, rep,
    loop_of_stepIter_inr
      (stepIter_chain (meval_entry p)
        (stepIter_chain (call_entry p) (stepIter_chain run lastM))),
    m + 1, loop_of_stepIter_inr (stepIter_chain hm lastD)⟩

/-! ## Families infinite in data structure -/

/-- A list of atoms as a program: right-nested `cons`, `tt`-ended
    (the machine's own nil convention). -/
def listP : List (Fin 8) → Prog
  | [] => .atom 0
  | k :: ks => .cons (.atom k) (listP ks)

/-- The direct value of a quoted list. -/
def listV : List (Fin 8) → Val
  | [] => .elem 0
  | k :: ks => .cell (.elem k) (listV ks)

/-- Every list program evaluates to its list value. -/
theorem listP_evd (l : List (Fin 8)) : EvD (listP l) [] (listV l) := by
  induction l with
  | nil => exact .atom 0 []
  | cons k ks ih => exact .cons (.atom k []) ih

/-- **Adequacy for every quoted list**: `cons`-chains of arbitrary
    length — an infinite family in *data* structure, the tagged
    result representing the direct list componentwise. -/
theorem adequacy_list (l : List (Fin 8)) :
    ∃ (n : Nat) (vT : Val), RepV 14 KRempty vT (listV l) ∧
      loop n (metaState (listP l)) = some vT ∧
      ∃ m, runM m [] [] (listP l) = some (listV l) :=
  adequacy_data (listP_evd l)

/-- **The constructor/projector roundtrip through the interpreter**:
    `car (cons a b)` interprets to `a`'s value, for all 64 element
    pairs — an instance of the master theorem, no kernel reduction
    left. -/
theorem adequacy_car_cons (j k : Fin 8) :
    ∃ n, loop n (metaState (.car (.cons (.atom j) (.atom k)))) =
      some (.cell (.elem 2) (.elem j)) ∧
    ∃ m, runM m [] [] (.car (.cons (.atom j) (.atom k))) =
      some (.elem j) := by
  obtain ⟨n, vT, rep, hloop, m, hrun⟩ :=
    adequacy_data (.carCell (.cons (.atom j []) (.atom k [])))
  obtain rfl := elemR_inv rep
  exact ⟨n, hloop, m, hrun⟩

end AdequacyData
end Dichotomic
