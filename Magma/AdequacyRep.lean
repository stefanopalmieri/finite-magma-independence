import Magma.FactorizationEqv
import Magma.AdequacyTags

/-!
# Adequacy campaign, rung 2: the representation relation

What it *means* for a value of the interpreted world to represent a
value of the direct world. META (the frozen image, `MetaImage.lean`)
represents object values as tagged cells `(tag . payload)` whose tags
are the five elements certified in `AdequacyTags.lean`. This file
defines:

* `RepV`/`RepEnv` — the mutual representation relation, parameterized
  by the knot-prefix length `K₀` (locations shift by the letrec
  knot's cells) and by an abstract continuation relation `KR`
  (host-absorbed continuations are behavioral, not structural; the
  step-indexed `KR` is rung 6's business — everything here is
  monotone in it, `RepV.mono`);
* `AlignedStore` — the one-tape invariant: the meta store is a fixed
  prefix `P` (the knot cells, written at startup and never again)
  followed by the direct store's cells in allocation order, pointwise
  represented — so the location map is canonically `i ↦ K₀ + i`,
  data-free;
* `chainNth` — META's environment lookup (`mnth`) at spec level,
  with the pleasant lemma that META's error default `(quo . tt)`
  represents the machine's error default `elem 0` — the two worlds
  agree even on their failure values;
* `EqvFree` — **the domain restriction, discovered at this rung**:
  the Eqv rung added a 14th form (`eqv`, sub-tagged 7 under the data
  tag) *after* META was written, and META's `mdata` tree reads
  sub-tag 7 as `ite`. META v1's adequacy domain is therefore the
  13-form fragment — proved here to be exactly the range of the
  certified `embed` from the data rung (`eqvFree_iff_embed`), so the
  domain is not an ad-hoc predicate but the image of the
  conservativity ladder.

The `IsTag` obligation from rung 0 becomes a theorem
(`RepV.car_isTag`): every represented value's car is one of the five
tags, so the discrimination trees are sound on everything the
relation can ever produce.
-/

set_option autoImplicit false

namespace Dichotomic
namespace AdequacyRep

open FactorizationEqv

/-! ## The eqv-free domain -/

/-- Programs of the 13-form fragment: no `eqv` anywhere. META v1's
    dispatch predates the eqv rung (its `mdata` tree reads sub-tag 7
    as `ite`), so this is the adequacy domain. -/
def EqvFree : Prog → Prop
  | .atom _ => True
  | .var _ => True
  | .lam b => EqvFree b
  | .app f x => EqvFree f ∧ EqvFree x
  | .callcc b => EqvFree b
  | .ref e => EqvFree e
  | .deref e => EqvFree e
  | .setref l e => EqvFree l ∧ EqvFree e
  | .cons a d => EqvFree a ∧ EqvFree d
  | .car e => EqvFree e
  | .cdr e => EqvFree e
  | .pairp e => EqvFree e
  | .ite c t e => EqvFree c ∧ EqvFree t ∧ EqvFree e
  | .eqv _ _ => False

theorem eqvFree_embed : ∀ p₀ : FactorizationData.Prog, EqvFree (embed p₀) := by
  intro p₀
  induction p₀ <;> simp [embed, EqvFree, *]

theorem exists_embed_of_eqvFree : ∀ p : Prog, EqvFree p → ∃ p₀, embed p₀ = p := by
  intro p
  induction p with
  | atom a => exact fun _ => ⟨.atom a, rfl⟩
  | var n => exact fun _ => ⟨.var n, rfl⟩
  | lam b ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨b₀, rfl⟩ := ih h; exact ⟨.lam b₀, rfl⟩
  | app f x ihf ihx =>
    intro h; simp only [EqvFree] at h
    obtain ⟨f₀, rfl⟩ := ihf h.1; obtain ⟨x₀, rfl⟩ := ihx h.2
    exact ⟨.app f₀ x₀, rfl⟩
  | callcc b ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨b₀, rfl⟩ := ih h; exact ⟨.callcc b₀, rfl⟩
  | ref e ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨e₀, rfl⟩ := ih h; exact ⟨.ref e₀, rfl⟩
  | deref e ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨e₀, rfl⟩ := ih h; exact ⟨.deref e₀, rfl⟩
  | setref l e ihl ihe =>
    intro h; simp only [EqvFree] at h
    obtain ⟨l₀, rfl⟩ := ihl h.1; obtain ⟨e₀, rfl⟩ := ihe h.2
    exact ⟨.setref l₀ e₀, rfl⟩
  | cons a d iha ihd =>
    intro h; simp only [EqvFree] at h
    obtain ⟨a₀, rfl⟩ := iha h.1; obtain ⟨d₀, rfl⟩ := ihd h.2
    exact ⟨.cons a₀ d₀, rfl⟩
  | car e ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨e₀, rfl⟩ := ih h; exact ⟨.car e₀, rfl⟩
  | cdr e ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨e₀, rfl⟩ := ih h; exact ⟨.cdr e₀, rfl⟩
  | pairp e ih =>
    intro h; simp only [EqvFree] at h
    obtain ⟨e₀, rfl⟩ := ih h; exact ⟨.pairp e₀, rfl⟩
  | ite c t e ihc iht ihe =>
    intro h; simp only [EqvFree] at h
    obtain ⟨c₀, rfl⟩ := ihc h.1
    obtain ⟨t₀, rfl⟩ := iht h.2.1
    obtain ⟨e₀, rfl⟩ := ihe h.2.2
    exact ⟨.ite c₀ t₀ e₀, rfl⟩
  | eqv a b _ _ =>
    intro h; simp only [EqvFree] at h

/-- The adequacy domain is exactly the range of the certified
    embedding from the data rung — not an ad-hoc predicate. -/
theorem eqvFree_iff_embed (p : Prog) :
    EqvFree p ↔ ∃ p₀ : FactorizationData.Prog, embed p₀ = p :=
  ⟨exists_embed_of_eqvFree p, by rintro ⟨p₀, rfl⟩; exact eqvFree_embed p₀⟩

/-- Quotation is injective (immediate from the certified
    `decode_quote`): a closure's body is determined by the quotation
    META stores. -/
theorem quoteD_inj : Function.Injective quoteD := by
  intro p q h
  have hp := decode_quote p
  rw [h, decode_quote q] at hp
  exact (Option.some.inj hp).symm

/-! ## The representation relation -/

mutual
  /-- Tagged interpreted value (left) represents direct value
      (right). Parameters: `K₀` the knot-prefix length (locations
      shift by it), `KR` the continuation relation (abstract here;
      step-indexed at rung 6). Tags per `AdequacyTags.lean`. -/
  inductive RepV (K₀ : Nat) (KR : Kont → Kont → Prop) : Val → Val → Prop where
    | elem (k : Fin 8) :
        RepV K₀ KR (.cell (.elem 2) (.elem k)) (.elem k)
    | clos {ρT : Val} {ρ : Env} (body : Prog) :
        RepEnv K₀ KR ρT ρ →
        RepV K₀ KR (.cell (.elem 3) (.cell (quoteD body) ρT)) (.clos body ρ)
    | kont {κT κ : Kont} :
        KR κT κ →
        RepV K₀ KR (.cell (.elem 4) (.cont κT)) (.cont κ)
    | loc (i : Nat) :
        RepV K₀ KR (.cell (.elem 5) (.loc (K₀ + i))) (.loc i)
    | cell {aT dT a d : Val} :
        RepV K₀ KR aT a → RepV K₀ KR dT d →
        RepV K₀ KR (.cell (.elem 6) (.cell aT dT)) (.cell a d)

  /-- META's environments are raw cons chains of tagged values ending
      in `tt` (the image's initial environment is the atom `tt`). -/
  inductive RepEnv (K₀ : Nat) (KR : Kont → Kont → Prop) : Val → Env → Prop where
    | nil : RepEnv K₀ KR (.elem 0) []
    | cons {vT ρT : Val} {v : Val} {ρ : Env} :
        RepV K₀ KR vT v → RepEnv K₀ KR ρT ρ →
        RepEnv K₀ KR (.cell vT ρT) (v :: ρ)
end

/-! ### Monotonicity in the continuation relation

Needed for step-indexing at rung 6: enlarging `KR` preserves every
representation derivation. -/

mutual
  theorem RepV.mono {K₀ : Nat} {KR KR' : Kont → Kont → Prop}
      (hK : ∀ κT κ, KR κT κ → KR' κT κ) :
      ∀ {vT v : Val}, RepV K₀ KR vT v → RepV K₀ KR' vT v
    | _, _, .elem k => .elem k
    | _, _, .clos body hρ => .clos body (RepEnv.mono hK hρ)
    | _, _, .kont hκ => .kont (hK _ _ hκ)
    | _, _, .loc i => .loc i
    | _, _, .cell ha hd => .cell (RepV.mono hK ha) (RepV.mono hK hd)

  theorem RepEnv.mono {K₀ : Nat} {KR KR' : Kont → Kont → Prop}
      (hK : ∀ κT κ, KR κT κ → KR' κT κ) :
      ∀ {ρT : Val} {ρ : Env}, RepEnv K₀ KR ρT ρ → RepEnv K₀ KR' ρT ρ
    | _, _, .nil => .nil
    | _, _, .cons hv hρ => .cons (RepV.mono hK hv) (RepEnv.mono hK hρ)
end

/-! ### Soundness of the discrimination trees on represented values -/

/-- Every represented value is a tagged cell whose tag is in the
    alphabet — so rung 0's discrimination matrix applies to
    everything the relation can produce, and the honesty lemma
    `tagloc_accepts_ff` can never bite. -/
theorem RepV.car_isTag {K₀ : Nat} {KR : Kont → Kont → Prop} {vT v : Val}
    (h : RepV K₀ KR vT v) :
    ∃ t p, vT = .cell (.elem t) p ∧ MetaTags.IsTag t := by
  cases h with
  | elem k => exact ⟨2, _, rfl, by decide⟩
  | clos body hρ => exact ⟨3, _, rfl, by decide⟩
  | kont hκ => exact ⟨4, _, rfl, by decide⟩
  | loc i => exact ⟨5, _, rfl, by decide⟩
  | cell ha hd => exact ⟨6, _, rfl, by decide⟩

/-! ### Inversion lemmas (rung-3 workhorses) -/

theorem RepV.elem_inv {K₀ : Nat} {KR : Kont → Kont → Prop} {p v : Val}
    (h : RepV K₀ KR (.cell (.elem 2) p) v) :
    ∃ k : Fin 8, p = .elem k ∧ v = .elem k := by
  cases h with
  | elem k => exact ⟨k, rfl, rfl⟩

theorem RepV.loc_inv {K₀ : Nat} {KR : Kont → Kont → Prop} {j : Nat} {v : Val}
    (h : RepV K₀ KR (.cell (.elem 5) (.loc j)) v) :
    ∃ i, j = K₀ + i ∧ v = .loc i := by
  cases h with
  | loc i => exact ⟨i, rfl, rfl⟩

/-- A represented closure's stored quotation decodes to its body:
    the bridge from the relation to the certified `decode_quote`. -/
theorem RepV.clos_decodes {K₀ : Nat} {KR : Kont → Kont → Prop}
    {q ρT : Val} {body : Prog} {ρ : Env}
    (h : RepV K₀ KR (.cell (.elem 3) (.cell q ρT)) (.clos body ρ)) :
    decodeD q = some body := by
  cases h with
  | clos body hρ => exact decode_quote body

/-! ## Environment lookup at spec level -/

/-- META's `mnth`, abstracted over a `Nat` index (rung 3 connects the
    numeral walk to `valToNat`). The fall-through arm is META's error
    default `(quo . tt)`. -/
def chainNth : Val → Nat → Val
  | .cell v _, 0 => v
  | .cell _ ρT, n + 1 => chainNth ρT n
  | _, _ => .cell (.elem 2) (.elem 0)

/-- Lookup preserves representation — including on misses, where
    META's default `(quo . tt)` represents the machine's default
    `elem 0`: the two worlds agree even on their failure values. -/
theorem RepEnv.chainNth {K₀ : Nat} {KR : Kont → Kont → Prop} :
    ∀ {ρT : Val} {ρ : Env}, RepEnv K₀ KR ρT ρ →
      ∀ n, RepV K₀ KR (chainNth ρT n) (ρ.getD n (.elem 0))
  | _, _, .nil, n => by
    simp only [AdequacyRep.chainNth, List.getD]
    exact .elem 0
  | _, _, .cons hv hρ, 0 => by
    simpa [AdequacyRep.chainNth] using hv
  | _, _, .cons hv hρ, n + 1 => by
    simpa [AdequacyRep.chainNth] using RepEnv.chainNth hρ n

/-! ## The one-tape alignment invariant -/

/-- The meta store is the knot prefix `P` (fixed at startup, never
    written again) followed by the direct store's cells in allocation
    order, pointwise represented. The location map is canonically
    `i ↦ K₀ + i` — no alignment data needed, because META allocates
    exactly when the object program allocates. -/
def AlignedStore (K₀ : Nat) (KR : Kont → Kont → Prop)
    (P σT σ : Store) : Prop :=
  P.length = K₀ ∧ ∃ σ', σT = P ++ σ' ∧ List.Forall₂ (RepV K₀ KR) σ' σ

/-! ### Forall₂ plumbing -/

theorem forall₂_getElem? {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      ∀ {i : Nat} {b : β}, l'[i]? = some b → ∃ a, l[i]? = some a ∧ R a b := by
  intro l l' h
  induction h with
  | nil => intro i b hb; simp at hb
  | @cons a b l l' hR _ ih =>
    intro i c hc
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨a, rfl, hR⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact ih hc

theorem forall₂_set {α β : Type*} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      ∀ {i : Nat} {a : α} {b : β}, R a b →
        List.Forall₂ R (l.set i a) (l'.set i b) := by
  intro l l' h
  induction h with
  | nil => intro i a b _; simp
  | @cons x y l l' hR hF ih =>
    intro i a b hab
    cases i with
    | zero => simpa using List.Forall₂.cons hab hF
    | succ i => simpa using List.Forall₂.cons hR (ih hab)

theorem forall₂_append {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      ∀ {l₃ : List α} {l₄ : List β}, List.Forall₂ R l₃ l₄ →
        List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄) := by
  intro l₁ l₂ h
  induction h with
  | nil => intro _ _ h'; simpa using h'
  | cons hR _ ih => intro _ _ h'; simpa using List.Forall₂.cons hR (ih h')

theorem set_append_right' {α : Type*} (P l : List α) (i : Nat) (a : α) :
    (P ++ l).set (P.length + i) a = P ++ l.set i a := by
  induction P with
  | nil => simp
  | cons x P ih =>
    simp only [List.cons_append, List.length_cons]
    rw [Nat.add_right_comm]
    exact congrArg (x :: ·) ih

/-! ### The alignment lemmas -/

theorem AlignedStore.length {K₀ : Nat} {KR : Kont → Kont → Prop}
    {P σT σ : Store} (h : AlignedStore K₀ KR P σT σ) :
    σT.length = K₀ + σ.length := by
  obtain ⟨hP, σ', rfl, hF⟩ := h
  simp [List.length_append, hP, hF.length_eq]

/-- Reads correspond: a direct read at `i` is a meta read at `K₀ + i`
    of a representing value. -/
theorem AlignedStore.read {K₀ : Nat} {KR : Kont → Kont → Prop}
    {P σT σ : Store} (h : AlignedStore K₀ KR P σT σ)
    {i : Nat} {v : Val} (hv : σ[i]? = some v) :
    ∃ vT, σT[K₀ + i]? = some vT ∧ RepV K₀ KR vT v := by
  obtain ⟨hP, σ', rfl, hF⟩ := h
  obtain ⟨vT, hvT, hR⟩ := forall₂_getElem? hF hv
  refine ⟨vT, ?_, hR⟩
  rw [List.getElem?_append_right (by omega)]
  have : K₀ + i - P.length = i := by omega
  rw [this]
  exact hvT

/-- Writes correspond and never touch the knot prefix. -/
theorem AlignedStore.write {K₀ : Nat} {KR : Kont → Kont → Prop}
    {P σT σ : Store} (h : AlignedStore K₀ KR P σT σ)
    {i : Nat} {vT v : Val} (hR : RepV K₀ KR vT v) :
    AlignedStore K₀ KR P (σT.set (K₀ + i) vT) (σ.set i v) := by
  obtain ⟨hP, σ', rfl, hF⟩ := h
  refine ⟨hP, σ'.set i vT, ?_, forall₂_set hF hR⟩
  rw [← hP, set_append_right']

/-- Allocations correspond: appending related values preserves
    alignment. -/
theorem AlignedStore.alloc {K₀ : Nat} {KR : Kont → Kont → Prop}
    {P σT σ : Store} (h : AlignedStore K₀ KR P σT σ)
    {vT v : Val} (hR : RepV K₀ KR vT v) :
    AlignedStore K₀ KR P (σT ++ [vT]) (σ ++ [v]) := by
  obtain ⟨hP, σ', rfl, hF⟩ := h
  exact ⟨hP, σ' ++ [vT], by rw [List.append_assoc],
    forall₂_append hF (List.Forall₂.cons hR List.Forall₂.nil)⟩

/-- The fresh location after corresponding allocations is itself
    represented: the direct machine's next index is `σ.length`,
    META's is `K₀ + σ.length` — exactly the `loc` clause. -/
theorem AlignedStore.fresh_loc {K₀ : Nat} {KR : Kont → Kont → Prop}
    {P σT σ : Store} (h : AlignedStore K₀ KR P σT σ) :
    σT.length = K₀ + σ.length ∧
      RepV K₀ KR (.cell (.elem 5) (.loc (K₀ + σ.length))) (.loc σ.length) :=
  ⟨h.length, .loc _⟩

/-- At startup: the knot prefix alone is aligned with the empty
    direct store (rung 3 proves running the image's knot produces a
    concrete `P` of length `K₀`). -/
theorem AlignedStore.init {K₀ : Nat} {KR : Kont → Kont → Prop}
    {P : Store} (hP : P.length = K₀) :
    AlignedStore K₀ KR P P [] :=
  ⟨hP, [], by simp, List.Forall₂.nil⟩

end AdequacyRep
end Dichotomic
