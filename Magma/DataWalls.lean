import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

/-!
# The data walls, abstract: no internal pairing, no internal recognizer

Two impossibility results that force data structure onto the tape,
previously SAT records plus hand proofs (`MACHINE.md` §1), here
theorems uniform in the carrier size.

* **The recognizer wall** (`recognizer_wall`,
  `recognizer_wall_trivial`): a faithful core-preserving constructor
  on a finite core is automatically *surjective* on the core —
  injective self-maps of finite sets are onto — so its image is the
  whole core and any internal recognizer of the image is trivial: it
  accepts everything. Recognition of constructed data cannot be an
  instruction; it must inspect the heap. No absorber laws, no
  extensionality, no dichotomy needed: finiteness alone.

* **The pairing wall** (`pairing_wall`): no magma on a 2-pointed
  carrier with at least three core elements has internal curried
  pairing with both projections. The pair map
  `(a, b) ↦ (P ⬝ a) ⬝ b` is injective off the absorbers (the
  projections recover the components), so `c² ≤ n = c + 2` — and
  `c ≥ 3` makes that impossible. Pure pigeonhole. The `c = 2` edge
  case is *not* covered by counting (`4 ≤ 4`); its status is settled
  separately by exhaustive search
  (`scripts/pairing_wall_c2.py`).

Together with K-infinity and the completeness wall
(`CompletenessWall.lean`): universality, data structure, and
recognition of data all live outside the algebra, in the driver and
on the tape. The two-level architecture is forced, not chosen.
-/

set_option autoImplicit false

namespace Dichotomic
namespace DataWalls

open Function

/-- **The recognizer wall, step 1**: a faithful (injective on core)
    core-preserving constructor is surjective on the core. Injective
    self-maps of a finite set are onto. -/
theorem recognizer_wall (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ k : Fin n)
    (hcore : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      dot k x ≠ z₁ ∧ dot k x ≠ z₂)
    (hinj : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot k x = dot k y → x = y) :
    ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      ∃ y : Fin n, y ≠ z₁ ∧ y ≠ z₂ ∧ dot k y = x := by
  -- package the core as a subtype and k's action as a self-map
  let Core := {x : Fin n // x ≠ z₁ ∧ x ≠ z₂}
  let f : Core → Core := fun x =>
    ⟨dot k x.val, hcore x.val x.property.1 x.property.2⟩
  have hf : Injective f := by
    intro a b hab
    have := hinj a.val b.val a.property.1 a.property.2
      b.property.1 b.property.2 (congrArg Subtype.val hab)
    exact Subtype.ext this
  have hs : Surjective f := Finite.injective_iff_surjective.mp hf
  intro x hx1 hx2
  obtain ⟨y, hy⟩ := hs ⟨x, hx1, hx2⟩
  exact ⟨y.val, y.property.1, y.property.2, congrArg Subtype.val hy⟩

/-- **The recognizer wall, step 2**: any internal recognizer of the
    constructor's image is trivial — it accepts every core element,
    because the image *is* the core. A non-trivial recognizer of
    constructed data is impossible; `pair?` must read the heap. -/
theorem recognizer_wall_trivial (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ k ρ : Fin n)
    (hcore : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      dot k x ≠ z₁ ∧ dot k x ≠ z₂)
    (hinj : ∀ x y : Fin n, x ≠ z₁ → x ≠ z₂ → y ≠ z₁ → y ≠ z₂ →
      dot k x = dot k y → x = y)
    (hacc : ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ →
      (∃ y : Fin n, y ≠ z₁ ∧ y ≠ z₂ ∧ dot k y = x) → dot ρ x = z₁) :
    ∀ x : Fin n, x ≠ z₁ → x ≠ z₂ → dot ρ x = z₁ := by
  intro x hx1 hx2
  exact hacc x hx1 hx2 (recognizer_wall n dot z₁ z₂ k hcore hinj x hx1 hx2)

/-- **The pairing wall**: on a 2-pointed carrier with `n ≥ 5` (at
    least three core elements), no `P`, `fst`, `snd` give internal
    curried pairing with both projections on the core. The pair map
    is injective off the absorbers, so `(n−2)² ≤ n` — impossible for
    `n ≥ 5`. -/
theorem pairing_wall (n : Nat) (dot : Fin n → Fin n → Fin n)
    (z₁ z₂ : Fin n) (hz : z₁ ≠ z₂) (hn : 5 ≤ n)
    (P fst snd : Fin n)
    (hfst : ∀ a b : Fin n, a ≠ z₁ → a ≠ z₂ → b ≠ z₁ → b ≠ z₂ →
      dot fst (dot (dot P a) b) = a)
    (hsnd : ∀ a b : Fin n, a ≠ z₁ → a ≠ z₂ → b ≠ z₁ → b ≠ z₂ →
      dot snd (dot (dot P a) b) = b) : False := by
  classical
  -- the core, as a Finset
  let S : Finset (Fin n) := Finset.univ \ {z₁, z₂}
  have hmem : ∀ x : Fin n, x ∈ S ↔ (x ≠ z₁ ∧ x ≠ z₂) := by
    intro x
    simp [S, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      not_or]
  have hScard : S.card = n - 2 := by
    show (Finset.univ \ {z₁, z₂}).card = n - 2
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_pair hz,
        Finset.card_univ, Fintype.card_fin]
  -- the pair map, injective on core × core
  let g : Fin n × Fin n → Fin n := fun p => dot (dot P p.1) p.2
  have hginj : Set.InjOn g ↑(S ×ˢ S) := by
    intro p hp q hq hpq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hq
    obtain ⟨hp1, hp2⟩ := hp
    obtain ⟨hq1, hq2⟩ := hq
    rw [hmem] at hp1 hp2 hq1 hq2
    have h1 : p.1 = q.1 := by
      have e1 := hfst p.1 p.2 hp1.1 hp1.2 hp2.1 hp2.2
      have e2 := hfst q.1 q.2 hq1.1 hq1.2 hq2.1 hq2.2
      rw [show dot (dot P p.1) p.2 = g p from rfl, hpq] at e1
      rw [show dot (dot P q.1) q.2 = g q from rfl] at e2
      rw [← e1, ← e2]
    have h2 : p.2 = q.2 := by
      have e1 := hsnd p.1 p.2 hp1.1 hp1.2 hp2.1 hp2.2
      have e2 := hsnd q.1 q.2 hq1.1 hq1.2 hq2.1 hq2.2
      rw [show dot (dot P p.1) p.2 = g p from rfl, hpq] at e1
      rw [show dot (dot P q.1) q.2 = g q from rfl] at e2
      rw [← e1, ← e2]
    exact Prod.ext h1 h2
  -- counting: (n−2)² ≤ n
  have hcount : (S ×ˢ S).card ≤ n := by
    have h : (S ×ˢ S).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card_of_injOn g
        (fun p _ => Finset.mem_univ (g p)) hginj
    rwa [Finset.card_univ, Fintype.card_fin] at h
  rw [Finset.card_product, hScard] at hcount
  -- arithmetic: (n−2)·(n−2) ≤ n with n ≥ 5 is absurd
  have h3 : 3 ≤ n - 2 := by omega
  have : 3 * (n - 2) ≤ (n - 2) * (n - 2) :=
    Nat.mul_le_mul_right (n - 2) h3
  omega

end DataWalls
end Dichotomic
