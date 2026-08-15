import Magma.ArtifactN8
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

/-!
# The canonicity census, certified

Two finite facts from the census (`scripts/canonicality/
census_frame_n8.py`), promoted to theorems:

* **`autA8_trivial`** — the artifact has *no* symmetries: every
  automorphism of the table is the identity. This sharpens
  `MirrorRow`'s `|Aut| ≤ 2` to equality with 1: the object is fully
  rigid.
* **`selfloc_unique`** (with `selfloc_attained`) — **the canonicity
  theorem at the core block**: every member of the hygienic,
  ICP-carrying, judge-closed frame family satisfying *self-location*
  is `S₃ × S₃`-conjugate to the artifact's core block. (ICP enters as
  the complementary introspector: `cArr` below assigns χ's complement
  — which in the swap world *is* `data? ∘ quote` — as one of the
  three classifier rows. The census funnel's own arrow for it is
  213,872 → 6,682 orbits; see `census_frame_n8.py`.) Self-location is
  the placement principle the census discovered to be the exact
  separator of the artifact's orbit among the eighteen: the judge
  row is held by the classifier member of the very cycle it judges,
  the shift operator is held by the target of its own swap, and the
  introspector is held by the cycle the judge swap leaves untouched.
  Self-reference selects the self-interpreter's home.

The family is parameterized as the census derived it from the frame
(each reduction backed by a certified theorem: the retraction forces
eval's row to be quote's inverse, `SortIntrospection` forces the
introspector's row exactly, class-swapping and faithfulness force
block-swap bijections; hygiene makes quote an involution, so eval's
row *equals* quote's): a quote involution (`Equiv.Perm (Fin 3)`,
its C→N half the inverse of its N→C half), an ordered pair of
distinct quote-cycles for the judge swap, the position of γ among
the operator elements, and the assignment of the three classifier
rows. 648 configurations; the theorem quantifies over all of them.

The frame is invisible to the absorber rows and columns, so the
theorem lives at the core block — the full-table residue beyond it
is the z-cells, outside the frame's vocabulary by construction.
-/

set_option autoImplicit false

namespace Dichotomic
namespace CanonicityCensus

/-! ## Full rigidity -/

set_option maxHeartbeats 1000000 in
/-- **The artifact has no symmetries**: every automorphism of the
    table is the identity — `MirrorRow`'s `|Aut| ≤ 2`, sharpened. -/
theorem autA8_trivial :
    ∀ π : Equiv.Perm (Fin 8),
      (∀ a b, π (dotA8 a b) = dotA8 (π a) (π b)) → π = 1 := by
  native_decide

/-! ## The core-block family -/

/-- Core positions `0,1,2` = operator elements `2,3,4`;
    positions `3,4,5` = classifier elements `5,6,7`. -/
def nPos (i : Fin 3) : Fin 6 := ⟨i, by omega⟩
def cPos (i : Fin 3) : Fin 6 := ⟨i.val + 3, by omega⟩

/-- The quote involution determined by its N→C half. -/
def sMap (pN : Equiv.Perm (Fin 3)) (x : Fin 6) : Fin 6 :=
  if h : x.val < 3 then cPos (pN ⟨x.val, h⟩)
  else nPos (pN.symm ⟨x.val - 3, by omega⟩)

/-- The class-respecting double transposition exchanging quote-cycles
    `p` and `q` (cycle `i` = `{nPos i, cPos (pN i)}`). -/
def cycSwap (pN : Equiv.Perm (Fin 3)) (p q : Fin 3) (x : Fin 6) : Fin 6 :=
  if x = nPos p then nPos q else if x = nPos q then nPos p
  else if x = cPos (pN p) then cPos (pN q)
  else if x = cPos (pN q) then cPos (pN p) else x

/-- γ's core row: the judge swap composed with quote. -/
def gMap (pN : Equiv.Perm (Fin 3)) (p q : Fin 3) (x : Fin 6) : Fin 6 :=
  cycSwap pN p q (sMap pN x)

/-- Core values into the table's alphabet. -/
def coreVal (x : Fin 6) : Fin 8 := ⟨x.val + 2, by omega⟩

/-- The block of a family member: `gpos` holds γ, the other two
    operator elements hold quote (hygiene: eval's row equals
    quote's); `cArr` assigns the introspector, its complement, and
    the judge row to the classifier elements. -/
def block (pN : Equiv.Perm (Fin 3)) (p q gpos : Fin 3)
    (cArr : Equiv.Perm (Fin 3)) (y x : Fin 6) : Fin 8 :=
  if h : y.val < 3 then
    if (⟨y.val, h⟩ : Fin 3) = gpos then coreVal (gMap pN p q x)
    else coreVal (sMap pN x)
  else
    let r := cArr.symm ⟨y.val - 3, by omega⟩
    if r = 0 then (if x.val < 3 then 1 else 0)          -- introspector χ
    else if r = 1 then (if x.val < 3 then 0 else 1)     -- complement
    else if x = nPos q ∨ x = cPos (pN q) then 1 else 0  -- judge row

/-- **Self-location**: γ is held by the target cycle's operator
    element, the judge row by the target cycle's classifier element,
    and the introspector by the untouched cycle's classifier
    element. -/
@[reducible] def SelfLoc (pN : Equiv.Perm (Fin 3)) (p q gpos : Fin 3)
    (cArr : Equiv.Perm (Fin 3)) : Prop :=
  gpos = q ∧ cArr 2 = pN q ∧ cArr 0 ≠ pN p ∧ cArr 0 ≠ pN q

/-- The symmetry action: `(πN, πC)` on positions… -/
def sigma6 (πN πC : Equiv.Perm (Fin 3)) (x : Fin 6) : Fin 6 :=
  if h : x.val < 3 then nPos (πN ⟨x.val, h⟩)
  else cPos (πC ⟨x.val - 3, by omega⟩)

/-- …and on values (absorber values fixed, core values follow). -/
def sigmaVal (πN πC : Equiv.Perm (Fin 3)) (v : Fin 8) : Fin 8 :=
  if h : v.val < 2 then v
  else coreVal (sigma6 πN πC ⟨v.val - 2, by omega⟩)

/-- The artifact's core block (rows and arguments `2..7`). -/
def artBlock (y x : Fin 6) : Fin 8 :=
  dotA8 ⟨y.val + 2, by omega⟩ ⟨x.val + 2, by omega⟩

set_option maxHeartbeats 1000000 in
/-- **The canonicity theorem at the core block**: every self-locating
    member of the hygienic judge-closed frame family is conjugate to
    the artifact. All 648 parameterizations, decided natively. -/
theorem selfloc_unique :
    ∀ (pN : Equiv.Perm (Fin 3)) (p q gpos : Fin 3)
      (cArr : Equiv.Perm (Fin 3)), p ≠ q →
      SelfLoc pN p q gpos cArr →
      ∃ πN πC : Equiv.Perm (Fin 3),
        ∀ y x : Fin 6,
          sigmaVal πN πC
            (block pN p q gpos cArr (sigma6 πN.symm πC.symm y)
              (sigma6 πN.symm πC.symm x)) = artBlock y x := by
  native_decide

set_option maxHeartbeats 1000000 in
/-- **Sharpness**: the artifact's core block itself realizes a
    self-locating member of the family. -/
theorem selfloc_attained :
    ∃ (pN : Equiv.Perm (Fin 3)) (p q gpos : Fin 3)
      (cArr : Equiv.Perm (Fin 3)),
      p ≠ q ∧ SelfLoc pN p q gpos cArr ∧
      ∀ y x : Fin 6, block pN p q gpos cArr y x = artBlock y x := by
  native_decide

end CanonicityCensus
end Dichotomic
