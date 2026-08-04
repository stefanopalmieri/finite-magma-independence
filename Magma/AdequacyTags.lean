import Magma.ArtifactN8

/-!
# Adequacy campaign, rung 0: the tag discrimination trees

First certified rung of the interpreter-adequacy campaign
(`ADEQUACY.md`): the metacircular evaluator `META_CLOSED`
(kamea-machine, `crates/kamea-scheme/src/lib.rs`) represents object
values as tagged cells whose **tags are table elements** —

| tag | represents |
|---|---|
| `quo` (2)    | element |
| `evl` (3)    | closure |
| `shf` (4)    | continuation (host-absorbed) |
| `data?` (5)  | location |
| `judge?` (6) | cell |

— and discriminates them with **extensionality decision trees**: no
`eqv?`, only applications and machine truthiness. The trees probe four
columns of the table: `data? ⬝ g`, `shift? ⬝ g`, `g ⬝ ff`, `g ⬝ quo`.

This file transcribes the five discriminators at table level (Bool
functions over `dotA8`, mirroring the Scheme trees arm for arm) and
certifies, by `decide`:

* each discriminator accepts exactly its own tag on the tag alphabet;
* the five discriminators partition the tag alphabet (exactly one
  fires on each tag);
* the four probes separate the five tags **through truthiness alone**
  (the trees never inspect a probe result beyond its truth value);
* the honesty lemma `tagloc_accepts_ff`: off the tag alphabet the
  trees are *not* sound (`tagloc` accepts the reject absorber), so
  every later rung's invariant must carry "the car of a tagged value
  is a tag" — recorded here as a theorem so the requirement cannot be
  forgotten.

The bridge from these table-level facts to the running trees (β +
`ite` steps on the certified machine) is rung 3's business; truthiness
`≠ ff` is the machine's certified `ite` law (`FactorizationData`).
-/

set_option autoImplicit false

namespace Dichotomic
namespace MetaTags

/-- Machine truthiness at table level: `ff` (element 1) is the only
    false value — the certified `ite` discipline. -/
def truthy (e : Fin 8) : Bool := e != 1

/-- `mnot (data? t)` — true on the operator block {quote, eval, shift}. -/
def minn (t : Fin 8) : Bool := !(truthy (dotA8 5 t))

/-- `mnot (shift? t)` — true exactly on {shift, shift?}. -/
def mshf (t : Fin 8) : Bool := !(truthy (dotA8 7 t))

/-- Tag test for `quo` (element payload): operator, not shift, and
    `g ⬝ ff` truthy. -/
def tage (g : Fin 8) : Bool := minn g && !(mshf g) && truthy (dotA8 g 1)

/-- Tag test for `evl` (closure payload): operator, not shift, and
    `g ⬝ ff` falsy. -/
def tagclo (g : Fin 8) : Bool := minn g && !(mshf g) && !(truthy (dotA8 g 1))

/-- Tag test for `shf` (continuation payload): operator and shift. -/
def tagk (g : Fin 8) : Bool := minn g && mshf g

/-- Tag test for `data?` (location payload): non-operator with
    `g ⬝ quo` falsy. -/
def tagloc (g : Fin 8) : Bool := !(minn g) && !(truthy (dotA8 g 2))

/-- Tag test for `judge?` (cell payload): non-operator with
    `g ⬝ quo` truthy. -/
def tagcell (g : Fin 8) : Bool := !(minn g) && truthy (dotA8 g 2)

/-- The tag alphabet: the five elements META uses as value tags. -/
def IsTag (g : Fin 8) : Prop :=
  g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6

instance (g : Fin 8) : Decidable (IsTag g) := by
  unfold IsTag; infer_instance

/-- `minn` reads the sort: true exactly on the operator block. -/
theorem minn_iff_operator :
    ∀ t : Fin 8, minn t = true ↔ (t = 2 ∨ t = 3 ∨ t = 4) := by decide

/-- `mshf` reads the shift pair: true exactly on {shift, shift?}. -/
theorem mshf_iff :
    ∀ t : Fin 8, mshf t = true ↔ (t = 4 ∨ t = 7) := by decide

/-- On the tag alphabet, `tage` accepts exactly the element tag. -/
theorem tage_on_tags :
    ∀ g : Fin 8, IsTag g → (tage g = true ↔ g = 2) := by decide

/-- On the tag alphabet, `tagclo` accepts exactly the closure tag. -/
theorem tagclo_on_tags :
    ∀ g : Fin 8, IsTag g → (tagclo g = true ↔ g = 3) := by decide

/-- On the tag alphabet, `tagk` accepts exactly the continuation tag. -/
theorem tagk_on_tags :
    ∀ g : Fin 8, IsTag g → (tagk g = true ↔ g = 4) := by decide

/-- On the tag alphabet, `tagloc` accepts exactly the location tag. -/
theorem tagloc_on_tags :
    ∀ g : Fin 8, IsTag g → (tagloc g = true ↔ g = 5) := by decide

/-- On the tag alphabet, `tagcell` accepts exactly the cell tag. -/
theorem tagcell_on_tags :
    ∀ g : Fin 8, IsTag g → (tagcell g = true ↔ g = 6) := by decide

/-- **Partition of unity**: on the tag alphabet exactly one
    discriminator fires — dispatch in `mapply`/`mdata`/`mstore` is
    total and unambiguous. -/
theorem tags_partitioned :
    ∀ g : Fin 8, IsTag g →
      (tage g).toNat + (tagclo g).toNat + (tagk g).toNat +
        (tagloc g).toNat + (tagcell g).toNat = 1 := by decide

/-- **Four probes suffice, through truthiness alone**: two tags that
    agree on the truth values of `data? ⬝ g`, `shift? ⬝ g`, `g ⬝ ff`,
    and `g ⬝ quo` are equal. This is the precise sense in which META
    needs no `eqv?`: the trees observe only truthiness of four
    applications, and that already separates the alphabet. -/
theorem four_probes_separate_tags :
    ∀ g h : Fin 8, IsTag g → IsTag h →
      truthy (dotA8 5 g) = truthy (dotA8 5 h) →
      truthy (dotA8 7 g) = truthy (dotA8 7 h) →
      truthy (dotA8 g 1) = truthy (dotA8 h 1) →
      truthy (dotA8 g 2) = truthy (dotA8 h 2) →
      g = h := by decide

/-- **Honesty lemma**: off the tag alphabet the trees are not sound —
    `tagloc` accepts the reject absorber. Every later rung must
    therefore carry the invariant "the car of a tagged value is a
    tag"; this theorem exists so the requirement is a certified fact
    rather than a comment. -/
theorem tagloc_accepts_ff : tagloc 1 = true := by decide

end MetaTags
end Dichotomic
