# Categorical canonicality of (S, D, C): a proposal

Draft research note. The goal is to upgrade the paper's "(S, D, C) is a
theorem-rich slice of a rich landscape" stance into a theorem of the
form: *(S, D, C) corresponds, up to natural equivalence, to the unique
triple of universal properties [characterising property]*. This note
sketches a candidate categorical setting (slice/coslice over a 2-element
set, equipped with magma structure), translates S, D, C into that
setting, and lists what would have to be proved to make the canonicality
claim rigorous.

## 1. The ambient category

Let `2` denote the 2-element set `{z₁, z₂}`. Define

    C = (2 ↪ FinSet)_inj
      = the category whose objects are (X, ι : 2 ↪ X)
        with X ∈ FinSet and ι an injection,
        and whose morphisms are commuting triangles
        f : X → Y with f ∘ ι_X = ι_Y.

(This is the coslice category of `FinSet` under the fixed object `2`,
restricted to objects where the structure map is injective — equivalently,
finite sets with a distinguished 2-element subset.)

For an object `(X, ι)`, the *core* is `core(X) = X \ ι(2)`. The forgetful
`U : C → FinSet` simply forgets `ι`.

## 2. E2PM as algebra-like structure on C

An **E2PM-object** is a tuple `(X, ι, μ)` where:

  - `(X, ι) ∈ C`
  - `μ : X × X → X` is a binary operation,
  - **Absorbers:** `μ(ι(z_i), x) = ι(z_i)` for `i ∈ {1,2}` and all `x ∈ X`,
  - **No other absorbers:** `∀y. (∀x. μ(y, x) = y) → y ∈ ι(2)`,
  - **Extensionality:** the row map `λ : X → X^X`, `λ(a)(b) = μ(a, b)`,
    is injective.

E2PM-morphisms are morphisms in `C` preserving `μ`. Call this category
`E2PM`.

## 3. The row-image partial monoid R(X)

For each E2PM `(X, ι, μ)`, the row map `λ : X ↪ X^X` is injective by
extensionality. Let

    R(X) = λ(X) ⊆ X^X.

`R(X)` is a finite set of self-maps of `X`. It carries a *partial*
monoid structure: composition `g ∘ f` is defined precisely when
`g ∘ f ∈ R(X)` (i.e. equals some `λ(c)` for `c ∈ X`). By extensionality,
the witnessing `c` is unique when it exists.

The non-associativity theorem (paper Thm 3.9) is exactly the statement
that this partial monoid is *not* a total monoid: composition is generally
not closed.

The three-category decomposition partitions `R(X)`:

  - `R_abs(X) = {λ(z) : z ∈ ι(2)}` — the two constant maps onto `ι(z_i)`,
  - `R_clas(X) = {λ(a) : a ∈ core(X), λ(a)|_core ⊆ ι(2)}` — *classifier
    rows* (image on core lies in the 2-element absorber set),
  - `R_core(X) = {λ(a) : a ∈ core(X), λ(a)|_core ⊆ core}` — *core-preserving
    rows*.

D asserts both `R_clas` and `R_core` are non-empty and cover `λ(core)`
disjointly (paper Thm 3.1: every core element is in `R_clas` or `R_core`,
not both).

## 4. The canonicality conjectures

I propose that S, D, C correspond to three universal-property fragments
on `R(X)`. The translations are tautological in one direction; the
*canonicality* claim is that they are forced by named categorical
concepts.

### 4.1 S as a section-retraction in R_core

A **retract structure** on `core(X)` (in `FinSet`) is a section/retraction
pair `(s, r)` with `r ∘ s = id_core`. Restricted to `R(X)`, the section
and retraction must themselves be row maps:

  `S(X) ⇔ ∃ a, b ∈ core. λ(b) ∘ λ(a)|_core = id_core
                       ∧ λ(a) ∘ λ(b)|_core = id_core`

This is exactly the standard categorical retract notion, internalised
to the partial monoid of rows.

**Universal property version:** `core(X)` is a retract of `λ(X)` inside
`(R(X), ∘_partial)`, witnessed by elements of `core(X)` themselves.

### 4.2 D as a partial subobject classifier

In a topos, the subobject classifier `Ω` represents the contravariant
subobject functor: `Sub(B) ≅ Hom(B, Ω)` naturally in `B`.

In our setting, `ι(2) ≅ 1 + 1` is a candidate `Ω`. A classifier element
`τ ∈ core` provides a map `λ(τ)|_core : core → ι(2)` — the
*characteristic function* of the subset `λ(τ)⁻¹(z₁) ⊆ core`. So D
witnesses that `ι(2)` *partially* classifies subobjects of `core`: the
classified subsets are exactly the preimages of classifier rows.

D asserts:

  1. There exists at least one classifier `τ`, so `Sub_λ(core) ≠ ∅`.
  2. **The classification is exhaustive on rows:** every row `λ(a)|_core`
     either is a classifier (image ⊆ `ι(2)`) or is core-preserving
     (image ⊆ `core`). No row "leaks across" the partition. This is a
     codomain-purity condition on `R(X)`.
  3. There exists a non-classifier (a core-preserving row), ensuring the
     setting isn't degenerate (purely classifier).

**Universal property version:** `ι(2)` is a *partial subobject classifier*
for the row-action: for every row `λ(a)|_core`, exactly one of
"`λ(a)|_core` factors through `ι(2)`" or "`λ(a)|_core` factors through
`core`" holds, and both possibilities are realised.

### 4.3 C as a partial internal hom

In a Cartesian closed category, the internal hom `[A, B]` represents
`Hom(- × A, B)`. The non-associativity theorem (Thm 3.9) implies the
partial monoid `R(X)` is generally not Cartesian-closed-in-disguise, so
no global internal hom exists. But ICP asserts at least one *partial*
internal hom:

  `C(X) ⇔ ∃ a, b, c ∈ core. λ(a)|_core = λ(c) ∘ λ(b)|_core,
                            λ(b)|_core ⊆ core,
                            λ(a)|_core non-constant.`

This says: the row `λ(a)` factors through the partial composition `λ(c)
∘ λ(b)` on `core`. Equivalently, `(b, c)` represents a partial internal
hom for some object in the row-action: the action of `λ(c)` on the image
of `λ(b)` corresponds to the action of `λ(a)`.

**Universal property version:** `R(X)|_core` admits at least one
non-trivial partial composition closure: a triple `(a, b, c)` such that
`λ(a)` represents the partial hom `[λ(b), λ(c)]` on `core`.

## 5. The canonicality theorem (conjectural)

**Conjecture (canonicality of (S, D, C)).** Among *operational axioms*
of a specific syntactic shape — existential statements about elements of
core that translate into structural properties of `R(X)` — the
properties

  - section-retraction in `R_core`,
  - codomain-purity decomposition into `R_clas ⊔ R_core` with both
    inhabited,
  - non-trivial partial composition closure on `R_core`,

are pairwise independent and constitute the three minimal non-degenerate
universal-property fragments. Any other operational axiom either
refines one of these (e.g. "the retraction is in addition idempotent")
or asserts an unrelated witness condition (e.g. "core has a commutative
pair").

A more formal statement would require:

  1. Define a fragment of category-theoretic universal-property language
     (objects, morphisms, mono/epi/section/retraction, classifier
     diagrams, hom-representability).
  2. Define what it means for an operational axiom on E2PMs to *witness*
     a universal-property fragment.
  3. Prove that S, D, C are exactly the witnesses of three named
     orthogonal universal-property fragments (retract, partial
     classifier, partial internal hom), and that this is the unique
     such triple up to natural equivalence.

This would convert "(S, D, C) is a theorem-rich slice" into "(S, D, C)
is the canonical triple of partial-topos witnesses on E2PM."

## 6. What's tractable today

The most immediate verifications:

  1. **Translation lemma:** `S(X) ↔` retract-in-R_core; `D(X) ↔`
     R = R_abs ⊔ R_clas ⊔ R_core with both R_clas, R_core inhabited;
     `C(X) ↔` partial composition closure on R_core. These are
     translations, not theorems — should be straightforward.
  2. **Computational test:** verify the translations hold on the 3901
     N=5 S+D+C iso classes from the cartography. Confirms the
     row-image perspective is internally consistent. (Done; see
     `scripts/row_image_invariants.py`.)
  3. **Independence of the universal-property fragments:** show that
     each of (retract, partial classifier, partial internal hom) can
     hold independently of the other two. The paper's existing
     independence theorem already gives this on the operational side;
     the categorical translation inherits it.

What's *not* tractable in one sitting:

  4. **The canonicality theorem.** Defining the right fragment of
     universal-property language, characterising "operational witnesses",
     and proving uniqueness up to natural equivalence is a real
     research project — possibly several papers.

## 7. Why this still matters even before the canonicality theorem

Even without the full canonicality theorem, the row-image partial monoid
view does several useful things:

  - It removes the "operational capability" framing in favour of a
    structural one. S, D, C are properties of `R(X)` as a partial
    transformation algebra, not loose computational analogies.
  - It makes the connection to topos theory precise (and partial). D's
    relationship to a subobject classifier is no longer hand-waving;
    it's a definite "partial" classifier in a precisely identified
    sense.
  - It identifies the right object of study going forward: the
    *category of partial transformation algebras with three-category
    decomposition*, of which E2PMs are the ones realised by row maps
    of magmas. This category may have its own structure theory worth
    investigating.

## 8. Ruling out adjacent settings

Quick eliminations of other suggested categorical homes:

  - **Racks/quandles**: rack rows are bijections, ours include constant
    maps (absorbers). Theorem `no-rsd` (no right self-distributivity)
    makes this incompatibility formal — racks are right
    self-distributive.
  - **Sheaves on the inclusion poset of absorber-containing subsets**:
    natural construction (assigning the magma's restriction to each
    sub-2-pointed-set), but the gluing conditions are vacuous on a
    finite poset — the resulting "sheaf" is just a presheaf, and S, D,
    C don't obviously become sheaf conditions. Worth a more careful
    look but doesn't immediately produce structure.
  - **Operadic / monad-algebra view**: E2PMs are not algebras for any
    finitary monad on FinSet, because extensionality and the
    no-other-absorbers axiom are non-equational (Horn / quasi-equational).
    They sit in a quasi-variety.

The slice / row-image partial-monoid path is the most concrete that
survives.

## 9. Literature search: this setting is genuinely new

A separate agent-driven search of the partial-transformation /
restriction-category / Ehresmann-semigroup / Brandt-semigroup
literature found no prior class that matches E2PM-with-(S, D, C).
Closest published gravity wells:

  - **Restriction categories** (Cockett–Lack 2002–2007). The "partial
    map classifier" of *Restriction Categories II* is the closest
    formal analog of D — a monad whose Kleisli category classifies
    partial maps. Mismatch: restriction categories track partiality
    via *idempotents* on a total ambient hom, whereas in E2PM the
    partiality is the failure of `R(X)` to be closed under composition,
    not internal idempotent restriction. There's also no published
    analog of the forced 2-block sink (D's codomain dichotomy with
    exactly two absorbers).
  - **Ehresmann semigroups / constellations** (Lawson; Gould–Hollings).
    Subsemigroups of partial transformation semigroups closed under
    domain/range projections, with a distinguished projection
    semilattice. Mismatch: their two distinguished elements are
    idempotents in a semilattice, not constant maps; the codomain
    decomposition `R = R_abs ⊔ R_clas ⊔ R_core` has no Ehresmann
    analog.
  - **Brandt / completely 0-simple inverse semigroups.** Single zero,
    not two; require global inverses.

Conclusion (Agent A's report): no clean prior name. The closest
citation neighborhood is the Cockett–Lack restriction-category /
partial-classifier axis. The forced uniform decomposition at N=5 (every
S+D+C magma realising the same `(|R_clas|, |R_core|, |mixed|)` block
sizes) is a feature of this setting that does *not* show up in
restriction categories or Ehresmann semigroups, both of which admit
families parametrised by arbitrary semilattices. The setting is
genuinely new. A working name: **"2-classified row-image algebra"** or
"bipointed extensional partial transformation algebra with codomain-pure
decomposition".
