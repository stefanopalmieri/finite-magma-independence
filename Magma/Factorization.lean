import Magma.ArtifactN8

/-!
# The Factorization Theorem: Metacircularity Certified Against the Algebra

The two-level correctness theorem promised in `MACHINE.md` §9, in its
minimal honest form. A driver is defined whose **only semantic step is
one Cayley-table lookup** in the certified N=8 artifact, and whose
user-level `quote`/`eval` route atomic instructions through the table's
internal duality (rows 2 and 3), with the two absorbers self-representing
— exactly R7RS's self-evaluating literals. Compound quotations become
inert heap cells, as the pairing wall requires.

The headline result, `eval_quote`: for **every** program p,

    evalD (quoteD p) = run p

— R7RS §6.12's defining law, *derived* rather than assumed. The
structural induction's base case is the bridge lemma `eatom_qatom`,
which is discharged by `decide` against the artifact table and is
precisely its certified retraction law (`ret_sec` of `artifactA8_frm`)
plus absorber self-representation. So the driver's metacircularity
factors through the machine-checked internal duality: change the table
and the law breaks; keep the table and the law holds at every program
size.

This also realizes the two-level architecture's proof obligation:
user-level quotation is sort-collapsing (everything becomes data — cells
or code-elements), which `Sorting.lean` proves is impossible to pair
with an *internal* eval (`constN_blocks_retraction`); here the collapse
lives at the driver level while its atomic core is the table's faithful
swap duality. Two quotes, two levels, one commuting law.

Scope note: this is the minimal calculus (atoms and application), not
R7RS — the extension path (environments, store, control) is
`MACHINE.md` §§4–6; the shape of this file's induction is what those
extensions must preserve.
-/

set_option autoImplicit false

namespace Dichotomic
namespace Factorization

/-- Programs: the driver's active syntax — instructions of the N=8
    artifact, and application. -/
inductive Prog where
  | atom : Fin 8 → Prog
  | app  : Prog → Prog → Prog
deriving DecidableEq

/-- Tape values: machine elements, and inert heap cells (the pairing
    wall forces compound data onto the tape). -/
inductive Val where
  | elem : Fin 8 → Val
  | cell : Val → Val → Val
deriving DecidableEq

/-- The driver's evaluator. The only semantic step is a table lookup;
    applying heap data (or applying to it) cuts against the halt-true
    absorber — errors are absorber values, per the machine reading. -/
def run : Prog → Val
  | .atom a => .elem a
  | .app f x =>
    match run f, run x with
    | .elem a, .elem b => .elem (dotA8 a b)
    | _, _ => .elem 0

/-- Atomic quotation: absorbers are self-representing (self-evaluating
    literals); core instructions are quoted by the table's internal
    quote, row 2. -/
def qatom (a : Fin 8) : Fin 8 :=
  if a = 0 ∨ a = 1 then a else dotA8 2 a

/-- Atomic code evaluation: the table's internal eval, row 3. -/
def eatom (a : Fin 8) : Fin 8 :=
  if a = 0 ∨ a = 1 then a else dotA8 3 a

/-- **The bridge lemma**: the driver's atomic round trip is the
    artifact's certified retraction law (plus absorber
    self-representation), checked directly against the table. -/
theorem eatom_qatom : ∀ a : Fin 8, eatom (qatom a) = a := by decide

/-- Driver-level (user-level) quote: programs to tape representations.
    Compound programs become inert cells — user quotation is
    sort-collapsing, as the theory requires of it. -/
def quoteD : Prog → Val
  | .atom a => .elem (qatom a)
  | .app f x => .cell (quoteD f) (quoteD x)

/-- Driver-level decode: the reading half of user-level eval. -/
def decodeD : Val → Option Prog
  | .elem b => some (.atom (eatom b))
  | .cell u v =>
    match decodeD u, decodeD v with
    | some f, some x => some (.app f x)
    | _, _ => none

/-- User-level eval: decode the representation, then run it; a
    non-code value cuts to the halt channel. -/
def evalD (v : Val) : Val :=
  match decodeD v with
  | some p => run p
  | none => .elem 0

/-- On core instructions, user quotation **is** the internal quote row. -/
theorem quote_atom_core (a : Fin 8) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    quoteD (.atom a) = .elem (dotA8 2 a) := by
  simp [quoteD, qatom, h0, h1]

/-- On core codes, decoding **is** the internal eval row. -/
theorem decode_atom_core (a : Fin 8) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    decodeD (.elem a) = some (.atom (dotA8 3 a)) := by
  simp [decodeD, eatom, h0, h1]

/-- Compound quotations are inert heap data, never applications. -/
theorem quote_app_is_cell (f x : Prog) :
    quoteD (.app f x) = .cell (quoteD f) (quoteD x) := rfl

/-- The driver's only semantic step is the table. -/
theorem run_app_atom (a b : Fin 8) :
    run (.app (.atom a) (.atom b)) = .elem (dotA8 a b) := rfl

/-- **Representation adequacy**: decoding a quotation recovers the
    program exactly. The base case of the induction is `eatom_qatom` —
    the certified table law carried from atoms to all programs. -/
theorem decode_quote (p : Prog) : decodeD (quoteD p) = some p := by
  induction p with
  | atom a => simp [quoteD, decodeD, eatom_qatom]
  | app f x ihf ihx => simp [quoteD, decodeD, ihf, ihx]

/-- **The factorization theorem (metacircularity)**: user-level
    `eval (quote p)` yields exactly the value of `p`, for every program.
    The driver's defining Lisp law is a consequence of the artifact's
    internal duality — metacircularity certified against the algebra. -/
theorem eval_quote (p : Prog) : evalD (quoteD p) = run p := by
  simp [evalD, decode_quote]

end Factorization
end Dichotomic
