-- Pairwise Independence of Splitting, Dichotomy, and Composition
-- in Finite Extensional Magmas
--
-- 30 paper files (333 theorems) + 1 supplementary (5 theorems), zero sorry.

-- Foundation
import Magma.Dichotomic
import Magma.NoCommutativity
import Magma.OneSidedSeparation
import Magma.Functoriality
import Magma.SelfSimulation  -- supplementary: not referenced by paper
import Magma.CapabilityInvariance

-- Independence counterexamples
import Magma.Countermodel
import Magma.Countermodels10
import Magma.E2PM
import Magma.ICP

-- Axiom-reduction prototype: D_struct + ICP ⇒ DichotomicRetractMagma
import Magma.DStruct

-- Coexistence witnesses
import Magma.Witness5
import Magma.Witness6
import Magma.Witness10

-- Parametric scaling witness: R+D+ICP for all N ≥ 5 (Theorem 7.3)
import Magma.WitnessAllN

-- Role rigidity (individual-role canonicity beyond the Z/C/N class decomposition)
import Magma.Rigidity
import Magma.RigidityPartial

-- N=5 structure theorem: Corollary 4.10 (strong S unsatisfiable at N=5)
import Magma.StructureN5

-- N=5 mirror-row theorem: every automorphism fixes both absorbers
import Magma.MirrorRow

-- Joint irredundance (R×D×H Boolean cube)
import Magma.BooleanCube

-- Tight N=5 counterexamples: S ⇏ D, S ⇏ C structural, S+D ⇏ C (all optimal)
import Magma.TightWitnesses

-- All six non-implications at every size: the scaling conjecture, resolved
import Magma.IndependenceAllN

-- The two walls: K-infinity, and completeness excludes the dichotomy
import Magma.CompletenessWall

-- Sorted magmas: the first connecting axiom (class-compositionality)
import Magma.Sorting

-- Homoiconic introspection: the quotation law is determined by the world
import Magma.Homoiconic

-- The canonical N=8 artifact (Stack A): certified Scheme microcode
import Magma.ArtifactN8

-- The factorization theorem: driver metacircularity certified against the table
import Magma.Factorization

-- Factorization with environments: the E component, conservative over the minimal form
import Magma.FactorizationEnv

-- Factorization with closures: β, fuel, certified divergence (Ω), conservative again
import Magma.FactorizationClos

-- Factorization with control: the System L machine, μ/call-cc, simulation theorem
import Magma.FactorizationCtrl

-- Factorization with the store: CESK completed, lockstep bisimulation conservativity
import Magma.FactorizationStore
