-- Pairwise Independence of Representation, Classification, and Composition
-- in Finite Extensional Magmas
--
-- 10 paper files (80 theorems) + 1 supplementary (5 theorems), zero sorry.

-- Foundation
import Magma.CatKripkeWallMinimal
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
