import HodgeConjecture.Boundary.AveragingAction
import HodgeConjecture.Boundary.Different
import HodgeConjecture.Boundary.ExtensionCriterion
import HodgeConjecture.Boundary.GaloisProjectorExtension
import HodgeConjecture.Boundary.HeightOneDifferent
import HodgeConjecture.Boundary.NoetherDifferentRamification
import HodgeConjecture.Boundary.Normalization.DeckAction
import HodgeConjecture.Boundary.Normalization.ExtensionBridge
import HodgeConjecture.Boundary.Normalization.FixedRingUnramified
import HodgeConjecture.Boundary.Normalization.FixedRingLocalization
import HodgeConjecture.Boundary.Normalization.GlobalExtension
import HodgeConjecture.Boundary.Normalization.InertiaDiagram
import HodgeConjecture.Boundary.Normalization.InvariantIntermediate
import HodgeConjecture.Boundary.Normalization.PrimeInertia
import HodgeConjecture.Boundary.Normalization.LocalizationBridge
import HodgeConjecture.Boundary.Normalization.PrimeInertiaDescent
import HodgeConjecture.Boundary.Normalization.SelectorComparison
import HodgeConjecture.Boundary.SheetProjectorExtension
import HodgeConjecture.Boundary.Sheets.GenericProjector
import HodgeConjecture.Boundary.Sheets.MarkedBlockProjector

/-!
# Boundary stage

This umbrella module collects generic sheet selectors, inertia averaging,
inertia saturation, normalization and valuation diagrams, differents, and
the codimension-one and global criteria for extending generic selectors and
Galois subgroup correspondence projectors across the boundary.  It also
contains the marked selector decomposition in which one and the same
base-sheet multiplication operator is diagonal in selector/CRT coordinates
and graph-shaped in constant-unit coordinates.
-/
