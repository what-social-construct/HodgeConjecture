import HodgeConjecture.Boundary.AveragingAction
import HodgeConjecture.Boundary.CompactifiedGraphProjector
import HodgeConjecture.Boundary.Different
import HodgeConjecture.Boundary.ExtensionCriterion
import HodgeConjecture.Boundary.GaloisProjectorExtension
import HodgeConjecture.Boundary.GraphRestriction
import HodgeConjecture.Boundary.GraphCycleRestriction
import HodgeConjecture.Boundary.HeightOneDifferent
import HodgeConjecture.Boundary.NoetherDifferentRamification
import HodgeConjecture.Boundary.ProjectorClosureDefect
import HodgeConjecture.Boundary.Normalization.BoundedOverring
import HodgeConjecture.Boundary.Normalization.AffineSections
import HodgeConjecture.Boundary.Normalization.BoundarySections
import HodgeConjecture.Boundary.Normalization.TraceDualBound
import HodgeConjecture.Boundary.Normalization.NormalizationTraceBound
import HodgeConjecture.Boundary.Normalization.SectionLocalization
import HodgeConjecture.Boundary.Normalization.HeightOneBoundaryPole
import HodgeConjecture.Boundary.Normalization.BoundaryPole
import HodgeConjecture.Boundary.Normalization.RegularPairBoundary
import HodgeConjecture.Boundary.Normalization.FullVisibleBoundary
import HodgeConjecture.Boundary.Normalization.FiniteAffineCover
import HodgeConjecture.Boundary.Normalization.FiniteAffineChart
import HodgeConjecture.Boundary.Normalization.FiniteFunctionField
import HodgeConjecture.Boundary.Normalization.SeparableFunctionField
import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import HodgeConjecture.Boundary.Normalization.FiniteNormalClosure
import HodgeConjecture.Boundary.Normalization.DeckAction
import HodgeConjecture.Boundary.Normalization.ConjugateBoundary
import HodgeConjecture.Boundary.Normalization.ConjugateNormalization
import HodgeConjecture.Boundary.Normalization.ExtensionBridge
import HodgeConjecture.Boundary.Normalization.FixedRingUnramified
import HodgeConjecture.Boundary.Normalization.FixedRingLocalization
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
and graph-shaped in constant-unit coordinates.  Its normal-closure comparison
also records the algebra equivalence with split sheet functions together with
the commuting augmentation/tensor-diagonal square. For an actual finite
étale extension, the closed graph of an extended deck automorphism pulls back
to the graph of its restriction, with equality of the defining ideal sheaves.
For an integral extended cover, this also gives restriction of actual graph
cycles and their rational weighted sums.

The bounded-overring lemma is the commutative-algebra input for a separate
boundary-section/trace-landing construction. It uses the existing colon
ideal and does not supply uniform geometric landing or boundary separation.

Actual finite normal affine algebras construct the normalization models through
the canonical algebra and scheme isomorphisms. Their full visibility makes
the existing moving and fixed--moving boundary ideals the unit ideal for
nontrivial subgroups, yielding separation without a regular-pair hypothesis.
Étaleness transports across the same algebra identification.

For a finite scheme morphism, the whole inverse image of an affine chart
supplies the actual finite section algebra, and scheme étaleness supplies
its étale algebra structure. On integral nonempty charts, explicit normal
stalks identify this model with normalization in the upstairs function field,
with the structural equality over the original base scheme.

For a dominant morphism of integral schemes, the actual generic-stalk map
commutes with pullback of sections. For a finite morphism, localizing the
finite affine algebra proves finite-dimensionality of that same function-field
extension, without any normality or étaleness premise.
Formal unramifiedness passes to the actual function-field extension for an
affine morphism. In the finite case it proves separability; scheme étaleness
supplies the formal-unramifiedness premise without a perfect-field assumption.
The resulting finite extension constructs the existing marked normal-closure
datum inside the algebraic closure of the upstairs field. Separability of the
marked extension gives separability and Galoisness of its normal closure,
again without a perfect-base-field premise.
Fixed-field, tensor-sheet and trace-dual consumers use that same extension's
separability. Core-freeness, full-visible separation and their inertia/extension
consequences require neither separability nor perfectness; their geometric
and source-input hypotheses remain explicit.
Over a normal Noetherian affine base, separability also proves finiteness of
the normal-closure normalization. One finite normal intermediate model, or
the actual affine inverse image with normal stalks, then constructs the
existing normalized cover without a separately supplied second affine model.

The broad normalization-purity/global-triviality prototype is preserved in
`research/archive/legacy-lean/`, not as an importable library module.
The normalization endpoint stops at the proved codimension-one statement.
Existence of the finite étale extension remains an explicit input, and the
scheme-theoretic graph restriction is not yet a Chow realization comparison.
-/
