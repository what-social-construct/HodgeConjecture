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
import HodgeConjecture.Boundary.Normalization.NormalClosureTensor
import HodgeConjecture.Boundary.Normalization.NormalizationTensor
import HodgeConjecture.Boundary.Normalization.NormalizationBaseChange
import HodgeConjecture.Boundary.Normalization.NormalClosureFactor
import HodgeConjecture.Boundary.Normalization.NormalizationIntegralFactor
import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosure
import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosureRestriction
import HodgeConjecture.Boundary.Normalization.AffineNormalizationOpenImmersion
import HodgeConjecture.Boundary.Normalization.GluedNormalization
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
The finite tensor product of the intermediate normalization has a canonical
integral evaluation map, compatible with the surjective tensor evaluation
onto the marked normal-closure field. The latter's actual kernel quotient
is that field. A finite normal étale intermediate model makes the integral
tensor source finite and étale. Canonical scalar extension identifies the
integral and generic tensor algebras, and the evaluation square commutes
as algebra homomorphisms.
For a separable marked extension, the generic tensor algebra is finite
étale and its evaluation kernel selects the original normal-closure field
as a direct factor. The first projection is the original evaluation; its
selecting idempotent is unique and the kernel is generated by one minus
that idempotent.
Over a normal base, the unramified separability tensor and integral field
trace construct a source-linear section of the actual integral evaluation.
Its value at one is an integral idempotent with complementary kernel ideal;
the quotient is the existing normalization, finite and étale over the whole
base. Scalar extension identifies this selector with the generic one.
This construction does not require a Noetherian base or normality of the
tensor source.

For the actual finite étale morphism, the same normal-closure normalization
is a finite étale surjective cover of each nonempty affine chart and refines
the original whole inverse image by a finite étale surjective map. The
normalization triangle commutes over both the chart and the original scheme.
Explicit normal-stalk hypotheses supply these chartwise constructions.

Enlarging the base gives the same-element inclusion between the existing
normalization rings. Localization identifies the target with the localized
source and with its canonical tensor base change. Principal restriction is
an open immersion with the expected inverse-image basic open. On actual
nested affine charts, the original germ maps, normalization isomorphisms,
chart structural maps and marked refinements all commute with restriction.

The actual restriction maps satisfy identity, composition and common-refinement
coherence. Common principal neighborhoods then identify restriction to any
nonempty affine subopen with the corresponding open inverse image in the
larger normalization. No separatedness or affine-intersection hypothesis is
needed for these chart comparisons.

The nonempty affine normalization charts form a locally directed diagram
of open immersions. Its colimit is a scheme covered by those same charts;
the original structural maps descend to a map to the original base. Two
chart points agree globally exactly when they lift to a common smaller
affine chart, and morphisms out are determined by their chart restrictions.

The broad normalization-purity/global-triviality prototype is preserved in
`research/archive/legacy-lean/`, not as an importable library module.
The general boundary-inertia branch retains its codimension-one endpoint.
Existence of a global finite étale extension remains an explicit input, and the
scheme-theoretic graph restriction is not yet a Chow realization comparison.
-/
