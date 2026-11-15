# Intrinsic holomorphic Poincaré comparison

Date: 2026-11-09.

This completes the intrinsic local-comparison step following
[forms descent](0043-holomorphic-forms-descent.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). The comparison is the actual
map from the native constant complex sheaf in degree zero to the existing
intrinsic holomorphic de Rham complex. It is a quasi-isomorphism in every
degree. The general singular and algebraic/analytic comparisons and
purity remain separate obligations.

## Local coordinates on the same descended complex

`Geometry.Holomorphic.AtlasCoordinates` constructs `fromChart`: a native
coordinate section on an intrinsic open contained in one chart source
extends to its full family of sections by derivative pullback in every
other chart. The existing pullback composition law and the equality of
coordinate maps on overlaps prove the derivative cocycle. No transition
or extension compatibility is supplied as a premise.

`fromChart_inChart` and `inChart_fromChart` prove both inverse laws.
`chartEquiv` is a linear equivalence between the original intrinsic forms
and the original native coordinate sections. The same differential
commutes with these identifications. `chartComplexIso` in
`Realization.DeRham.HolomorphicAtlasComplex` bundles them as an actual
isomorphism of the section complexes on a chart source.

`coordinateOpen` pulls a coordinate neighborhood back to an open of the
original manifold topology. Its containment lemmas keep the restrictions
in the local comparison on the same points and section carriers.

## Constants and actual local primitives

`Geometry.Holomorphic.AtlasPoincare` constructs intrinsic constants using
the existing coordinate constant sections. The degree-zero pullback
equation is proved, these sections are closed, restriction preserves them,
and constants remain injective on every nonempty intrinsic open.

For a closed positive-degree intrinsic form, restrict to a chart source,
apply the already proved coordinate `locally_exact_positive`, pull its
coordinate neighborhood back to the original topology, then use
`fromChart` to obtain the actual intrinsic primitive. The derivative and
restriction laws prove its defining equation. The radial integral is the
existing coordinate construction, rather than a newly supplied primitive.

The same procedure transports `locally_constant_zero`. It proves local
constancy, without assuming every open is connected or identifying the
constant sheaf with globally constant functions.

## The same constant-sheaf comparison

`Realization.DeRham.HolomorphicAtlasPoincare` constructs the augmentation
by the native sheafification universal property, on the original manifold
topology. Local constancy proves augmentation exactness; injectivity on
nonempty opens proves its monomorphism after sheafification. Actual local
primitives prove sheaf exactness in every positive degree through the
existing `LocalExactness.exact_of_exists_local_preimage` criterion.

The resulting `comparison` is a native cochain map
`constantSheaf M [0] ⟶ HolomorphicAtlas.complex E M`.
`comparison_quasiIsoAt_zero`, `comparison_quasiIsoAt_positive` and
`comparison_quasiIso` prove the full local holomorphic de Rham comparison.
The model is any native complex C∞ manifold with the compatible real
scalar structure needed by the existing coordinate Poincaré proof.

`Scheme.ComplexPoints.holomorphicComparison` specializes this same map to
canonical analytic points of schemes smooth of fixed relative dimension.
`holomorphicComparison_quasiIso` proves it in every degree, including
relative dimension zero. The original glued P¹ uses its existing proved
smoothness instance and the same canonical point topology.

## Shared owners and proof reuse

The original coordinate constant section and its derivative-zero proof
have moved unchanged from `HolomorphicComplex` into
`Geometry.Holomorphic.FunctionAlgebra`, preserving their public names.
The intrinsic and coordinate constructions therefore share these sections.

`SheafCohomology.ConstantLift` owns aliases for the native constant
(pre)sheaves, the actual sheafification lift and its generic monomorphism
proof. `SheafCohomology.AugmentedComplex` owns the native cochain-map
assembly and exact augmented-complex criterion. The existing coordinate
comparison reuses these proofs and retains its previous API. Both helpers
remain independent of geometry, realizations and geometric source inputs.

No axioms, proof placeholders, comparison-data structures, external proof
ports or new dependencies are introduced. The native Mathlib revision and
existing proof attributions are unchanged.

## Validation and remaining work

The focused target is `make check-intrinsic-poincare`, using
`research/IntrinsicPoincareVerification.lean`. It constructs forms on
actual canonical affine-scheme chart sources, tests nonzero two- and
three-form coefficients, a nonclosed one-form, a local primitive of the
nonzero intrinsic two-form, distinct constants, and the full comparisons
on canonical affine spaces and the original P¹. The suite audits the
axiom boundaries of the construction and the shared proofs. The focused
module build, verification file and import guards pass. The full build
passes with 5,219 jobs. A combined public-root regression passes all four
verification suites: 60 coordinate Poincaré/Kähler audits, 30 atlas audits,
42 forms-descent audits and 33 intrinsic-comparison audits, plus 22 new
public export checks. All 165 audited declarations use only `propext`,
`Classical.choice` and `Quot.sound`.

The next comparison is between analytic constant-sheaf cohomology and
the existing singular cochains, under the intended geometric hypotheses.
Proper algebraic/analytic comparison, the general period isomorphism and
purity remain open. The new quasi-isomorphism concerns the analytic sheaf
complex; it does not identify cohomology of arbitrary global holomorphic
sections with singular cohomology. Item 5's geometric cycle construction,
projector-defect realization and prescribed-class coverage are unchanged.
