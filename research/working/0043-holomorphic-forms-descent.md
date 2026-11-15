# Atlas descent and the all-degree algebraic forms map

Date: 2026-11-09.

Subsequent status: [0044](0044-intrinsic-holomorphic-poincare.md) now proves
the chart complex identifications and full intrinsic constant-sheaf
quasi-isomorphism. The validation and remaining-work statements below
record the scope of this earlier forms-descent checkpoint.

This advances item 4 of the [active checklist](../TARGET_BRIDGE.md), after
the [constructed analytic atlas](0042-canonical-analytic-atlas.md).

## Coordinate pullback and intrinsic forms

`Geometry.Holomorphic.Pullback` defines actual pullback on the existing
native alternating-form sections. At a coordinate point z, every argument
is precomposed with the complex Fréchet derivative of the coordinate map.
Identity, composition, restriction and commutation with the exterior
derivative are proved. The last uses Mathlib's `extDeriv_pullback`, with
locality removing the auxiliary extensions outside the coordinate opens.

`Geometry.Holomorphic.Atlas` defines intrinsic forms as the submodule of
families of these original coordinate sections satisfying the actual
pullback equation on every atlas overlap. Transition regularity follows
from the native manifold structure. The coordinate differential preserves
the overlap equations, squares to zero and commutes with restriction.
This construction works on any native complex C∞ manifold, including the
canonical analytic point spaces constructed for schemes smooth of fixed
relative dimension. It retains their existing topology and atlas.

`Realization.DeRham.HolomorphicAtlasComplex` proves the sheaf property:
glue the original coordinate sections using their existing sheaf, then
verify the derivative overlap equations locally. Thus compatible local
intrinsic forms have a unique gluing. The descended differential is a
sheaf morphism and gives the all-degree intrinsic de Rham sheaf complex.

## The original algebraic source and all degrees

`Geometry.Holomorphic.Wedge` constructs a determinant wedge of covectors,
then of the original holomorphic one-form sections. Its coefficient is
exactly the determinant, including degrees zero and one, with no extra
factorial. Degree one recovers the same original section.

`Realization.DeRham.HolomorphicFormsMap` composes the existing algebraic
forms functor with the existing Kähler lift and the exterior-power
universal property. The source remains the original
`⋀[A]^n Ω[A⁄ℂ]`; no formal-symbol replacement is introduced. The map
extends the previous `algebraicOneFormsMap`. On a spanning generator
`a₀ da₁ ∧ ... ∧ daₙ`, its value is φ(a₀) times the determinant of the
actual derivatives of the φ(aᵢ).

`HolomorphicFormsNaturality` proves coordinate pullback, restriction and
algebra-map precomposition compatibility using the same shared algebraic
spanning theorem. `HolomorphicFormsDifferential` realizes each generator
as pullback of `z₀ dz₁ ∧ ... ∧ dzₙ` on ℂⁿ⁺¹. Laplace expansion proves its
derivative is the constant volume form. The already proved pullback law
for d then gives compatibility with the original algebraic differential
in every degree, and an actual morphism of sectionwise cochain complexes.

`SchemeHolomorphicForms` feeds the already constructed `chartEvaluation`
maps into this construction. Coordinate naturality proves their descent
equations, so they define the all-degree map into intrinsic forms on the
actual analytic open. This map commutes with d and the original section
restriction maps. Its components form a natural transformation from the
existing scheme algebraic-forms presheaf to the descended analytic forms
evaluated on algebraic opens; these transformations commute with the
original presheaf-complex differential. `analyticPresheafComplex` evaluates
this actual analytic complex on algebraic opens, and
`algebraicComplexComparison` bundles these maps as a native morphism from
the existing scheme algebraic de Rham presheaf complex.

## Shared objects and source boundaries

The original section base map, induced algebra and restriction algebra
maps have moved without changing their definitions or public names from
`Realization.DeRham.SheafComplex` to `Geometry.SectionAlgebra`.
`regularFunctionsAlgebra` now refers to that same algebra. Both sides of
the comparison therefore use the same scalar structure on the original
section rings. The shared holomorphic-function carrier and scalar tower
have likewise moved from `HolomorphicKaehler` to
`Geometry.Holomorphic.FunctionAlgebra`. The new geometric wedge and atlas
modules do not import a realization layer.

The import guard permits the extracted section-algebra leaf in the
otherwise geometry-independent scheme-filtration layer. A separate guard
requires this leaf to have no project imports. All analytic and concrete
geometry dependencies remain forbidden there.

No external proof port or new dependency was needed. The native exterior
derivative pullback theorem, continuous multilinear antisymmetrization,
exterior-power universal property and determinant Laplace expansion are
from the existing pinned Mathlib revision. No axioms, proof placeholders,
or supplied comparison data are added.

## Validation and remaining comparison work

The focused target is `make check-holomorphic-descent`, using
`research/HolomorphicDescentVerification.lean`. It checks nonclosedness
and a determinant-one two-form, the degree-three differential, the
reciprocal-coordinate Jacobian, the same original P¹ overlap point,
canonical affine-space and P¹ sheaf-complex instances, and the axiom
boundaries of the construction. The focused module build and import
guards pass, as does the full `lake build` (5,214 jobs). The verification
suite includes the final bundled-complex declarations. A combined public-root
regression passes all three verification suites: 42 new descent audits,
60 coordinate Poincaré/Kähler audits, and 30 analytic atlas audits, plus
19 new public export checks. All 132 audited declarations use only
`propext`, `Classical.choice` and `Quot.sound`. The explicit determinant-one
algebraic two-form and nonclosed one-form controls pass, as do the
reciprocal −1/z² coefficient and actual affine/P¹ instantiations.

The previous all-degree local Poincaré comparison is still a coordinate
sheaf theorem. The next step is to construct the local identifications
with the complex in each chart, then transport its local exactness and constant
augmentation to this intrinsic sheaf complex. Comparison of
analytic sheaf hypercohomology with singular cohomology, proper
algebraic/analytic comparison, the general period isomorphism and purity
remain open. An all-degree map is not a claimed comparison isomorphism.
The cycle construction, projector-defect realization and prescribed
Hodge-class coverage in item 5 are unchanged.
