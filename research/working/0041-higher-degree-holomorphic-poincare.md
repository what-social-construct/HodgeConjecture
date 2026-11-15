# Higher-degree holomorphic Poincaré comparison

Date: 2026-11-09.

Historical checkpoint. [0042](0042-canonical-analytic-atlas.md) subsequently
constructs compatible analytic charts and actual regular evaluations for
smooth schemes of fixed relative dimension. The remaining-scope text
below describes the earlier coordinate construction.

This advances item 4 of the [active checklist](../TARGET_BRIDGE.md), building
on [0040](0040-holomorphic-derham-local-poincare.md). The existing constant
to holomorphic de Rham comparison is now a full sheaf quasi-isomorphism in
every complex coordinate dimension. The construction uses the original
native alternating coefficients, complex C∞ sections, restrictions and
exterior derivative throughout.

## The actual radial operator

For a positive-degree form η of degree n + 1 on a convex coordinate open U
and a base point a in U, `radialHomotopy` constructs

\[
(K_a\eta)(x)=\int_0^1 t^n\,\iota_{x-a}\eta(a+t(x-a))\,dt.
\]

The integral is Mathlib's interval integral with values in the native
continuous alternating coefficient space. Insertion is native currying
followed by evaluation, bundled as the continuous linear map `contraction`.
The parameter is extended to ℂ when checking complex smoothness, and
`radialMap_ofReal` identifies its real restriction with the original
segment parameter.

`Geometry.Holomorphic.Contraction` proves the insertion/alternation
identity and the Euler identity

\[
d(\iota_{x-a}\eta)+\iota_{x-a}(d\eta)
  =(n+1)\eta+D\eta\,(x-a).
\]

These identities are proved on the original alternating maps, including
the finite-sum signs and the native unnormalized exterior differential.
They hold for vector-valued forms over any nontrivially normed field;
there is no additional exterior-algebra carrier or supplied identity.

`Geometry.Holomorphic.ParameterIntegral` proves that fixed-interval
integration preserves complex C∞ regularity in the other variables.
Continuity of the parameter derivative and compactness of [0,1] give a
uniform derivative bound on a common neighborhood. Mathlib's dominated
parameter differentiation theorem then computes the derivative. Induction
on derivative order proves complex C∞ regularity, rather than assuming it
or replacing it with real smoothness. A vector-valued complex-to-real
derivative lemma supplies the coefficient-valued fundamental theorem of
calculus step.

`Geometry.Holomorphic.RadialHomotopy` combines those proofs. Differentiating
the weighted radial slice and integrating its time derivative gives

\[
dK_a\eta+K_a d\eta=\eta
\]

in every positive degree. The zero endpoint vanishes because the degree
is positive. This proves both the normalization and the sign in the
actual operator, including its action on nonclosed forms.

In degree one, `radialIntegral_zero_eq_segmentPrimitive` identifies the
operator with the existing segment integral. For a closed one-form,
`radialHomotopy_zero_eq_primitive` proves equality with the previous
normalized zero-form section. The old low-degree API remains available;
the degree-one sheaf exactness theorem now specializes the general proof.

## Local exactness and comparison

For a closed positive-degree form on an arbitrary coordinate open,
`locally_exact_positive` shrinks to a ball and uses the constructed radial
primitive. The shared `SheafCohomology.LocalExactness` lemma turns those
same local sections and restrictions into `HolomorphicDeRham.exact_positive`.
Thus `complex_exactAt_positive` proves exactness in every positive degree.

The existing augmentation exactness and monicity prove the degree-zero
comparison. Combining them with positive-degree exactness gives
`HolomorphicDeRham.comparison_quasiIso` for every complex normed coordinate
space with compatible real scalar restriction. Finite dimensionality is
not needed by this coordinate theorem. The previous complex-line theorem
is a compatibility specialization of the general result.

## Remaining geometric obligations

This is a local sheaf quasi-isomorphism on coordinate spaces. It does not
identify global-section cohomology with singular cohomology. Compatible
analytic charts on canonical scheme complex points, the all-degree map
from algebraic Kähler forms, analytic/singular comparison, proper
algebraic/analytic comparison and general Hodge purity remain open within
item 4. The class-dependent geometric Chow construction and projector
defect realization remain open within item 5.

## Verification

`make check-holomorphic-derham` checks the existing low-degree controls and
the new degree-two controls: the nonzero constant form dz₁ ∧ dz₂, its
actual primitive (z₁ dz₂ − z₂ dz₁)/2, the differential of that primitive,
and a nonclosed two-form on complex three-space. It also checks the full
comparison on ℂ² and ℂ³ and audits the new proof dependencies against the
standard three Lean axioms. The shared geometry import guards cover all
three new modules.

Validation passed: full `lake build` (5,179 jobs),
`make check-holomorphic-derham` (60 standard-three axiom audits plus the
concrete controls), 24 root-import export checks, all import guards,
local documentation links and `git diff --check`. No new axiom or `sorry`
is introduced. The full build retains the existing unrelated warnings in
`Challenge.lean` and older modules; the new library modules compile without
warnings.
