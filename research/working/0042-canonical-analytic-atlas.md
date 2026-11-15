# Analytic charts on canonical complex scheme points

Date: 2026-11-09.

Subsequent status: [0043](0043-holomorphic-forms-descent.md) now constructs
intrinsic forms descent, the sheaf differential and the all-degree
algebraic forms map. The validation and remaining-work statements below
record the scope of this earlier atlas checkpoint.

This advances item 4 of the [active checklist](../TARGET_BRIDGE.md), after
[the coordinate Poincaré proof](0041-higher-degree-holomorphic-poincare.md).
For a scheme X smooth of fixed relative dimension d over ℂ, its original
canonical complex-point space now has a constructed native analytic
manifold structure modelled on `Fin d → ℂ`. Every regular function on every
scheme open is holomorphic, and every morphism over ℂ between such smooth
schemes is analytic, allowing different source and target dimensions.

## The actual atlas and its topology

`Geometry.PolynomialComplexPoints` reuses the existing affine structure
map, actual scheme points, generated evaluation topology and shared
presentation-coordinate homeomorphism. There are no relations for the
original polynomial variables, so the canonical points of Spec ℂ[Fin d]
are homeomorphic to `Fin d → ℂ`. The inverse is proved to be the original
scheme-valued point of polynomial evaluation. Native standard smoothness
proves smoothness of this coordinate model in relative dimension d.

`Geometry.EtaleAnalyticCoordinates` adapts the local étale construction
from the pinned Axiom Weil source. Standard étale presentations express
regular functions as rational functions of the base coordinates and one
implicit root. The original complex point supplies that root, and the
invertible polynomial derivative supplies the actual implicit inverse.
The constructed open partial homeomorphism restricts the original scheme
map; its source and target are opens of the existing analytic topology.

The source's first-differentiability conclusion is strengthened to native
complex analyticity, `ContDiff ℂ ω`. The polynomial equation is analytic,
and Mathlib's implicit-function theorem retains that regularity. Analytic
regularity also supplies a common open neighborhood on which the implicit
root is analytic. Rational expressions with nonzero denominator preserve
it. No several-variable differentiability-implies-analyticity theorem or
new holomorphy premise is needed. The unrelated Nullstellensatz and
étale-site consequences of the upstream file are omitted.

`Geometry.SmoothComplexManifold` uses native standard-smooth local
structure to produce an étale morphism to Spec ℂ[Fin d] around every point.
The proved étale inverse and the polynomial coordinate homeomorphism give
an actual algebraic analytic chart. Regular functions on arbitrary opens
are analytic in this chart after shrinking to an affine neighborhood.
The native `ChartedSpace` atlas consists of these proved algebraic charts;
its sources cover every canonical point. Their coordinate functions are
regular, so the already proved regular-function expressions establish
analyticity of every transition. This proves

`IsManifold 𝓘(ℂ, Fin d → ℂ) ω (Scheme.ComplexPoints x)`.

The topology is the original evaluation topology throughout. Separation
and countability remain governed by that original point space; this
construction supplies its native analytic chart structure. The chart
predicate is proved to have a witness at every point from smoothness; it
is not a supplied atlas or an assumed comparison record.

## Regular functions, morphisms and the existing projective line

The same chart proofs establish `contMDiffOn_evalOrZero` and
`contMDiff_map`. The latter reads a target chart's regular coordinates
through the original scheme pullback, then applies the source's proved
regular-function holomorphy. Different source and target dimensions are
allowed.

`Geometry.Holomorphic.SchemeEvaluation` bundles the actual evaluations as
algebra maps into native complex C∞ functions, both on the corresponding
analytic open and on any coordinate chart of the atlas. The source scalar
structure is explicitly the original `constHom` from the structure
morphism. It is not installed as an ambiguous global instance on section
rings. Evaluation preserves the original restrictions and scheme
pullbacks, and chartwise evaluation equals evaluation at the same original
point. `chartEvaluation` is the actual degree-zero input for the existing
Kähler realization API.

`Geometry.ProjectiveLineSmooth` proves that the original glued projective
line is smooth of relative dimension one, over any commutative base ring.
The proof uses its existing two polynomial charts and source locality.
Thus the new atlas applies to the same projective-line scheme used by the
existing Chow, period and canonical Betti constructions. No replacement
Proj model or supplied smoothness hypothesis is introduced.

## Remaining comparison work

The next construction is descent of the existing coordinate forms and
differential through this atlas, using derivative pullback on overlaps,
and the all-degree algebraic-to-holomorphic forms map. The previous
all-degree Poincaré theorem is still a coordinate sheaf theorem; this
checkpoint does not assert an already glued intrinsic de Rham complex on
every scheme's point space. Analytic/singular comparison, proper
algebraic/analytic comparison and general purity remain open. The atlas
here treats smooth schemes of fixed relative dimension, not arbitrary
singular schemes or a variable-dimension atlas.

## Verification

`make check-analytic-charts` checks the native atlas in arbitrary finite
dimension, an analytic square-root family with two independent complex
parameters, an actual nonconstant regular function on canonical ℂ², an
actual nonlinear scheme morphism ℂ² → ℂ with its original point value,
both original projective-line chart morphisms, and the original overlap
identity and analytic reciprocal coordinate change. It audits the proof
dependencies against the standard three Lean axioms. The shared geometry
import guards cover all five new modules.

Validation passed: full `lake build` (5,204 jobs),
`make check-analytic-charts` (30 standard-three axiom audits and the concrete
controls), and a root-import regression containing all 60 earlier
holomorphic de Rham audits and controls plus 18 new public export checks.
All import guards, local documentation links and `git diff --check` pass.
The five new library modules compile without warnings, with no new axiom
or `sorry`. Existing unrelated warnings in the full build retain their
previous scope.
