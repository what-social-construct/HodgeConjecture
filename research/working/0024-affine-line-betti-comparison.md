# Complex affine-line Betti–de Rham comparison in degree zero

Date: 2026-11-05. The mathematical target remains first; the submission
candidate and Palomar packaging are not changed by this checkpoint.

## Original points and topology

`Betti/Examples/AffineLineComplexPoints.lean` defines actual points as
`ℂ[X] →ₐ[ℂ] ℂ`, with the topology induced by evaluation of every regular
function into ordinary `ℂ`. Polynomial evaluation proves that the coordinate
map is a homeomorphism to `ℂ`; the topology is not declared by transporting
labels. Path connectedness follows from that homeomorphism. Each point is an
actual scheme morphism over `Spec ℂ`. Polynomial substitution gives both
the original affine-scheme self-map and its continuous complex-point map,
with their compatibility proved.

## Actual singular cocycles

`Betti/SingularPathConnected.lean` turns a path into an actual singular
one-simplex using Mathlib's standard simplex/unit-interval homeomorphism.
Both faces are identified with the correct endpoint point-simplices. The
existing coboundary equation therefore proves that zero-cocycle evaluations
agree on joined points. A path-connected space has rational `H0` identified
with `ℚ`, by evaluation at any specified point and the actual constant
cocycle inverse. The equivalence is independent of the chosen point and
commutes with continuous pullback. No continuity or local constancy is
imposed on arbitrary rational zero-cochains.

## Comparison and original maps

`DeRham/AffineLineComparison.lean` combines this Betti calculation with the
proved polynomial de Rham kernel computation. `Complexification` is the
genuine tensor product `ℂ ⊗[ℚ] Betti`; scalar extension and the tensor unit
equivalence compute its complex coordinates. The resulting algebra
equivalence is

```text
bettiComparison : AffineDeRham.H0 ℂ ℂ[X] ≃ₐ[ℂ]
  (ℂ ⊗[ℚ] SingularDegreeZero.H0 AffineLineComplexPoints.Point).
```

`complexEvaluation` is defined independently from actual singular evaluation
at each point using the tensor-product universal property. Its equality to
constant coordinates is then proved. Under `bettiComparison` it agrees with
evaluation of the original regular function at every actual point.

Complex constants, rational normalization and cup multiplication are
compatible. `rationalEmbedding` is the actual `1 ⊗ h` map and is injective;
the complex class with coordinate `I` is outside its image. The algebraic
pullback is the original closed-function map induced by polynomial
substitution. The Betti pullback precomposes actual singular simplices by
the continuous polynomial point map. Their square commutes after genuine
scalar extension, including nonlinear and constant polynomials.

`cohomologyZeroComparison` also identifies categorical degree-zero homology
of the original constructed de Rham complex. Pullback naturality is proved
on its closed-function model. No independently constructed pullback cochain
map on all exterior powers is claimed.

## Limits and focused checks

This is a positive-dimensional degree-zero comparison. Higher de Rham and
Betti cohomology, general scheme hypercohomology/analytic comparison,
positive-codimension cycle classes and prescribed-Hodge-class generation
remain open. The finite split Chow comparison remains separate; no new
general Hodge-conjecture case follows.

`make check-affine-line-comparison` builds only the new comparison entry
point and runs `research/AffineLineComparisonVerification.lean`. Its eight
project-module closure excludes project Chow, cycles, correspondences and
boundary geometry. Existing algebraic core/component targets remain
independent of Betti. The main README remains 69 lines.

The eight regressions cover actual nonlinear point evaluation, path
constancy, a separating zero-cochain that is not a cocycle, independent
classes on the two complex components of `ℂ ⊕ ℂ`, a genuinely complex tensor
and its inverse image, exclusion from the rational image, both nonlinear
and constant polynomial naturality, and actual scalar-extended evaluation.
Twenty-three declarations have enforced standard-three axiom audits.

The focused build passes 2,905 dependency jobs and all eight examples and
23 audits. The existing comparison suite passes its 25 audits after the
3,582-job comparison-umbrella build. The complete default build passes
4,177 jobs; the root inventory passes 1,274 declaration checks, 565 examples
and 1,166 axiom reports. All reported axioms lie in `propext`,
`Classical.choice` and `Quot.sound`; one root report needs no axioms.
Job counts include cached dependencies. All 388 production modules pass the
proof-token scan. Import boundaries, both new indirect-negative checks,
dependency pins, local documentation links and whitespace checks pass.
Lean 4.35.0, the Mathlib pin, the main README length and existing release
sign-offs are retained. Baseline Lean style warnings and the intentional
Challenge statement placeholders keep their existing scope.
