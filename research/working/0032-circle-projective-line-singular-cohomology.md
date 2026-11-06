# Actual circle H¹ and projective-line singular H²

Scope checkpoint: 2026-11-06. This continues the proved full rational
[singular Mayer–Vietoris sequence](0031-singular-cohomology-mayer-vietoris.md).
The new endpoints compute actual rational singular H¹ of native `Circle`
and H² of the original over-ℂ projective-line points as rational lines.
No dimension, vanishing or cohomological equivalence is supplied as a
premise at either concrete endpoint.

## Homotopy and the original degree-zero coordinates

[SingularHomotopy.lean](../../HodgeConjecture/Realization/Betti/SingularHomotopy.lean)
transposes the native singular-chain homotopy and carries it through the
proved actual cochain comparison. Homotopic original continuous maps
therefore induce equal pullbacks on actual rational singular cohomology.
A proved topological homotopy equivalence gives the corresponding
contravariant cohomology isomorphism in every degree.

[SingularContractible.lean](../../HodgeConjecture/Realization/Betti/SingularContractible.lean)
uses native positive-degree point-chain exactness and exact unrestricted
rational dualization to prove point cohomology vanishes. An actual
contraction then proves positive-degree cohomology vanishes on any
contractible space, without a finiteness assumption.

[SingularDegreeZeroNaturality.lean](../../HodgeConjecture/Realization/Betti/SingularDegreeZeroNaturality.lean)
proves the canonical H⁰ identification commutes with original continuous
pullback, by tracking the unique actual zero-cocycle representative.
[SingularComponents.lean](../../HodgeConjecture/Realization/Betti/SingularComponents.lean)
computes actual H⁰ from a continuous discrete-component label, actual
sample points and paths to those points. It retains original zero-simplex
evaluation; the two-component function space is a proved coordinate model.

## The original circle boundary quotient

[CircleTopology.lean](../../HodgeConjecture/Realization/Betti/Examples/CircleTopology.lean)
uses the native circle as the complex unit sphere. Its opens remove −1
and 1. Continuous argument and complex exponential give genuine interval
homeomorphisms and contractibility. The actual intersection is homeomorphic
to the disjoint union of `(-π,0)` and `(0,π)`. Its two path components are
proved, with samples at angles −π/2 and π/2. The original inclusions into
either chart join the two sample points.

[CircleCohomology.lean](../../HodgeConjecture/Realization/Betti/Examples/CircleCohomology.lean)
identifies actual overlap H⁰ with `Bool → ℚ`, false for the negative-argument
component and true for the positive one. H⁰ pullback naturality and chart
path connectedness prove that the actual first-minus-second difference
map has exactly the constant-pair image. Original constant cocycles
produce every such pair.

Contractible-chart H¹ vanishing and actual Mayer–Vietoris exactness prove
the original boundary is surjective, with exactly that kernel.
[TwoComponentBoundary.lean](../../HodgeConjecture/Realization/Betti/TwoComponentBoundary.lean)
computes the resulting quotient by the true value minus the false value.
`h1Equiv` thus gives `H¹(Circle, ℚ) ≃ₗ[ℚ] ℚ`. The cover generator is the
actual connecting image of the positive-component indicator, and its
coordinate is one. Its nonvanishing follows from the proved quotient.

## The original projective-line affine-chart boundary

[PuncturedComplexCircle.lean](../../HodgeConjecture/Realization/Betti/Examples/PuncturedComplexCircle.lean)
uses the native polar homeomorphism and an explicit radial homotopy to
identify punctured ℂ with `Circle` up to homotopy. The inverse map is
original inclusion at radius one.

[ProjectiveLineAnalyticCover.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineAnalyticCover.lean)
uses the ranges of the original finite and reciprocal affine charts in
the already constructed projective-line complex-point topology. Each is
homeomorphic to ℂ and contractible. Their actual overlap is homeomorphic
to punctured ℂ in the original finite coordinate, giving the actual radial
map to the native circle.

[ProjectiveLineSingularCohomology.lean](../../HodgeConjecture/Realization/Betti/Examples/ProjectiveLineSingularCohomology.lean)
uses positive-degree chart vanishing at both adjacent exactness positions.
This proves the actual native connecting map
`H¹(U ∩ V) → H²(P¹(ℂ))` is both mono and epi, hence itself an isomorphism.
Its composition with actual radial pullback gives `circleIso`; its forward
map is proved to be precisely those original maps.

[ProjectiveLineCohomology.lean](../../HodgeConjecture/Realization/Betti/ProjectiveLineCohomology.lean)
combines this with the proved circle H¹ calculation. In namespace
`ProjectiveLineBettiCohomology`, `h2Equiv` identifies actual rational
singular H² with ℚ. The cover generator is the original P¹ connecting
image of the original radial pullback of the circle cover generator.
`coverGenerator_eq_connecting` records this exact formula;
`h2Equiv_coverGenerator` gives coordinate one and
`eq_smul_coverGenerator` expresses every actual H² class in that basis.

## Remaining comparison

These computations provide an independently constructed rational singular
target. They do not identify its cover generator with a standard oriented
loop pairing or with the algebraic de Rham Chern coordinate. The circle
first-minus-second and de Rham infinity-minus-zero cover conventions must
be compared explicitly, together with complex scalar extension and actual
integration. Matching rational dimensions does not prove this map or sign.

The next target is that oriented comparison and the ordinary cycle-class
compatibility, using the earlier actual analytic `2πi` period. A general
positive-dimensional Hodge structure, general Betti/purity comparisons
and prescribed-class coverage remain open. No new Hodge-conjecture case
is claimed. The separate general characteristic-zero
[degeneration audit](0030-hodge-derham-degeneration-audit.md) remains unchanged.

## Build boundaries

`make check-circle-cohomology` builds the standalone `Betti.Circle` entry
point and checks homotopy, topology and the actual boundary quotient.
Its 36 project modules exclude project geometry, cycles, Chow,
correspondences, de Rham and sheaf cohomology.

`make check-projective-line-cohomology` separately builds actual P¹ H²
and checks the original analytic cover, native connecting isomorphism and
final generator. Its 52 project modules include the original scheme
geometry and its foundational finite-type dimension dependency, while
excluding Chow realization, correspondences, de Rham and sheaf cohomology.
The earlier P¹ topology/cochain input target remains separate.

The development uses pinned native Mathlib APIs and proved local singular
cochains; no external Stacks package or supplied Betti comparison is imported.

## Validation

The two focused Make checks pass the 2,689-job standalone circle build and
3,256-job actual P¹ build. Six suites pass 52 examples, 16 named
mathematical checks and 165 enforced standard-three axiom audits, with
zero suite errors and warnings. They include original point/interval/plane
contractions, actual chart inclusions and disconnected overlap, a genuine
two-value H⁰ class on `ℝ ⊕ ℝ`, the actual boundary quotient, radial formulas,
and uniqueness of the actual P¹ generator coefficients. Build-job counts
include reused dependencies.

The full default build passes 5,068 jobs. Root verification passes 1,512
declaration checks, 574 examples and 1,376 axiom reports within `propext`,
`Classical.choice`, `Quot.sound`; one report needs no axioms. Its 92 existing
style warnings remain. All 505 library modules plus the root pass source
scanning. Seventeen import boundaries, three indirect-negative checks,
dependency pins, local documentation links and whitespace checks pass.
The main README remains 69 lines. An independent source review confirms
the concrete endpoints have no supplied cohomology computation and the P¹
forward map retains the original radial pullback and connecting morphism.

These are working-tree checks, with existing build-warning scope retained;
they do not replace clean-clone or human release sign-offs. Submission
candidate selection and packaging remain unchanged.
