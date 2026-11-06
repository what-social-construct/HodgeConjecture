# Rational singular cohomology Mayer–Vietoris

Scope checkpoint: 2026-11-06. Focused verification and full integration pass.
This continues the proved rational
[small-chain comparison](0029-small-singular-chains.md). The new endpoint
is the full singular cohomology cover sequence, with actual subtype spaces
and original continuous inclusion maps. The constructions use literal ℚ
coefficients and universe-zero spaces, including the original P¹(ℂ).
No finite-dimensionality hypothesis is imposed.

## Exact unrestricted dualization

[RationalDual.lean](../../HodgeConjecture/Realization/Betti/RationalDual.lean)
constructs the contravariant rational linear dual functor on the original
module category. Exactness follows from the proved native kernel and range
annihilator identities. The functor therefore preserves homology.
Taking opposite chain complexes and applying this functor gives actual
dual cochain complexes. The differential is the original boundary
transpose; there is no degree shift or additional sign. Quasi-isomorphisms
are preserved, using the native homological-complex constructions.

[CochainDualCoordinates.lean](../../HodgeConjecture/Realization/Betti/CochainDualCoordinates.lean)
identifies the unrestricted dual of the native singular-chain coproduct
with all rational functions on its original simplices. It uses the proved
finite-chain coordinate equivalence and the free-module linear extension
equivalence. Infinite-dimensional source modules are allowed: no finite
support condition is placed on cochains. Boundary and pullback formulas
are proved on the original objects.

[CochainDualComparison.lean](../../HodgeConjecture/Realization/Betti/CochainDualComparison.lean)
packages the actual complex isomorphism and its simplicial naturality.
The proved small-chain inclusion quasi-isomorphism dualizes to the original
full-to-small singular cochain restriction. `smallRestriction_quasiIso`
requires only an actual two-open cover. `smallCohomologyIso` is fixed by
that original restriction's homology map in every degree; no comparison
is supplied as a hypothesis.

## Original spaces and Mayer–Vietoris maps

[CochainPair.lean](../../HodgeConjecture/Realization/Betti/CochainPair.lean)
identifies the componentwise pair complex's cohomology with the product
of the two actual cohomologies, using its original projections and
inclusions. [SingularMayerVietoris.lean](../../HodgeConjecture/Realization/Betti/SingularMayerVietoris.lean)
also identifies contained simplices with the singular set of the actual
subtype topology, including the intersection.

The original short exact sequence on the small singular union is then
carried through these proved comparisons. It gives all three exactness
positions of the sequence

`Hⁿ(X) → Hⁿ(U) × Hⁿ(V) → Hⁿ(U ∩ V) → Hⁿ⁺¹(X)`

for every genuine two-open cover. The connecting map is constructed from
the original native short-exact-sequence boundary. The degree-zero
restriction is proved injective, so the sequence also has its initial
`0 → H⁰(X)` term. All adjacent compositions vanish.

[SingularMayerVietorisMaps.lean](../../HodgeConjecture/Realization/Betti/SingularMayerVietorisMaps.lean)
proves that the first map is the pair of original continuous inclusion
pullbacks. The second is pullback along `U ∩ V → U` minus pullback along
`U ∩ V → V`. These map formulas hold for arbitrary subsets; openness and
coverage are needed for the comparison and exactness. They determine the
convention independently of a dimension calculation.

The first-minus-second convention must be matched explicitly to the
earlier de Rham infinity-minus-zero convention when comparing oriented
generators. No oriented Betti normalization follows merely from this
exact sequence.

## Scope and next target

The full singular cohomology cover sequence and original restriction-map
formulas are now constructed. Next compute the circle from a concrete
two-arc cover and apply the P¹ affine charts to obtain its independent
rational singular H². Contractibility and overlap comparisons must be
proved for those actual spaces. The oriented rational generator, its
complex scalar extension and agreement with the analytic `2πi` period
remain open. No new Hodge-conjecture case is claimed.

The separate [degeneration audit](0030-hodge-derham-degeneration-audit.md)
finds no completed general characteristic-zero Hodge–de Rham degeneration
proof here. The upstream general reduction retains substantive explicit
inputs. No external submission copy of that unproved general theorem was
created. This cohomology checkpoint does not establish that theorem.

## Validation

`make check-singular-cohomology` passes its 2,489-job pure dependency build
and separate 2,949-job original P¹ chart-topology build. Its four suites
pass 40 examples, three named calculations and 86 enforced standard-three
axiom audits, with zero errors and warnings. They include infinite-dimensional
duals, actual signs and pullbacks, empty-cover cases, all three exactness
positions and the original P¹ affine-chart cover. Build counts include
cached dependencies, rather than only newly compiled modules.

The full default build passes 5,018 jobs. Root verification passes 1,411
declaration checks, 574 examples and 1,275 axiom reports within `propext`,
`Classical.choice`, `Quot.sound`; one report requires no axioms. The 493
library modules plus the root pass source scanning. Fourteen transitive
import boundaries, three indirect-negative checks, dependency pins, local
documentation links and whitespace checks pass. The pure target has 27
project modules and excludes project geometry, cycles, Chow,
correspondences, de Rham and sheaf cohomology.

The source uses native Mathlib APIs and local proved singular chains;
no external package or assumed dual comparison is imported. Existing
warning scope remains; the main README remains 69 lines. Submission
candidate selection and release sign-offs are unchanged.
