# Rational small singular chains

Scope checkpoint: 2026-11-06. Focused verification and full integration pass.
This continues the actual Betti inputs in
[0028](0028-projective-line-betti-inputs.md). The chain and cochain coefficient field is ℚ;
the native chain comparison uses universe-zero topological spaces,
which include the constructed P¹(ℂ).

## Actual small subcomplex and chain coordinates

[SingularSubcomplexes.lean](../../HodgeConjecture/Realization/Betti/SingularSubcomplexes.lean)
defines the simplicial subcomplex of original continuous singular simplices
whose whole image lies in a subset. It is proved isomorphic to the singular
set of the actual subtype space. For two subsets its simplicial union
consists of simplices lying wholly in either member. The original face and
degeneracy maps preserve this condition. An open cover contains every
zero-simplex, but can omit higher simplices from this union.

The permanent crossing-interval example uses the two opens
`(-∞, 2/3)` and `(1/3, ∞)` in ℝ. They cover ℝ, but the original continuous
simplex with endpoint values zero and one lies in neither member.

[SingularChainCoordinates.lean](../../HodgeConjecture/Realization/Betti/SingularChainCoordinates.lean)
identifies actual finite-support rational simplex coordinates with
Mathlib's native singular-chain coproduct, using the two proved colimit
universal properties. Its alternating differential is the native chain
differential. [SubcomplexChainCoordinates.lean](../../HodgeConjecture/Realization/Betti/SubcomplexChainCoordinates.lean)
identifies the actual inclusion range with chains supported in the
subcomplex, proves injectivity and retains the original boundary.

[AffineSingularRealization.lean](../../HodgeConjecture/Realization/Betti/AffineSingularRealization.lean)
also realizes affine vertex chains faithfully in the native singular
complex of a real normed space. A separate regression proves that the
existing actual singular cochain coboundary is dual to the coordinate
boundary, including its signs.

## Constructed subdivision and homotopy

[AffineSimplexChains.lean](../../HodgeConjecture/Realization/Betti/AffineSimplexChains.lean)
uses ordered vertex tuples, with the empty tuple retained for augmentation.
Deleting vertices gives the actual alternating boundary. Prepending a
vertex gives a cone with proved boundary formula and square-zero boundary.

[VertexSubdivision.lean](../../HodgeConjecture/Realization/Betti/VertexSubdivision.lean)
recursively subdivides the boundary of each tuple and cones it to its
chosen center. A second explicit finite cone recursion proves
`dH + Hd = id - sd`. These are constructed operators on finite chains.
[Naturality](../../HodgeConjecture/Realization/Betti/VertexSubdivisionNaturality.lean)
and [locality](../../HodgeConjecture/Realization/Betti/VertexSubdivisionLocality.lean)
hold when the actual vertex map or subset respects the chosen centers.
The barycentric specialization discharges these center conditions.

[NativeSimplexGeometry.lean](../../HodgeConjecture/Realization/Betti/NativeSimplexGeometry.lean)
works on Mathlib's original standard-simplex probability type. Its affine
realization is continuous by the original finite weights embedding;
vertex, composition, face and barycenter identities are proved. The
coordinate homeomorphism also supplies a genuine compact-cover Lebesgue
number, measured by the sup norm of the actual weights.

[SingularSubdivision.lean](../../HodgeConjecture/Realization/Betti/SingularSubdivision.lean)
subdivides each original singular simplex inside that native domain, then
composes every resulting cell with the original continuous map. The
constructed endomorphism of Mathlib's rational singular chain complex
commutes with its differential.
[SingularSubdivisionHomotopy.lean](../../HodgeConjecture/Realization/Betti/SingularSubdivisionHomotopy.lean)
realizes the explicit vertex homotopy, including its degree-zero identity.
[SingularSubdivisionHomology.lean](../../HodgeConjecture/Realization/Betti/SingularSubdivisionHomology.lean)
bundles it as a native chain homotopy and proves subdivision and its powers
act identically on the original singular homology.

## Actual mesh shrinking and cover comparison

[SubdivisionGeometry.lean](../../HodgeConjecture/Realization/Betti/SubdivisionGeometry.lean)
proves the quantitative bound for barycenters of nested nonempty faces.
[BarycentricMesh.lean](../../HodgeConjecture/Realization/Betti/BarycentricMesh.lean)
proves that every tuple occurring in the recursive subdivision has such
a flag of faces. Its diameter therefore contracts by `n/(n+1)` for an
`n`-simplex. The resulting mesh bound applies to the actual recursive
chain operator and its iterates, with one count for each entire finite
chain, including cancellations and negative coefficients.

[SingularSubdivisionSmallness.lean](../../HodgeConjecture/Realization/Betti/SingularSubdivisionSmallness.lean)
transfers that estimate through the actual native weights coordinates,
applies the proved Lebesgue number to the pullback of a genuine two-open
cover, and proves `exists_iteration_small` for every original finite
singular chain. It also proves preservation of small chains under further
subdivision, allowing a common iteration count over finite supports.
[SingularSubdivisionLocality.lean](../../HodgeConjecture/Realization/Betti/SingularSubdivisionLocality.lean)
proves the explicit singular homotopy stays in the same small subcomplex.

The final algebra compares actual cycles and primitives through the
native small-chain inclusion. Subdivision replaces full cycles by small
ones without changing their class. If a small cycle bounds a full chain,
sufficient subdivision makes that primitive small; the local homotopy
identifies its subdivided class with the original small class.
[SmallSingularComparison.lean](../../HodgeConjecture/Realization/Betti/SmallSingularComparison.lean)
proves `inclusion_quasiIso` for the actual inclusion and constructs
`homologyIso` from its actual native homology map in every degree.
The generic [cycle-class criterion](../../HodgeConjecture/Realization/Betti/ChainHomologyClasses.lean)
uses categorical cycle representatives and actual incoming primitives;
the cover endpoint supplies every hypothesis from the constructions above.

## Cochain sequence and next obligations

[SubcomplexCochains.lean](../../HodgeConjecture/Realization/Betti/SubcomplexCochains.lean)
constructs rational cochains on arbitrary simplicial sets, their pullbacks,
and the actual short exact sequence

`0 → C*(A ⊔ B) → C*(A) × C*(B) → C*(A ⊓ B) → 0`.

The difference map is the first restriction minus the second. Function
gluing and extension prove degreewise exactness; the native connecting map
and all three positions of the long exact sequence are constructed. For
a topological cover, its first term is cochains on the small singular
subcomplex. The chain comparison still needs rational dualization before
it identifies that sequence with full singular cohomology.

The next dualization can use an additive functor
`D : (ModuleCat ℚ)ᵒᵖ ⥤ ModuleCat ℚ` with objects `Module.Dual ℚ M` and maps
`LinearMap.dualMap`. Native `range_dualMap_eq_dualAnnihilator_ker` and
`ker_dualMap_eq_dualAnnihilator_range` prove exactness over ℚ, using
`ShortComplex.Exact.unop`; `Functor.preservesHomology_of_map_exact` then
supplies homology preservation. `HomologicalComplex.opFunctor` reverses
chain shape to cochain shape without a shift or added differential sign.
Its quasi-isomorphism preservation, followed by
`HomologicalComplex.quasiIso_map_of_preservesHomology`, carries the actual
small-chain comparison to dual cochains. Degreewise identification with
the existing cochain functions uses the dual of the proved native chain
coordinate equivalence followed by `(Finsupp.llift ℚ ℚ ℚ _).symm`.
The actual coordinate-boundary formula fixes the alternating signs and
the restriction-map naturality. These are native ingredients for the next
proof, with no finite-dimensionality premise; this dual functor and complex
comparison are not implemented by the present checkpoint.

Next establish that dualization comparison, then compute the circle and
P¹ singular groups using the actual cover sequence. Finally identify the
oriented rational generator and its complex scalar extension with the
already constructed `2πi` analytic period. This checkpoint supplies no P¹
singular H² dimension, oriented Betti comparison or new Hodge-conjecture case.

## Validation

`make check-small-chains` passes its 2,263-job pure target and separately
builds the original P¹ chart topology for the cover regression (2,949
jobs). The eleven suites pass 111 examples, 13 named calculations and
264 enforced standard-three axiom audits, with zero errors and warnings.
They include the genuine crossing-simplex obstruction before subdivision,
uniform finite-chain shrinking, boundary signs, local homotopies and the
actual P¹ chart-cover inclusion in degree two. Build counts include cached
dependencies, rather than counting only newly compiled files.

The full default build passes 5,012 jobs. Root verification passes 1,395
declaration checks, 574 examples and 1,263 axiom reports within `propext`,
`Classical.choice`, `Quot.sound`; one report requires no axioms. The 487
library modules plus the root pass source scanning. Thirteen transitive
import boundaries, three indirect-negative checks, dependency pins, local
documentation links and whitespace checks pass. The pure small-chain
entry point has 23 project modules and excludes project geometry, cycles,
Chow, correspondences, de Rham and sheaf cohomology.

The source proofs use native Mathlib objects and local new constructions;
no Axiom package or assumed small-chain comparison is imported. Existing
warning scope remains; the main README remains 69 lines. Submission
candidate selection and release sign-offs are unchanged.
