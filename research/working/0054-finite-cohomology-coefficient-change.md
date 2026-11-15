# Coefficient change with finite-dimensional cohomology

Date: 2026-11-10.

Following [0053](0053-complex-coefficients-holomorphic-comparison.md), this
proves the algebraic coefficient-change step needed for invertibility of
the constructed analytic comparison in item 4 of the
[active checklist](../TARGET_BRIDGE.md):

\[
\mathbb C\otimes_{\mathbb Q}H^n(C_\mathbb Q^\bullet(X))
\;\cong\;
H^n(\operatorname{Hom}_{\mathbb Q}(C_\bullet(X,\mathbb Q),\mathbb C)),
\]

when the original rational singular cohomology in degree n is finite
dimensional. No finiteness is imposed on the singular chain modules or
the sets of simplices. The map is induced by literal scalar evaluation
on the original cochains. This checkpoint does not yet identify its target
with complex constant-sheaf cohomology or its map with the existing
holomorphic comparison.

## Shared exact functionals

`LinearAlgebra.HomCoefficients` owns the exact contravariant functor
V ↦ Hom_k(V,A), for a field k and a commutative k-algebra A. Its coefficient
action and precomposition maps are native linear maps. Exactness uses
factorization through the original kernel quotient, followed by native
extension of a functional from a subspace. All vector spaces may be infinite.

The original `RationalDual.functor` now delegates to the specialization
k = A = ℚ, with its original public name, coefficient carriers and maps
retained. Its exactness theorem delegates to the shared proof. Existing
dual complexes, their transpose differential, subdivision and small-chain
comparisons retain their original interfaces. Verification checks that
the original rational functor and dual complex are definitionally the
shared specialization.

The native `IsBaseChange.linearMapRightBaseChangeEquiv` proves
A ⊗_k Hom_k(V,k) → Hom_k(V,A) bijective when V is finite dimensional.
The shared `comparison` has the explicit formula
(a ⊗ φ)(v) = a · algebraMap(φ(v)). The finite-dimensional isomorphism
retains that exact map.

## The actual cochain map

`tensorFunctor` applies native `LinearMap.baseChange` with the existing
coefficient algebra action. Native flatness over the field proves exactness.
It retains the original tensor product used by `RationalComplexification`.

The coefficient-evaluation maps form `coefficientTransform`, a natural
transformation between two exact functors. Applying it to the opposite
of an original chain complex constructs `complexComparison`. Its terms
need not be isomorphisms.

The native short-complex theorem `homologyMap_mapNatTrans` expresses the
induced map on cohomology as the conjugate of coefficient evaluation at
the actual homology object. Therefore finiteness is needed only for that
homology object in the degree being compared. The native opposite-homology
isomorphism fixes its relation to the original chain homology.

`cohomologyComparison` has the original tensor product of cohomology as
source, through exact scalar extension's native homology isomorphism.
`tensorHomologyIso_cohomologyComparison` proves it is induced by the actual
cochain map. `cohomologyComparison_isIso` and `cohomologyIso` retain that map
and discharge invertibility with the finite homology hypothesis.

## Original singular objects

`Betti.CoefficientChange` specializes these constructions to the existing
`SingularChainCoordinates.complex` on the native singular simplicial set.
`complexCochains` consists of unrestricted complex-valued functionals on
those original rational chains. Its differential is their actual transpose.
`complexCoordinates` identifies each term with all complex-valued functions
on the original simplices, using the existing native coproduct coordinates
and `Finsupp.llift`. No independent chain differential is reconstructed.

`rationalComplexIso` is the inverse of the existing
`CochainDualComparison.comparisonIso`. The resulting `cochainComparison`
is exactly φ ↦ (σ ↦ c · φ(σ)) on c ⊗ φ. Its original tensor cohomology
source is `RationalComplexification.Space (SingularCochains.Cohomology X n)`.
`cohomologyComparison_induced` proves the actual chain-to-cohomology square,
using the native scalar-extension homology naturality.

The already proved rational duality identifies the original rational
cohomology with the dual of original rational homology. Native
`Module.finite_dual_iff` turns finiteness of the former into finiteness of
the latter. Thus the public `SingularCoefficientChange.cohomologyIso`
requires only finiteness of the existing rational cohomology in that degree.
It has no topology hypothesis and no assumed comparison isomorphism.

## Controls and remaining scope

Controls include an infinite-dimensional split sequence with unrestricted
complex coefficients; the original rational functor and complex; the
actual transpose and alternating simplex-face differential in every degree;
positive degrees on contractible spaces; and degree two on both the original
and canonical P¹ point spaces. P¹ finiteness comes from the existing rational
calculation and canonical Betti equivalence. The original cover generator
has a proved nonzero image in the actual complex-functional cohomology target.
This is separate from the nonzero holomorphic image proved in 0053.

Next connect these unrestricted complex cochains to the native complex
constant sheaf and prove coefficient compatibility with the original
rational resolution. That compatibility must identify this cochain-induced
map with the exact map constructed in 0053. Its holomorphic invertibility
is not inferred merely from existence of the new cochain isomorphism.
The previous rational cochain patching, subdivision and sheaf comparison
proofs should be reused through shared coefficient constructions.

Finiteness of rational cohomology for general smooth proper schemes remains
a geometric obligation. It is proved for the P¹ degree used here, not supplied
as a general geometric instance. General scheme topology, proper
algebraic/analytic comparison, periods, purity and prescribed-class coverage
retain their earlier scope. No interchange of scalar extension with arbitrary
infinite products is asserted.

## Verification

`make check-singular-coefficient-change` includes the preceding analytic,
rational, whole-complex and original dual/cochain controls. The focused
verification passes all 45 standard-three axiom checks. The original
rational-dual and cochain-coordinate verification files also pass all 13
and 18 checks respectively, with no errors or warnings.

Full `lake build` passes with 5,269 jobs. All 120 import guards pass. The
combined root-import regression passes all 601 standard-three axiom checks
and 97 public-export checks, with no errors or warnings. This includes the
preceding holomorphic and rational comparisons, the new coefficient map,
both P¹ point models, actual differential and nonzero-generator controls,
and the original rational-dual tests under the root imports.

The whitelist remains `propext`, `Classical.choice` and `Quot.sound`.
No new production declaration uses a proof placeholder or project-level
axiom. The full library build still replays the preexisting `Challenge.lean`
proof-placeholder warnings. Local documentation links, the Makefile target
dry run and `git diff --check` pass.
