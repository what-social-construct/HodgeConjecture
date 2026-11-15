# Original holomorphic Betti comparison on canonical P¹

Date: 2026-11-10.

Following [0055](0055-complex-singular-derived-comparison.md), this proves
invertibility of the **original** `Scheme.ComplexPoints.holomorphicBettiComparison`
for the canonical complex points of P¹ in degree two. The theorem concerns
the exact map constructed in [0053](0053-complex-coefficients-holomorphic-comparison.md),
not a replacement chosen from an isomorphism.

## The two one-dimensional spaces

The source is the existing tensor complexification of the canonical rational
singular H². The proved homeomorphism from the original P¹ model transports
its cover-generator coordinate, giving `sourceCoordinates : Source ≃ₗ[ℂ] ℂ`.

The target is the existing intrinsic holomorphic hypercohomology in degree
two. Its dimension is established using the separately constructed
cochain-induced isomorphism from 0055. This use of that isomorphism fixes the
target's dimension; it does not assert equality of its map with the older
holomorphic Betti comparison.

## The original map

The transported rational cover generator is nonzero. The previously proved
zero-detection theorem for the original holomorphic Betti map shows that
its image under the rational embedding is nonzero in the target.

Conjugating the original map by the two coordinate equivalences gives a
complex-linear endomorphism `scalarComparison` of ℂ. It satisfies
`scalarComparison z = z * scalarComparison 1`, and its value at one is
nonzero because the original generator has nonzero image. Multiplication
by that scalar is bijective. Transporting this bijection back proves
`comparison_bijective`, the exact categorical
`holomorphicBettiComparison_isIso`, and `comparisonEquiv` whose forward map
is the original comparison.

The proof requires no generic equality between the maps from 0053 and 0055.
That equality, general scheme topology, and general Betti–de Rham comparison
remain open.

## Verification

The focused P¹ module build passes with 4,706 jobs. Its verification
elaborates the exact original `IsIso` statement and passes seven
standard-three axiom audits. The permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The full exported library build passes
with 5,291 jobs, and root-import verification, import boundaries and
`git diff --check` pass.
