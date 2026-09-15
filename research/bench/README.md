# Standalone research bench

This folder preserves valid auxiliary results and narrowly scoped diagnostics
outside the active library and its verification spine. Benching a result does
not identify or close a gap in the target-equivalence argument.

## Matrix restriction obstruction

`MatrixRestrictionObstruction.lean` was moved byte-for-byte from
`HodgeConjecture/LinearAlgebra/MatrixRestrictionObstruction.lean`. Its
`HodgeConjecture.MatrixRestrictionObstruction` namespace is retained.

The theorem rules out a unital ring homomorphism from the full rational
two-by-two matrix algebra to a nontrivial commutative ring. This is a valid
diagnostic for that particular proposed map, not an obstruction to all
correspondence constructions, a required premise of the active proof, or a
remaining target-equivalence gap.

Check it independently from the repository root:

```sh
lake env lean research/bench/MatrixRestrictionObstruction.lean
```

The finite-span incidence matrices and matrix-coordinate descriptions used by
the active split Chow and Betti proofs remain in the library.

## Auxiliary projector reconstruction

`ProjectorReconstruction.lean` preserves `reconstructedGraphProjectorLift`,
formerly in `HodgeConjecture/Realization/Chow/MarkedAugmentedRealization.lean`,
with the same definition and `HodgeConjecture.MarkedProjectorActionComparison`
namespace. Its three reconstruction regressions and axiom check are kept here.

This auxiliary construction chooses `encode (decode Π)`. Equality with the
chosen projector `Π` is unproved and is not part of this result. The helper is
not an active proof step: the active spine keeps the chosen projector and its
supplied extension restriction law. Core Chow detection remains in the library.

Check the helper and its regressions independently:

```sh
lake env lean research/bench/ProjectorReconstruction.lean
```
