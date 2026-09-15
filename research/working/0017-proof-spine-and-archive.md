# Proof-dependency and archive checkpoint

Date: 2026-09-14.
Status: ARCHIVAL AND BENCH IMPLEMENTED; AUTOMATED PROOF CHECKS PASS;
HUMAN SEMANTIC AND RELEASE GATES OPEN.

This is a pruning audit, not a new mathematical result or another proof
outline. Current theorem scope is in `../CLAIM_LEDGER.md`; the current
geometric task is in `../GAP_MAP.md`. There is one active manuscript,
`../../paper/main.tex` and `../../paper/main.pdf`.

## What the current proofs actually use

`../ProofDependencies.lean` traverses checked declaration types and
proof/definition bodies transitively. Importing a file is not counted as
using all its declarations. The audit concerns the current proof terms;
it does not establish mathematical necessity for any future proof strategy.

| Audited endpoint | Modules under `LinearAlgebra/` in its declaration closure |
| --- | --- |
| `SplitGaloisMarkedComparison.palomarTargetSquare` | `BlockGraphProjector`, `MarkedAugmentedAlgebra`, `UniversalIdempotentAlgebra` |
| `SplitGaloisMarkedComparison.markedEmbedding_action` | `BlockGraphProjector`, `MarkedAugmentedAlgebra` |
| `PrescribedChowProjectorLift.rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage` and its `iff` counterpart | `BlockGraphProjector` only |
| Both fixed-ring theorems in `Solution.lean` | None |

These are real transitive dependencies through higher-level wrappers, not
direct calls to every listed module from the endpoint body.

The other retained modules have different roles:

- `MarkedAugmentedAlgebraDecomposition` proves a genuine algebra
  equivalence, preserving multiplication. It supports the multiplicative
  sheet wrappers, but is in none of the six endpoint closures above.
- `FiniteSpanMatrix` supports the separate finite-span/additive-quotient/Chow
  comparison; it is not an input to the two audited split endpoint proofs.

`MatrixRestrictionObstruction` was subsequently moved unchanged to
[`../bench/`](../bench/README.md) at the user's request. It is separately
checkable, no longer an active supporting module or dependency-audit target,
and is not a geometric obstruction in the [target sketch](../TARGET_BRIDGE.md).

The retained utilities are not deleted merely for being absent from one
chosen endpoint. The `LinearAlgebra/` directory contains both operator utilities and supporting
algebra; its name is not a classification of every declaration as linear
or as necessary for the geometric construction.

## What is not the geometric bridge

For every vector `α`, `P_α(t,x)=(t,tα)` is idempotent. Encoding a class as
this operator and changing coordinates do not prove its algebraicity. The
constant-marked shear is an invertible linear map, not a lossy projection;
it is not thereby an algebra isomorphism or an algebraic correspondence.
The selector-coordinate product-algebra decomposition is a different map.

In the general comparison, the residual map and its action square remain
explicit inputs. The finite split model constructs them geometrically,
but its marked multiplicative residual produces the negative fundamental
class. The proved rigidity theorem prevents surjective multiplicative
residual maps from furnishing arbitrary classes simply by varying that map.
The free-span realization's genuine loss is separately identified with
the point-decomposition ideal, not with the invertible shear.

## Physical archive

Six unused modules were moved out of `HodgeConjecture/` without changing
their contents:

- `Boundary/Normalization/GlobalExtension.lean`;
- `Realization/BoundaryProjector.lean`;
- `Realization/CohomologicalProjector.lean`;
- `Realization/CompactificationProjector.lean`;
- `Realization/Chow/SelectorRealization.lean`;
- `Realization/Chow/SheetLinearization.lean`.

Their paths and reasons are recorded in
[`../archive/legacy-lean/README.md`](../archive/legacy-lean/README.md).
Before moving them, all importers were checked to lie within this retired
set. Their old public import paths are retired; the archive is a recoverable
source snapshot, not a supported build target. No project theorem was
replaced with an axiom or a hypothesis during pruning.

The obsolete plans `0001`, `0002`, `0003`, `0004`, and `0006`, plus the
`0001` companion review, were moved unchanged to
[`../archive/planning/`](../archive/planning/README.md). Earlier proof
checkpoints `0007`--`0009` remain as dated history with corrected current
status pointers. The gap map and ledgers, not old unchecked planning lists,
now govern the current reading order.

Retained: the declaration-free `InertiaSaturation.lean` import shim, active
supporting lemmas, and embedded compatibility adapters. SP9 retirement and
human semantic/release gates remain open. This is not a claim that every
possible redundant helper has been removed or that every folder has been
redesigned. The empty Planar directory was removed separately; its archived
sources remain intact.

## Verification

- All twelve archived files match their pre-move SHA-256 hashes.
- No active source imports the retired modules.
- The persistent declaration audit passes all six endpoint assertions and
  its two retained supporting reports after benching the matrix diagnostic.
- `lake build`: PASS (3027 jobs); only the two intentional Challenge
  placeholders are reported as warnings.
- `lake env lean research/Verification.lean`: PASS, no warnings or errors;
  all 98 axiom reports contain only `propext`, `Classical.choice`, and
  `Quot.sound`.
- The unchanged benched matrix theorem separately checks. It has no active
  source importers, verification entries, or manuscript proposition.
- New target-sketch and bench links resolve; active imports contain none
  of the retired modules. Historical checkpoint paths remain provenance.
- The single `paper/main.pdf` rebuilds: 32 pages; final TeX log has no
  warnings, unresolved references, or overfull/underfull boxes.
- `git diff --check`: PASS. Changes remain uncommitted.
- No publication, toolchain migration, or new Palomar statement is included.
