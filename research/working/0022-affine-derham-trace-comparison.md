# Affine de Rham trace, comparison and modular checks

Date: 2026-11-05. Lean 4.35.0 and the existing Mathlib pin are retained.
Axiom Stacks proof references remain pinned at
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

## Constructed objects

`CommutativeAlgebra/DeRham/Differential.lean` adapts the actual differential
on exterior powers of Kähler differentials, its defining rule, uniqueness
and square-zero proof from the pinned `RingTheory/DeRham/Basic.lean`.
`Complex.lean` adapts the cochain-complex packaging. The base-change and
quotient-descent portions of the upstream source are omitted. Attribution
and the Apache-2.0 license are preserved in
[the source inventory](../../third_party/axiom-stacks/README.md).

`Realization/DeRham/AffineDegreeZero.lean` defines closed functions by the
actual universal-derivation equation. Exterior-power coordinates and
Mathlib's homology API identify that kernel with degree-zero homology of
the constructed complex. Formal unramifiedness proves every function closed
in the special case where the differential module vanishes.

For arbitrary algebras this is the **naive Kähler de Rham complex**.
[Kreuzer–Long, Example 3.2](https://arxiv.org/html/2609.34819v1) exhibits a
one-point nonreduced algebra with three-dimensional `ker d`. A general
nilpotent-invariance or Betti comparison must not be inferred from this
construction. The current unramified and finite split comparison hypotheses
remain essential; the paper's counterexamples have not been formalized here.

`FiniteUnramifiedTrace.lean` uses the original algebra map for pullback and
Mathlib's actual algebra trace for pushforward on these kernels. For source
and target formally unramified over the base, an actual finite basis proves
`trace ∘ pullback = degree • id`. No splitting of the algebras is required.
Over ℚ, nonzero degree supplies the existing rational transfer structure,
pullback injectivity and normalized projector.

`AffineGeometricDegree.lean` identifies the degree with the geometric rank
of the same affine scheme map. The previous finite-flat rank theorem then
identifies it with the original computed cycle-fiber degree. This is a
comparison of actual degrees, rather than a supplied operator identity.

For finite split complex schemes, `SplitComparison.lean` constructs cycle
class from the existing actual point-cycle coefficients, independently of
the comparison map. Its target is the actual de Rham kernel of the original
coordinate algebra. Evaluation gives an equivalence with the existing
genuine `ℂ ⊗[ℚ] H⁰_B`. Pullback, pushforward and intersection commute with
the existing finite split Chow maps; both pullback and trace intertwine
with complexified singular maps. A reduced point has characteristic class
one at that point and zero at the other points. On split projections, trace
is identified componentwise with the ordinary algebra trace.

The finite-fiber summation helper is shared by the Betti and de Rham maps,
with its original rational `SingularDegreeZero.fiberSum` API retained.

## Dependency decision

The upstream general finite-syntomic cohomology trace reaches 4,080 Stacks
modules, about 1.4 million source lines and 75.7 MB of source at the pin.
An isolated build against the current toolchain encountered incompatible
sheaf/tensor APIs before reaching the trace theorem. That full source tree
was not added to this repository or used to discharge a premise.
The compact [experiment record](../archive/axiom-stacks-trace-import-2026-11-05.json)
preserves the pin, dependency counts and compatibility findings. The
upstream checkout, generated caches and raw scratch logs in `/tmp` are
temporary and disposable; they are not project dependencies or an archive.

The selected affine construction supplies a smaller verified first step.
General scheme hypercohomology, the finite-syntomic trace on it, the full
de Rham Weil cycle-class construction, positive-dimensional analytic/Betti
comparison, Tate-period normalization in positive codimension and
prescribed-Hodge-class generation remain open. This checkpoint does not
claim a new general Hodge-conjecture case.

## Build boundaries

The generic transfer definitions and proof bodies moved unchanged to
`Realization.Transfer`. `Chow.TransferProjector` re-exports their original
names and retains the cohomological-projector conversion. The algebraic
trace therefore imports the common API without the Chow model.

`Realization.DeRham.Core` has six project modules in its transitive import
closure, excluding project geometry, Chow and Betti. The original trace
entry point had 14 project modules before this split. The core build has
2,367 dependency jobs; that count includes cached Mathlib jobs and is not
a count of files rebuilt on every invocation.

The [granular commands](../BUILDING.md) separate algebraic, Chow, Betti,
comparison and full integration checks. `scripts/check_layers.py` enforces
the core, Chow and Betti import boundaries. Its negative check detects an
indirect forbidden import and reports the dependency path.

## Validation

The final complete default build passes 4,172 jobs after the transfer-layer
split. Focused builds pass independently: the affine core has 2,367 dependency
jobs, finite flat Chow transfer 3,920, and the comparison umbrella 3,559.
These totals include cached dependencies.

Five standalone files pass: `DeRhamCoreVerification.lean`,
`DeRhamVerification.lean`, `FiniteFlatRankVerification.lean`,
`FiniteFlatChowVerification.lean` and `Verification.lean`. The new core and
comparison suites have eight examples and 37 enforced standard-three axiom
audits. They test a nonzero affine-line differential, transfer for arbitrary
finite extensions of ℚ without a splitting, nonuniform and empty fibers,
degree two and complex coefficients outside the rational image. The existing
rank/Chow suites retain five examples and 32 enforced audits.

The root-import inventory passes 1,255 declaration checks, 565 examples and
1,147 axiom reports. All reported axioms lie in `propext`, `Classical.choice`
and `Quot.sound`; one report needs no axioms. The three import-boundary
checks pass, including a separate negative test for an indirect forbidden
import. All 383 production modules under `HodgeConjecture/` pass the
proof-token scan. Dependency-pin checks, local file links and
`git diff --check` pass. Lean style/deprecation warnings and the two
pre-existing `Challenge.lean` statement placeholders retain their baseline
scope.

The main README stays at 69 lines. No toolchain or dependency pin changes,
new project axioms, proof placeholders, package split or external Stacks
dependency are introduced. Existing clean-clone and human-release sign-offs
retain their previous status.
