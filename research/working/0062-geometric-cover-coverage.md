# Actual geometric cover coverage (2026-11-26)

`Realization/Chow/FiniteCoverCoverage.lean` supplies an adapter to the existing
exact aggregate for a fixed rational Hodge model and its complete finite target basis.
The original target, cycle map, basis index set, and exact modular rank checker
are explicit parameters. The constructor does not infer upstairs generation
from the existence of a finite cover.

Its transfer `T : RationalDegreeTransfer HY HX` has positive natural degree
`ν` and the proved law `T.push.comp T.pull = ν • LinearMap.id`. An original
cycle pushforward `pushCH` must satisfy the exact comparison square
`M.cycleClass.comp pushCH = T.push.comp clY`. Selected actual upstairs cycles
must realize the pullbacks of every matrix column in the fixed full basis.

`normalizedCoverCycles` constructs `ν⁻¹ • pushCH (upstairs j)` in the original
downstairs Chow module. `of_degree_transfer` proves their original cycle-class
column bindings and produces the unchanged `FiniteCoverageCertificate` type.
Its existing arithmetic acceptance theorem then gives full-target coverage.
`of_degree_transfer_harmonic` can prove the selected column equations through
an injective harmonic witness map and exact witness differences. These remain
explicit proof gates; the generic constructor supplies no generation theorem.

`Correspondence/Examples/SplitFiniteCover.lean` defines the actual projection
`coverProjection K I J : Spec ((I × J) → K) ⟶ Spec (I → K)`. Existing scheme
APIs prove it finite, étale, and flat, and it is surjective when `J` is nonempty.
`coverProjection_finrank` computes its original geometric rank as `card J`,
using `productIso`, finite flat base change, and the structural algebra rank.
`twoSheetCover` specializes to `I = J = Fin 2`, an actual rank-two morphism
from four reduced points to two reduced points.

`Realization/Chow/Examples/SplitOrdinaryChow.lean` bridges the original ordinary
rational Chow quotient to the existing split-cycle presentation. The bridge
retains identical cycle representatives. Every integral support has dimension
zero, and there are no one-dimensional integral carriers for principal relations.
The ordinary rational relation submodule is therefore zero. The version
`ordinaryChowEquivOfStructure` retains an explicit original structure morphism.

The original finite cycle pushforward has the same scheme-theoretic support
image and residue degree one. `finiteFiberMultiplicity_eq_one` computes the
original local scheme-fiber multiplicity as the length of a field. These give
`finitePushforward_eq_split`, `finiteFiberPullback_eq_split`, and the quotient
comparison squares for the original finite Chow pushforward and flat pullback.

`Realization/Betti/Examples/SplitCoverTransfer.lean` identifies canonical
scheme-valued complex points with the existing algebra-valued points through
`schemePointHomeomorph`. Naturality is proved for the identical original
`mapOfFunction` morphism in the regular-function evaluation topology.
The Betti maps are native singular `H⁰` pullback by the actual continuous map
and transfer summed over its actual point fibers. The degree law follows from
the actual fiber cardinalities, and `projectionTransfer_degree_eq_finrank`
identifies this degree with the original scheme morphism's geometric rank.

`SplitOrdinaryBetti.cycleClassOfStructure` combines the representative-preserving
ordinary Chow bridge with the already constructed native singular cycle map.
Both original-map comparison squares are proved, including the exact composite
structure map upstairs. The complete Hodge target and point-evaluation basis
are fixed through the independent native Hodge computation before choosing
the cycles for an aggregate certificate.

`Realization/Betti/Examples/SplitGeometricCoverage.lean` uses the actual
four-to-two cover. `actualPull` and `actualPush` are the original finite flat
Chow pullback and finite Chow pushforward. Its selected upstairs cycles are
the actual pullbacks of the two original reduced point classes. Both comparison
squares hold, the geometric and native degrees equal two, and the original
Chow degree law proves normalized pushforward recovers those same point classes.
The full target has dimension two; the aggregate uses `C = I₂`, denominator
one, integer matrix `I₂`, modulus three, and modular inverse `I₂`.

This is a complete zero-dimensional geometric cover comparison. It proves
the selected upstairs column equations in that example. It supplies no new
positive-dimensional cover comparison, no general upstairs generation theorem,
and no new case of the Hodge conjecture.

Provenance: the new adapters and example use existing project APIs and pinned
Mathlib. No new external source copy or additional license input is introduced.

Validation on 2026-11-26: `make check-geometric-cover-coverage` passes
11 named normalization, fiber-coverage and degree controls, 40 enforced axiom
audits, and all 134 import guards. Every audited dependency is among
`propext`, `Classical.choice` and `Quot.sound`. The public-library build
`lake build HodgeConjecture` passes 5,415 jobs. The complete root inventory
passes with 1,858 nonempty standard-three axiom lists and 1 axiom-free report.
All 745 active library/root/Solution sources pass proof-gap scanning;
intentional Challenge statement placeholders remain separate. Local links,
dependency pins, unique manuscript labels and whitespace checks pass.
The canonical 109-page manuscript rebuilds without overfull boxes, undefined
references or LaTeX errors. Rendered pages 7–8 and 80–81 verify the new theorem,
concrete example and declaration crosswalk. Nonblocking wider-library Lean
style/deprecation warnings and one existing bibliography underfull-box notice
remain. This records cached working-tree validation; clean-clone and human
release sign-offs remain separate.
