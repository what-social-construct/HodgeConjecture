# Axiom Stacks: reuse and overlap audit

Assessed: 2026-11-04 against the current Hodge working tree, including the
SP107--SP113 files already present as local changes. This is an external-source
and interface comparison. No external theorem has been compiled into this
repository or used to discharge an existing premise by this audit.

## Decision

Reuse selected proofs, starting with **flat pullback and the finite locally
free degree formula**. Keep the existing cycle and Chow objects. Our
norm--order theorem has a better consumer-facing signature for this project;
our integral/rational Chow localization is already implemented on the actual
quotients used by the boundary consumers. Replacing either now would add
comparison work without advancing the next geometric step.

Axiom also supplies a source implementation of **the exact fixed-inertia
theorem** currently left as an input here, and a much broader algebraic
correspondence construction. These are real reuse candidates, with separate
integration costs. Their abstract Weil-cohomology interface does not by itself
construct our intended rational Betti/Hodge realization.

This comparison supports the existing Chow-to-Betti work order in
[TARGET_BRIDGE.md](../TARGET_BRIDGE.md), rather than a new proof route.

## Snapshot and compatibility

The [release website](https://stacks.axiommath.ai/) links to
[AxiomMath/Stacks at `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`](https://github.com/AxiomMath/Stacks/tree/f8e70c5dd04bfabcb423d5e325461f527c85a5d6).
All upstream links below are pinned to that snapshot.

| Dependency | Hodge repository | Axiom snapshot |
| --- | --- | --- |
| Lean | `4.24.0`, confirmed with `lake env lean --version` | `4.34.0-rc2` |
| Mathlib commit | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` | `16edf57de7933555826307a3d81b4391a3657a09` |
| Library layer of the candidates below | Existing project modules | `StacksFrontier` |

The [upstream contributor guide](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/CONTRIBUTING.md)
distinguishes human-reviewed `StacksCore` from `StacksFrontier`, where checking
the mathematical statement against its source remains necessary. The release
reports kernel-checked proofs using the standard logical axioms. This audit
read source statements and proof bodies; it did not independently rebuild that
claim or run `#print axioms` under their toolchain.

An unchanged dependency import cannot be added to our present pin. Options are
a selective backport, retaining our definitions, or a separately validated
Lean/Mathlib migration followed by explicit equivalences. A source theorem
existing upstream does not change an in-repository gap's status until that
integration is checked.

## Candidate inventory

| Object or result | Upstream evidence | Existing Hodge object or gap | Disposition |
| --- | --- | --- | --- |
| Flat pullback, including nonreduced multiplicities | `Stacks.Chow.flatPullback` and `flatPullback_cycleAssociatedToClosedSubscheme`, Tags 02RB | Arbitrary flat pullback is the next missing cycle operation; open restriction and split-point pullback already exist | **First reuse target:** adapt the finite flat, relative-dimension-zero case to our cycles |
| Descent of flat pullback to Chow | `flatPullbackFactorsThroughRationalEquivalence_general` and `flatPullbackChowOfRelativeDimension`, Tag 02S1 | Our `ChowGroup` and `RationalChowGroup` use actual principal-relation quotients | Reuse the geometric relation-preservation proof, with an explicit comparison to our relations |
| Finite locally free push--pull degree | `fibreDegreeIsRank_of_isFiniteLocallyFreeOfRank` and `properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank`, Tag 02RH | Actual Chow degree law remains open; `RationalDegreeTransfer` consumes a supplied law | **First reuse target:** the source discharges the fiber-degree premise; use our existing finite-scheme length formula where possible |
| General proper pushforward and flat base change | `properPushforwardDescends` and `flatPullbackChow_comp_properChowPushforward_of_isPullback`, Tags 02S2/02RG | Finite pushforward, norm descent, and composition are already proved here | Adopt when a genuinely nonfinite proper map or a base-change square is needed; retain current finite maps |
| Fixed-inertia invariant ring is locally étale | `MulSemiringAction.exists_etale_away_fixedPoints_inertia`, Tag 0BST | `NormalizationPrimeInertiaFixedRingUnramifiedAt` is still an explicit premise | Strong candidate to discharge an actual open source input after identifying inertia and the full invariant base |
| DVR inertia-fixed integral closure is locally étale | `inertia_fixedSubalgebra_isIntegralClosure_and_etale_localization`, Tag 09EH | Height-one/DVR normalization route | Smaller alternative port to evaluate; it does not replace the arbitrary-base statement without localization comparisons |
| Norm--order identity | `ord_norm_eq_sum_inertiaDeg_mul_ord`, Tag 02MJ | `localOrder_norm_eq_sum` already supplies the identity used in finite Chow descent | **Keep ours:** it derives several side conditions that the upstream tagged signature exposes |
| Chow localization | `surjective_chowGroupRestrict` and `exact_chowPushforward_chowGroupRestrict`, Tag 02RX | SP63/SP110 already prove integral/rational restriction surjectivity and boundary exactness | **Keep ours:** the required result is already on the quotients consumed here |
| General smooth-projective correspondences and graph functor | `canonicalCorrespondenceCompositionData`, `canonicalCorrespondences_gradedCategory`, `canonicalGraphFunctor`, Tags 0FG2/0FG3 | General geometric convolution is missing; our split degree-zero correspondence algebra is constructed | Substantial later reuse target; preserve the split model as an actual realization check |
| Actual Chow operations packaged for a classical Weil theory | `chowCycleData`, `ChowClassicalWeilCohomologyTheory` | General rational Chow--Betti map and independent Hodge subspace remain unconstructed | Useful algebraic interface; supplying a classical theory is still an additional construction |

### Flat pullback and degree: read the downstream discharge

The actual raw operation and its multiplicities are in
[Gysin42/FlatPullback.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/Gysin42/FlatPullback.lean).
The generator formula identifies pullback with the cycle of the actual
scheme-theoretic inverse image in
[FlatPullback/Cycles.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/Cycles.lean).
[GeneralRationalEquivalence.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/GeneralRationalEquivalence.lean)
proves preservation of rational equivalence and constructs the induced Chow
map under flatness, local finite type, and a specified relative dimension.

The helper `properPushforward_flatPullback` in
[FiniteLocallyFree.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/FiniteLocallyFree.lean)
takes `FibreDegreeIsRank` as a premise. Its header describes that premise as
missing. However,
[FiniteLocallyFreeFibreDegree.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/FiniteLocallyFreeFibreDegree.lean)
**proves the premise** and the resulting cycle identity for finite locally
free maps of rank `d`. Do not classify 02RH as conditional from the first
file alone. The displayed degree theorem is on cycles; applying it to our
Chow groups additionally requires descent and compatibility of the maps.

Our working tree already contains
[FiniteFiberLength.lean](../../HodgeConjecture/CommutativeAlgebra/FiniteFiberLength.lean)
and [FiniteSchemeLength.lean](../../HodgeConjecture/Cycles/FiniteSchemeLength.lean).
In particular, `finiteScheme_finrank_eq_sum_stalkLength` handles actual finite
schemes over a field, including empty and nonreduced ones, with the structural
residue-field actions retained. This is a useful existing ingredient for the
same weighted fiber-degree calculation. What is still needed is its comparison
with the multiplicities of the actual flat pullback, not a second independent
degree package.

General proper pushforward descent is discharged in
[ProperPushforwardDescent.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/BivariantComposition/ProperPushforwardDescent.lean).
The fully discharged flat/proper Chow base-change theorem is in
[ProperPushforwardChowBaseChangeUnconditional.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/FlatPullback/ProperPushforwardChowBaseChangeUnconditional.lean).
These supply proof references beyond the finite case, rather than reasons to
rebuild SP107/SP113.

### Fixed inertia: an exact source match with two adapters

[Invariant/Inertia.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/Invariant/Inertia.lean)
states 0BST for a finite group acting on any commutative ring. With
`I := q.inertia G`, it constructs an element `g` of the inertia-fixed ring
outside the contraction of `q`, such that localizing at `g` is étale over
the full invariant ring. The signature does not assume the conclusion as
another inertia/unramifiedness package.

To consume this in our existing normalization descent, prove:

1. Our `primeInertiaSubgroup Q`, defined using the stabilizer's residue-action
   kernel, equals the upstream `Ideal.inertia` subgroup, using the already
   proved membership characterization.
2. The invariant subring inclusions agree with our
   `FullInvariantNormalizationRing` and fixed subalgebra maps. Localize the
   supplied étale neighborhood at the selected prime and take the unramified
   consequence.

Only after those maps agree does it produce our named input. Any subsequent
identification of the full invariant ring with an affine base `B` retains
the existing normality/separability hypotheses. Valuation inertia and prime
inertia still require our localization comparison.

The [DVR implementation of 09EH](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/DiscreteValuationRing/Inertia/InvariantRing.lean)
has a much smaller Stacks import closure. Its exact assumptions are a DVR,
its fraction field, a finite Galois extension, the actual integral closure,
and a selected maximal ideal. It supplies integral-closure identification
and étaleness at the selected localization. It is a promising bounded port
for the height-one route, not a proof of global étaleness over any affine base.

### Where our version is preferable

The [upstream 02MJ signature](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/RingTheory/OrderOfVanishing/Norm.lean)
asks for a `Fintype` of maximal ideals, Noetherianity and a dimension bound on
each localization, compatible localization-to-fraction-field algebra data,
an injectivity argument, and an explicitly identified nonzero norm value.
Our [LocalOrderNormFormula.lean](../../HodgeConjecture/Cycles/LocalOrderNormFormula.lean)
derives the semilocal and localization conditions from the finite extension
and evaluates on units of the original fraction field. It assumes neither
normality, freeness nor separability. Retain this API and its already proved
scheme/Chow descendants. This is a comparison of the named signatures, not a
claim that no other upstream helper can derive any of those conditions.

[Upstream Chow localization](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/LocalizationSequenceOpenImmersion.lean)
works in its general locally Noetherian base situation. Our
[ChowLocalization.lean](../../HodgeConjecture/Cycles/ChowLocalization.lean)
already proves the exact integral and rational sequence needed here for a
Noetherian ambient scheme and supplied dimension function. The external
version has broader ambient scope; the local version is already connected
to the boundary-correction consumer. There is no immediate missing result
to gain by replacing it.

### General correspondences and realization

[CanonicalGradedCategory.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/WeilCohomology/Correspondences/CanonicalGradedCategory.lean)
instantiates correspondence composition with the canonical diagonal Gysin
classes and proved associativity/unit inputs, and supplies the graph functor.
This is a much broader algebraic construction than our finite split example.
Reading only the earlier intersection-product definition would miss these
downstream laws and their discharge.

[ClassicalChowCycleData.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/WeilCohomology/ClassicalChowCycleData.lean)
packages actual Chow groups and operations. Its
`ChowClassicalWeilCohomologyTheory` is a type of supplied classical Weil
theories over those groups. The underlying
[ClassicalTheory.lean](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/StacksFrontier/AlgebraicGeometry/WeilCohomology/ClassicalTheory.lean)
includes cycle-class and duality compatibilities as structure data.
These declarations alone do not instantiate rational singular cohomology
on arbitrary complex varieties, its Hodge structure, or our separately
prescribed Hodge classes. No inspected declaration closes that realization
gap. Our actual split Chow/singular-Betti/Hodge model remains useful as a
comparison case; arbitrary-class recipe generation remains a separate step.

## Import cost and object compatibility

A source import traversal of the downloaded snapshot gave the following
closures. Counts include the named module and every reachable
`StacksCore`/`StacksFrontier` module; they exclude Mathlib and other packages.
They measure source imports, not the minimal logical dependencies of a theorem
or the size of a possible specialized backport.

| Candidate module, under `StacksFrontier` | Stacks modules | Stacks source lines |
| --- | ---: | ---: |
| `RingTheory.DiscreteValuationRing.Inertia.InvariantRing` | 19 | 9,082 |
| `RingTheory.Invariant.Inertia` | 289 | 136,394 |
| `AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFreeFibreDegree` | 1,041 | 365,454 |
| `AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence` | 1,074 | 367,436 |
| `AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent` | 3,930 | 1,275,338 |

The complete source snapshot has 62,972 modules below the two tier directories
(445 Core and 62,527 Frontier). No unresolved Stacks module import was found
in the listed closures. Counts were obtained by reading Lean import commands
and traversing the resulting module graph, without invoking Lake.

There is also a genuine representation comparison to prove:

- Our `Cycles X R` is a finitely supported function on actual integral
  ideal-sheaf subschemes, over general coefficients. Their `CycleGroup` is
  a dimension subgroup of Mathlib's point-indexed, locally finite
  `AlgebraicCycle X ℤ`, in a `ChowSituation` over a locally Noetherian,
  universally catenary base with a dimension function.
- Our existing `pointEquivIntegralClosedSubscheme` supplies the generator
  identification. It is not yet a cycle/Chow equivalence: one must compare
  finite and locally finite supports in the chosen Noetherian setting,
  the dimension gradings, and the principal-relation subgroups.
- The Chow comparison must retain the actual open restriction, finite
  pushforward and cycle-class maps. An additive equivalence by itself does
  not identify any of those operations.
- The newer Mathlib also has `AlgebraicGeometry/Normalization.lean`, imported
  by their normalization modules, whereas our pinned Mathlib lacks that file.
  A future migration should compare this canonical construction with our
  marked gluing construction before adding another normalization object.

## Bounded continuation

1. Use 02RB/02S1/02RH as proof references for finite flat pullback on our
   existing finite cycles and Chow quotients. Prove the fiber-multiplicity
   comparison against `finiteScheme_finrank_eq_sum_stalkLength`, then the
   actual Chow push--pull degree law. Preserve the same morphism and maps
   throughout; a new supplied degree-law structure would not fill the gap.
2. Evaluate the 19-module DVR inertia route as a separate bounded backport.
   Use 0BST directly if its greater generality is required and the version
   cost is justified. Retain all current conditional statuses until a proof
   under this repository's pin supplies the exact existing input.
3. Reconsider a dependency migration before copying the general proper/Gysin/
   correspondence library. Its algebraic coverage is valuable, but the
   comparison with our quotients and the rational Betti realization still
   require work.

Validation for this audit: read the pinned source snapshot, compared the
named signatures with existing working-tree definitions, inspected downstream
discharges of the degree/descent/canonical-correspondence hypotheses, and
traversed candidate source imports. No production Lean code, dependency pin,
theorem status or manuscript claim is changed.

## Follow-up (2026-11-05)

The [Lean 4.35 migration](0020-lean-4-35-migration.md) supersedes the
4.24 dependency baseline above. A bounded fiber-residue proof adaptation
and actual finite-fiber cycle pullback/degree calculation now compile on
our existing objects; the current claim ledger states their exact scope.
The remaining continuation still includes principal-relation preservation,
Chow descent, constant-rank comparison and fixed-inertia local étaleness.
The historical source-inspection validation above does not certify those steps.
