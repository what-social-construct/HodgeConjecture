# Fixed-inertia étale bridge (2026-11-12)

## Target and source

The current normalization descent takes
`NormalizationPrimeInertiaFixedRingUnramifiedAt Q` as an explicit input. The
general [Stacks fixed-inertia theorem, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST)
instead proves étaleness of `S^G → S^(I_Q)` for the actual inertia group
`I_Q` at `Q`. [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks/tree/f8e70c5dd04bfabcb423d5e325461f527c85a5d6)
formalizes that theorem. Its proof uses a sizeable étale base-change and
equivariant idempotent decomposition package, so a selective local port is a
substantial task.

The narrower [DVR theorem, Tag 09EH](https://stacks.math.columbia.edu/tag/09EH)
gives the selected-prime étaleness needed after height-one localization.
The local port uses the pinned Axiom source
`StacksFrontier/RingTheory/DiscreteValuationRing/Inertia/InvariantRing.lean`
as a proof reference, with Apache-2.0 attribution in the adapted module and
`third_party/axiom-stacks/`.

## Verified pieces

- `PrimeInertia.primeInertiaSubgroup_eq_inertia` identifies the existing
  stabilizer-kernel subgroup with Mathlib's `Ideal.inertia`. Its focused Lean
  build passed.
- `FixedInertiaEtaleBridge` converts étaleness at the fixed-ring prime, an
  étale prime localization, or an étale principal neighborhood into the
  exact bundled local unramifiedness premise. Its generic focused build passed.
- `DvrInertiaEtale.etale_atPrime_of_ramificationIdx_eq_one` adapts Axiom's
  finite-presentation and index-one criterion. Its focused build passed.
- `DvrInertiaEtale.ramificationIdx_eq_one_and_isSeparable_of_inertia`
  adapts the Galois prime-count and subgroup-cardinality calculation. Its
  focused build passed.
- `DvrInertiaFixedRing.inertia_fixedSubalgebra_etale_atPrime` assembles the
  actual DVR integral-closure and inertia-fixed-ring instances and proves
  the étaleness component of Tag 09EH. Its focused build passed. This is not
  the arbitrary-ring Tag 0BST theorem.
- `make check-fixed-inertia` builds the retained DVR, inertia, localization,
  base-DVR, and transport modules separately. The expanded check passed and
  audited twenty-eight public theorem and definition types; each uses only
  `propext`, `Classical.choice`, and `Quot.sound` (some need only two).
- `LocalizationInertia.normalization_inertia_map_of_isLocalization` proves that
  the chosen normalization prime has the same Mathlib inertia after base
  localization at denominators fixed by the Galois action. Its focused Lake
  build and standard-axiom audit passed.
- `LocalizedEtaleTransport.formallyUnramified_of_etale_localized_equiv` proves
  the final abstract implication from an étale localized model and a local
  algebra equivalence to formal unramifiedness over an intermediate source.
  Its focused Lake build passed.
- `FixedRingLocalizationComparison.fixedSubalgebra_isLocalization_of_injective`
  and `FixedRingAtPrimeComparison.fixedSubalgebra_localizationAtPrimeEquiv`
  prove that fixed rings commute with injective equivariant localization at
  fixed denominators and identify the selected local rings. Their focused
  builds and the expanded axiom audit passed.
- `FixedRingPrimeLocalization.fixedSubalgebra_under_map_of_isLocalization`
  identifies the original selected fixed-ring prime with the contraction of
  its image after equivariant localization. Its focused Lake build passed.
- `HeightOneDvrBase` proves the normal-base height-one contraction, DVR
  localization, fraction-field map, and maximality of a selected prime after
  an integral localization. `FullInvariantBaseProperties` proves the exact
  full-invariant base is normal with fraction field `K` and a height-one DVR
  localization even without normality of the original affine base. Both
  modules passed the focused build and expanded axiom audit.
- `HeightOneDvrBaseChange.normalizationBaseChange_selectedPrime_isMaximal`
  specializes the maximal-prime statement to the actual normalization
  base-change map; its focused build passed.
- `NormalizationFixedRingLocalization.normalizationFixedRing_isLocalization`
  specializes generic equivariant fixed-ring localization to the actual
  normalization base-change map. Its focused build and axiom audit passed.
- `NormalizationFixedRingPrimeComparison` identifies the selected contracted
  fixed-ring prime and gives the corresponding local-ring equivalence under
  normalization base change. Both declarations passed the focused build and
  axiom audit.
- `FixedPointsBaseComparison` proves the fixed-ring carrier and selected
  ideal are unchanged by presenting the localized ring over `B` or `C`, and
  transfers the selected local étaleness statement. Its focused build and
  axiom audit passed.
- `HeightOneDvrInertiaEtale.normalization_heightOne_inertia_etale_atPrime`
  applies Tag `09EH` at the selected prime of the height-one DVR
  localization of a normal Noetherian base. Its focused build and axiom audit
  passed.
- `HeightOneInertiaGroupComparison.normalizationPrimeInertiaGroup_eq_localized_inertia`
  identifies the project's original prime-inertia group with inertia at the
  selected localized prime. Its focused build and axiom audit passed.
- `NormalizationActionComparison` proves equality of the project's Galois
  action on the localized integral closure and Mathlib's integral-closure
  action used by Tag `09EH`. `FixedPointsAtPrimeTower` proves coherence of the
  original-base and localized-base maps into the selected local fixed ring.
  Both modules passed focused builds and the axiom audit.
- `NormalizationActionInertiaComparison` derives equality of the two selected
  inertia subgroups from the action equality, without rewriting the full
  étaleness statement. It passed the focused build and axiom audit.
- `NormalizationActionFixedPointsComparison` proves equality of the localized
  fixed subalgebras under the two action constructions. Its focused build and
  axiom audit passed.
- `NormalizationActionEtaleComparison` transports the DVR étaleness statement
  across that action equality and the `C`- versus `B`-based fixed-ring
  presentations. Both its local statements passed focused builds and the
  axiom audit.

## Remaining proof steps

1. Assemble the verified action, inertia, base-map, selected-prime, local-ring,
   and étaleness comparisons into the exact local formal-unramifiedness proof
   needed for `hI`. The individual comparisons and étaleness theorem are
   verified; this single composite remains open. A scratch assembly identifies
   the local fixed rings and supplies the localized étaleness conclusion,
   but the final `B → F → U` scalar-tower instance must agree with Ore
   localization's scalar action before its algebra equivalence can transport
   formal unramifiedness. The scratch proof is outside the build.
2. Align the fixed-ring algebra structure over the localized base with the
   same underlying fixed ring over the original base. For the more general
   `S^G` route, also prove compatibility of its map to `K` with its natural
   inclusion in `N`.
3. Transport the DVR étaleness conclusion and supply the named local
   unramifiedness premise to
   `PrimeInertiaDescent`; retain the existing normality and separability
   hypotheses when identifying the full invariant ring with the affine base.

Even a completed 09EH specialization leaves the current generic Palomar
statement conditional, because that statement permits arbitrary base `A`
and subgroup `I`. A new compared theorem would be needed to advertise the
actual-inertia specialization. The general Tag 0BST remains open locally.
