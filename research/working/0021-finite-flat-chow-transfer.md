# Finite flat Chow pullback and geometric degree

Date: 2026-11-05. Working-tree checkpoint on Lean 4.35.0 and the existing
Mathlib pin. The Axiom Stacks proof reference remains pinned at
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

## Result and scope

The computed finite-fiber degree equals Mathlib's geometric rank of the
same finite flat morphism. On Noetherian source and target schemes locally
of finite type over a field, the original finite-fiber cycle pullback
preserves the original principal-relation span and descends to the original
integral and rational Chow quotients. Ambient integrality and reducedness
are unnecessary.

Constant geometric rank `d` gives `f_* f^* = d • id` on both quotients.
The degree law permits `d = 0`. For `d ≠ 0`, the existing
`RationalDegreeTransfer` is instantiated using these actual maps. Its
rational pullback is injective and its normalized pull--push is idempotent.
No relation-preservation, fiber-multiplicity compatibility, or operator
degree law is supplied as an input field.

## Proof chain

1. `Cycles/FiniteFlatRank.lean` compares actual fiber global sections with
   Mathlib's stalk rank, using finite affine schemes and rank base change.
2. `CommutativeAlgebra/Multiplicity/` retains the bounded prime-filtration,
   periodic-additivity and regular-element colength proofs needed for
   [Stacks 02QG](https://stacks.math.columbia.edu/tag/02QG). The general
   Cohen–Macaulay module theory is omitted.
3. `Cycles/IdealComap.lean`, `IdealStalk.lean`, `StalkBaseChange.lean`,
   `PullbackStalk.lean`, `FiberStalkKernel.lean` and `FiberMultiplicityLocal.lean`
   compare the original scheme-fiber local ring with the original source
   stalk modulo the extended target maximal ideal.
4. `ComponentStalk.lean`, `FlatComponents.lean` and `ComponentLocalLength.lean`
   identify the actual reduced components through a point with the minimal
   primes of its stalk, and identify their original generic-point lengths.
   `EquidimensionalDivisorPoint.lean` supplies the local dimension-one step.
5. `FlatComponentFunction.lean`, `FiniteFlatLocalOrder.lean`,
   `FiniteFlatComponentOrder.lean` and `FiniteFlatPrincipalDivisor.lean`
   prove the weighted principal-divisor sum on the original cycle module.
   Component and fiber nilpotent multiplicities are retained.
6. `QuotientLengthBaseChange.lean` and `FiniteFiberClosedBaseChange.lean`
   prove the actual closed pushforward square. `FiniteFlatPrincipalRelations.lean`
   applies that square to every genuine closed relation carrier and assembles
   the finite sum of actual source principal relations, as in
   [Stacks 02S1](https://stacks.math.columbia.edu/tag/02S1).
7. `FiniteFlatChowPullback.lean` descends the same maps and proves their
   integral-to-rational comparison. `FiniteFlatChowDegree.lean` descends the
   geometric degree law of [Stacks 02RH](https://stacks.math.columbia.edu/tag/02RH).
   `Realization/Chow/FiniteFlatTransfer.lean` supplies the actual transfer instance.

All cycle generators remain the existing integral ideal-sheaf subschemes.
All Chow groups remain their existing canonically graded principal-relation
quotients. The Axiom library is a proof reference, not a Lake dependency;
[the attribution inventory](../../third_party/axiom-stacks/README.md) records
the selected adaptations and preserved Apache-2.0 license.

## Public entry points

- `finiteFiberDegree_eq_finrank`.
- `finiteFiberPullback_closedImmersionPushforward`.
- `finiteFlat_pullback_principalDivisor_eq_sum_components`.
- `chowFiniteFlatPullback`, `rationalChowFiniteFlatPullback`.
- `rationalChowFiniteFlatPullback_rationalize`.
- `chowFinitePushforward_finiteFlatPullback_of_finrank_eq` and its rational version.
- `finiteFlatChowTransfer`, `rationalChowFiniteFlatPullback_injective`,
  `finiteFlatChow_normalizedProjector_isIdempotent`.

The cycle and Chow API is exported through `HodgeConjecture.Correspondence`;
the transfer instance is exported through `HodgeConjecture.Realization.Chow`.

## Validation

The targeted transfer build passed (3919 jobs), and the complete default
build passed (4142 jobs). The integrated root-import inventory passed all
1255 declaration checks, 565 examples and 1147 axiom reports.

Seven standalone files passed: `Verification.lean`,
`FiniteFlatRankVerification.lean`, `FiniteFlatChowVerification.lean`,
`FiniteFiberPullbackVerification.lean`, `FiniteNormChowVerification.lean`,
`FinitePushforwardCompositionVerification.lean` and `ChowLocalizationVerification.lean`.
The two new suites include five examples and 32 enforced axiom audits
(six rank audits and 26 Chow/transfer audits). The Chow suite uses the root
import and tests degree two for the actual square-zero thickening over a
field on the actual rational Chow quotient. Observed theorem axioms stay
within `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` is present.

The active production proof-token scan, exact dependency-pin/manifest check,
124 local file links in nine current documents and `git diff --check` pass.
The main README remains 69 lines. Existing Lean style/deprecation warnings
and the two pre-existing `Challenge.lean` statement placeholders remain.
These are working-tree checks, not clean-clone or human release sign-offs.

Reproduce the core checks from the repository root:

```sh
lake build
lake env lean research/Verification.lean
lake env lean research/FiniteFlatRankVerification.lean
lake env lean research/FiniteFlatChowVerification.lean
```

## Remaining work

General positive-dimensional flat pullback and further functoriality are
separate extensions. General Betti/purity/Gysin comparison, cycle-class
compatibility for these covers, and generation of each prescribed rational
Hodge class remain open. This checkpoint proves no new Hodge-conjecture case.
The separately reviewed Saito paper is a scoped reference for later boundary
methods, as recorded in the source ledger.
