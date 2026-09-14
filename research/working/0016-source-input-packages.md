# Explicit literature-input packages

Status: CONDITIONAL CONSEQUENCES PROVED; FULL BUILD, VERIFICATION, AND SINGLE-PDF CHECKS PASS.

Date: 2026-09-14. This follows
[0015-split-galois-marked-comparison.md](0015-split-galois-marked-comparison.md).
Canonical manuscript: `paper/main.tex`, producing the single `paper/main.pdf`.

## Checkpoint

The three manuscript source blocks now have small, separately consumable
Lean interfaces. Each records the selected conclusion needed downstream, not a
formalization of the full cited theorem. The formal consequences are proved
with explicit premises; no project axiom, blanket literature hypothesis, or
global instance asserts any of these inputs.

| Input | Selected datum or proposition | Formal consumer |
| --- | --- | --- |
| Fixed inertia | The selected prime of `S^I` is unramified over the supplied base | Existing localized subgroup descent, with the same explicit `hI` |
| Finite étale extension | An actual finite étale scheme over `X` with an isomorphism from its pullback to the given cover of `U` | A chosen extension from a separate existence premise |
| Deck extension | The actual automorphism restriction homomorphism for that extension is bijective | Unique extension of automorphisms and a lifted deck action |
| Chow localization | Rational-linear `im(i_*) = ker(r)` and surjectivity of `r` | Raw lifts and boundary preimages of differences; with a separate algebra restriction, boundary preimages of convolution defects |

## One canonical fixed-inertia premise

`NormalizationInertia.InertiaFixedRingUnramifiedAt` moves unchanged to
`HodgeConjecture/Inputs/FixedInertia.lean`. Its name, field, and explicit
argument convention are retained. The old fixed-ring module imports this
definition; it does not maintain a second record.
`inertiaFixedRingUnramifiedAt_iff` proves equivalence with the unbundled
Mathlib `Algebra.IsUnramifiedAt` premise used by the submission wrapper.
Moving the record proves no new unramifiedness theorem.

The source is [Stacks, Lemma 58.12.4, Tag 0BST](https://stacks.math.columbia.edu/tag/0BST).
Its application must identify the full invariant base and the actual prime
inertia subgroup. The arbitrary base and proposed subgroup in the generic
record do not establish those identifications.

## Actual extension objects; separate existence and deck restriction

For scheme maps `j:U→X` and `p:Y→U`, the namespace `LiteratureInputs` in
`Inputs/FiniteEtaleExtension.lean` defines an actual extension witness

```text
E ∈ ℰ_j(p):
  p̄ : Ȳ → X finite and étale,
  Y ≅ U ×_X Ȳ over U.
```

`FiniteEtaleExtensionHypothesis j p` asserts only that this witness type is
nonempty. The type is meaningful for arbitrary `j,p`; openness, density,
regularity, and codimension-one conditions are not hidden behind a label.
When `j` is an open immersion, the witness's actual inclusion into `Ȳ` is
proved to be an open immersion.

Pullback followed by the witness isomorphism constructs

```text
res_E : Aut_X(Ȳ) →* Aut_U(Y).
```

`DeckExtensionHypothesis E` separately asserts bijectivity of this exact
map. This upgrades restriction to `E.deckEquiv`; its inverse gives
`E.liftDeckAction`, with restriction compatibility and uniqueness proved.
Cover existence alone does not supply this premise.

The relevant production obligations are recorded in the existing source
ledger: [0H2W](https://stacks.math.columbia.edu/tag/0H2W) supplies finite étale
extension under its boundary hypotheses;
[0BQF](https://stacks.math.columbia.edu/tag/0BQF) supplies full faithfulness
under its distinct hypotheses. The latter specializes to the selected
automorphism map. Neither full geometric theorem is formalized here.

## Additive localization and a boundary-valued raw defect

For rational vector spaces `B,C,U`, the proposition class
`ChowLocalizationHypotheses (i:B→ₗ[ℚ]C) (r:C→ₗ[ℚ]U)` has exactly the
fields `range_eq_ker` and `restriction_surjective`. Each consumer explicitly
requests this particular class instance. The module name expresses the
intended application; arbitrary vector spaces are not thereby Chow groups.

`ChowLocalization.exists_lift` and `two_lifts_differ_by_boundary` prove

```text
∀ a:U, ∃ c:C, r(c)=a,
r(c₁)=a=r(c₂)  ⇒  ∃ b:B, i(b)=c₁−c₂.
```

For a separately supplied rational algebra map `r:C→ₐ[ℚ]U` and an
idempotent `e∈U`, `projectorClosure` reuses the canonical
`AlgebraProjectorClosure` with literal witness fiber `{c:C // r(c)=e}`.
This definition needs no localization assumption; `projectorClosure_nonempty`
uses the assumption on `r.toLinearMap` to prove existence. It supplies no
linear or multiplicative section.

For any raw closure package `P`, not just that fiber construction,
`convolutionDefect_mem_range` and `exists_boundary_of_convolutionDefect`
combine exactness with the existing restriction-kernel calculation:

```text
Π²−Π ∈ im(i),
∃ b:B, i(b)=Π²−Π.
```

These are boundary-image statements, not defect vanishing or an idempotent
lift. The separate algebra-map premise is essential: additive localization
does not establish compatibility with correspondence multiplication.

[Stacks, Lemma 42.19.3, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
is the exact additive source. Applying this rational-linear interface to
that integral Chow sequence still requires rationalization and identification
of its maps, as well as the source's geometric hypotheses. No such general
geometric instance is asserted by defining the class.

## Semantic parity and submission boundary

This checkpoint is A11n / SP26. The three source blocks in the manuscript
remain distinct, and their statements are cited without repeating the source
proofs. The notation registry distinguishes `ℰ_j(p)`, `res_E`, and additive
boundary exactness from the already canonical raw closure and extension
objects. The hypothesis classes are local inputs, not new theorem names for
the complete Stacks statements.

`Challenge.lean`, `Solution.lean`, and `comparator.json` retain their two
existing statements and signatures. The fixed-inertia bundle is internal;
the compared statement still prints its Mathlib unramifiedness premise.
The [Palomar handoff](PALOMAR_FIXED_RING_HANDOFF.md) gives the separate recipe
for future explicit-premise wrappers. No new submission scope, metadata,
license, toolchain migration, or publication is introduced.

## Exact next gap

Source-known input production and application-specific constructions are
tracked separately:

1. Identify the geometric schemes, rings, and Chow maps and verify the cited
   hypotheses before constructing an instance of each selected input.
2. From an extended deck action, construct the actual Chow graph map and its
   restriction square; alternatively prove a boundary-defect correction or
   vanishing theorem. Exactness alone does neither.
3. Prove the prescribed cohomological action comparison and class-dependent
   coverage beyond the fixed finite-split generated class.

The existing split Chow/Betti/Hodge construction does not acquire these
general compactification conclusions merely by importing the input umbrella.

## Verification record

- Full `lake build`: PASS, 3028 jobs. The only warnings are the two
  intentional statement holes in `Challenge.lean`.
- `Challenge.lean`, `Solution.lean`, and `comparator.json`: source diffs are
  empty; the existing Solution proofs rebuild successfully.
- Independent source and semantic review: PASS.
- Single manuscript: PASS, 31 pages, 653270 bytes. Visual review of the
  conditional localization consequence and selected-input section (pages
  11 and 28) passes; the final TeX/BibTeX logs have no warnings, undefined
  references/citations, or overfull/underfull diagnostics.
- New input/submission verification section: PASS independently, without
  warnings. All 22 new axiom reports contain exactly `propext`,
  `Classical.choice`, and `Quot.sound`. The tests cover all three
  no-automatic-instance guards, explicit exactness and raw-lift consumers,
  unique action lifting, and a nonzero boundary defect. In the last example,
  `r:ℚ×ℚ→ℚ` is first projection, `i(b)=(0,b)`, and the raw lift `(1,2)`
  of `1` has defect `(0,2)≠0`, despite exactness and boundary support.
- Full `lake env lean research/Verification.lean`: PASS, exit 0, no warnings
  or errors. The automatic allowlist audit checks all 99 axiom reports:
  every dependency belongs to `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check`: PASS. No Comparator/NanoDa run or clean-clone check
  is claimed by this checkpoint.

These are worktree checks, not clean-clone or human release sign-offs; those
remain in `research/RELEASE_CHECKLIST.md`.
