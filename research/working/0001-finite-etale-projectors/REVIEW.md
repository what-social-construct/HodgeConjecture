# Publication-scope review

Reviewed: 2026-09-10.

## Verdict

This material supports a short Lean formalization/infrastructure note. It does
not currently support a paper advertised as a proof, partial proof, or new case
of the Hodge conjecture. The most coherent unit is the finite-etale
correspondence algebra, finite-group and Hecke projectors, and the conditional
Galois collision calculation.

## Safe mathematical scope

- The finite-etale span classes form a convolution algebra, and finite deck
  actions send rational group-algebra idempotents to correspondence
  idempotents. The finite-group average and Hecke-corner calculations are
  formal theorems.
- `FiniteEtaleAlgebraModel` has source the finite-etale free algebra and assumes
  additivity only for finite coproducts (`FiniteEtaleModel.lean`, lines 44--63).
  Thus the migrated Galois result no longer quantifies over arbitrary spans or
  countable coproduct additivity. This removes the Eilenberg-swindle defect from
  this theorem path.
- For `[Fintype G]`, `[IsFinite f]`, and `[IsEtale f]`, a supplied
  `GaloisCollisionDecomposition` and a supplied `FiniteEtaleAlgebraModel` imply
  the graph-sum formula and the normalized collision idempotence
  (`GaloisCollision.lean`, lines 148--189 and 246--297). Neither supplied
  structure is constructed in general by these theorems.
- Independently, for an essentially finite-type commutative algebra, the
  collision Noether different and the annihilator of relative Kahler
  differentials have the same prime support, so the collision different detects
  the non-unramified locus (`NoetherDifferentRamification.lean`, lines 34--181).
  This is an unconditional formal theorem under the stated finite-type
  hypothesis and formalizes a known support result; it is not an equality with
  the classical Dedekind different.
- The marked intermediate normalization is now formally identified with the
  subgroup-fixed ring in the normal-closure normalization. The
  chosen-representative collision evaluation morphism sends the
  formal-unramified diagonal element to the marked singleton-sheet selector.
  Neither theorem uses compactification purity.
- The exact prime-inertia group `I_Q` used by Stacks Tag `0BST` is now
  formalized.  The local implication from `I_Q <= H` to unramifiedness of the
  selected `H`-fixed branch is proved after the explicitly named
  prime-inertia fixed-ring input.  The proof now descends through the selected
  localizations and requires Dedekind only for the local `H`-fixed ring, not
  for the global fixed ring.  At height one, invariant-theoretic going down
  and normality of the fixed normalization derive that local DVR condition
  over a Noetherian base.  The exact composite endpoint now remains over the
  full invariant ring `S^G`, so it consumes the literal Tag `0BST`-shaped
  premise without silently transporting it to `B`.  Tag `0BST` identifies
  the source input but is not yet a Mathlib theorem; Tag `09EH` supplies only
  the narrower DVR version.
- Centered valuation inertia is formally proved to satisfy `I_val <= I_Q`.
  A separate localization bridge proves the reverse inclusion and hence
  equality over a Noetherian affine base: the finite normal ring localized at
  the supplied height-one center is identified with the centered valuation
  ring.  Without Noetherianity or direct localization data, the reverse
  comparison remains explicit.
- The normalized pull--push operator is formally idempotent from the degree
  relation `push ∘ pull = d · id`. This is a rational linear-algebra theorem,
  not a construction of Chow pushforward and pullback.

## Claims still outside the formal result

- No concrete Chow or bivariant realization instantiates
  `FiniteEtaleAlgebraModel`.
- No extraction of cycle classes or compatibility with refined Chow
  convolution is proved.
- Boundary purity and compactified extension remain supplied interfaces.
- Bijectivity of the normal-closure tensor evaluation morphism is proved under
  `PerfectField K`; it is not required for the weaker selector comparison.
- Equality with a separately prescribed cohomological or Hodge projector is an
  input, not a conclusion.
- No new family of smooth projective varieties or Hodge classes is shown to
  satisfy the Hodge conjecture.

## Recommended public claim

Use a title such as *Finite-etale span projectors and collision decompositions
in Lean*. State the Galois endpoint with “given a finite-etale cover, an
explicit torsor decomposition, and a finite-etale realization model.” Present
the Noether-different theorem as a separate formalized support theorem, not as
evidence that the boundary or Hodge realization is complete.

Queueing should wait for a clean-clone build, exact literature and novelty
checks, author and license metadata, and independent mathematical review.
