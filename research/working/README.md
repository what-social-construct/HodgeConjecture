# Working drafts

Drafts here may be mathematically or bibliographically incomplete. Promote a
draft to `../queue/` only after every claim has an entry in the claim ledger,
every imported mathematical input has an exact source, and the release
checklist passes.

Active research and proof-maintenance queue:

- `0001-finite-etale-projectors.md` is the historical Paper II scope note. Its
  unconditional center is A1--A7 and A9--A11b; A8 is a separately labeled
  conditional torsor/realization corollary, A12/A14/A15 are cited to the
  height-one fixed-ring draft, and C5b appears only as conditional outlook.
  It is retained for provenance alongside the manuscript snapshots in
  `../archive/manuscripts/`; `0006` controls the canonical manuscript.

- `0002-fixed-ring-pruning-parity.md` audits the fixed-ring manuscript against
  the Lean dependency spine and stages the self-contained prime-inertia
  closure without deleting existing declarations.
- `0003-hodge-target-equivalence.md` states the fixed-model and indexed-family
  rational Hodge schemas, records the Tate-block graph-projector equivalence,
  records the marked Galois selector block calculation and conditional
  lower-left/surjective-cancellation endpoint over a noncommutative ambient
  correspondence algebra, and separates those formal implications from the
  still-open geometric extension, residual realization, action square,
  Hodge-compatibility, and coverage instances.
- `0004-boundary-projector-theorem-audit.md` preserves the proposed
  boundary-unramified collision-projector theorem as an open program.  It
  separates the pointwise sheet algebra, group/Hecke convolution, and Chow
  convolution, audits the finite-etale base case, and lists the precise
  Chow, purity, realization, Hodge, and coverage inputs still required.
- `0005-semantic-parity-cleanup.md` records the completed automated
  declaration-pruning and notation pass.  It assigns one TeX symbol to each
  retained semantic object, identifies exact implementation duplicates,
  quarantines superseded interfaces, and keeps the human release gates open.
- `0006-lean-spine-manuscript-outline.md` is implemented by
  `../../paper/main.tex`, producing the single active PDF
  `../../paper/main.pdf`. It replaces the historical two-paper narrative
  with one dependency-ordered manuscript, putting the Hodge target, projector
  constructions, boundary theorem, and realization gap in the main line and
  relegating fixed-ring/source material to appendices.
- `0007-split-point-realization.md` records the first actual split-point scheme
  projector, its separate matrix coefficient calculation, the obstruction to
  restricting a full matrix algebra to sheets, and the formerly missing
  additive cycle realization, now proved in `0008`.
- `0008-split-span-cycle-realization.md` records the actual scheme-span
  coefficient map, its well-definedness on geometric classes, its
  multiplicativity and coproduct laws, and the point projector's
  geometric-source target square. Its genuine Chow/Betti identifications
  are advanced in `0011`--`0013`.
- `0009-split-span-additive-quotient.md` proves the exact finite
  point-decomposition kernel and the quotient-to-matrix algebra equivalence.
- `0010-split-integral-subschemes.md` classifies actual integral closed
  subschemes of finite split schemes and proves the absence of curves.
- `0011-split-zero-cycles.md` constructs zero-cycles on those actual
  subschemes, evaluates rational equivalence using the empty curve type,
  and identifies the resulting additive Chow groups by point coordinates.
- `0012-split-chow-composition.md` computes actual image and fiber
  multiplicities, constructs the cycle/Chow operations, and proves that
  geometric correspondence composition and action have their matrix laws.
  Its actual Chow endomorphism algebra is identified with the existing
  additive split-span quotient, preserving point generators.
- `0013-split-betti-cycle-class.md` constructs the actual complex-point
  topology, singular degree-zero cocycles, and the point-normalized
  cycle-class isomorphism. Pullback, cup product, and finite transfer give
  the cohomological correspondence action and its Chow intertwining.
  Its independent Hodge and Tate-block comparison is advanced in `0014`.
- `0014-split-hodge-tate-block.md` supplies the actual tensor
  complexification and independent effective degree-zero Hodge structure.
  On the actual scheme coproduct with one point, geometric Chow encoding
  and lower-left pullback detection instantiate the graph/Hodge/Palomar
  target interfaces, with the actual Betti action comparison proved.
