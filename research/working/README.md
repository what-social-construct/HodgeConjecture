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
  restricting a full matrix algebra to sheets, and the still-missing additive
  cycle realization between these two formal layers.
