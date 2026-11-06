# Current records and dated checkpoints

Drafts here may be mathematically or bibliographically incomplete. Promote a
draft to `../queue/` only after every claim has an entry in the claim ledger,
every imported mathematical input has an exact source, and the release
checklist passes.

## Current authority

Start with [the target bridge](../TARGET_BRIDGE.md). Use `../GAP_MAP.md`
for the detailed mathematical gap, `../CLAIM_LEDGER.md`
for exact theorem scope, and the single `../../paper/main.tex` for the
manuscript. Do not combine old checkpoint descriptions into a proof plan.

- `0005-semantic-parity-cleanup.md` is the canonical pruning and notation
  registry; deferred compatibility and human review gates remain explicit.
- `0017-proof-spine-and-archive.md` records the checked declaration
  dependencies, physical archival, and the supporting role of the retained
  block/coordinate calculations. It is an audit, not a new Hodge proof.
- `0018-geometric-pair-input-audit.md` records the missing actual normalized
  cover, a deleted-ramification boundary model, and standalone algebraic
  controls for choosing a regular pair. It separates the available criteria
  from the next geometric design choice; the manuscript is unchanged.
- `0019-axiom-stacks-reuse-audit.md` compares the pinned Axiom Stacks release
  with the current cycle/Chow and normalization objects. It identifies flat
  pullback/degree and fixed inertia as reuse candidates, records overlap worth
  retaining and toolchain/import costs, and leaves compiled gap statuses intact.
- [0020-lean-4-35-migration.md](0020-lean-4-35-migration.md) records the current
  toolchain port, bounded finite-fiber backport, and validation scope.
- [0023-polynomial-derham-components.md](0023-polynomial-derham-components.md)
  records degree-zero polynomial invariance and the affine-component basis.
- [0024-affine-line-betti-comparison.md](0024-affine-line-betti-comparison.md)
  records actual complex points, the path/cocycle calculation and degree-zero
  comparison for the complex affine line.
- [0025-graph-chow-convolution.md](0025-graph-chow-convolution.md) records the
  resumed marked-Galois spine, actual graph Chow algebra and absolute-product
  comparison, keeping prescribed realization and class coverage open.
- `PALOMAR_FIXED_RING_HANDOFF.md` records the separate submission boundary.
- [0026-positive-degree-cycle-realization.md](0026-positive-degree-cycle-realization.md)
  records actual positive-degree cohomology, the nonzero ordinary Čech
  first-Chern construction and its original ordinary Chow-source map.
- [0027-projective-line-scheme-comparison.md](0027-projective-line-scheme-comparison.md)
  records actual sheaf forms, affine acyclicity and the derived P¹ comparison,
  with a separate ordinary Chow-source entry point and completed integration
  validation. Betti and general-variety comparisons remain open.
- [0028-projective-line-betti-inputs.md](0028-projective-line-betti-inputs.md)
  records actual P¹ complex topology, all-degree rational singular cochains
  and analytic scheme periods, with the singular H² comparison still open.
- [0029-small-singular-chains.md](0029-small-singular-chains.md) records actual
  barycentric subdivision, its local homotopy, finite-chain shrinking and
  the two-open small-chain comparison. Its full singular cohomology
  comparison is completed by 0031 below.
- [0030-hodge-derham-degeneration-audit.md](0030-hodge-derham-degeneration-audit.md)
  audits the missing general characteristic-zero degeneration theorem and
  the explicit premises of upstream reductions; no submission copy is made.
- [0031-singular-cohomology-mayer-vietoris.md](0031-singular-cohomology-mayer-vietoris.md)
  records exact rational dualization, the full/small cochain comparison and
  full singular Mayer–Vietoris with original continuous inclusion maps.
- `../bench/` holds the standalone matrix-restriction diagnostic outside
  active imports; this is not an obstruction in the intended target route.

## Dated proof checkpoints

The entries below document work at their stated dates. Later checkpoints
advance earlier ones; the current gap and claim ledgers take precedence.

- `0016-source-input-packages.md` separates the fixed-inertia premise,
  actual finite étale extension and automorphism restriction inputs, and
  rational-linear Chow exactness. It records their explicit conditional
  consumers, boundary-image defect theorem, and unchanged Palomar wrappers.

- `0015-split-galois-marked-comparison.md` records the actual split torsor
  and homogeneous sheet cover, the multiplicative residual Chow equivalence,
  actual diagonal embedding and Chow shear, and their marked Betti/Palomar
  comparison for the negative fundamental class. It separates that fixed
  class from class-dependent coverage using multiplicative residual rigidity.

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
  Its canonical marked-sheet residual/action bridge is advanced in `0015`.

## Archived plans

The old Paper II plan and companion review (`0001`), fixed-ring pruning plan
(`0002`), target plan (`0003`), boundary-program audit (`0004`), and unified
outline (`0006`) are preserved in
[`../archive/planning/`](../archive/planning/README.md). Their superseded
status statements and old relative links are historical, not current
instructions. Six retired Lean modules are separately preserved in
[`../archive/legacy-lean/`](../archive/legacy-lean/README.md).
