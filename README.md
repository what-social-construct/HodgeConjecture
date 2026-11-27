# Collision Decompositions and Correspondence Projector Lifting

A Lean development toward constructing algebraic cycles representing rational
Hodge classes on smooth projective complex varieties. The current work starts
with actual Chow groups and their cycle maps; correspondences, collision
geometry, and boundary inertia provide supporting construction tools.

**Current status:** proved mechanisms include finite split Chow/Betti/Hodge
comparison, a P¹ Hodge-cycle model, and an oriented zero-point Gysin/cycle comparison.
The two zero fibers form a basis of the actual rational degree-one Chow group
of P¹ × P¹, and their supported Gysin classes form a basis of its rational
singular H². The resulting fiber-normalized Chow-to-Betti map is an
isomorphism for this product. General divisor cycle maps and naturality
remain open.
General Betti comparison and prescribed-class generation remain open.
No new case of the Hodge conjecture is claimed.

## Start here

- [Target and proof strategy](research/TARGET_BRIDGE.md): the intended
  statement, existing equivalence bridge, and current work order.
- [Current gaps](research/GAP_MAP.md): the missing geometric constructions
  and comparisons.
- [Claim ledger](research/CLAIM_LEDGER.md): exact proved statements and
  hypotheses.
- [Implementation reference](research/IMPLEMENTATION_REFERENCE.md): the
  detailed module and theorem inventory formerly in this README.

## What is implemented

- Scheme cycles, Chow groups, localization, finite pushforward and finite flat
  pullback, with graph correspondences and finite-group projectors.
- A finite split Chow/Betti/Hodge model, a degree-normalized P¹ Chow map
  with point Gysin factorization, and conditional generation and
  boundary-correction theorems.
- The actual P¹ × P¹ complex-point topology and rational singular
  degree-two basis, proved through two-chart Mayer–Vietoris calculations;
  actual codimension-one fiber Chow basis and its normalized Betti realization.
- Canonical complex points of schemes, a smooth analytic atlas, intrinsic
  holomorphic forms, and an all-degree local holomorphic Poincaré comparison.
- Rational and complex singular-cochain sheaves, open-cover comparisons,
  flasque resolutions, and comparison with derived constant-sheaf cohomology
  under the stated topology hypotheses.
- The [finite-point Gysin family](research/working/0066-projective-line-finite-point-gysin.md)
  constructs actual supported and absolute maps at every finite P¹ point,
  independently of the nonzero affine complex normal-coordinate scale.
  Actual scheme charts, native affine homotopy and original ordinary point
  cycles give certificates retaining the same full Hodge target.
- The [ramified Gysin comparison](research/working/0065-projective-line-ramification-comparison.md)
  computes local relative Thom pullback and carries it through the original
  normal chart and excision. The same actual scheme-fiber multiplicity weights
  the original zero cycle and supplies a certificate for the unchanged full Hodge target.
- The [connected branched P¹ square cover](research/working/0064-projective-line-square-cover.md)
  has geometric degree two and actual branch multiplicity two. Its native H²
  pullback is computed independently of Chow; a trace through the singleton
  zero support and the existing point-Gysin isomorphism gives the degree-two
  aggregate with the original full Hodge target. General branched trace remains open.
- The [split double cover of P¹](research/working/0063-projective-line-split-double-cover.md)
  has transfer on native singular cochains, original ordinary Chow
  pull–push comparisons in H², and an accepted full-target aggregate.
- An [actual geometric cover aggregate](research/working/0062-geometric-cover-coverage.md)
  uses the degree-two finite étale cover from four complex points to two,
  with original ordinary Chow maps, native singular H⁰ comparisons,
  and coverage of the full two-dimensional Hodge target.
- [Galois descent and harmonic transport](research/working/0061-galois-harmonic-coverage.md)
  supply coefficient-invariance and faithful transport proof gates, with
  accepted P¹ aggregates over the degree-two coefficient extension ℚ(i).
- An [exact aggregate coverage certificate](research/working/0060-finite-coverage-certificate.md)
  binds actual cycle images to a complete rational Hodge basis and certifies
  spanning by a modular inverse, with an accepted geometric P¹ instance.
- Finite cellular harmonic class certificates and an upstairs-descent adapter.
  The [original-cover P¹ comparison](research/working/0059-finite-cover-harmonic-comparison.md)
  computes actual Betti H², preserves the ordinary Chow map, and transports
  the existing geometric Hodge filtration.
- A complex Betti-to-holomorphic map that detects rational classes. On P¹ in
  degree two the original map is an isomorphism; general invertibility and
  equality with the separate cochain-induced map remain open.

The next geometric obligations are general Betti/purity comparisons and a
construction covering each independently prescribed Hodge class. Selected
proof adaptations cite [Axiom Stacks](third_party/axiom-stacks/README.md) and
[Axiom Weil](third_party/axiom-weil/README.md) at pinned revisions; the
[reuse audit](research/working/0019-axiom-stacks-reuse-audit.md) records the
remaining comparisons.

## Build

Lean **4.35.0** and matching Mathlib are pinned in [lean-toolchain](lean-toolchain),
[lakefile.lean](lakefile.lean), and [lake-manifest.json](lake-manifest.json).
From the repository root:

```sh
lake build
lake env lean research/Verification.lean
```

Use [granular checks](research/BUILDING.md) for focused work; the
[release checklist](research/RELEASE_CHECKLIST.md) records validation scope.

## Repository guide

| Path | Contents |
| --- | --- |
| [HodgeConjecture/](HodgeConjecture/) | Active Lean library |
| [Challenge.lean](Challenge.lean), [Solution.lean](Solution.lean) | Two fixed-ring comparator statements and proofs |
| [research/](research/) | Current ledgers, source audit, verification files, and dated records |
| [paper/main.tex](paper/main.tex) | Single active manuscript |
| [research/archive/](research/archive/) | Historical sources and plans |
| [research/bench/](research/bench/) | Standalone diagnostics outside the active proof path |

Use the current ledgers for proof status; dated checkpoints and archived
plans record their own scope. The
[semantic parity registry](research/working/0005-semantic-parity-cleanup.md#proof-role-index-core-objects-and-objects-under-investigation)
tracks the role of each major object and its Lean/LaTeX representation.
