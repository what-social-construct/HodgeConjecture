# Collision Decompositions and Correspondence Projector Lifting

A Lean development toward constructing algebraic cycles representing rational
Hodge classes on smooth projective complex varieties. The current work starts
with actual Chow groups and their cycle maps; correspondences, collision
geometry, and boundary inertia provide supporting construction tools.

**Current status:** proved mechanisms include finite split Chow/Betti/Hodge
comparison and ordinary projective-line cycle classes in scheme de Rham `H²`.
General Betti realization and prescribed-class generation remain open.
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

- Scheme-theoretic cycles, principal relations, integral and rational Chow
  groups, open localization, finite pushforward with composition laws, and
  finite flat Chow pullback with its geometric rank degree law.
- Scheme correspondences, actual graph-generated Chow convolution, finite-group
  projectors, and conditional extension/descent results.
- A concrete finite split Chow/Betti/Hodge model, including correspondence
  actions and the marked-projector comparison.
- Conditional generation and boundary-correction theorems using explicitly
  supplied geometric cycles and realization comparisons.

The next geometric obligations are general Betti/purity comparisons and a
construction covering each independently prescribed Hodge class. The
[Axiom Stacks reuse audit](research/working/0019-axiom-stacks-reuse-audit.md)
identifies useful upstream proofs and the comparisons needed to reuse them.

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
