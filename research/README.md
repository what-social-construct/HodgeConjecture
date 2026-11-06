# Research workspace

Use these documents in order:

1. [TARGET_BRIDGE.md](TARGET_BRIDGE.md): intended target and current proof strategy.
2. [GAP_MAP.md](GAP_MAP.md): missing constructions and component evidence.
3. [CLAIM_LEDGER.md](CLAIM_LEDGER.md): exact theorem scope and hypotheses.
4. [SOURCE_LEDGER.md](SOURCE_LEDGER.md): external mathematical inputs and source status.
5. [IMPLEMENTATION_REFERENCE.md](IMPLEMENTATION_REFERENCE.md): detailed module inventory.
6. [RELEASE_CHECKLIST.md](RELEASE_CHECKLIST.md): validation requirements and recorded checks.

The [semantic parity registry](working/0005-semantic-parity-cleanup.md#proof-role-index-core-objects-and-objects-under-investigation)
tracks core target/Chow objects, candidate-route objects, and their Lean/LaTeX
representations. The [Axiom Stacks audit](working/0019-axiom-stacks-reuse-audit.md)
compares upstream objects and proof costs with this library.
The [finite flat Chow checkpoint](working/0021-finite-flat-chow-transfer.md)
records the implemented pullback, rank comparison and positive-degree transfer.
The [affine de Rham checkpoint](working/0022-affine-derham-trace-comparison.md)
records the constructed complex and bounded trace/comparison case.
The [polynomial/component checkpoint](working/0023-polynomial-derham-components.md)
records polynomial invariance in degree zero and the affine-line component basis.
The [affine-line comparison](working/0024-affine-line-betti-comparison.md)
connects that kernel to genuine complexified rational singular cohomology.
The [graph-Chow checkpoint](working/0025-graph-chow-convolution.md) resumes the
marked-Galois spine with actual graph-generated Chow convolution.
The [positive-degree construction](working/0026-positive-degree-cycle-realization.md)
builds the ordinary Čech first-Chern map and an actual ordinary Chow-source
cycle map on the projective line.
The [scheme comparison checkpoint](working/0027-projective-line-scheme-comparison.md)
connects that target to actual sheaf de Rham hypercohomology on the same P¹;
integration validation passes, and the singular comparison remains open.
[Focused build commands](BUILDING.md) separate the algebraic core, Chow,
scheme comparison, Betti and integration checks.

The current library includes finite cycle/Chow pushforward composition,
finite flat Chow pullback and degree, an actual affine de Rham complex and
degree-zero split comparison, actual Chow localization, marked
cycle maps, and conditional supported-class
and boundary-correction consumers. General flat pullback beyond the finite case,
Betti/purity comparisons, and prescribed-class generation remain open.
Exact statements and checks belong in the ledgers, rather than this index.

## Working material

- `inbox/`: exploratory material.
- `working/`: dated checkpoints and focused investigations.
- `queue/`: frozen publication candidates after the release checks pass.
- [bench/](bench/README.md): retained standalone diagnostics outside active imports.
- [archive/](archive/): retired Lean sources, manuscripts, and planning history.
- `*Verification.lean`: executable declaration, example, and axiom checks;
  run from the repository root with `lake env lean research/<file>.lean`.

Keep the current endpoint in `GAP_MAP.md`, theorem claims in
`CLAIM_LEDGER.md`, and external inputs in `SOURCE_LEDGER.md`. Dated records
preserve their original validation scope and do not replace the live work order.

The single active manuscript is [../paper/main.tex](../paper/main.tex).
Queued work must distinguish unconditional theorems, results with explicit
hypotheses, and formalization reports about known mathematics. A claim about
the Hodge conjecture must construct an algebraic cycle for an independently
specified Hodge class without assuming the required realization or algebraicity.
