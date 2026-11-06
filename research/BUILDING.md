# Focused builds and checks

Use the smallest entry point that covers the change. Lake builds that module
and its dependencies, using the same pinned toolchain and manifest as the full
repository. Existing build artifacts are reused.

| Work area | Build | Build, examples and axiom checks |
| --- | --- | --- |
| Generic linear transfer | `make build-transfer` | Included in the de Rham core checks |
| Affine de Rham complex and algebra trace | `make build-derham-core` | `make check-derham-core` |
| Polynomial closed functions and affine-component basis | `make build-derham-components` | `make check-derham-components` |
| Complex affine-line topology and degree-zero Betti comparison | `make build-affine-line-comparison` | `make check-affine-line-comparison` |
| Finite flat cycles and Chow transfer | `make build-chow` | `make check-chow` |
| Graph-generated Chow convolution and absolute products | `make build-graph-chow` | `make check-graph-chow` |
| Positive-degree forms and ordinary projective-line cycle classes | `make build-positive-degree` | `make check-positive-degree` |
| Projective-line scheme de Rham comparison and ordinary cycle classes | `make build-scheme-comparison` | `make check-scheme-comparison` |
| Actual P¹ complex topology and all-degree singular cochains | `make build-projective-line-betti` | `make check-projective-line-betti` |
| Analytic Laurent integrals, scheme periods and ordinary cycle normalization | `make build-projective-line-periods` | `make check-projective-line-periods` |
| Existing singular Betti realization | `make build-betti` | Covered by comparison and integration checks |
| De Rham/geometric degree and Chow–Betti squares | `make build-comparison` | `make check-comparison` |
| Complete library and public imports | `make build` | `make check-integration` |

`make help` lists the commands. `make check` runs all eleven verification groups
and checks the import boundaries. Make runs the groups sequentially; Lake
retains its own build parallelism. A failed command stops the checks.

Direct Lake targets also work:

```sh
lake build HodgeConjecture.Realization.DeRham.Core
lake build HodgeConjecture.Realization.DeRham.AffineComponents
lake build HodgeConjecture.Realization.DeRham.AffineLineComparison
lake build HodgeConjecture.Realization.Chow.FiniteFlatTransfer
lake build HodgeConjecture.Correspondence.GraphChowBaseComparison
lake build HodgeConjecture.Realization.DeRham.PositiveDegree
lake build HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass
lake build HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison
lake build HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass
lake build HodgeConjecture.Realization.Betti.ProjectiveLine
lake build HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods
lake build HodgeConjecture.Realization.Betti
lake build HodgeConjecture.Realization.DeRham
```

The generic `RationalDegreeTransfer` definitions and proofs live in
`Realization.Transfer`, which imports no project geometry or realization
models. `Chow.TransferProjector` re-exports that API and adds the existing
cohomological-projector conversion, preserving its original declaration names.

The de Rham core has six project modules in its import closure. Its algebraic
checks import `Realization.DeRham.Core`; comparison checks import the de Rham
umbrella. The finite flat Chow checks import their transfer entry point.
The large `Verification.lean` inventory retains the root import to check
integration and public exports.

The polynomial/component target has five project modules and imports neither
the algebra-trace layer nor project geometry. Its seven regression examples
include the affine plane, distinct and empty components, and a nonconstant
closed polynomial in characteristic two. It has its own enforced axiom audits.

The affine-line comparison target has eight project modules. It imports the
actual point topology and singular cocycles, while excluding project cycles,
Chow, correspondences and boundary geometry. Its standalone suite checks
connected and disconnected examples, noncocycles, complex tensor coefficients
and nonlinear/constant polynomial pullbacks.

The graph-Chow target has 151 project modules and builds the actual Chow quotient, graph actions,
graph-generated convolution algebra and relative-to-absolute pushforward.
It excludes project collision schemes and all project realization modules.
Its dimension-function construction retains the normalization algebra it
actually uses; it has no dependency on Betti or de Rham comparison.

The algebraic positive-degree entry point has 18 project modules. It includes the actual
projective-line cover, logarithmic forms, quotient cup product and nonzero
Čech first-Chern class. It excludes project Betti/Chow realization,
correspondence and boundary machinery. The build command also builds the
separate ordinary projective-line cycle-class entry point. That target uses
112 project modules: the actual Chow quotient, grading and normalization algebra, while excluding
Betti, the old assumed Chow-realization layer and graph-Chow convolution.
Its actual principal-divisor degree theorem discharges relation invariance.

The pure scheme-comparison target has 50 project modules. It constructs the
actual sheaf complex, derived sections and the P¹ Čech comparison while
excluding project cycles, Chow realization, correspondences, collision
geometry and Betti. The separate ordinary-source target has 150 project
modules and composes that bridge with the original Chow maps.
`make build-scheme-comparison` builds this latter entry point;
`make check-scheme-comparison` also runs `SchemeComparisonVerification.lean`.
The [scheme checkpoint](working/0027-projective-line-scheme-comparison.md)
records the scope and completed integration validation.

The Betti-input target keeps actual complex-point topology and all-degree
singular cochains separate from de Rham. Its checks include the new H⁰
bridge and actual chart inversion at infinity. The analytic Laurent period
target has three project modules and excludes scheme geometry and sheaf
cohomology. Its integration into P¹ scheme H² is a separate target;
the algebraic positive-degree and scheme entry points exclude both new
period modules. These inputs do not compute P¹'s singular H² or establish
a Betti comparison. See [0028](working/0028-projective-line-betti-inputs.md).

`make check-layers` enforces twelve transitive project-import boundaries:

- The de Rham core excludes scheme cycles, Chow, Betti and comparison modules.
- Polynomial/component calculations have the same exclusions as the core.
- Affine-line comparison excludes project cycles, Chow, correspondences and boundary geometry.
- Finite flat Chow transfer excludes Betti and de Rham realization.
- Betti realization excludes de Rham realization.
- Graph Chow convolution excludes collision geometry and project realization.
- Positive-degree algebraic realization excludes Betti, existing Chow realization and boundary/correspondence machinery.
- Ordinary projective-line cycle classes exclude Betti, the assumed Chow-realization layer, collision geometry and graph-Chow convolution.
- Pure projective-line scheme comparison excludes project cycles, Chow realization, correspondences, collision geometry and Betti.
- Ordinary projective-line scheme cycle classes exclude Betti, the assumed Chow-realization layer, collision geometry and graph-Chow convolution.
- All-degree singular cochains exclude project geometry, cycles, correspondences, Chow, de Rham and sheaf cohomology.
- Analytic Laurent periods exclude project geometry, cycles, correspondences, Chow, Betti and sheaf cohomology.

The existing core, polynomial/component, affine-line, positive-degree and
ordinary Čech cycle-class entry points also exclude the new sheaf-cohomology
foundation. Import-closure counts above are read from source by
`scripts/check_layers.py`; they are not build-job or verification counts.

This remains one Lake package and one dependency lockfile. A smaller target
still builds all of its actual dependencies: the upstream general Stacks
de Rham trace would still require its roughly 4,000-module dependency chain.
There is no Axiom/Stacks package import in this repository: selected proofs
are adapted locally, with citations and the upstream license retained.
Irrelevant arithmetic and analysis imports inherited in the selected sheaf
restriction helper were pruned from the local adaptation.
The selective affine adaptation avoids that dependency; it does not establish
the general scheme trace or general positive-dimensional Betti comparison.

Run the focused checks while editing, then run `make check-integration` at
integration checkpoints. The [release checklist](RELEASE_CHECKLIST.md) records
additional release requirements; these commands do not replace human review
or clean-clone validation.

For the current Palomar candidate, `make build-palomar` builds only Challenge
and Solution. `make check-palomar-proofs` checks their theorem types and
Solution axioms in separate Lean environments. `make check-palomar` runs a
static preparation scan and exits nonzero while packaging issues remain;
it is deliberately separate from ordinary development checks. Independent
Comparator replay needs a Linux runner. The [handoff](working/PALOMAR_FIXED_RING_HANDOFF.md)
records current results, limits and unresolved submission choices.
