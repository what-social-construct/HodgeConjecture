# Focused builds and checks

Use the smallest entry point that covers the change. Lake builds that module
and its dependencies, using the same pinned toolchain and manifest as the full
repository. Existing build artifacts are reused.

| Work area | Build | Build, examples and axiom checks |
| --- | --- | --- |
| Galois coefficient descent, harmonic naturality and actual P¹ aggregates | `make build-galois-harmonic-coverage` | `make check-galois-harmonic-coverage` |
| Fixed-target aggregate coverage and modular rank certificates | `make build-finite-coverage` | `make check-finite-coverage` |
| Original circle/P¹ covers, finite harmonic model and geometric Hodge filtration | `make build-cover-harmonic-comparison` | `make check-cover-harmonic-comparison` |
| Finite harmonic certificates, upstairs descent and product coordinates | `make build-harmonic-witness` | `make check-harmonic-witness` |
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
| Rational singular subdivision and two-open small-chain comparison | `make build-small-chains` | `make check-small-chains` |
| Exact rational dualization and full singular Mayer–Vietoris | `make build-singular-cohomology` | `make check-singular-cohomology` |
| Actual circle singular H¹ and its cover generator | `make build-circle-cohomology` | `make check-circle-cohomology` |
| Actual projective-line singular H² and its cover generator | `make build-projective-line-cohomology` | `make check-projective-line-cohomology` |
| Actual P¹ × P¹ topology and singular H² basis | `make build-projective-line-product` | `make check-projective-line-product` |
| Codimension-one product fiber Chow classes and supported Betti classes | `make build-projective-line-product-fibers` | `make check-projective-line-product-fibers` |
| Actual positive circle cycle and original generator pairing | `make build-circle-orientation` | `make check-circle-orientation` |
| Actual P¹ boundary periods, tensor extension and ordinary Chow square | `make build-projective-line-period-comparison` | `make check-projective-line-period-comparison` |
| Actual derived Hodge filtration and P¹ H² calculation | `make build-hodge-filtration` | `make check-hodge-filtration` |
| Geometric type (1,1) and the fixed P¹ Hodge-cycle model | `make build-projective-line-hodge` | `make check-projective-line-hodge` |
| General filtered rational target and explicit scheme comparison adapter | `make build-filtered-hodge-target` | `make check-filtered-hodge-target` |
| Cyclic filtered detector of the existing projector defect | `make build-filtered-projector-defect` | `make check-filtered-projector-defect` |
| Proved Tate/Hodge compatibility and existing target equivalence | `make build-tate-hodge-bridge` | `make check-tate-hodge-bridge` |
| Canonical scheme complex points, Betti functor and existing P¹ comparison | `make build-scheme-betti` | `make check-scheme-betti` |
| Holomorphic sheaf complex, radial primitives and all-degree local Poincaré comparison | `make build-holomorphic-derham` | `make check-holomorphic-derham` |
| Canonical analytic atlas, actual regular evaluations and analytic scheme maps | `make build-analytic-charts` | `make check-analytic-charts` |
| Intrinsic atlas forms sheaf, descended d and all-degree algebraic map | `make build-holomorphic-descent` | `make check-holomorphic-descent` |
| Intrinsic chart identifications and full constant-sheaf Poincaré comparison | `make build-intrinsic-poincare` | `make check-intrinsic-poincare` |
| Original singular cochains and local rational constant-sheaf resolution | `make build-singular-sheaves` | `make check-singular-sheaves` |
| Arbitrary open-cover chain/cochain comparison and acyclic vanishing kernel | `make build-open-cover-small-chains` | `make check-open-cover-small-chains` |
| Actual global sheafification kernel, locally zero cochains and native acyclicity | `make build-sheafification-kernel` | `make check-sheafification-kernel` |
| Original global unit surjectivity and quasi-isomorphism on paracompact Hausdorff spaces | `make build-global-singular-sheaves` | `make check-global-singular-sheaves` |
| Original open-subspace section lifts and native flasque singular cochain sheaves | `make build-open-singular-sheaves` | `make check-open-singular-sheaves` |
| Positive derived sections of original flasque sheaves, on every open | `make build-flasque-derived` | `make check-flasque-derived` |
| Original whole-complex underived-to-derived comparison for flasque sheaf complexes | `make build-singular-derived-comparison` | `make check-singular-derived-comparison` |
| Original rational singular groups and actual derived constant-sheaf cohomology | `make build-singular-constant-comparison` | `make check-singular-constant-comparison` |
| Complex coefficient comparison and actual holomorphic derived target | `make build-analytic-betti-comparison` | `make check-analytic-betti-comparison` |
| Finite-cohomology scalar change on the original singular cochains | `make build-singular-coefficient-change` | `make check-singular-coefficient-change` |
| Complex singular/derived comparison and the original canonical P¹ holomorphic isomorphism | `make build-complex-singular-comparison` | `make check-complex-singular-comparison` |
| Actual relative cochains, excision and boundary sign | `make build-relative-cohomology` | `make check-relative-cohomology` |
| Oriented P¹ zero-point Gysin and original cycle comparison | `make build-projective-line-point-gysin` | `make check-projective-line-point-gysin` |
| DVR fixed-inertia étaleness and the local unramifiedness consumer | `make build-fixed-inertia` | `make check-fixed-inertia` |
| Existing singular Betti realization | `make build-betti` | Covered by comparison and integration checks |
| De Rham/geometric degree and Chow–Betti squares | `make build-comparison` | `make check-comparison` |
| Complete library and public imports | `make build` | `make check-integration` |

`make help` lists the commands. `make check` runs the verification groups above
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
lake build HodgeConjecture.Realization.Betti.SmallChains
lake build HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
lake build HodgeConjecture.Realization.Betti.Circle
lake build HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
lake build HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing
lake build HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison
lake build HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration
lake build HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass
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

The small-chain target has 23 project modules and constructs actual subset simplicial subcomplexes,
native singular chain coordinates, barycentric subdivision and its local
homotopy, uniform finite-chain shrinking and the two-open homology
comparison. Its cochain gluing sequence retains the small union as its
first term; the singular-cohomology target below supplies its full-cochain
comparison. The P¹ group calculation is a separate obligation. It excludes project geometry, cycles, Chow,
correspondences, de Rham and sheaf cohomology. See
[0029](working/0029-small-singular-chains.md).
Its check target separately builds the actual P¹ chart topology for the
cover regression; the pure library entry point retains those exclusions.

The singular-cohomology target has 27 project modules. It adds exact
unrestricted dualization, the canonical full/small cochain comparison and
full singular Mayer–Vietoris with original continuous maps. Its four
suites include infinite-dimensional duals, differential signs, empty-cover
cases and the actual P¹ chart cover. The check target builds that chart
topology separately. The pure library entry point has the same exclusions
as the small-chain target. See
[0031](working/0031-singular-cohomology-mayer-vietoris.md).

The circle entry point has 36 project modules, including its umbrella.
Its three suites check actual homotopy invariance, contractible-space
vanishing, original circle-chart homeomorphisms and components, and the
actual Mayer–Vietoris H¹ boundary quotient. It excludes project geometry,
cycles, Chow, correspondences, de Rham and sheaf cohomology.

The separate P¹ singular H² entry point has 52 project modules. It includes
the original scheme and complex-point geometry, including its foundational
finite-type dimension dependency. It excludes Chow realization,
correspondences, de Rham and sheaf cohomology. Its three suites check the
actual affine charts, radial homotopy, original connecting isomorphism and
nonzero rational generator of actual H². The original Betti-input target
remains separate. See
[0032](working/0032-circle-projective-line-singular-cohomology.md).

The positive-circle entry point has 40 project modules and keeps the same
pure singular exclusions. Its four suites check native connecting
representatives, actual closed-chain pairing and Stokes, literal positive
arc simplices, and generator pairing +1. The cycle is also proved to have
no native filling two-chain.

The separate actual P¹ tensor target has 59 project modules. The independent
ordinary Betti cycle map has 143, including the existing Chow degree and
normalization/finite-group projector foundation; it excludes de Rham,
sheaf cohomology, Chow realization, collision geometry and graph-Chow
consumers. Analytic positive arc integration has four project modules and
keeps the pure Laurent-period exclusions. The final boundary-period
comparison has 205 project modules, intentionally combining actual scheme
de Rham, singular cohomology, analytic integration and ordinary Chow maps.
Its check target runs the independent ordinary-cycle suite, analytic-arc
suite and final actual period/tensor square suite. See
[0033](working/0033-oriented-boundary-period-comparison.md).

The native degree-filtration layer has one project module and imports no
other project source. The generic scheme image filtration has 11 modules;
the actual P¹ H² filtration has 55. It excludes project cycles, Chow,
Betti, correspondences and collision geometry. Its checks distinguish
brutal from smart truncation and test the actual nonzero Chern filtration
degree over ℚ and characteristic two. The check target explicitly builds
the native complex and finite-field instances used by these standalone
regressions.

The independent Betti Hodge structure has 60 project modules, with no
cycle-map, Chow realization or de Rham imports. The filtered comparison has
212 modules and the final fixed-codimension model has 214, intentionally
combining the original scheme, period, Betti and ordinary Chow constructions.
Its focused checks cover rational tensor conjugation, all integer filtration
levels, geometric type recovery and explicit infinity-class witnesses. See
[0034](working/0034-projective-line-hodge-filtration.md).

The relative-cohomology target builds actual pair kernels, strict union
gluing, open-cover excision and the positive native boundary comparison.
Its check target also builds the pure circle endpoint for an actual
nonzero sign regression. The zero-point Gysin target combines the oriented
local complex pair, original projective-line chart and scheme support,
inverse excision and forgetting. Its focused suites check local absolute
vanishing, global nonvanishing, positive sign and both original Chow maps.
Neither target imports de Rham. See
[0035](working/0035-projective-line-zero-point-gysin.md).
The relative-boundary entry point has 32 project modules and the local
complex Thom class has 43. The original chart-boundary comparison has 62;
the geometric point Gysin has 67. The final ordinary-cycle comparison has
159, adding the independent actual Chow branch only at that endpoint.

`make check-layers` enforces thirty-seven transitive project-import boundaries:

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
- Small-chain subdivision and cover comparison have the same exclusions.
- Exact rational dualization and full singular Mayer–Vietoris have the same exclusions.
- The circle H¹ calculation has the same exclusions.
- The original P¹ connecting calculation excludes Chow realization, correspondences, de Rham and sheaf cohomology.
- The final P¹ H² entry point has those same exclusions.
- Analytic Laurent periods exclude project geometry, cycles, correspondences, Chow, Betti and sheaf cohomology.
- The actual positive-circle pairing has the pure singular exclusions.
- P¹ positive boundary orientation and genuine tensor extension each have the P¹ singular exclusions.
- The independent P¹ Betti cycle map excludes de Rham, sheaf cohomology, Chow realization, collision and graph-Chow consumers.
- Analytic positive arc integration has the pure Laurent-period exclusions.
- The native degree-filtration layer excludes project geometry, cycles, boundary, correspondences, sheaf/derived consumers and other realization layers.
- The generic scheme filtration excludes project geometry, cycles, Chow, Betti and correspondence/collision machinery.
- The actual P¹ H² filtration has the pure scheme-comparison exclusions.
- The independent Betti Hodge decomposition excludes cycle-map modules, Chow realization, de Rham, sheaf cohomology and correspondences.
- Relative kernel cochains, short-exact quasi-isomorphism comparison, relative union, excision and boundary comparison have the pure singular exclusions.
- The local complex Thom class has the pure singular exclusions.
- The original point support and normal-chart comparisons have the P¹ singular exclusions.
- The geometric zero-point Gysin additionally excludes both ordinary Betti cycle-map modules.
- The final zero-point Gysin/cycle comparison has the existing independent Betti cycle-map exclusions.

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
