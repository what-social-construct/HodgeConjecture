# Projective-line scheme de Rham comparison

Validation completed: 2026-11-06.

The selected next obligation is to connect the existing ordinary
projective-line cycle map to actual scheme de Rham hypercohomology.
Rational singular cohomology and the Betti comparison remain separate.

## Target and construction

The scheme is the original two-chart `projectiveLine k`. The base is a
field for the scheme comparison; no algebraic-closure or characteristic-zero
hypothesis is needed for this comparison itself.

`PresheafComplex.lean` constructs functorial maps on the original Kähler
exterior powers and proves compatibility with the original de Rham
differential. `SheafComplex.lean` uses the actual structural morphism
`X → Spec k` for all scalar actions, restrictions and section algebras.
Degreewise sheafification gives a complex of actual sheaves of `k`-modules.
The differential is base-linear, rather than a morphism of `𝒪_X`-modules.

`SheafHypercohomology.lean` defines derived global sections with Mathlib's
bounded-below right derived functor in the actual Grothendieck abelian
category of fixed-ring sheaves. The complex extends by zero to integer
degrees. Its homology is the scheme target; neither that target nor the
comparison is supplied as a premise. Single-sheaf cohomology and exact
coefficient forgetting agree with the ordinary injective-resolution
right derived functors.

## Affine sections and acyclicity

The actual polynomial chart images cover the original scheme, and their
intersection is the original Laurent open subscheme. Scheme sections have
their original coordinate rings; both actual restriction maps retain the
polynomial-to-Laurent map and the infinity-coordinate inversion.

On a PID spectrum every open is principal. Localization of the actual
Kähler module gives a natural one-form basis on every such open. This
identifies the local one-form presheaf with the actual function sheaf and
proves higher forms vanish. The polynomial and Laurent rings over a field
therefore have proved canonical sheafification-unit isomorphisms. Open
immersion compatibility carries these identities to the original P¹.
These are identifications of sheaves and restrictions, not just dimensions
of their cohomology spaces.

Selected local adaptations of the pinned Axiom standard-cover and
basis-vanishing arguments establish affine quasi-coherent acyclicity.
A localized version applies to natural trivializations below a chosen
affine open in the original ambient category. Fixed-ring injective sheaves
have surjective restrictions by an actual supported-section proof. This
discharges the chart/overlap acyclicity of the P¹ form sheaves without an
assumed affine-vanishing or derived-restriction comparison.

## Degree-two comparison

Every Laurent function is a difference of chart functions. Its differential
is consequently already a difference of chart one-forms. Thus the original
total Čech H² is exactly the cokernel of chart one-form restrictions.

The two-open sequence of sections of an actual injective resolution is
short exact. Its connecting morphism identifies this cokernel with sheaf
`H¹(Ω¹)`, using the proved affine acyclicity. The overlap sign explicitly
retains the original infinity-minus-zero convention.

The higher P¹ form sheaves vanish. The actual two-term short exact sequence
`Ω¹[-1] → Ω• → 𝒪` therefore supplies a distinguished derived triangle.
`H¹(𝒪)=H²(𝒪)=0` follows from the same two-open sequence and the Laurent
function calculation. The derived inclusion of the one-form term then
identifies scheme de Rham H² with `H¹(Ω¹)`.

`schemeComparisonIso` in `ProjectiveLineSchemeComparison.lean` composes these actual
maps. Its overlap formula is fixed by the original representative,
Mayer–Vietoris boundary, and derived inclusion. The resulting scalar
coordinate equivalence and nonzero Chern class follow from the existing
residue calculation; they do not choose an arbitrary comparison between
one-dimensional spaces.

## Ordinary cycle classes and limits

`ProjectiveLineSchemeCycleClass.lean` transports the original ordinary
integral and rational Chow maps into this actual scheme target and proves
the comparison square. Integral classes require an algebraically closed
field; rational classes additionally require characteristic zero. Point
normalization, principal invariance, rationalization, nonzero classes and
the rational coefficient bound retain their original meanings.
The Chern class is the image of the preceding transition-unit construction;
agreement with a separate general geometric Picard/Chern API is not asserted.

No rational singular target, analytic integration comparison, independent
Hodge structure, arbitrary-variety realization or higher-codimension
comparison is asserted here. A future Betti comparison must specify its
Chern-class period normalization. No new Hodge-conjecture case or revised
submission candidate is claimed.

## Build boundaries and validation

`make build-scheme-comparison` and `make check-scheme-comparison` isolate
the new bridge. The existing algebraic, positive-degree and Chow-source
entry points exclude the sheaf-cohomology foundation. There is no external
Axiom/Stacks Lake dependency; the selected proofs and preserved license
are recorded in `third_party/axiom-stacks/README.md`.

The ordinary scheme-cycle entry point passes the 3,693-job focused Make
build. The permanent suite passes 38 examples, its named logarithmic
representative regression, and 58 enforced standard-three axiom audits,
with no warnings. It checks actual sheaf units and restrictions, derived
comparisons, characteristic two, integral/rational point normalization,
the original comparison square and rational coefficient bounds.

The full default build passes 4,578 jobs. Root verification passes 1,350
declaration checks, 574 examples and 1,236 axiom reports, all within
`propext`, `Classical.choice` and `Quot.sound` (one report needs no axioms).
All 460 library modules plus the root pass proof-token and external-import
scanning. All ten import boundaries, three indirect-negative checks,
dependency pins, local documentation links and whitespace checks pass.
Job counts include cached dependencies; the root inventory retains its
92 existing warnings. The main README remains 69 lines. Submission
selection and independent comparator replay remain separate.
