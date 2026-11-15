# The existing global singular sheafification comparison

Date: 2026-11-09.

This completes the global-unit surjectivity step following
[0047](0047-global-sheafification-kernel.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). On every paracompact Hausdorff
space, the existing `SingularCochains.globalCochainsToSheaf` is surjective
in every degree and is a quasi-isomorphism. Its target is the ordinary
global sections of the existing singular sheaf complex, taken term by
term. Comparison with derived global sections still requires sheaf-term
acyclicity.

## Actual representatives and patching

`SheafCohomology.SheafifyLocalLifts` reuses the existing native unit and
`LocalExactness.sheafifyStalkIso`. Mathlib's stalkwise local-surjectivity
criterion supplies an actual presheaf section representing any sheafified
section on a smaller open neighborhood. The same stalk isomorphism and
original germ equality detect local equality of original sections.
Neither statement assumes a separation or compactness condition.

`SingularCochainPatching.openExtension` applies the existing
`RelativeCochains.extension` to the original subset/subspace simplex
identification. Extension is a right inverse to the original open
pullback. Thus every local representative extends to an original global
cochain, still representing the given sheaf section on that open.

For a genuine open cover of a paracompact Hausdorff space, Mathlib's
`precise_refinement` and `exists_iUnion_eq_closed_subset` supply a locally
finite closed refinement subordinate to that cover. This uses the proved
normality of paracompact Hausdorff spaces. At each point only finitely
many of these closed sets contain it. A neighborhood avoids all the
others by `LocallyFinite.iInter_compl_mem_nhds`.

`exists_cochain_locally_eq_of_closed_cover` patches the original cochain
functions. On each original simplex, choose an index whose closed set
contains a fixed actual point of that simplex, and use that index's
original cochain value. No nonempty index type is assumed globally; the
point of a supplied simplex provides the required local choice. Around
each space point, finitely many germ equalities can be realized on one
neighborhood. On simplices in that neighborhood, every chosen index is
among these finitely many compatible representatives. This proves local
agreement with the given representatives on the original cochains.

`SingularSheafGlobalSections.globalCochainsToSheaf_surjective` applies
this construction to actual local lifts of an arbitrary section of the
existing sheafification. Equality in that sheaf is detected on its
original stalks. The resulting preimage belongs to the existing rational
cochain module; no new cochain carrier or replacement global map is used.

## The original map on cohomology

`SheafCohomology.ComplexKernelComparison` proves the generic native-kernel
criterion for a degreewise surjective module-valued cochain map. Its
actual kernel sequence is short exact. The original long exact homology
sequence and acyclicity of that kernel make the original homology map
both mono and epi in every degree.

`globalCochainsToSheaf_quasiIso` applies this criterion to the surjectivity
just proved and the existing `sheafificationKernel_acyclic` from 0047.
`globalCochainsToSheaf_homologyIso` is the isomorphism induced by the
original unit itself. This is a comparison with termwise global sections;
no underived-to-derived comparison has been assumed or proved here.

The scheme wrapper retains the explicit paracompactness and Hausdorff
hypotheses on the original canonical complex point topology. These
properties are independently proved for canonical affine spaces in every
dimension and the original glued P¹, using their existing homeomorphisms
to complex coordinate space and `OnePoint ℂ`. These are proved properties
of the original topologies, installed only locally where needed.
No smoothness assumption is needed for the global-unit theorem itself.

## Remaining obligations

Update: [0049](0049-open-singular-sheaf-restrictions.md) now proves open-subspace
lifts and native flasqueness of the original cochain sheaves under its
explicit topology hypotheses, verified for canonical affine spaces and
P¹. The following paragraph records this checkpoint's remaining
obligations at the time; positive derived-cohomology vanishing and the
derived comparison remain open.

Next prove the required sheaf-term acyclicity and identify the existing
underived-to-derived global-sections comparison. For a flasqueness route,
surjectivity must be established on the relevant open subspaces, with
their topological hypotheses proved. General smooth projective point
spaces still need the appropriate topological properties beyond the
affine and P¹ cases checked here. Neither raw presheaf surjectivity nor
the global-unit quasi-isomorphism alone discharges sheaf-term acyclicity.

Complex coefficients, proper algebraic/analytic comparison, general
periods, purity and prescribed-class Chow coverage retain their earlier
open status. There are no new axioms, proof placeholders, external proof
ports or dependencies.

## Verification

`make check-global-singular-sheaves` includes the previous cover and
native-kernel controls, extended on their original fixtures. The real
line's global unit is a quasi-isomorphism, although the same nonzero
long-edge detector maps to zero in degree one. Thus the new comparison
does not assert injectivity on every cochain module. Canonical affine
spaces in all dimensions, including zero, and the original glued P¹
check both surjectivity and the actual global-map quasi-isomorphism.
The empty space checks the boundary without a global index choice.

The focused suite passed all 94 declaration audits against only
`propext`, `Classical.choice` and `Quot.sound`, without warnings or errors.
It includes the existing cover/kernel fixtures and 26 new
global-comparison checks. All 103 import-boundary guards passed; local
documentation links and whitespace checks passed. The full `lake build`
passed all 5,249 jobs; existing repository warnings retain their earlier
scope. The combined root regression passed 401 standard-three axiom
audits and 49 public-export checks without warnings or errors. It
includes the previous analytic, singular sheaf, native-kernel,
subdivision, two-open, rational-dual and infinite-cover checks, alongside
the new global-unit and canonical topology controls. Builders completed
sequentially before the root regression.
