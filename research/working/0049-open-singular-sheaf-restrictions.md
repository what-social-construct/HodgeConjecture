# Open-subspace lifting and native flasque singular cochain sheaves

Date: 2026-11-09.

This continues [0048](0048-global-singular-sheaf-sections.md), within item
4 of the [active checklist](../TARGET_BRIDGE.md). The existing native
sheafification unit is surjective on any open whose subspace topology
is paracompact Hausdorff. Every section there lifts to an original
cochain on the entire ambient space. Consequently the original
singular cochain sheaves have surjective restriction maps whenever the
smaller open satisfies those hypotheses.

If every open is paracompact and the ambient space is Hausdorff, this
gives the native `TopCat.Sheaf.IsFlasque` property of the same existing
module-valued sheaf in every degree. Locally compact second-countable
Hausdorff spaces satisfy the required open-subspace conditions. These
properties are proved for canonical affine spaces in every dimension
and the original glued P¹.

## Native restriction and the original unit

`SheafCohomology.SheafifyOpen` reuses `restrictPresheaf` and
`local_restrictSheaf` from the existing `OpenImmersionRestriction`
owner. No second restriction functor is introduced. Open embeddings
lift covering sieves by taking actual inverse-image opens. The native
`pushforwardContinuousSheafificationCompatibility` isomorphism then
identifies sheafifying the restricted presheaf with restricting the
original sheafification. Its native unit-compatibility theorem is
retained as `toSheafify_sheafifyOpenIso`.

Generic module-valued helpers transfer surjectivity through a presheaf
isomorphism and through this same open-restriction comparison. They use
the original naturality square and actual component isomorphisms. The
top open of the subspace maps to the original ambient open; this is the
native `Opens.isOpenEmbedding_obj_top` identity, rather than a newly
identified section object.

`SingularOpenRestriction.openPresheafIso` applies the original cochain
functor to the native image homeomorphism of each original subopen.
Degreewise evaluation gives the presheaf isomorphism, with the same
singular simplices, pullbacks and cochain modules. This transfers 0048's
global-unit surjectivity on the open subspace to the actual ambient
unit component on that open. No new singular cochain model or
sheafification is constructed.

## Actual global extensions and flasqueness

`toSheafify_open_surjective` supplies an original cochain on the given
open representing an arbitrary sheafified section. The existing
`openExtension` extends it to an original ambient cochain. Naturality
of the existing global unit proves `exists_global_cochain_open_lift`.
Restricting that actual global sheaf section to any larger open proves
`cochainSheaf_restriction_surjective`. The larger open and ambient
space need no paracompactness hypothesis for this particular extension.

`cochainSheaf_isFlasque` installs this result in the native flasque
property of `SingularCochains.cochainSheaf X n`, retaining its original
fixed-ring module coefficients. Its hypotheses explicitly require
paracompactness of all opens and ambient Hausdorffness. Paracompactness
of the ambient space alone has not been used to infer that condition.

`cochainSheaf_isFlasque_of_locallyCompact_secondCountable` proves the
condition from local compactness, second countability and Hausdorffness.
An open subspace is locally compact and inherits a countable basis;
native sigma-compactness and paracompactness then apply. The scheme
wrapper retains these explicit properties of the original canonical
complex point topology.

For polynomial affine spaces, the existing coordinate homeomorphism
proves local compactness and second countability. For P¹, the existing homeomorphism to `OnePoint ℂ` proves local
compactness. Its original two canonical affine charts give an open
quotient map, through which a countable basis descends from those same
affine point spaces.
These are additional proved properties of the existing topology;
they do not replace it or add global transported topology instances.

## Remaining obligations

Update: [0050](0050-flasque-derived-sections.md) now proves positive
right-derived section vanishing for these original sheaf terms on every
open. The following paragraph records this checkpoint's remaining
obligations at the time; the bounded-below whole-complex comparison
remains open.

Next use flasqueness to prove vanishing of the actual positive right
derived global-sections functors on these sheaf terms. Then identify
the existing bounded-below underived-to-derived comparison. Native
flasqueness has been established here; the derived comparison is still
an explicit remaining theorem.

General smooth projective point spaces still need their relevant
topological properties established beyond the canonical affine and P¹
cases. Complex coefficients, proper algebraic/analytic comparison,
general periods, purity and prescribed-class Chow coverage retain
their previous open status. There are no new axioms, proof placeholders,
external proof ports or dependencies.

## Verification

`make check-open-singular-sheaves` includes the previous global-unit,
cover and native-kernel checks. The new verification tests arbitrary
real opens and actual ambient cochain lifts, all canonical affine
dimensions including zero, and the original glued P¹ in every degree.
P¹ restriction is also tested on its actual canonical affine chart,
proved noncompact, so the open-subspace argument is exercised beyond
compact subspaces. The empty space checks the degenerate boundary.

The full `lake build` passed all 5,251 jobs. Existing repository warnings
retain their earlier scope. All 105 import-boundary guards, local
documentation links and whitespace checks passed. The combined root
regression passed all 427 standard-three axiom audits and 57
public-export checks, without warnings or errors. Its 26 new audits
include the noncompact-chart fixture, actual open lifts,
surjective restrictions and native flasqueness; the earlier 401 analytic,
sheaf, kernel, subdivision, duality and cover checks remain green.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Builders completed sequentially before this regression.
