# Arbitrary open-cover small-chain and cochain comparison

Date: 2026-11-09.

This completes the arbitrary-cover step following
[0045](0045-singular-cochain-sheaf-resolution.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). For every indexed open cover of
any topological space, the original small-chain inclusion is a
quasi-isomorphism. Exact rational dualization proves the same for the
original cochain restriction. This restriction is degreewise surjective,
and its existing relative kernel complex is acyclic in every degree.
The global singular/sheaf-cohomology comparison remains open.

## The same native singular objects

`CoverSingular` defines `coverSingular X U` as the native supremum of the
existing `subsetSingular X (U i)`. Membership means that the whole
original singular simplex lies in one member, rather than merely in the
union of the members. The original native chain complex, inclusion and
supported inclusion range supply `coverComplex`, `coverInclusion` and
`coverChains`. The index type can be infinite, uncountable, or empty when
the covered space is empty.

`coverSingular_bool` proves that the two-member indexed family gives
exactly the existing binary simplicial union. No new singular simplex,
chain, differential, or cochain carrier replaces the original objects.
Refinements induce the native subcomplex inclusions.

## Actual shrinking and the restricted original homotopy

The existing `NativeSimplexGeometry.lebesgue_number` already works for
arbitrary indexed open covers of the native standard simplex.
`lebesgue_number_diam` derives its whole-cell diameter form using the
same original weights coordinates. The previous two-member diameter
bound specializes that proof.

`SingularSubdivisionIteration` owns the original mesh estimate, affine
naturality, reference realization and iteration laws. Their namespace and
public names are retained. Pulling an arbitrary cover back along an
original continuous singular simplex gives a genuine cover of its
compact native domain. The Lebesgue number and the existing shrinking
mesh place all subdivided cells in cover members. Subdivision preserves
the same small subcomplex, so a maximum of the finitely many counts in
an original chain's support works for that entire chain. No finite
subcover of the whole target space is assumed or constructed.

The explicit original singular homotopy also stays in the image of
each original simplex. `CoverSubdivisionHomotopy` restricts the original
subdivision map and native homotopy to the same small chain complex.
Openness and coverage are not needed for this preservation statement.
`CoverSmallChains.inclusion_quasiIso` applies the existing native
homology-class criterion to these actual operators and the proved
finite-chain shrinking. Its `homologyIso` is the homology map of the
original inclusion, in every degree. Refinement maps commute with the
inclusions and are themselves quasi-isomorphisms between open covers.

## Original cochains and the existing vanishing kernel

`CoverSmallCochains.restriction` is ordinary restriction of original
rational simplex functions. The existing `CochainDualComparison` and exact
`RationalDual` send the proved native chain comparison to this actual
cochain restriction. No finite-dimensionality assumption is used.
Refinement restrictions are the original simplicial pullbacks and
commute with full-to-small restriction.

Degreewise surjectivity reuses `RelativeCochains.extension` and its
already proved extension-by-zero right inverse. `vanishingComplex` is
an abbreviation for the original relative kernel complex: cochains
vanishing on all simplices small for this cover. The native long exact
sequence of the actual short exact relative sequence proves
`vanishingComplex_acyclic`, including degree zero.
`exists_vanishing_primitive` supplies actual positive-degree primitives
inside this same kernel. Thus the primitive vanishes on the same cover,
not merely after choosing another cover.

## Shared owners and backward compatibility

`SubcomplexOperators` restricts supported operators, native chain maps
and native homotopies through the existing `chainSubmoduleEquiv`.
Injectivity of the original inclusion proves the identities once.
`SingularSupportedChains` owns the shared finite-support realization
argument. Both the indexed and existing two-open constructions use these
helpers.

The previous `smallChains` name now delegates directly to the existing
native `chainSubmodule`, replacing a second comap description of its
already proved equal supported range. The existing two-open smallness,
locality and inclusion-comparison theorems specialize the indexed proofs.
The old restricted subdivision and homotopy use the shared restriction
construction, retaining their original native complexes and public names.
No second subdivision, simplex-function differential or rational dual
implementation is introduced.

There are no new axioms, proof placeholders, external proof ports or
dependencies. The pinned Mathlib revision and existing attributions are
unchanged.

## Remaining global obligations

Update: [0047](0047-global-sheafification-kernel.md) now identifies the
actual global-unit kernel with locally zero cochains and proves its
native acyclicity. The following paragraph records the obligations at
this checkpoint. [0048](0048-global-singular-sheaf-sections.md) subsequently
proves global-unit surjectivity and comparison with termwise sections on
paracompact Hausdorff spaces; sheaf-term acyclicity and derived sections
remain open.

The acyclic kernel above is attached to one indexed cover. It has not
yet been identified with the actual global sheafification-unit kernel.
The next step is to identify that kernel through locally zero cochains,
then prove the global unit and acyclicity statements needed to compute
derived global sections. Any required topological hypotheses in the
classical sheafification argument must be established for the intended
spaces. Surjective presheaf restrictions alone do not prove flasqueness
after sheafification.

The rational-to-complex coefficient comparison, proper algebraic/analytic
comparison, general periods, purity and prescribed-class coverage retain
their earlier open status. In particular, tensoring rational cochains
with the complex numbers is not silently identified with all
complex-valued cochains on an infinite simplex set.

## Verification

`make check-open-cover-small-chains` checks the cover by all real unit
balls and proves that it has no finite subcover. The original edge from
zero to three is not small; a positive number of actual subdivision
steps makes its original chain small. The actual chain and cochain
comparisons apply to this infinite cover.

An indicator cochain on that long edge is nonzero and restricts to zero
on small cochains. Its differential evaluates to one on an original
affine two-simplex, giving a nonzero closed vanishing cochain. The proved
kernel acyclicity supplies a primitive still vanishing on the same
infinite cover. An empty-index cover of the empty space checks the
nonempty-index boundary. The focused audit checks 32 declarations against
only `propext`, `Classical.choice` and `Quot.sound`.

The focused verification passed all 32 audits without warnings or errors.
All 95 import-boundary guards, local documentation links and whitespace
checks passed. The full `lake build` passed all 5,238 jobs. Existing
repository warnings retain their prior scope. The combined root regression
passed 339 standard-three axiom checks and 35 public-export checks, with
no warnings or errors. This includes the previous analytic and sheaf
regressions, the original subdivision/two-open smallness/inclusion and
rational-dual comparison checks, and the new infinite-cover controls.
Builders completed sequentially before the root regression.
