# The actual global singular sheafification kernel

Date: 2026-11-09.

This completes the kernel step following
[0046](0046-arbitrary-open-cover-small-chains.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). The existing
`SingularCochains.globalCochainsToSheaf` kills exactly the locally zero
original rational singular cochains. Its native categorical kernel is
acyclic in every degree. These statements hold for every topological
space, without separation, local contractibility or cover-finiteness
assumptions. The global derived-section comparison remains open.

## Identifying the existing unit

`SheafCohomology.SheafifyKernel.toSheafify_app_eq_zero_iff` works for a
module-valued presheaf over any commutative ring. It characterizes the
kernel of the actual native sheafification unit on each original open:
a section maps to zero precisely when it restricts to zero near each
point. The proof reuses `LocalExactness.sheafifyStalkIso`, equality of
original germs on a smaller open, and stalkwise detection of equality
in the sheaf. No alternative sheafification or sheaf instance is added.

`SingularLocallyZero.LocallyZero` is only a predicate on the original
cochains. `globalCochainsToSheaf_eq_zero_iff` applies the generic theorem
to the existing global map, including its actual top-open identification.
Original open-subspace pullback and `subsetSingular` restriction have
the same kernel, using the existing simplex maps in both directions.

Local zero witnesses choose an actual open neighborhood for each original
point. These form an indexed open cover on which the cochain vanishes.
Conversely, vanishing on the small simplices of any indexed open cover
implies local vanishing. `globalCochainsToSheaf_ker_eq_iSup` identifies
the actual degreewise linear kernel with the join of the existing cover
restriction kernels. The stronger elementwise cover-witness statement
is proved as well; no assertion that one fixed cover works for the
whole kernel is needed.

## Primitives in the native categorical kernel

`SheafCohomology.ComplexKernel` exposes degreewise elements of the native
kernel of a module-valued cochain map. Its kernel sequence remains exact
after evaluation, so the actual inclusion has precisely the original
linear kernel as its range. This provides injectivity, actual preimages
and differential compatibility, without building another kernel complex.

`SingularSheafificationKernel.sheafificationKernel` abbreviates
`Limits.kernel (globalCochainsToSheaf X)`. The native inclusion identifies
its degreewise range with locally zero original cochains. Every closed
locally zero positive-degree cochain has a primitive still locally zero:
choose its original witness cover and apply the existing
`CoverSmallCochains.exists_vanishing_primitive` in that cover's original
relative kernel. `exists_kernel_preimage` then lifts this primitive
through the actual native kernel inclusion. Injectivity and the original
cochain-map identity prove the required equation in the native kernel.

In degree zero, a locally zero cochain vanishes on every original
zero-simplex. Thus the native degree-zero kernel object is zero, and
positive primitives prove `sheafificationKernel_acyclic` in all degrees.
`Scheme.ComplexPoints.singularSheafificationKernel_acyclic` specializes
this to every original canonical scheme point space, without smoothness
or an analytic atlas hypothesis.

There are no new axioms, proof placeholders, dependencies or external
proof ports. Existing singular cochains, sheafification, relative cover
kernels and the native categorical kernel retain their original owners.

## Remaining global obligations

Update: [0048](0048-global-singular-sheaf-sections.md) now proves
surjectivity and the actual unit's quasi-isomorphism to termwise global
sections on paracompact Hausdorff spaces, including canonical affine
spaces and P¹ with proved topological hypotheses. The following paragraph
records this checkpoint's remaining obligations at the time; sheaf-term
acyclicity and derived sections remain open.

Next prove global surjectivity of the existing unit under the appropriate
topological hypotheses, and the sheaf-term acyclicity needed for the
existing derived-global-sections comparison. Acyclicity of the native
kernel alone does not prove that the unit is a quasi-isomorphism; its
image and cokernel still need control. Surjective raw presheaf
restrictions alone do not establish acyclicity after sheafification.

Rational-to-complex coefficient compatibility, proper algebraic/analytic
comparison, general periods, purity and prescribed-class coverage remain
open. Tensoring rational cochains with the complex numbers has not been
identified with all complex-valued functions on an infinite simplex set.

## Verification

`make check-sheafification-kernel` reuses the original infinite cover of
the real line by all unit balls. The same nonzero indicator one-cochain
maps to zero under the actual global unit, and has an actual preimage in
the native degree-one kernel. Its differential is a nonzero closed
degree-two native kernel element, detected by the original triangle
evaluation. The theorem supplies a primitive in that same native kernel.
These checks extend the existing cover fixtures without copying them.

Additional controls check all canonical affine dimensions including zero,
the original glued projective line, the empty space, and survival of a
literal nonzero rational constant under the existing unit. The combined
focused audit checks 68 declarations against only `propext`,
`Classical.choice` and `Quot.sound`.

The focused verification passed all 68 audits without warnings or errors.
The full `lake build` passed all 5,242 jobs; existing repository warnings
retain their earlier scope. All 99 import-boundary guards, local
documentation links and whitespace checks passed. The combined root
regression passed 375 standard-three axiom audits and 41 public-export
checks, without warnings or errors. This includes the previous analytic,
sheaf, subdivision, two-open, rational-dual and infinite-cover regressions,
alongside the new native-kernel controls. Builders completed sequentially
before the root regression.
