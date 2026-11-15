# Complex coefficients and the original holomorphic derived target

Date: 2026-11-10.

Following [0052](0052-rational-singular-constant-sheaf-comparison.md),
this constructs the actual complex-linear comparison map in item 4 of the
[active checklist](../TARGET_BRIDGE.md):

\[
\mathbb C\otimes_{\mathbb Q} H^n_{\mathrm{sing}}(M,\mathbb Q)
\longrightarrow
\mathbb H^n(M,\Omega^\bullet_{\mathrm{hol}}).
\]

The source is the existing `RationalComplexification.Space` of the existing
`SingularCochains.Cohomology`. The target is literally the existing
`SheafHypercohomology.hypercohomology` of `HolomorphicAtlas.complex`.
Neither endpoint is a newly transported cohomology object. The map is
constructed in every nonnegative degree for the existing complex-smooth
manifold and scalar-tower hypotheses, with a contractible-neighborhood basis.
Its invertibility remains open.

## Shared coefficient layer

`SheafCohomology.ScalarRestriction` uses native `ModuleCat.restrictScalars`
and `sheafCompose`. Sections and restriction functions are unchanged.
The native extension/restriction adjunction gives preservation of limits;
the same native local-surjectivity sieves give preservation of epimorphisms,
and hence exactness. Native flasqueness is preserved. The existing
`LinearRestriction.injective_linear_restriction_surjective` supplies
flasqueness of restricted injective terms without a second supported-section proof.

`coefficientModuleMap` is the original ring map as a linear morphism into
the restricted coefficient module. `constantIso` is the native
`constantCommuteCompose` isomorphism. `constantMap` applies the native
constant-sheaf functor to that linear morphism and then this isomorphism.
The original `ConstantLift.sheaf` objects are retained; there is no second
constant-sheaf construction or bespoke sheafification map.

`DerivedScalarRestriction.cohomologyIso` identifies

\[
R^n\Gamma_R(\operatorname{Res}_{R}^{S}F)
\cong \operatorname{Res}_{R}^{S}(R^n\Gamma_S(F)).
\]

Both sides use one actual injective resolution of F in S-module sheaves.
Exact restriction gives its original resolution map as a quasi-isomorphism.
Restricted terms are flasque, so the existing whole-complex comparison
computes the left side. The original `rightDerivedPostcomposeIso` computes
the right side through the same resolution. Preservation of injective
sheaves by scalar restriction is not assumed. `constantCohomologyMap`
is ordinary derived functoriality on `constantMap`, followed by this isomorphism.

## Original holomorphic resolution and tensor map

`DeRham.HolomorphicHypercohomology` applies the existing
`HolomorphicAtlas.comparison_quasiIso` and shared
`hypercohomologyIsoOfQuasiIso` to prove

\[
R^n\Gamma_{\mathbb C}(\mathbb C_M)
\cong \mathbb H^n(M,\Omega^\bullet_{\mathrm{hol}}).
\]

`constantSheafDerivedIso_resolution` fixes this isomorphism by the original
Poincaré resolution map. No acyclicity of individual holomorphic form sheaves
or computation using only their global sections is assumed.

`AnalyticBettiComparison.rationalComparison` composes:

1. The previous original rational singular/constant-sheaf comparison.
2. `constantCohomologyMap` for coefficient inclusion ℚ → ℂ.
3. The original holomorphic resolution isomorphism, with scalars restricted.

`complexComparison` extends this rational map through the native tensor
universal property. The shared `extendLinear` uses `LinearMap.liftBaseChange`
with the existing coefficient algebra, and `IsScalarTower.of_compHom` for
the native restricted target action. Its source is exactly the original
tensor complexification, and the proved formula sends c ⊗ α to c times
the original rational comparison of α. No new complex-valued cochain
complex is introduced.

## Rational detection and canonical controls

An injective field coefficient map splits linearly by native
`LinearMap.exists_leftInverse_of_injective`. The constant-sheaf and ordinary
derived functors preserve that split monomorphism. This proves injectivity
of `rationalComparison` when the previous rational comparison is an
isomorphism: Hausdorff, locally compact, second-countable topology and a
contractible-neighborhood basis. The coefficient splitting occurs only in
the proof; the constructed comparison remains fixed by coefficient inclusion.

`complexComparison_embedding_eq_zero_iff` consequently detects zero on the
existing rational diagonal α ↦ 1 ⊗ α. This does not assert injectivity of
the map on the whole complexification.

`Scheme.ComplexPoints.holomorphicBettiComparison` uses the existing canonical
point topology, `SchemeBetti.Cohomology` and the smooth fixed-relative-dimension
analytic atlas. Strong local contractibility comes from that existing atlas.
The general zero-detection wrapper keeps Hausdorffness, local compactness
and second countability explicit; canonical affine spaces and P¹ already
have those proved properties.

The P¹ control uses the existing `ProjectiveLineCanonicalComparison.bettiEquiv`
and original `coverGenerator`. Its actual image under this comparison is
proved nonzero in intrinsic holomorphic degree-two hypercohomology. The
target and generator are not replaced, and the old bounded period comparison
is not used to define the new map.

## Remaining scope

Next prove invertibility of this exact complex-linear coefficient comparison
on the intended spaces, through a justified coefficient/base-change theorem.
The subsequent [0054 checkpoint](0054-finite-cohomology-coefficient-change.md)
proves finite-cohomology coefficient change for the actual singular cochain
map, allowing infinite chain modules. Identifying that cochain-induced map
with this exact holomorphic comparison through the complex constant-sheaf
resolution remains open.
Tensoring rational functions on all simplices with ℂ does not automatically
give all complex-valued functions on those simplices: scalar extension
through infinite products has not been asserted. The rational-diagonal
injection alone is insufficient for the required complex isomorphism.

General scheme point-topology properties, proper algebraic/analytic comparison,
the general period isomorphism, compatibility with the existing bounded P¹
period comparison, purity and prescribed-class Chow coverage remain open.
The constructions are objectwise; no separate derived pullback functor or
new natural-isomorphism claim between spaces is added.

## Verification

`make check-analytic-betti-comparison` includes the preceding rational,
whole-complex and flasque-term controls. New controls check original native
constant-sheaf compatibility, actual ordinary derived endpoints, the
holomorphic resolution square, pure tensors, rational-diagonal detection
on the complex line and all canonical affine dimensions/degrees, dimension
and degree zero, and the nonzero image of the original canonical P¹ class.

The focused verification passes all 34 standard-three axiom checks.
Full `lake build` passes with 5,265 jobs. All 118 import guards pass.
The combined root-import regression passes all 543 standard-three axiom
checks and 89 public-export checks, with no errors or warnings. These
include the original P¹ class's nonzero image in the actual holomorphic
target. The whitelist remains `propext`, `Classical.choice` and `Quot.sound`.
Local documentation links, the Makefile target dry run and `git diff --check`
pass. The full library build still replays the preexisting `Challenge.lean`
proof-placeholder warnings; no new production declaration uses a proof
placeholder or project-level axiom.
