# Rational singular cohomology and the original constant sheaf

Date: 2026-11-10.

This assembles the comparison following
[0051](0051-singular-derived-comparison.md), within item 4 of the
[active checklist](../TARGET_BRIDGE.md). For a locally compact,
second-countable Hausdorff space with a basis of contractible
neighborhoods, the original rational singular cohomology now identifies
the actual ordinary right-derived sections of the original rational
constant sheaf, in every nonnegative degree:

\[
H^n_{\mathrm{sing}}(X,\mathbb Q)
\;\cong\;
\bigl(R^n\Gamma(X,-)\bigr)(\mathbb Q_X).
\]

The source is `SingularCochains.Cohomology X n`. The target is literally
`((SheafHypercohomology.globalSections ℚ X).rightDerived n).obj
(SingularCochains.constantSheaf X)`, with the constant sheaf definitionally
the existing `ConstantLift.sheaf ℚ X`. Neither cohomology carrier is replaced.

## The original maps

`Betti.SingularConstantSheafCohomology` composes the already proved maps:

1. The original `globalCochainsToSheaf` induces a map on the original
   nonnegative singular cohomology.
2. Native extension by zero identifies that sections homology with the
   integer-degree homology used by the existing derived construction.
3. The original `comparisonFromComplexHomology` maps to the existing
   hypercohomology of the original singular sheaf complex.
4. The inverse of the map induced by the original constant-sheaf resolution
   identifies hypercohomology of the constant sheaf placed in degree zero.
5. The existing `singleIsoRightDerived` identifies this with the ordinary
   right-derived global-sections object, through its actual injective resolution.

The local-resolution inverse needs `StronglyLocallyContractibleSpace`,
the proved contractible-neighborhood-basis condition. Invertibility of
the global steps uses the existing global-unit and native flasque
whole-complex comparison proofs. Locally compact second-countable
Hausdorff spaces satisfy their global topology hypotheses. The intermediate
global comparison also retains the explicit paracompactness and flasque-term
variant, separately from local contractibility.

`cohomologyToConstantSheafDerived` is this composite map.
`cohomologyIsoConstantSheafDerived` packages its proved invertibility,
with the same hom map. The proved resolution square recovers the original
map to singular-sheaf hypercohomology after undoing the single-sheaf
identification and applying the original local resolution. Zero-class
detection is proved for every class in every degree.

## Shared helpers and canonical schemes

`SheafCohomology.HypercohomologyComparison` owns the generic helpers.
`nonnegativeSectionsHomologyIso` reuses the existing `mapExtendIso` and
native `extendHomologyIso`. The original derived-sections and hypercohomology
maps invert a quasi-isomorphism by native extension and localization.
`hypercohomologyIsoOfQuasiIso` retains that original map as its hom.
No second resolution, cochain complex, constant sheaf or derived target is constructed.

The generic local-exactness module now imports native Mathlib local
contractibility directly. Its previous geometry helper contained chart
specializations that it did not use. The scheme wrapper imports that
existing helper directly where the normed-space and atlas results are
used. Import guards now exclude local geometry from both the generic
local-exactness and singular-resolution modules, as well as this composite.

Scheme wrappers start with the existing `SchemeBetti.Cohomology` on the
existing canonical point topology. For smooth schemes of fixed relative
dimension, the existing atlas theorem supplies strong local contractibility.
Hausdorffness, local compactness and second countability remain explicit
in the general scheme wrapper; they are already proved for canonical
affine spaces in every dimension and the original glued P¹.

The P¹ control transports the original nonzero singular degree-two
generator through the already proved canonical homeomorphism, then maps
it by the assembled comparison. Its image is proved nonzero in the
actual `R²Γ(ℚ_X)` target itself.

## Remaining scope

The rational comparison above is now constructed objectwise in every
nonnegative degree, with the original comparison maps fixed. This
checkpoint does not construct a separate derived pullback functor between
different spaces or assert a new natural isomorphism against such a functor.

The subsequent [0053 checkpoint](0053-complex-coefficients-holomorphic-comparison.md)
constructs the complex-linear map from the original tensor complexification
to actual holomorphic hypercohomology and proves rational-diagonal zero
detection. Invertibility of that coefficient comparison is next.
General scheme point-topology
properties, proper algebraic/analytic comparison, the general period
isomorphism, purity and prescribed-class Chow coverage retain their
earlier open scope.

## Verification

`make check-singular-constant-comparison` includes the preceding global-unit,
termwise-vanishing and whole-complex checks. New controls cover the real
line and its arbitrary opens, the empty space, all canonical affine
dimensions and cohomology degrees, dimension/degree zero, canonical P¹,
the original resolution square and the nonzero class in the actual
derived P¹ target.

The focused verification passes all 32 standard-three axiom checks,
including the actual nonzero derived P¹ class. All 114 import guards pass.
Full `lake build` passes with 5,260 jobs after the import cleanup. Local
documentation links and `git diff --check` pass. The final combined
root-import regression passes all 509 standard-three axiom checks and
81 export checks with no errors or warnings. The axiom whitelist remains
`propext`, `Classical.choice` and `Quot.sound`.
