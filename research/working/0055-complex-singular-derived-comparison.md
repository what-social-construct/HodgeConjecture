# Complex singular cochains and the native constant sheaf

Date: 2026-11-10.

This checkpoint continues [0054](0054-finite-cohomology-coefficient-change.md)
with the **same unrestricted complex-valued functionals** on the original
rational singular chains. It proves their comparison with derived sections
of the native complex constant sheaf. It does not identify the resulting
map with the holomorphic comparison constructed in [0053](0053-complex-coefficients-holomorphic-comparison.md).

## Original coefficient maps

`SingularCoefficientSheafMap` defines literal postcomposition by
ℚ → ℂ on the original rational singular cochains. Its simplex formula is
φ(σ) ↦ φ(σ) considered in ℂ. The map is natural under the original
continuous pullbacks. It induces maps between the original rational and
complex presheaf complexes and their native sheafifications. The two
constant-sheaf augmentations and the complete local resolution maps
commute strictly with it.

`SingularCoefficientGlobalUnit` proves that the original global cochain
maps to the two sheafified complexes commute with coefficient inclusion,
termwise, as cochain maps, and on induced homology. Exact scalar restriction
identifies homology of the restricted complex with the underlying rational
module of complex singular cohomology; `coefficientCohomologyMap` uses the
induced map on the original cochain complexes.

`SingularCoefficientTensorBridge` also factors the original cochain map
strictly through the pure-tensor unit and the existing complex-linear
cochain comparison. `SingularCoefficientDerivedSquare` proves the
coefficient square through actual termwise global sections and constructs
the scalar-restriction isomorphism for any flasque complex of sheaves.

## Complex global sections

The indexed-cover small-chain inclusion from 0046 is dualized through the
exact functor Hom_ℚ(−,ℂ). It gives an actual complex-valued small-cochain
quasi-isomorphism for every indexed open cover, with no finiteness
assumption on chains or simplices. Extension of functionals makes this
restriction degreewise surjective, so its native kernel is acyclic.

The original complex global-unit kernel consists exactly of cochains that
vanish on a neighborhood of each point. A small-cover primitive is shown
to be locally zero, proving the native kernel acyclic in every degree.
On paracompact Hausdorff spaces, locally finite closed refinements patch
actual complex-valued simplex functions. Every section of the sheafification
then lifts to a global original cochain, and the global unit is a
quasi-isomorphism. The proofs retain the original complex differential and
do not replace unrestricted functionals by tensor products of cochains.

Zero extension along an open embedding is a right inverse to the original
cochain pullback. It supplies section lifts on paracompact Hausdorff opens
and flasqueness of the same complex cochain sheaves when all opens satisfy
that condition. Locally compact second-countable Hausdorff spaces do.

## Derived target and remaining comparison

`ComplexSingularConstantSheafCohomology` composes the original complex
global unit, the whole-complex underived-to-derived comparison for these
flasque terms, and the inverse of the native complex constant-sheaf local
resolution. The resulting map

\[
H^n(\operatorname{Hom}_{\mathbb Q}(C_\bullet(X,\mathbb Q),\mathbb C))
\longrightarrow R^n\Gamma(X,\underline{\mathbb C})
\]

is an isomorphism for locally compact second-countable Hausdorff spaces
with strongly locally contractible topology. Its definition and resolution
square fix the exact map being inverted.

Composing with the already proved holomorphic Poincaré resolution gives
`complexSingularToHolomorphic`, an isomorphism onto the same intrinsic
holomorphic hypercohomology. Composing it with the finite-cohomology
cochain map from 0054 gives `cochainHolomorphicComparison`, also an
isomorphism under those topology and finiteness hypotheses. This is a
separately named map until its equality with the 0053 map is proved.

**Still open:** identify the original coefficient-induced rational-to-complex
derived square with `ScalarRestriction.constantCohomologyMap`, then prove
that the tensor extension of that square is the specific holomorphic map
`AnalyticBettiComparison.complexComparison`. Invertibility of that
holomorphic map is not asserted here; the subsequent
[0056](0056-projective-line-holomorphic-comparison-iso.md) proves its canonical
P¹ degree-two case independently. General smooth-scheme point-topology
hypotheses, proper algebraic/analytic comparison, purity, and prescribed
Hodge-class coverage remain separate.

The remaining map equality needs two canonicality arguments: transport the
pure-tensor cochain unit through the native tensor and scalar-restriction
homology isomorphisms, and identify the flasque-resolution scalar map with
the older ordinary derived map defined through an injective resolution.

## Verification

Focused builds and standard-three axiom audits cover the original coefficient
square, indexed small-cochain comparison, native kernel, global-unit
quasi-isomorphism, open section lifts, flasqueness, and the derived
constant-sheaf comparison. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The targeted build/check command is
`make check-complex-singular-comparison`. The full library build passes
with 5,291 jobs through the subsequent 0056 export; the root-import
regression, import-boundary check, and
`git diff --check` also pass. These checks do not prove the remaining
holomorphic naturality square.
