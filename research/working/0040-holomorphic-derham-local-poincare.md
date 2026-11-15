# Holomorphic de Rham complex and local Poincaré comparison

Date: 2026-11-09.

Historical checkpoint. [0041](0041-higher-degree-holomorphic-poincare.md)
subsequently proves the higher-degree radial homotopy and full coordinate
sheaf comparison. The bounded scope and validation below describe this
earlier construction.

This advances item 4 of the [active checklist](../TARGET_BRIDGE.md).
There is now an actual all-degree holomorphic de Rham sheaf complex on
complex coordinate spaces, a constructed constant-sheaf comparison, and
proved local exactness in degrees zero and one in every coordinate
dimension. On the complex line the comparison is a full quasi-isomorphism.
The higher-degree local Poincaré lemma in higher dimensions, identification
of analytic charts on general scheme complex points, and general
algebraic/analytic and singular comparisons remain open.

## Actual coefficients, sections and differential

For a complex normed space E and an open U, the degree-n coefficients are
Mathlib's native continuous complex alternating maps
`E [⋀^Fin n]→L[ℂ] ℂ`. Sections are the existing bundled complex C∞ maps
from U to that coefficient space. No new function carrier or independently
supplied differential is introduced. Complex C∞ is the holomorphic
coefficient model used here; the construction does not add a new formal
first-differentiability/analyticity equivalence in several variables.

`Geometry.Holomorphic.Forms` defines d by the native `extDeriv` of a
local extension. Extension by zero is only an auxiliary way to compute
derivatives at points inside U. Its local smoothness is proved, and the
result agrees with every local extension having the same values. Native
Fréchet-derivative linearity, smoothness and symmetry prove complex
linearity, preservation of holomorphic sections and d² = 0. The same
locality proof gives restriction compatibility on the original sections.

`HolomorphicDeRham.formsSheaf` upgrades Mathlib's actual complex
smooth-function sheaf to fixed-complex-scalar modules. The sheaf property
is inherited through the forgetful functor. The constructed arrows give
`HolomorphicDeRham.complex`; `sectionComplex` evaluates those same objects
and maps on an open, without constructing a different differential.

Constants map to native zero-forms. Sheafification gives the actual
augmentation from the constant complex-coefficient sheaf. Its composition
with d is zero, so `HolomorphicDeRham.comparison` is a genuine cochain map
from that constant sheaf concentrated in degree zero to the analytic
complex. Its degree-zero component is proved to be the augmentation.

## Local Poincaré proofs and exact scope

Native empty- and singleton-alternating-map equivalences identify
zero-forms with functions and one-forms with continuous-linear-map
coefficients. The degree-zero differential becomes the actual complex
Fréchet derivative. Evaluating the degree-one differential on two vectors
proves the expected antisymmetric derivative formula with its original
sign and normalization.

For a closed holomorphic one-form η on a convex coordinate open U and
a base point a in U, the primitive is the actual native curve integral

\[
F(x)=\int_{[a,x]}\eta.
\]

Closedness gives the coefficient-derivative symmetry required by
Mathlib's proved curve-integral Poincaré theorem. Restriction from complex
to real derivatives supplies its real differentiability hypotheses. Its
conclusion is the complex derivative dF = η. The primitive is itself
complex C∞ because its derivative equals the original complex C∞
coefficient function. F(a) = 0 is proved using the constant segment.

`differential_primitive` identifies this same integral with the actual
zero-form witness, and `locally_exact_one` shrinks an arbitrary coordinate
open to a ball contained in it. These statements hold in every complex
coordinate dimension, not just on the complex line.

The degree-zero kernel is locally constant: vanishing derivative on a
small ball and the native mean-value theorem prove constancy there. No
connectedness of the original open, global primitive, or equality with
the image of global constant sections is asserted. A shared fixed-ring
sheaf local-lift lemma, adapted narrowly from Axiom Weil, turns these
actual local witnesses into sheaf exactness. Local injectivity of the
constant presheaf proves monicity of the sheafified augmentation.

Thus `comparison_quasiIsoAt_zero` and `comparison_quasiIsoAt_one` are
proved in every coordinate dimension. Native alternating coefficients
vanish above the actual finite complex dimension. In particular on E = ℂ
all terms in degrees at least two vanish, and
`complexLine_comparison_quasiIso` proves the full constant-to-holomorphic
quasi-isomorphism. This is a local/sheaf comparison; it does not by itself
identify analytic sheaf cohomology with the repo's singular cochains or
compute hypercohomology by arbitrary global sections.

## Existing algebraic forms retain their meaning

`HolomorphicKaehler` proves that this same differentiation is a derivation
of the native holomorphic-function algebra. The existing Kähler universal
property supplies `kaehlerRealization`. For an actual algebra map
φ : A →ₐ[ℂ] O(U), `algebraicOneFormsMap` first applies the existing
`AlgebraDeRham.kaehlerMap`, then that universal lift. Its generator formula
is the proved equality da ↦ d(φ(a)). It is not a supplied compatibility
field, an isomorphism assertion or a different model of algebraic forms.

The complex-line polynomial evaluation map is constructed as the native
`Polynomial.aeval` at the original coordinate function. Its values are
proved equal to ordinary pointwise polynomial evaluation. General
holomorphic regular evaluation for arbitrary scheme sections and the
all-degree algebraic-to-analytic forms map remain separate constructions.

## Sources and ownership

The exterior derivative, d², bundled-map sheaf, Fréchet calculus,
mean-value theorem and one-form Poincaré proof are imported from the
repo's pinned Mathlib. The shared local-lift criterion adapts only
`TopCat.Sheaf.exact_of_exists_local_preimage` from Axiom Weil revision
`27cdb2049be62ee2911429b47f54774078450e32`,
`Weil/Geometry/Manifold/Sheaf/Holomorphic.lean`, generalized to the
existing fixed-ring module sheaves. [Attribution and license](../../third_party/axiom-weil/README.md)
record the port. Weil's audited exponential/Kummer and curve Dolbeault
files are not imported as de Rham or higher-dimensional Poincaré results.

Geometry owns the native analytic form and primitive APIs; the shared
sheaf layer owns the local-exactness argument. The realization layer
assembles the complex, comparison and Kähler adapter. Import guards keep
the analytic complex and comparison independent of Chow, Betti, boundary,
source-input and project algebraic-differential modules. Only the Kähler
adapter imports the existing algebraic differential layer.

## Remaining item 4 work

1. Prove the higher-degree analytic contraction/local Poincaré lemma in
   complex dimension at least two. Only degrees zero and one are complete
   there; the differential and all higher sheaf terms are already built.
2. Construct compatible analytic charts/holomorphic structure on the
   canonical complex point spaces of the intended smooth schemes, and
   identify regular evaluation and the full algebraic forms map.
3. Identify constant analytic sheaf cohomology with the existing rational
   singular tensor, and prove the proper algebraic/analytic comparison
   for the existing scheme hypercohomology. Preserve actual maps and the
   previously verified P¹ period normalization.
4. Prove geometric finite dimension, boundedness and opposedness/purity.

The active checklist stays in TARGET_BRIDGE; this checkpoint records
the exact new theorem scope rather than marking general comparison or
purity complete.

## Validation

The focused command is `make check-holomorphic-derham`. Its controls use
the actual nonclosed form z₁ dz₂ in dimension two, the primitive x − a of
the constant one-form, the value 6 of d(z²) at z = 3, degree-zero/one
quasi-isomorphisms in dimension two, and the full complex-line comparison.
The axiom audit checks the actual exterior derivative, primitives, sheaf
exactness, quasi-isomorphisms and original Kähler map.

`make check-holomorphic-derham` passed, including all 36 standard-three
axiom audits (`propext`, `Classical.choice`, `Quot.sound`) and the three
explicit controls above. The full library build passed (5,175 jobs),
all import guards passed, and a focused root-import inventory checked all
20 new public declarations. The final new modules produced no warnings.
Local documentation targets and `git diff --check` passed. Unrelated
existing warnings, including the prior `Challenge.lean` placeholders,
retain their previous scope; none occurs in the new modules or their
audited dependencies.
