# Chow-class witness checkpoint (2026-11-12)

## The proof obligation

For a smooth projective complex `X`, a codimension `p`, and an independently
specified rational Hodge class `α`, construct an ordinary rational Chow class
`z : CH^p(X)_ℚ` and prove `cl_X^p z = α`. This is the elementwise target in
[`HodgeClasses.lean`](../../HodgeConjecture/Realization/HodgeClasses.lean).
`ClassDependentChowBettiGeneration` in
[`UpstairsGeneration.lean`](../../HodgeConjecture/Realization/Chow/UpstairsGeneration.lean)
packages the same obligation after a chosen cover: construct an actual
upstairs cycle recipe whose class is the pullback of `α`. Its normalized
pushforward theorem already constructs the downstairs Chow witness once that
equality and the Chow–Betti transfer square are supplied.

The existing `MarkedCycleMap` sends supplied sheet cycles to actual Chow
classes and computes their realized span. `SupportedClass` constructs a cycle
from a supplied algebraic support and component comparison. Neither selects
sheet cycles or a suitable support from an arbitrary `α`; adding another
abstract coverage predicate would not prove a new witness.

## Checked examples and next geometric case

- `ProjectiveLineHodgeCycleClass.infinity_class_witness` gives a witness in
  the original rational Chow group for every class of the bounded
  degree-normalized `H²(P¹, ℚ)` model: a rational multiple of the
  infinity-point class.
- `SplitBettiTateBlock` gives actual degree-zero Chow witnesses for finite
  split complex schemes.

The first new positive-dimensional test case is codimension one on
`P¹_ℂ × P¹_ℂ`. Its intended witness is `a [fiber₁] + b [fiber₂]` for the
class with Betti coordinates `(a,b)`. This is a test of the witness mechanism,
not a replacement for the arbitrary `X,p,α` goal.

## Product checkpoint (2026-11-15)

- `Geometry/ProjectiveLineProduct.lean` constructs the actual scheme fiber
  product and projections over `Spec k`. `ProjectiveLineProductSections.lean`
  constructs a rational zero section, proves it is a closed immersion, and
  pairs it with the identity to give both coordinate maps from `P¹`.
- `Geometry/ProjectiveLineProductComplexPoints.lean` proves that complex
  points of the scheme product are in bijection with pairs of complex points
  of `P¹`, and that the projection to that pair is continuous.
- `Geometry/AffineComplexPointsProduct.lean` proves that the original
  evaluation topology on complex-algebra points of `A ⊗[ℂ] B` is the product
  topology on the two factor point spaces.
- `Geometry/ProjectiveLineProductTopology.lean` glues that affine comparison
  over the four actual open scheme charts, proving the global homeomorphism
  between complex points of the scheme product and the product of the two
  canonical projective-line point spaces.
- `Geometry/ProjectiveLineProductAffineChart.lean` constructs an actual open
  product chart `Spec (k[X] ⊗ₖ k[X])` and computes both projection maps on its
  tensor factors. `ProjectiveLineProductAffineDimension.lean` identifies that
  ring with a two-variable polynomial ring and proves it has Krull dimension
  two. `ProjectiveLineProductAffinePrime.lean` proves that the ideal generated
  by the first coordinate variable has height one. The later fiber
  codimension module computes the height of each actual generic point in
  this affine chart.
- `Cycles/ProjectiveLineProductFibers.lean` constructs both actual closed
  fiber subschemes by pulling back point-closure ideal sheaves and proves
  their support formulas. `ProjectiveLineProductIntegralCandidates.lean`
  constructs two integral reduced closures inside the zero fibers, with
  generic projection onto the free coordinate.
- `Geometry/ProjectiveLineProductZeroFibers.lean` proves both zero-coordinate
  maps are closed immersions by identifying them with base changes of the
  zero section. `Cycles/ProjectiveLineProductZeroCarriers.lean` identifies
  their integral closed images with the earlier reduced closures and proves
  both carrier schemes are isomorphic to `P¹`. It also identifies their ideal
  sheaves with the pulled-back zero-point ideals, so the exact
  scheme-theoretic zero fibers are integral.
- `Cycles/ProjectiveLineProductChowClasses.lean` puts each actual fiber's
  fundamental cycle in the degree-one cycle module of the product's
  field-induced dimension function, maps it into the ordinary degree-one
  Chow quotient, and rationalizes it. The generic-point lift and
  finite-type dimension calculation in
  `Cycles/ProjectiveLineProductFiberCodimension.lean` prove that both
  integral carriers have support codimension one in the product.
- `Realization/Betti/ProjectiveLineProductClasses.lean` constructs the two
  canonical singular `H²` projection-pullback classes and proves their linear
  independence by restriction to the coordinate maps. The P¹ generator is
  the established image of the actual infinity Chow class. The product
  cycle-class comparison remains open.
- `Realization/Betti/ProjectiveLineDegreeOne.lean` proves the actual rational
  `H¹(P¹(ℂ)) = 0`: path connectedness makes degree-zero overlap classes
  constant, the chart-difference map is surjective, and singular
  Mayer–Vietoris exactness finishes the proof. This is an input to the
  product degree-two calculation.
- `Realization/Betti/ProjectiveLinePointGysin.lean` constructs the actual
  supported Thom/excision Gysin map for the distinguished zero point of
  `P¹`. `ProjectiveLineGysinCycleClass.lean` proves its unit matches the
  original zero-point Chow class and factors the degree-normalized rational
  Chow map through this point Gysin. This is a specific point construction,
  not a general closed-point or higher-codimension cycle map.
- `Realization/Betti/ProjectiveLineProductSpanningCriterion.lean` proves that
  the two fiber probes split off `ℚ²` inside actual product `H²`. Its
  Mayer–Vietoris criterion proves spanning from three local inputs on a
  two-open product cover: a one-dimensional overlap `H¹`, one chart's `H²`
  generated by the second projection class, and injectivity of the opposite
  chart's `H²` restriction to the overlap. The stronger criterion derives the
  boundary normalization from vanishing of the first class on both charts.
  The later chart and overlap modules supply these inputs.
- `Realization/Betti/ProductContractibleFactor.lean` proves that projection
  `A × Y → Y` induces an isomorphism in original singular cohomology when
  `A` is contractible, and transports a one-dimensional generator through
  that actual pullback. The product chart module now specializes it.
- `Realization/Betti/ProjectiveLineProductAffineChartH2.lean` identifies both
  first-factor affine chart point spaces with `A¹(ℂ) × P¹(ℂ)`, proves they
  cover the actual scheme-product complex points, and identifies the second
  scheme projection on chart points. Its `chartH2Iso` transports chart
  cohomology to the topological product. `chartH2Iso_secondClass` identifies
  the restricted actual `secondClass` with the contractible-factor pullback;
  `chartH2_generated` proves that class spans `H²` on either chart.
  `chart_firstClass_eq_zero` proves the first projection class vanishes on
  both chart restrictions.
- `Realization/Betti/ProjectiveLineProductAffineOverlapH2.lean` fixes first
  affine coordinate one to obtain a section through the actual chart
  overlap. Pullback of the restricted second class along this section is
  the nonzero projective-line generator; because the second class spans
  chart `H²`, restriction from the opposite chart to overlap is injective.
- `Realization/Betti/ProjectiveLineProductOverlapH1.lean` computes
  `H¹(ℂ*,ℚ) ≃ ℚ` from the circle and proves its generator stays nonzero in
  `H¹(ℂ* × P¹,ℚ)` by a fixed-point section.
  `ProductSecondFactorCover.lean` constructs the actual second-factor
  product cover and proves its degree-zero Mayer–Vietoris difference is
  surjective under path-connected overlap hypotheses.
  `ProductSecondFactorH1Local.lean` computes each contractible second-factor
  chart's `H¹` from the first factor, and
  `ProductSecondFactorH1Criterion.lean` reduces the product `H¹` span to
  those chart restrictions and a nonzero overlap restriction.
  `ProjectiveLineProductOverlapH1Spanning.lean` discharges these inputs for
  `ℂ* × P¹`, proving that its rational `H¹` is generated by the pulled-back
  punctured-line class.
- `Realization/Betti/ProjectiveLineProductAffineOverlapTopology.lean`
  identifies the actual first-factor chart intersection with `ℂ* × P¹`.
  `ProjectiveLineProductAlmostSpanning.lean` packages all other
  Mayer–Vietoris inputs into one overlap `H¹` hypothesis, and
  `ProjectiveLineProductSpanning.lean` transports the calculated generator
  through the homeomorphism, proves the two projection classes span actual
  product `H²`, and constructs the fiber-probe linear equivalence
  `H²(P¹ × P¹, ℚ) ≃ₗ[ℚ] ℚ × ℚ`.
- `ProjectiveLineProductFiberClassInputs.lean` identifies each product Betti
  basis class as the projection pullback of the already proved zero-point
  Chow/Gysin class on `P¹`, and identifies each fiber carrier ideal with
  the corresponding pulled-back point ideal.
  `ProjectiveLineProductFiberSupportedClass.lean` pulls the actual
  zero-point relative Thom class back to each product projection. Its
  simplicial complement is exactly the complement of the corresponding
  scheme-theoretic zero fiber, and forgetting support yields the two
  product Betti basis classes.
  `ProjectiveLineProductFiberChowBettiData.lean` binds each actual
  codimension-one carrier, its named ordinary Chow classes, exact fiber
  support, and pulled-back Thom class in one checked certificate.
  `ProjectiveLineProductFiberPairedWitness.lean` uses the Betti basis
  coordinates of any class to construct a rational combination of the
  actual fiber cycles, its ordinary Chow class, and the matching supported
  Betti combination. The supported combination forgets to that class.

The focused `make check-projective-line-product` target builds the product
topology and H² basis modules and audits 68 selected declarations for only
`propext`, `Classical.choice`, and `Quot.sound`. The separate
`make check-projective-line-product-fibers` target builds the added
fiber Chow, codimension, certificate, supported-class, and paired-witness
modules and audits 40 selected declarations under the same boundary.
The remaining comparison is a product ordinary Chow-to-Betti cycle-class
map respecting rational equivalence, with the two fiber classes sent to
these independently constructed supported Betti classes.

## Work order

1. Completed: prove the analytic product homeomorphism from the affine
   tensor-product evaluation comparison and four open product charts.
2. Completed: prove an actual singular `H²` spanning theorem for the
   product, using Mayer–Vietoris on the first-factor affine chart cover.
3. Completed: compute codimension one for both integral zero fibers using
   their affine generic-point lifts, form their ordinary degree-one Chow
   classes, and construct supported Betti fiber classes equal to the
   independently computed product basis after forgetting support. The
   paired construction uses these basis coordinates for every product
   Betti class.
4. Prove the ordinary product Chow-to-Betti cycle-class compatibility for
   those two fibers, then use the basis coordinates to exhibit the
   coefficientwise Chow witness.
5. For the general target, supply a class-dependent geometric construction
   of cycles or support and prove its Betti class identity. The current
   finite-cover, normalization, and fixed-inertia results support this step
   but do not themselves produce `z` for a prescribed `α`.

The Chen–Hu symmetric-product calculation is a useful finite-quotient
Chow/Betti transfer model, but its general coarse quotients are singular and
its rational cycle-class isomorphism does not construct witnesses for
arbitrary smooth projective varieties. See [SOURCE_LEDGER.md](../SOURCE_LEDGER.md).
