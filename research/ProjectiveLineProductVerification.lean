module

public import HodgeConjecture.Geometry.AffineComplexPointsProduct
public import HodgeConjecture.Geometry.ProjectiveLineProductComplexPoints
public import HodgeConjecture.Geometry.ProjectiveLineProductTopology
public import HodgeConjecture.Geometry.ProjectiveLineProductAffinePrime
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriers
public import HodgeConjecture.Realization.Betti.ProductContractibleFactor
public import HodgeConjecture.Realization.Betti.ProductSecondFactorCover
public import HodgeConjecture.Realization.Betti.ProductSecondFactorH1Local
public import HodgeConjecture.Realization.Betti.ProductSecondFactorH1Criterion
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductOverlapH1
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductOverlapH1Spanning
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineChartH2
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineOverlapH2
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineOverlapTopology
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductAlmostSpanning
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanning
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanningCriterion
public import HodgeConjecture.Realization.Betti.ProjectiveLineDegreeOne
public import Lean.Util.CollectAxioms

/-!
Focused axiom audit for the geometric and Betti parts of the P¹ × P¹
Chow-witness checkpoint. This verifies the actual declarations that exist;
it does not assert codimension, a product cycle-class square, or H² spanning.
-/

@[expose] public section

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `AlgebraicGeometry.projectiveLineProductSnd_comp_structureMorphism,
      `AlgebraicGeometry.projectiveLineZeroSection_comp_structureMorphism,
      `AlgebraicGeometry.projectiveLineProductZeroFirst_fst,
      `AlgebraicGeometry.projectiveLineProductZeroSecond_snd,
      `AlgebraicGeometry.projectiveLineProductAffineChart_fst,
      `AlgebraicGeometry.projectiveLineProductAffineChart_snd,
      `AlgebraicGeometry.projectiveLineAffineProduct_ringKrullDim,
      `AlgebraicGeometry.projectiveLineAffineProduct_firstVariable_height_one,
      `AlgebraicGeometry.projectiveLineAffineProduct_secondVariable_height_one,
      `AlgebraicGeometry.projectiveLineProductZeroFirstPullbackIso,
      `AlgebraicGeometry.projectiveLineProductZeroSecondPullbackIso,
      `AlgebraicGeometry.projectiveLineProductZeroFirstCarrierIso,
      `AlgebraicGeometry.projectiveLineProductZeroSecondCarrierIso,
      `AlgebraicGeometry.projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal,
      `AlgebraicGeometry.projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal,
      `AlgebraicGeometry.projectiveLineProduct_firstZeroFiber_isIntegral,
      `AlgebraicGeometry.projectiveLineProduct_secondZeroFiber_isIntegral,
      `AlgebraicGeometry.projectiveLineProduct_firstOriginFiber_isIntegral,
      `AlgebraicGeometry.projectiveLineProduct_secondOriginFiber_isIntegral,
      `HodgeConjecture.AffineComplexPointsProduct.pointEquiv,
      `HodgeConjecture.AffineComplexPointsProduct.homeomorph,
      `HodgeConjecture.ProjectiveLineProductComplexPoints.pointsEquiv,
      `HodgeConjecture.ProjectiveLineProductComplexPoints.continuous_pointsEquiv,
      `HodgeConjecture.ProjectiveLineProductComplexPoints.continuous_pointsEquiv_symm,
      `HodgeConjecture.ProjectiveLineProductComplexPoints.pointsHomeomorph,
      `HodgeConjecture.ProjectiveLineProductFibers.mem_firstFiber_support,
      `HodgeConjecture.ProjectiveLineProductFibers.mem_secondFiber_support,
      `HodgeConjecture.ProjectiveLineProductIntegralCandidates.firstZeroCarrier_support_le_fiber,
      `HodgeConjecture.ProjectiveLineProductIntegralCandidates.secondZeroCarrier_support_le_fiber,
      `HodgeConjecture.ProjectiveLineProductBetti.lineGenerator_eq_cycleClass_infinity,
      `HodgeConjecture.ProjectiveLineProductBetti.classes_independent,
      `HodgeConjecture.ProjectiveLineProductBetti.coordinateProbe_section,
      `HodgeConjecture.ProjectiveLineProductBetti.coordinateProbe_surjective,
      `HodgeConjecture.ProjectiveLineProductBetti.classes_span_of_coordinateProbe_injective,
      `HodgeConjecture.ProjectiveLineProductBetti.classes_span_of_mayer_vietoris,
      `HodgeConjecture.ProjectiveLineProductBetti.classes_span_of_local_cover,
      `HodgeConjecture.ProductContractibleFactor.projectionHomotopyEquiv,
      `HodgeConjecture.ProductContractibleFactor.cohomologyIso_hom,
      `HodgeConjecture.ProductContractibleFactor.cohomology_generated,
      `HodgeConjecture.ProductSecondFactorCover.chartHomeomorph,
      `HodgeConjecture.ProductSecondFactorCover.chart_cover,
      `HodgeConjecture.ProductSecondFactorCover.difference_zero_surjective,
      `HodgeConjecture.ProductSecondFactorH1Local.chartH1Iso_hom,
      `HodgeConjecture.ProductSecondFactorH1Local.chartH1_generated,
      `HodgeConjecture.ProductSecondFactorH1Criterion.generated_of_chart_data,
      `HodgeConjecture.ProjectiveLineProductOverlapH1.planeH1Coordinate,
      `HodgeConjecture.ProjectiveLineProductOverlapH1.planeH1_generated,
      `HodgeConjecture.ProjectiveLineProductOverlapH1.planeProjection_pullback_injective,
      `HodgeConjecture.ProjectiveLineProductOverlapH1.planeGenerator_product_ne_zero,
      `HodgeConjecture.ProjectiveLineProductOverlapH1.productH1_generated,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chartHomeomorph,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chartSet_cover,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chart_secondProjection_map,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chartH2Iso,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chartH2Iso_secondClass,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chartH2_generated,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chartH2Iso_firstClass_eq_zero,
      `HodgeConjecture.ProjectiveLineProductAffineChartH2.chart_firstClass_eq_zero,
      `HodgeConjecture.ProjectiveLineProductAffineOverlapH2.overlapSection_pullback_secondClass,
      `HodgeConjecture.ProjectiveLineProductAffineOverlapH2.overlapRestriction_injective,
      `HodgeConjecture.ProjectiveLineProductAffineOverlapH2.overlapHomeomorph,
      `HodgeConjecture.ProjectiveLineProductAlmostSpanning.classes_span_of_overlapH1_generated,
      `HodgeConjecture.ProjectiveLineProductSpanning.canonicalOverlapHomeomorph,
      `HodgeConjecture.ProjectiveLineProductSpanning.overlapH1_generated,
      `HodgeConjecture.ProjectiveLineProductSpanning.classes_span,
      `HodgeConjecture.ProjectiveLineProductSpanning.coordinateProbe_injective,
      `HodgeConjecture.ProjectiveLineProductSpanning.coordinateEquiv,
      `HodgeConjecture.ProjectiveLineDegreeOne.isZero_h1] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end
