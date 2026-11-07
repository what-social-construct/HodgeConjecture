module

public import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriodComparison
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The actual positive boundary pairing, genuine tensor extension, analytic
overlap period, and independently constructed ordinary Chow maps are checked
together. An imaginary scalar checks that the complex target is larger
than the embedded rational singular lattice.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct HodgeConjecture KaehlerDifferential
open ProjectiveLineDeRham ProjectiveLineBettiComplexification ProjectiveLinePeriodComparison

namespace ProjectiveLinePeriodComparisonVerification

example : ProjectiveLineBettiOrientation.boundaryPairing
    ProjectiveLineBettiCohomology.coverGenerator = 1 :=
  ProjectiveLineBettiOrientation.boundaryPairing_coverGenerator

example : Function.Injective rationalEmbedding := rationalEmbedding_injective

example (c : ℂ) : complexBoundaryPairing
    (c ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator) = c := by simp

theorem imaginaryTensor_not_rational :
    (Complex.I ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator) ∉
      Set.range rationalEmbedding := by
  rintro ⟨z, hz⟩
  have hc := congrArg coordinates hz
  simp only [coordinates_rationalEmbedding, coordinates_tmul,
    ProjectiveLineBettiCohomology.h2Equiv_coverGenerator, Rat.cast_one, mul_one] at hc
  have hi := congrArg Complex.im hc
  norm_num at hi

example (z : SchemeH2 ℂ) :
    complexBoundaryPairing (comparison z) = ProjectiveLinePeriods.schemeIntegral z :=
  boundaryPeriod_comparison z

example (f : SchemeH2 ℂ →ₗ[ℂ] Complexification)
    (hf : ∀ z, complexBoundaryPairing (f z) = ProjectiveLinePeriods.schemeIntegral z) :
    f = comparison.toLinearMap := comparison_unique f hf

example : comparison (schemeChernCoordinate ℂ) =
    (2 * Real.pi * Complex.I) ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator :=
  comparison_chernCoordinate

example : normalizedComparison (schemeChernCoordinate ℂ) =
    rationalEmbedding ProjectiveLineBettiCohomology.coverGenerator := by
  apply coordinates.injective
  rw [coordinates_normalizedComparison, ProjectiveLinePeriods.normalizedSchemeIntegral_eq_residue,
    schemeResidueEquiv_chernCoordinate, coordinates_rationalEmbedding,
    ProjectiveLineBettiCohomology.h2Equiv_coverGenerator, Rat.cast_one]

example : comparison (schemeOverlapClass ℂ (LaurentDeRham.dlogT ℂ)) =
    (2 * Real.pi * Complex.I) ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator := by
  rw [comparison_overlapClass, LaurentPeriods.integral_dlogT]

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    complexBoundaryPairing (comparison (schemeOverlapClass ℂ ω)) =
      LaurentOrientedArcs.firstArcIntegral ω + LaurentOrientedArcs.secondArcIntegral ω :=
  boundaryPeriod_overlapClass_twoArcs ω

example (c : ℂ) : comparison (c • schemeChernCoordinate ℂ) =
    (c * (2 * Real.pi * Complex.I)) ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator := by
  rw [map_smul, comparison_chernCoordinate]
  simp only [smul_tmul', smul_eq_mul, period]

example (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    normalizedComparison
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
      rationalEmbedding (ProjectiveLineBettiCycleClass.cycleClass z) :=
  normalizedComparison_cycleClass z

example (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    comparison
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
      (2 * Real.pi * Complex.I) • rationalEmbedding (ProjectiveLineBettiCycleClass.cycleClass z) :=
  comparison_cycleClass z

example : Function.Surjective ProjectiveLineBettiCycleClass.cycleClass :=
  ProjectiveLineBettiCycleClass.cycleClass_surjective

end ProjectiveLinePeriodComparisonVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineBettiOrientation.boundaryPairing,
      `HodgeConjecture.ProjectiveLineBettiOrientation.boundaryPairing_eq_coordinate,
      `HodgeConjecture.ProjectiveLineBettiOrientation.boundaryPairing_coverGenerator,
      `HodgeConjecture.ProjectiveLineBettiComplexification.coordinates,
      `HodgeConjecture.ProjectiveLineBettiComplexification.coordinates_tmul,
      `HodgeConjecture.ProjectiveLineBettiComplexification.rationalEmbedding,
      `HodgeConjecture.ProjectiveLineBettiComplexification.coordinates_rationalEmbedding,
      `HodgeConjecture.ProjectiveLineBettiComplexification.coordinates_tmul_boundaryPairing,
      `HodgeConjecture.ProjectiveLineBettiComplexification.complexBoundaryPairing,
      `HodgeConjecture.ProjectiveLineBettiComplexification.complexBoundaryPairing_tmul,
      `HodgeConjecture.ProjectiveLineBettiComplexification.complexBoundaryPairing_eq_coordinates,
      `HodgeConjecture.ProjectiveLineBettiComplexification.rationalEmbedding_injective,
      `HodgeConjecture.ProjectiveLineBettiComplexification.coordinates_symm_apply,
      `HodgeConjecture.ProjectiveLineBettiComplexification.eq_tmul_coverGenerator,
      `HodgeConjecture.ProjectiveLinePeriodComparison.period_ne_zero,
      `HodgeConjecture.ProjectiveLinePeriodComparison.schemePeriodEquiv,
      `HodgeConjecture.ProjectiveLinePeriodComparison.schemePeriodEquiv_apply,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison,
      `HodgeConjecture.ProjectiveLinePeriodComparison.coordinates_comparison,
      `HodgeConjecture.ProjectiveLinePeriodComparison.boundaryPeriod_comparison,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison_unique,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison_overlapClass,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison_overlapClass_twoArcs,
      `HodgeConjecture.ProjectiveLinePeriodComparison.boundaryPeriod_overlapClass_twoArcs,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison_chernCoordinate,
      `HodgeConjecture.ProjectiveLinePeriodComparison.normalizedComparison,
      `HodgeConjecture.ProjectiveLinePeriodComparison.coordinates_normalizedComparison,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison_eq_period_smul,
      `HodgeConjecture.ProjectiveLinePeriodComparison.normalizedComparison_cycleClass,
      `HodgeConjecture.ProjectiveLinePeriodComparison.comparison_cycleClass,
      `ProjectiveLinePeriodComparisonVerification.imaginaryTensor_not_rational] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
