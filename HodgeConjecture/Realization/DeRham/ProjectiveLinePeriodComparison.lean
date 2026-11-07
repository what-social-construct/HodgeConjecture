module

public import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods
public import HodgeConjecture.Realization.DeRham.LaurentOrientedArcs
public import HodgeConjecture.Realization.Betti.ProjectiveLineComplexification
public import HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass

@[expose] public section

/-!
# The projective-line comparison fixed by its boundary period

The actual Laurent integral, descended to actual scheme de Rham H²,
specifies a map to the genuine tensor complexification of independently
computed rational singular H². On every original overlap representative
its coefficient is that actual integral. The unnormalized Chern period
is 2πi; dividing by this period intertwines the independently constructed
ordinary Chow maps. This is a bounded period comparison, not a general
analytic sheaf comparison or a construction of Poincaré duality.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLinePeriodComparison

open CategoryTheory TensorProduct ProjectiveLineDeRham KaehlerDifferential
open ProjectiveLineBettiComplexification

/-- The actual complex unit-circle period. -/
def period : ℂ := 2 * Real.pi * Complex.I

theorem period_ne_zero : period ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The actual descended scheme integral is a linear equivalence for this computed P¹. -/
def schemePeriodEquiv : SchemeH2 ℂ ≃ₗ[ℂ] ℂ :=
  (schemeResidueEquiv ℂ).trans (LinearEquiv.smulOfNeZero ℂ ℂ period period_ne_zero)

theorem schemePeriodEquiv_apply (z : SchemeH2 ℂ) :
    schemePeriodEquiv z = ProjectiveLinePeriods.schemeIntegral z :=
  (ProjectiveLinePeriods.schemeIntegral_eq_residue z).symm

/-- The unique comparison with the original analytic boundary period as its tensor coordinate. -/
def comparison : SchemeH2 ℂ ≃ₗ[ℂ] Complexification :=
  schemePeriodEquiv.trans coordinates.symm

@[simp]
theorem coordinates_comparison (z : SchemeH2 ℂ) :
    coordinates (comparison z) = ProjectiveLinePeriods.schemeIntegral z := by
  change coordinates (coordinates.symm (schemePeriodEquiv z)) = _
  rw [LinearEquiv.apply_symm_apply, schemePeriodEquiv_apply]

/-- The comparison preserves the actual analytic period and the actual positive boundary pairing. -/
theorem boundaryPeriod_comparison (z : SchemeH2 ℂ) :
    complexBoundaryPairing (comparison z) = ProjectiveLinePeriods.schemeIntegral z := by
  rw [complexBoundaryPairing_eq_coordinates]
  exact coordinates_comparison z

/-- This actual period identity uniquely specifies the comparison on the original scheme target. -/
theorem comparison_unique (f : SchemeH2 ℂ →ₗ[ℂ] Complexification)
    (hf : ∀ z, complexBoundaryPairing (f z) = ProjectiveLinePeriods.schemeIntegral z) :
    f = comparison.toLinearMap := by
  apply LinearMap.ext
  intro z
  change f z = comparison z
  apply coordinates.injective
  rw [coordinates_comparison]
  have h := hf z
  rw [complexBoundaryPairing_eq_coordinates] at h
  change coordinates (f z) = ProjectiveLinePeriods.schemeIntegral z at h
  exact h

/-- Every actual overlap form retains its actual, unnormalized analytic circle integral. -/
theorem comparison_overlapClass (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    comparison (schemeOverlapClass ℂ ω) =
      LaurentPeriods.integral ω ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator := by
  apply coordinates.injective
  rw [coordinates_comparison, ProjectiveLinePeriods.schemeIntegral_overlapClass,
    coordinates_tmul, ProjectiveLineBettiCohomology.h2Equiv_coverGenerator]
  simp

/-- The same period is the actual derivative-weighted integral over the two positive arcs. -/
theorem comparison_overlapClass_twoArcs (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    comparison (schemeOverlapClass ℂ ω) =
      LaurentOrientedArcs.twoArcIntegral ω ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator := by
  rw [comparison_overlapClass, LaurentOrientedArcs.integral_eq_twoArcIntegral]

/-- Original cohomological boundary pairing agrees with integration over those same angular arcs. -/
theorem boundaryPeriod_overlapClass_twoArcs (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    complexBoundaryPairing (comparison (schemeOverlapClass ℂ ω)) =
      LaurentOrientedArcs.twoArcIntegral ω := by
  rw [boundaryPeriod_comparison, ProjectiveLinePeriods.schemeIntegral_overlapClass,
    LaurentOrientedArcs.integral_eq_twoArcIntegral]

theorem comparison_chernCoordinate :
    comparison (schemeChernCoordinate ℂ) =
      period ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator := by
  apply coordinates.injective
  rw [coordinates_comparison, ProjectiveLinePeriods.schemeIntegral_chernCoordinate,
    coordinates_tmul, ProjectiveLineBettiCohomology.h2Equiv_coverGenerator]
  simp [period]

/-- The Tate-normalized period comparison on the same genuine tensor target. -/
def normalizedComparison : SchemeH2 ℂ ≃ₗ[ℂ] Complexification :=
  (schemeResidueEquiv ℂ).trans coordinates.symm

@[simp]
theorem coordinates_normalizedComparison (z : SchemeH2 ℂ) :
    coordinates (normalizedComparison z) = ProjectiveLinePeriods.normalizedSchemeIntegral z := by
  change coordinates (coordinates.symm (schemeResidueEquiv ℂ z)) = _
  rw [LinearEquiv.apply_symm_apply, ProjectiveLinePeriods.normalizedSchemeIntegral_eq_residue]

theorem comparison_eq_period_smul (z : SchemeH2 ℂ) :
    comparison z = period • normalizedComparison z := by
  apply coordinates.injective
  rw [coordinates_comparison, map_smul, coordinates_normalizedComparison,
    ProjectiveLinePeriods.normalizedSchemeIntegral_eq_residue,
    ProjectiveLinePeriods.schemeIntegral_eq_residue]
  rfl

/-- The independently constructed ordinary Betti and scheme maps agree after period normalization. -/
theorem normalizedComparison_cycleClass
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    normalizedComparison
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
      rationalEmbedding (ProjectiveLineBettiCycleClass.cycleClass z) := by
  apply coordinates.injective
  rw [coordinates_normalizedComparison, ProjectiveLinePeriods.normalizedSchemeIntegral_cycleClass,
    coordinates_rationalEmbedding, ProjectiveLineBettiCycleClass.coordinate_cycleClass]

/-- The unnormalized comparison retains the actual factor 2πi on ordinary cycle classes. -/
theorem comparison_cycleClass
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    comparison
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
      period • rationalEmbedding (ProjectiveLineBettiCycleClass.cycleClass z) := by
  rw [comparison_eq_period_smul, normalizedComparison_cycleClass]

end HodgeConjecture.ProjectiveLinePeriodComparison
