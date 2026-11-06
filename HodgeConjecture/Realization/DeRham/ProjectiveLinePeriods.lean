module

public import HodgeConjecture.Realization.DeRham.LaurentPeriods
public import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeCycleClass
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# Projective-line analytic period and ordinary cycles

The actual Laurent unit-circle integral annihilates the entire incoming
Čech–de Rham differential. It therefore descends to the original Čech H²
and, through the proved scheme comparison, to actual scheme de Rham H².
Dividing this analytic integral by `2πi` recovers the original rational
degree on ordinary rational Chow classes. No singular H² computation or
Betti comparison is supplied by this analytic normalization.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLinePeriods

open KaehlerDifferential AffineDeRham ProjectiveLineDeRham CategoryTheory

/-- Integrate the coefficient of an actual closed overlap one-form. -/
def closedFormIntegral : closedForms ℂ (LaurentPolynomial ℂ) 1 →ₗ[ℂ] ℂ :=
  LaurentPeriods.integralLinear.comp
    ((LinearMap.restrictScalars ℂ
      (exteriorPower.oneEquiv (LaurentPolynomial ℂ) Ω[LaurentPolynomial ℂ⁄ℂ]).toLinearMap).comp
        (closedForms ℂ (LaurentPolynomial ℂ) 1).subtype)

theorem closedFormIntegral_eq_residue (ω : closedForms ℂ (LaurentPolynomial ℂ) 1) :
    closedFormIntegral ω = (2 * Real.pi * Complex.I) * LaurentDeRham.closedFormResidue ℂ ω :=
  LaurentPeriods.integral_eq_two_pi_I_mul_residue _

/-- All total boundaries have zero analytic integral, including both chart one-form terms. -/
theorem cechBoundaries_le_ker_integral :
    cechBoundaries ℂ ≤ LinearMap.ker closedFormIntegral := by
  intro ω hω
  have h := cechBoundaries_le_ker_residue ℂ hω
  change LaurentDeRham.closedFormResidue ℂ ω = 0 at h
  change closedFormIntegral ω = 0
  rw [closedFormIntegral_eq_residue, h, mul_zero]

/-- Quotient descent of the actual analytic integral through the original total boundaries. -/
def cechIntegral : CechH2 ℂ →ₗ[ℂ] ℂ :=
  (cechBoundaries ℂ).liftQ closedFormIntegral cechBoundaries_le_ker_integral

theorem cechIntegral_eq_residue (z : CechH2 ℂ) :
    cechIntegral z = (2 * Real.pi * Complex.I) * cechResidue ℂ z := by
  obtain ⟨ω, rfl⟩ := (cechBoundaries ℂ).mkQ_surjective z
  exact closedFormIntegral_eq_residue ω

/-- Every actual overlap representative is evaluated by its original unit-circle integral. -/
theorem cechIntegral_overlapClass (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    cechIntegral (overlapClass ℂ ω) = LaurentPeriods.integral ω := by
  change LaurentPeriods.integral
    ((exteriorPower.oneEquiv (LaurentPolynomial ℂ) Ω[LaurentPolynomial ℂ⁄ℂ])
      ((exteriorPower.oneEquiv (LaurentPolynomial ℂ) Ω[LaurentPolynomial ℂ⁄ℂ]).symm ω)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Carry the proved quotient period to actual scheme de Rham hypercohomology. -/
def schemeIntegral : SchemeH2 ℂ →ₗ[ℂ] ℂ :=
  cechIntegral.comp (schemeComparisonIso ℂ).inv.hom

theorem schemeIntegral_comparison (z : CechH2 ℂ) :
    schemeIntegral ((schemeComparisonIso ℂ).hom z) = cechIntegral z := by
  change cechIntegral ((schemeComparisonIso ℂ).toLinearEquiv.symm
    ((schemeComparisonIso ℂ).toLinearEquiv z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- In particular the period of the actual signed Mayer–Vietoris overlap class is the analytic
integral of its original differential, with the sign fixed by the constructed scheme bridge. -/
theorem schemeIntegral_overlapClass (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    schemeIntegral (schemeOverlapClass ℂ ω) = LaurentPeriods.integral ω := by
  rw [← schemeComparisonIso_overlapClass, schemeIntegral_comparison, cechIntegral_overlapClass]

theorem schemeIntegral_eq_residue (z : SchemeH2 ℂ) :
    schemeIntegral z = (2 * Real.pi * Complex.I) * schemeResidueEquiv ℂ z :=
  cechIntegral_eq_residue _

@[simp]
theorem schemeIntegral_chernCoordinate :
    schemeIntegral (schemeChernCoordinate ℂ) = 2 * Real.pi * Complex.I := by
  rw [schemeIntegral_eq_residue, schemeResidueEquiv_chernCoordinate, mul_one]

/-- The usual `2πi` normalization of the actual analytic scheme period. -/
def normalizedSchemeIntegral : SchemeH2 ℂ →ₗ[ℂ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • schemeIntegral

theorem normalizedSchemeIntegral_eq_residue (z : SchemeH2 ℂ) :
    normalizedSchemeIntegral z = schemeResidueEquiv ℂ z := by
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  change (2 * Real.pi * Complex.I : ℂ)⁻¹ * schemeIntegral z = _
  rw [schemeIntegral_eq_residue, inv_mul_cancel_left₀ hp]

/-- On every class in the original ordinary rational Chow quotient the normalized analytic
period is its actual rational degree, embedded in `ℂ`. -/
theorem normalizedSchemeIntegral_cycleClass
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    normalizedSchemeIntegral
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ) (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
        (ProjectiveLineCycles.rationalChowDegree ℂ z : ℂ) := by
  rw [normalizedSchemeIntegral_eq_residue, ProjectiveLineSchemeCycleClass.residue_cycleClass]

end HodgeConjecture.ProjectiveLinePeriods
