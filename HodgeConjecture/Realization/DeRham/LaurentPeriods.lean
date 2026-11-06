module

public import HodgeConjecture.Realization.DeRham.LaurentDifferentials
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

/-!
# Analytic periods of actual Laurent differentials

Evaluate the finite Laurent series of an actual Kähler form on the punctured
complex line and integrate it around the positively oriented unit circle.
The resulting analytic integral is `2πi` times the algebraic residue. This
is a period calculation; no singular-cohomology comparison is assumed here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.LaurentPeriods

open LaurentPolynomial KaehlerDifferential
open scoped Real

/-- Scalar multiples of a complex integer-power function. -/
def powerFunction (n : ℤ) : ℂ →ₗ[ℂ] (ℂ → ℂ) where
  toFun a z := a * z ^ n
  map_add' a b := by ext z; exact add_mul a b _
  map_smul' a b := by ext z; simp [mul_assoc]

/-- Finite Laurent evaluation, with an integer shift of the exponents.
Only its values away from zero will be used analytically. -/
def shiftedEvaluation (s : ℤ) : LaurentPolynomial ℂ →ₗ[ℂ] (ℂ → ℂ) :=
  (Finsupp.lsum ℂ fun n ↦ powerFunction (n + s)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp]
theorem shiftedEvaluation_single (s n : ℤ) (a z : ℂ) :
    shiftedEvaluation s (.single n a) z = a * z ^ (n + s) := by
  simp only [shiftedEvaluation, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.lsum_single, powerFunction, LinearMap.coe_mk, AddHom.coe_mk]

@[simp]
theorem shiftedEvaluation_monomial (s n : ℤ) (a z : ℂ) :
    shiftedEvaluation s (C a * T n) z = a * z ^ (n + s) := by
  rw [← single_eq_C_mul_T, shiftedEvaluation_single]

/-- At a nonzero complex point this is the original Laurent algebra evaluation. -/
theorem shiftedEvaluation_zero_eq_eval₂ (f : LaurentPolynomial ℂ) (z : ℂ) (hz : z ≠ 0) :
    shiftedEvaluation 0 f z =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 z hz) f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Pi.add_apply, hf, hg]
  | C_mul_T n a => simp

theorem shiftedEvaluation_neg_one (f : LaurentPolynomial ℂ) (z : ℂ) (hz : z ≠ 0) :
    shiftedEvaluation (-1) f z = shiftedEvaluation 0 f z * z⁻¹ := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simp only [map_add, Pi.add_apply, hf, hg, add_mul]
  | C_mul_T n a => simp [zpow_add₀ hz, mul_assoc]

/-- The coefficient of `dz` in an actual Kähler differential, evaluated analytically. -/
def coefficientFunction (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : ℂ → ℂ :=
  shiftedEvaluation (-1) (LaurentDeRham.kaehlerCoordinates ℂ ω)

/-- The analytic coefficient agrees with evaluation of the actual Laurent coefficient of
`dlog T`, divided by the coordinate. -/
theorem coefficientFunction_eq_eval₂ (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (z : ℂ) (hz : z ≠ 0) :
    coefficientFunction ω z =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 z hz)
        (LaurentDeRham.kaehlerCoordinates ℂ ω) * z⁻¹ := by
  rw [coefficientFunction, shiftedEvaluation_neg_one _ _ hz,
    shiftedEvaluation_zero_eq_eval₂ _ _ hz]

theorem circleIntegrable_power (n : ℤ) :
    CircleIntegrable (fun z : ℂ ↦ z ^ n) 0 1 := by
  simpa using (circleIntegrable_sub_zpow_iff (c := 0) (w := 0) (R := 1) (n := n)).2
    (Or.inr (Or.inr (by simp)))

theorem circleIntegrable_shiftedEvaluation (s : ℤ) (f : LaurentPolynomial ℂ) :
    CircleIntegrable (shiftedEvaluation s f) 0 1 := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => simpa only [map_add] using hf.add hg
  | C_mul_T n a =>
    convert (circleIntegrable_power (n + s)).const_smul (a := a) using 1
    ext z
    simp

theorem circleIntegral_shiftedEvaluation (f : LaurentPolynomial ℂ) :
    (∮ z in C(0, 1), shiftedEvaluation (-1) f z) =
      (2 * Real.pi * Complex.I) * LaurentDeRham.constantCoefficient ℂ f := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add, Pi.add_apply]
    rw [circleIntegral.integral_add (circleIntegrable_shiftedEvaluation _ f)
      (circleIntegrable_shiftedEvaluation _ g), hf, hg, mul_add]
  | C_mul_T n a =>
    simp_rw [shiftedEvaluation_monomial]
    rw [circleIntegral.integral_const_mul, ← single_eq_C_mul_T,
      LaurentDeRham.constantCoefficient_single]
    by_cases hn : n = 0
    · subst n
      have hi : (∮ z in C(0, 1), (z : ℂ)⁻¹) = 2 * Real.pi * Complex.I := by
        simpa only [sub_zero] using
          circleIntegral.integral_sub_center_inv (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)
      simp only [zero_add, zpow_neg_one, ↓reduceIte]
      rw [hi, mul_comm]
    · have hpower : n + -1 ≠ -1 := by omega
      have hi := circleIntegral.integral_sub_zpow_of_ne hpower (0 : ℂ) 0 1
      simpa [hn] using congrArg (a * ·) hi

/-- The actual, unnormalized unit-circle integral of the original universal differential. -/
def integral (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : ℂ :=
  ∮ z in C(0, 1), coefficientFunction ω z

/-- The analytic residue formula, proved by evaluating and integrating every Laurent monomial. -/
theorem integral_eq_two_pi_I_mul_residue (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    integral ω = (2 * Real.pi * Complex.I) * LaurentDeRham.kaehlerResidue ℂ ω :=
  circleIntegral_shiftedEvaluation _

/-- Linearity of the actual analytic integral on universal Kähler differentials. -/
def integralLinear : Ω[LaurentPolynomial ℂ⁄ℂ] →ₗ[ℂ] ℂ where
  toFun := integral
  map_add' ω η := by simp only [integral_eq_two_pi_I_mul_residue, map_add, mul_add]
  map_smul' a ω := by
    simp only [integral_eq_two_pi_I_mul_residue, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem integral_dlogT : integral (LaurentDeRham.dlogT ℂ) = 2 * Real.pi * Complex.I := by
  rw [integral_eq_two_pi_I_mul_residue, LaurentDeRham.kaehlerResidue_dlogT, mul_one]

@[simp]
theorem integral_exact (f : LaurentPolynomial ℂ) : integral (D ℂ (LaurentPolynomial ℂ) f) = 0 := by
  rw [integral_eq_two_pi_I_mul_residue, LaurentDeRham.kaehlerResidue_D, mul_zero]

/-- Divide the actual analytic integral by the usual complex period `2πi`. -/
def normalizedIntegral (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : ℂ :=
  integral ω / (2 * Real.pi * Complex.I)

theorem normalizedIntegral_eq_residue (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    normalizedIntegral ω = LaurentDeRham.kaehlerResidue ℂ ω := by
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [normalizedIntegral, integral_eq_two_pi_I_mul_residue, mul_div_cancel_left₀ _ hp]

@[simp]
theorem normalizedIntegral_dlogT : normalizedIntegral (LaurentDeRham.dlogT ℂ) = 1 := by
  rw [normalizedIntegral_eq_residue, LaurentDeRham.kaehlerResidue_dlogT]

end HodgeConjecture.LaurentPeriods
