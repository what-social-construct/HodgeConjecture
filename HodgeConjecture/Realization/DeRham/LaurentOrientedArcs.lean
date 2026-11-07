module

public import HodgeConjecture.Realization.DeRham.LaurentPeriods
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

@[expose] public section

/-!
# The analytic period on the two positive semicircles

The actual Laurent circle integral is the sum of the actual angular
integrals on [−π/2,π/2] and [π/2,3π/2]. Periodicity proves invariance
under the initial angle shift, and interval-integral additivity supplies
the split. The underlying curve is the original complex exponential.
This analytic module imports no project singular or geometric objects.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.LaurentOrientedArcs

open KaehlerDifferential MeasureTheory

/-- The native unit-circle curve is the same original complex exponential. -/
theorem unitCircleMap_eq_exp (θ : ℝ) : circleMap 0 1 θ = (Circle.exp θ : ℂ) := by
  simp [circleMap, Circle.coe_exp]

/-- The derivative-weighted actual Laurent coefficient in the angular parameter. -/
def angularIntegrand (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (θ : ℝ) : ℂ :=
  deriv (circleMap 0 1) θ • LaurentPeriods.coefficientFunction ω (circleMap 0 1 θ)

/-- The integrand uses the positive angular derivative of the original exponential curve. -/
theorem angularIntegrand_eq_exp (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (θ : ℝ) :
    angularIntegrand ω θ = ((Circle.exp θ : ℂ) * Complex.I) *
      LaurentPeriods.coefficientFunction ω (Circle.exp θ : ℂ) := by
  simp [angularIntegrand, deriv_circleMap, unitCircleMap_eq_exp, smul_eq_mul]

theorem angularIntegrand_periodic (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    Function.Periodic (angularIntegrand ω) (2 * Real.pi) := by
  intro θ
  simp only [angularIntegrand, deriv_circleMap, periodic_circleMap 0 1 θ]

/-- The actual integrand is integrable on every angular interval. -/
theorem angularIntegrand_intervalIntegrable (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (a b : ℝ) :
    IntervalIntegrable (angularIntegrand ω) volume a b := by
  apply (angularIntegrand_periodic ω).intervalIntegrable₀
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) ?_ a b
  exact (LaurentPeriods.circleIntegrable_shiftedEvaluation (-1)
    (LaurentDeRham.kaehlerCoordinates ℂ ω)).out

/-- The actual integral over the right semicircle, traversed with increasing angle. -/
def firstArcIntegral (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : ℂ :=
  ∫ θ in (-Real.pi / 2)..(Real.pi / 2), angularIntegrand ω θ

/-- The actual integral over the left semicircle, continuing with increasing angle. -/
def secondArcIntegral (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : ℂ :=
  ∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), angularIntegrand ω θ

/-- The sum of the actual two positive angular arc integrals. -/
def twoArcIntegral (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : ℂ :=
  firstArcIntegral ω + secondArcIntegral ω

/-- The original Laurent unit-circle period is exactly its two-positive-arc integral. -/
theorem integral_eq_twoArcIntegral (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    LaurentPeriods.integral ω = twoArcIntegral ω := by
  have hshift := (angularIntegrand_periodic ω).intervalIntegral_add_eq (-Real.pi / 2) 0
  have hend : -Real.pi / 2 + 2 * Real.pi = 3 * Real.pi / 2 := by ring
  change (∫ θ in 0..(2 * Real.pi), angularIntegrand ω θ) =
    (∫ θ in (-Real.pi / 2)..(Real.pi / 2), angularIntegrand ω θ) +
      (∫ θ in (Real.pi / 2)..(3 * Real.pi / 2), angularIntegrand ω θ)
  rw [intervalIntegral.integral_add_adjacent_intervals
    (angularIntegrand_intervalIntegrable ω _ _) (angularIntegrand_intervalIntegrable ω _ _)]
  simpa only [zero_add, hend] using hshift.symm

@[simp]
theorem twoArcIntegral_dlogT : twoArcIntegral (LaurentDeRham.dlogT ℂ) =
    2 * Real.pi * Complex.I := by
  rw [← integral_eq_twoArcIntegral, LaurentPeriods.integral_dlogT]

@[simp]
theorem twoArcIntegral_exact (f : LaurentPolynomial ℂ) :
    twoArcIntegral (D ℂ (LaurentPolynomial ℂ) f) = 0 := by
  rw [← integral_eq_twoArcIntegral, LaurentPeriods.integral_exact]

end HodgeConjecture.LaurentOrientedArcs
