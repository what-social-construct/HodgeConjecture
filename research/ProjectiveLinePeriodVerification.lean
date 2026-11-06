module

import HodgeConjecture.Realization.DeRham.ProjectiveLinePeriods
import Lean.Util.CollectAxioms

/-!
Actual analytic evaluation, circle-integral and quotient-descent checks.
These tests use ordinary Chow sources and the original scheme H² target;
they do not postulate or compute a rational singular H².
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open HodgeConjecture KaehlerDifferential LaurentPolynomial
open HodgeConjecture.ProjectiveLineDeRham HodgeConjecture.ProjectiveLinePeriods

example (f : LaurentPolynomial ℂ) (z : ℂ) (hz : z ≠ 0) :
    LaurentPeriods.shiftedEvaluation 0 f z =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 z hz) f :=
  LaurentPeriods.shiftedEvaluation_zero_eq_eval₂ f z hz

-- Negative powers are evaluated on actual complex points, rather than just their residue.
example : LaurentPeriods.shiftedEvaluation 0 (C (3 : ℂ) * T (-2)) 2 = 3 / 4 := by
  rw [LaurentPeriods.shiftedEvaluation_monomial]
  norm_num

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (z : ℂ) (hz : z ≠ 0) :
    LaurentPeriods.coefficientFunction ω z =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 z hz)
        (LaurentDeRham.kaehlerCoordinates ℂ ω) * z⁻¹ :=
  LaurentPeriods.coefficientFunction_eq_eval₂ ω z hz

example : LaurentPeriods.integral (LaurentDeRham.dlogT ℂ) = 2 * Real.pi * Complex.I :=
  LaurentPeriods.integral_dlogT

example (f : LaurentPolynomial ℂ) : LaurentPeriods.integral (D ℂ (LaurentPolynomial ℂ) f) = 0 :=
  LaurentPeriods.integral_exact f

-- All integer unit exponents, including negative ones, retain their actual period sign.
example (n : ℤ) : LaurentPeriods.integral
    ((T (-n) : LaurentPolynomial ℂ) • D ℂ (LaurentPolynomial ℂ) (T n)) =
      (2 * Real.pi * Complex.I) * (n : ℂ) := by
  rw [LaurentPeriods.integral_eq_two_pi_I_mul_residue]
  exact congrArg ((2 * Real.pi * Complex.I) * ·)
    (LaurentDeRham.kaehlerResidue_monomial_dlog ℂ n)

example (x : CechOne ℂ) :
    closedFormIntegral (cechToClosedForms ℂ x) = 0 := by
  exact cechBoundaries_le_ker_integral ⟨x, rfl⟩

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    cechIntegral (overlapClass ℂ ω) = LaurentPeriods.integral ω :=
  cechIntegral_overlapClass ω

example (ω : Ω[Polynomial ℂ⁄ℂ]) :
    cechIntegral (overlapClass ℂ (chartZeroFormsMap ℂ ω)) = 0 := by
  rw [overlapClass_chartZero, map_zero]

example (ω : Ω[Polynomial ℂ⁄ℂ]) :
    cechIntegral (overlapClass ℂ (chartInfinityFormsMap ℂ ω)) = 0 := by
  rw [overlapClass_chartInfinity, map_zero]

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    schemeIntegral (schemeOverlapClass ℂ ω) = LaurentPeriods.integral ω :=
  schemeIntegral_overlapClass ω

example : schemeIntegral (schemeChernCoordinate ℂ) = 2 * Real.pi * Complex.I :=
  schemeIntegral_chernCoordinate

example : normalizedSchemeIntegral (schemeChernCoordinate ℂ) = 1 := by
  rw [normalizedSchemeIntegral_eq_residue, schemeResidueEquiv_chernCoordinate]

example (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    normalizedSchemeIntegral
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ) (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
        (ProjectiveLineCycles.rationalChowDegree ℂ z : ℂ) :=
  normalizedSchemeIntegral_cycleClass z

example : normalizedSchemeIntegral
    (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
      (ProjectiveLineSchemeCycleClass.cycleClass ℂ
        ((-3 / 2 : ℚ) • ProjectiveLineCycleClass.rationalInfinityClass ℂ))) = -3 / 2 := by
  rw [normalizedSchemeIntegral_cycleClass, map_smul, smul_eq_mul,
    ProjectiveLineCycleClass.rationalChowDegree_infinity, mul_one]
  norm_num

example (d : SchemeCycles.PrincipalRelationData (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    normalizedSchemeIntegral
      (RestrictScalars.addEquiv ℚ ℂ (SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ
          (SchemeCycles.rationalClassMap (ProjectiveLineCycles.dimensionFunction ℂ) 0
            (SchemeCycles.cyclesOfDegreeRationalize (ProjectiveLineCycles.dimensionFunction ℂ) 0
              (SchemeCycles.principalRelation (ProjectiveLineCycles.dimensionFunction ℂ) 0 d))))) = 0 := by
  rw [ProjectiveLineSchemeCycleClass.cycleClass_principalRelation, map_zero, map_zero]

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.LaurentPeriods.shiftedEvaluation_zero_eq_eval₂,
    `HodgeConjecture.LaurentPeriods.coefficientFunction_eq_eval₂,
    `HodgeConjecture.LaurentPeriods.circleIntegrable_shiftedEvaluation,
    `HodgeConjecture.LaurentPeriods.circleIntegral_shiftedEvaluation,
    `HodgeConjecture.LaurentPeriods.integral_eq_two_pi_I_mul_residue,
    `HodgeConjecture.LaurentPeriods.integral_dlogT,
    `HodgeConjecture.LaurentPeriods.integral_exact,
    `HodgeConjecture.LaurentPeriods.normalizedIntegral_eq_residue,
    `HodgeConjecture.ProjectiveLinePeriods.cechBoundaries_le_ker_integral,
    `HodgeConjecture.ProjectiveLinePeriods.cechIntegral,
    `HodgeConjecture.ProjectiveLinePeriods.cechIntegral_overlapClass,
    `HodgeConjecture.ProjectiveLinePeriods.schemeIntegral_comparison,
    `HodgeConjecture.ProjectiveLinePeriods.schemeIntegral_overlapClass,
    `HodgeConjecture.ProjectiveLinePeriods.schemeIntegral_chernCoordinate,
    `HodgeConjecture.ProjectiveLinePeriods.normalizedSchemeIntegral_eq_residue,
    `HodgeConjecture.ProjectiveLinePeriods.normalizedSchemeIntegral_cycleClass]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
