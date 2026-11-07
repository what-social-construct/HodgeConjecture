module

public import HodgeConjecture.Realization.DeRham.LaurentOrientedArcs
public import Lean.Util.CollectAxioms

@[expose] public section

/-! Original angular curves, shifted integrability and positive/reversed actual arc periods. -/

set_option autoImplicit false

noncomputable section

open HodgeConjecture KaehlerDifferential MeasureTheory LaurentOrientedArcs

namespace LaurentOrientedArcsVerification

example (θ : ℝ) : circleMap 0 1 θ = (Circle.exp θ : ℂ) := unitCircleMap_eq_exp θ

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (θ : ℝ) : angularIntegrand ω θ =
    ((Circle.exp θ : ℂ) * Complex.I) * LaurentPeriods.coefficientFunction ω (Circle.exp θ : ℂ) :=
  angularIntegrand_eq_exp ω θ

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    Function.Periodic (angularIntegrand ω) (2 * Real.pi) := angularIntegrand_periodic ω

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) (a b : ℝ) :
    IntervalIntegrable (angularIntegrand ω) volume a b := angularIntegrand_intervalIntegrable ω a b

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) : LaurentPeriods.integral ω =
    firstArcIntegral ω + secondArcIntegral ω := integral_eq_twoArcIntegral ω

example : twoArcIntegral (LaurentDeRham.dlogT ℂ) = 2 * Real.pi * Complex.I := twoArcIntegral_dlogT

example (f : LaurentPolynomial ℂ) : twoArcIntegral (D ℂ (LaurentPolynomial ℂ) f) = 0 :=
  twoArcIntegral_exact f

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    twoArcIntegral ω / (2 * Real.pi * Complex.I) = LaurentDeRham.kaehlerResidue ℂ ω := by
  rw [← integral_eq_twoArcIntegral]
  exact LaurentPeriods.normalizedIntegral_eq_residue ω

example (ω : Ω[LaurentPolynomial ℂ⁄ℂ]) :
    (∫ θ in (Real.pi / 2)..(-Real.pi / 2), angularIntegrand ω θ) +
      (∫ θ in (3 * Real.pi / 2)..(Real.pi / 2), angularIntegrand ω θ) =
        -LaurentPeriods.integral ω := by
  rw [intervalIntegral.integral_symm (-Real.pi / 2) (Real.pi / 2),
    intervalIntegral.integral_symm (Real.pi / 2) (3 * Real.pi / 2), ← neg_add]
  change -twoArcIntegral ω = -LaurentPeriods.integral ω
  rw [← integral_eq_twoArcIntegral]

end LaurentOrientedArcsVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.LaurentOrientedArcs.unitCircleMap_eq_exp,
      `HodgeConjecture.LaurentOrientedArcs.angularIntegrand,
      `HodgeConjecture.LaurentOrientedArcs.angularIntegrand_eq_exp,
      `HodgeConjecture.LaurentOrientedArcs.angularIntegrand_periodic,
      `HodgeConjecture.LaurentOrientedArcs.angularIntegrand_intervalIntegrable,
      `HodgeConjecture.LaurentOrientedArcs.firstArcIntegral,
      `HodgeConjecture.LaurentOrientedArcs.secondArcIntegral,
      `HodgeConjecture.LaurentOrientedArcs.twoArcIntegral,
      `HodgeConjecture.LaurentOrientedArcs.integral_eq_twoArcIntegral,
      `HodgeConjecture.LaurentOrientedArcs.twoArcIntegral_dlogT,
      `HodgeConjecture.LaurentOrientedArcs.twoArcIntegral_exact] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
