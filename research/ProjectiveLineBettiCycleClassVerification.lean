module

public import HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass
public import Lean.Util.CollectAxioms

@[expose] public section

/-! Ordinary Chow classes into actual rational singular H², independently of de Rham. -/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry HodgeConjecture SchemeCycles ProjectiveLineCycles
open ProjectiveLineBettiCohomology ProjectiveLineBettiCycleClass

namespace ProjectiveLineBettiCycleClassVerification

example : integralCycleClass integralInfinityClass = coverGenerator := integralCycleClass_infinity

example : cycleClass rationalInfinityClass = coverGenerator := cycleClass_infinity

example (x : projectiveLine ℂ) (hx : x ≠ genericPoint (projectiveLine ℂ)) :
    cycleClass (rationalClassMap (dimensionFunction ℂ) 0 (pointCycle ℂ ℚ x hx)) =
      coverGenerator := cycleClass_pointCycle x hx

example (x : projectiveLine ℂ) (hx : x ≠ genericPoint (projectiveLine ℂ)) :
    integralCycleClass (classMap (dimensionFunction ℂ) 0 (pointCycle ℂ ℤ x hx)) =
      coverGenerator := integralCycleClass_pointCycle x hx

example (z : ChowGroup (dimensionFunction ℂ) 0) :
    cycleClass (chowRationalize (dimensionFunction ℂ) 0 z) = integralCycleClass z :=
  cycleClass_chowRationalize z

example (z : RationalChowGroup (dimensionFunction ℂ) 0) :
    h2Equiv (cycleClass z) = rationalChowDegree ℂ z := coordinate_cycleClass z

example (q : ℚ) : cycleClass (q • rationalInfinityClass) = q • coverGenerator := by
  rw [map_smul, cycleClass_infinity]

example : h2Equiv (cycleClass ((-3/2 : ℚ) • rationalInfinityClass)) = -3/2 := by
  rw [map_smul, cycleClass_infinity, map_smul, h2Equiv_coverGenerator, smul_eq_mul, mul_one]

example (z : RationalChowGroup (dimensionFunction ℂ) 0) :
    cycleClass z = 0 ↔ rationalChowDegree ℂ z = 0 := by
  rw [← coordinate_cycleClass]
  exact h2Equiv.map_eq_zero_iff.symm

example (q : ℚ) (hq : q ≠ 0) : cycleClass (q • rationalInfinityClass) ≠ 0 := by
  intro h
  have he := congrArg h2Equiv h
  simp only [map_smul, cycleClass_infinity, h2Equiv_coverGenerator, smul_eq_mul, mul_one,
    map_zero] at he
  exact hq he

example (d : PrincipalRelationData (dimensionFunction ℂ) 0) :
    integralCycleClass (classMap (dimensionFunction ℂ) 0
      (principalRelation (dimensionFunction ℂ) 0 d)) = 0 :=
  integralCycleClass_principalRelation d

example (d : PrincipalRelationData (dimensionFunction ℂ) 0) :
    cycleClass (rationalClassMap (dimensionFunction ℂ) 0
      (cyclesOfDegreeRationalize (dimensionFunction ℂ) 0
        (principalRelation (dimensionFunction ℂ) 0 d))) = 0 := cycleClass_principalRelation d

example : cycleClass ≠ 0 := cycleClass_ne_zero

example : Function.Surjective cycleClass := cycleClass_surjective

end ProjectiveLineBettiCycleClassVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineBettiCycleClass.infinity_ne_genericPoint,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralInfinityClass,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.rationalInfinityClass,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralChowDegree_infinity,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.rationalChowDegree_infinity,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralCycleClass,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralCycleClass_classMap,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_classMap,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralCycleClass_pointCycle,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_pointCycle,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralCycleClass_infinity,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_infinity,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.coordinate_cycleClass,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_chowRationalize,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.integralCycleClass_principalRelation,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_principalRelation,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_ne_zero,
      `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_surjective] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
