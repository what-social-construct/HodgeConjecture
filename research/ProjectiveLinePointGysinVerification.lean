module

public import HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The original zero-point support, local-versus-global forgetting and positive
orientation are checked before comparison with the actual Chow quotient.
Only the distinguished zero point and its original finite chart are used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory AlgebraicGeometry HodgeConjecture
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover ProjectiveLinePointSupport
open ProjectiveLinePointGysin ProjectiveLineGysinCycleClass

namespace ProjectiveLinePointGysinVerification

example : reciprocalOpen = supportᶜ := reciprocalOpen_eq_puncturedOpen

example (q : Spec (.of ℂ)) :
    schemeMorphism zeroPoint q = projectiveLineZero ℂ := zeroPoint_scheme_base q

example (x : ↥({0} : Set ℂ)) :
    (pointHomeomorph x : Point) = finite x.val := pointHomeomorph_coe x

example : projectiveLineZero ℂ ≠ genericPoint (projectiveLine ℂ) :=
  schemeZero_ne_genericPoint

example : pointPullbackIso.hom pointUnit = ComplexPointThom.pointUnit :=
  pointPullbackIso_pointUnit

example : ComplexPointThom.boundaryPairing ComplexPointThom.thomClass = 1 :=
  ComplexPointThom.boundaryPairing_thomClass

/-- Local absolute cohomology cannot carry the geometric class. -/
theorem local_absolute_forget_zero :
    RelativeCochains.forget ComplexPointThom.puncturedSubcomplex 2
      ComplexPointThom.thomClass = 0 := ComplexPointThom.forget_thomClass

/-- The same oriented class has a nonzero image after actual inverse excision. -/
theorem global_supported_forget_nonzero :
    RelativeCochains.forget complementSubcomplex 2 supportedThomClass ≠ 0 := by
  rw [forget_supportedThomClass]
  exact ProjectiveLineBettiCohomology.coverGenerator_ne_zero

example : supportedThomClass ≠ 0 := supportedThomClass_ne_zero

example : IsIso (RelativeCochains.forget complementSubcomplex 2) := inferInstance

example : supportedGysin pointUnit = supportedThomClass := supportedGysin_pointUnit

example : Function.Bijective gysin := gysin_bijective

example : ProjectiveLineBettiCohomology.h2Equiv (gysin pointUnit) = 1 := by
  rw [gysin_pointUnit, ProjectiveLineBettiCohomology.h2Equiv_coverGenerator]

/-- A reversed local orientation cannot satisfy the original positive cycle normalization. -/
theorem gysin_rejects_opposite_orientation :
    gysin pointUnit ≠ -ProjectiveLineBettiCohomology.coverGenerator := by
  intro h
  have h' := congrArg ProjectiveLineBettiCohomology.h2Equiv h
  rw [gysin_pointUnit, map_neg, ProjectiveLineBettiCohomology.h2Equiv_coverGenerator] at h'
  norm_num at h'

example : gysin pointUnit = ProjectiveLineBettiCycleClass.integralCycleClass integralZeroClass :=
  gysin_pointUnit_eq_integralZeroClass

example : gysin pointUnit = ProjectiveLineBettiCycleClass.cycleClass rationalZeroClass :=
  gysin_pointUnit_eq_rationalZeroClass

example : gysin (pointClass (3 / 2 : ℚ)) =
    (3 / 2 : ℚ) • ProjectiveLineBettiCohomology.coverGenerator := by
  rw [pointClass_eq_smul, map_smul, gysin_pointUnit]

example (z : Source) : ProjectiveLineBettiCycleClass.cycleClass z =
    gysin (pointClass (ProjectiveLineCycles.rationalChowDegree ℂ z)) :=
  cycleClass_factorization z

example (z : SchemeCycles.ChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    ProjectiveLineBettiCycleClass.integralCycleClass z =
      gysin (pointClass (ProjectiveLineCycles.integralChowDegree ℂ z : ℚ)) :=
  integralCycleClass_factorization z

end ProjectiveLinePointGysinVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLinePointSupport.zeroPoint,
      `HodgeConjecture.ProjectiveLinePointSupport.reciprocalOpen_eq_puncturedOpen,
      `HodgeConjecture.ProjectiveLinePointSupport.puncturedOpen_isOpen,
      `HodgeConjecture.ProjectiveLinePointSupport.zeroPoint_scheme_base,
      `HodgeConjecture.ProjectiveLinePointSupport.schemeZero_ne_genericPoint,
      `HodgeConjecture.ProjectiveLinePointSupport.pointHomeomorph,
      `HodgeConjecture.ProjectiveLinePointSupport.pointHomeomorph_coe,
      `HodgeConjecture.ProjectiveLinePointSupport.pointCoordinates,
      `HodgeConjecture.ProjectiveLinePointSupport.pointUnit,
      `HodgeConjecture.ProjectiveLinePointSupport.pointCoordinates_pointUnit,
      `HodgeConjecture.ProjectiveLinePointGysin.pointPullbackIso,
      `HodgeConjecture.ProjectiveLinePointGysin.pointPullbackIso_pointUnit,
      `HodgeConjecture.ProjectiveLinePointGysin.thomToSupportIso,
      `HodgeConjecture.ProjectiveLinePointGysin.supportedThomClass,
      `HodgeConjecture.ProjectiveLinePointGysin.supportedThomClass_ne_zero,
      `HodgeConjecture.ProjectiveLinePointGysin.complementCohomology_isZero,
      `HodgeConjecture.ProjectiveLinePointGysin.forget_isIso,
      `HodgeConjecture.ProjectiveLinePointGysin.forgetIso,
      `HodgeConjecture.ProjectiveLinePointGysin.forget_supportedThomClass,
      `HodgeConjecture.ProjectiveLinePointGysin.supportedGysin,
      `HodgeConjecture.ProjectiveLinePointGysin.gysin,
      `HodgeConjecture.ProjectiveLinePointGysin.supportedGysin_pointUnit,
      `HodgeConjecture.ProjectiveLinePointGysin.gysin_pointUnit,
      `HodgeConjecture.ProjectiveLinePointGysin.gysinIso,
      `HodgeConjecture.ProjectiveLinePointGysin.gysinIso_apply,
      `HodgeConjecture.ProjectiveLinePointGysin.gysin_bijective,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.integralZeroClass,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.rationalZeroClass,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.pointClass,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.pointClass_one,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.pointClass_eq_smul,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.gysin_pointUnit_eq_integralZeroClass,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.gysin_pointUnit_eq_rationalZeroClass,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.cycleClassViaZeroGysin,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.cycleClassViaZeroGysin_eq_cycleClass,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.cycleClass_factorization,
      `HodgeConjecture.ProjectiveLineGysinCycleClass.integralCycleClass_factorization,
      `ProjectiveLinePointGysinVerification.local_absolute_forget_zero,
      `ProjectiveLinePointGysinVerification.global_supported_forget_nonzero,
      `ProjectiveLinePointGysinVerification.gysin_rejects_opposite_orientation] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
