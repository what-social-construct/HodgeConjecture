module

public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import HodgeConjecture.Realization.Betti.ProjectiveLineDegreeOne
public import Lean.Util.CollectAxioms

@[expose] public section

/-! Actual P¹ singular H² and its original affine-chart boundary generator. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory HodgeConjecture
open ProjectiveLineBettiCohomology

namespace ProjectiveLineCohomologyVerification

example : SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2 ≃ₗ[ℚ] ℚ :=
  h2Equiv

example : h2Equiv coverGenerator = 1 := h2Equiv_coverGenerator

example : coverGenerator ≠ 0 := coverGenerator_ne_zero

example : ProjectiveLineSingularCohomology.circleIso.hom CircleCohomology.coverGenerator =
    coverGenerator := rfl

example : coverGenerator = ProjectiveLineSingularCohomology.connecting
    (SingularCochains.cohomologyPullback
      (TopCat.ofHom ProjectiveLineAnalyticCover.overlapCircleHomotopyEquiv.toFun) 1
        CircleCohomology.coverGenerator) := coverGenerator_eq_connecting

example (z : SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2) :
    z = h2Equiv z • coverGenerator := eq_smul_coverGenerator z

example (q : ℚ) : h2Equiv (q • coverGenerator) = q := by
  rw [map_smul, h2Equiv_coverGenerator, smul_eq_mul, mul_one]

example (q r : ℚ) : q • coverGenerator = r • coverGenerator ↔ q = r := by
  constructor
  · intro h
    have he := congrArg h2Equiv h
    simpa using he
  · rintro rfl
    rfl

example (z : SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2) :
    z = 0 ↔ h2Equiv z = 0 := by
  exact h2Equiv.map_eq_zero_iff.symm

example : Function.Bijective
    (fun q : ℚ ↦ q • coverGenerator) := by
  constructor
  · intro q r h
    have he := congrArg h2Equiv h
    simpa using he
  · intro z
    exact ⟨h2Equiv z, (eq_smul_coverGenerator z).symm⟩

end ProjectiveLineCohomologyVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineBettiCohomology.h2Equiv,
      `HodgeConjecture.ProjectiveLineBettiCohomology.coverGenerator,
      `HodgeConjecture.ProjectiveLineBettiCohomology.coverGenerator_eq_connecting,
      `HodgeConjecture.ProjectiveLineBettiCohomology.h2Equiv_circleIso,
      `HodgeConjecture.ProjectiveLineBettiCohomology.h2Equiv_coverGenerator,
      `HodgeConjecture.ProjectiveLineBettiCohomology.coverGenerator_ne_zero,
      `HodgeConjecture.ProjectiveLineBettiCohomology.eq_smul_coverGenerator,
      `HodgeConjecture.ProjectiveLineDegreeOne.overlapH0_eq_constant,
      `HodgeConjecture.ProjectiveLineDegreeOne.difference_zero_surjective,
      `HodgeConjecture.ProjectiveLineDegreeOne.isZero_h1] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
