module

public import HodgeConjecture.Realization.Betti.Circle
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The actual circle boundary is surjective, annihilates constant overlap
values, and produces a nonzero class spanning the original H¹. A separate
disjoint-union example checks that component coordinates retain independent
values on actual continuous zero-simplices.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open HodgeConjecture

namespace CircleCohomologyVerification

def separatedClass : SingularDegreeZero.H0 (ℝ ⊕ ℝ) :=
  (SingularComponents.sumEquiv ℝ ℝ 0 0).symm (TwoComponentBoundary.step 1)

theorem separatedClass_left :
    SingularDegreeZero.eval (ℝ ⊕ ℝ) separatedClass (Sum.inl 0) = 0 := by
  change SingularComponents.sumEquiv ℝ ℝ 0 0 separatedClass false = 0
  rw [separatedClass, AlgEquiv.apply_symm_apply]
  rfl

theorem separatedClass_right :
    SingularDegreeZero.eval (ℝ ⊕ ℝ) separatedClass (Sum.inr 0) = 1 := by
  change SingularComponents.sumEquiv ℝ ℝ 0 0 separatedClass true = 1
  rw [separatedClass, AlgEquiv.apply_symm_apply]
  rfl

theorem separatedClass_ne_zero : separatedClass ≠ 0 := by
  intro h
  have he := separatedClass_right
  rw [h] at he
  exact zero_ne_one he

theorem component_decomposition (f : Bool → ℚ) :
    f = TwoComponentBoundary.diagonal (f false) +
      TwoComponentBoundary.step (TwoComponentBoundary.jump f) := by
  funext i
  cases i <;> simp [TwoComponentBoundary.diagonal, TwoComponentBoundary.step,
    TwoComponentBoundary.jump]

theorem actual_boundary_surjective : Function.Surjective CircleCohomology.connecting :=
  CircleCohomology.connecting_surjective

theorem actual_boundary_constant (q : ℚ) :
    CircleCohomology.componentBoundary (TwoComponentBoundary.diagonal q) = 0 := by
  have h : TwoComponentBoundary.diagonal q ∈
      LinearMap.range TwoComponentBoundary.diagonal := ⟨q, rfl⟩
  rw [← CircleCohomology.ker_componentBoundary] at h
  exact h

theorem actual_upper_boundary_coordinate :
    CircleCohomology.h1Equiv
      (CircleCohomology.connecting
        (CircleCohomology.overlapZeroEquiv.symm (TwoComponentBoundary.step 1))) = 1 := by
  rw [CircleCohomology.h1Equiv_connecting, LinearEquiv.apply_symm_apply,
    TwoComponentBoundary.jump_step]

theorem actual_generator_ne_zero : CircleCohomology.coverGenerator ≠ 0 :=
  CircleCohomology.coverGenerator_ne_zero

theorem actual_generator_spans
    (z : SingularCochains.Cohomology (TopCat.of Circle) 1) :
    z = CircleCohomology.h1Equiv z • CircleCohomology.coverGenerator := by
  apply CircleCohomology.h1Equiv.injective
  rw [map_smul, CircleCohomology.h1Equiv_coverGenerator]
  simp

end CircleCohomologyVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularComponents.evaluationOnSamples,
      `HodgeConjecture.SingularComponents.classFromComponents,
      `HodgeConjecture.SingularComponents.componentEquiv,
      `HodgeConjecture.SingularComponents.componentEquiv_constantClass,
      `HodgeConjecture.SingularComponents.cohomologyZeroEquiv,
      `HodgeConjecture.SingularComponents.sumEquiv,
      `HodgeConjecture.TwoComponentBoundary.ker_jump,
      `HodgeConjecture.TwoComponentBoundary.quotientEquiv,
      `HodgeConjecture.TwoComponentBoundary.boundaryEquiv,
      `HodgeConjecture.TwoComponentBoundary.boundaryEquiv_apply,
      `HodgeConjecture.TwoComponentBoundary.boundary_step_ne_zero,
      `HodgeConjecture.CircleCohomology.overlapZeroEquiv,
      `HodgeConjecture.CircleCohomology.difference_coordinates,
      `HodgeConjecture.CircleCohomology.difference_constant,
      `HodgeConjecture.CircleCohomology.connecting_surjective,
      `HodgeConjecture.CircleCohomology.componentBoundary,
      `HodgeConjecture.CircleCohomology.componentBoundary_surjective,
      `HodgeConjecture.CircleCohomology.ker_componentBoundary,
      `HodgeConjecture.CircleCohomology.h1Equiv,
      `HodgeConjecture.CircleCohomology.h1Equiv_connecting,
      `HodgeConjecture.CircleCohomology.coverGenerator,
      `HodgeConjecture.CircleCohomology.h1Equiv_coverGenerator,
      `HodgeConjecture.CircleCohomology.coverGenerator_ne_zero,
      `CircleCohomologyVerification.separatedClass,
      `CircleCohomologyVerification.separatedClass_left,
      `CircleCohomologyVerification.separatedClass_right,
      `CircleCohomologyVerification.separatedClass_ne_zero,
      `CircleCohomologyVerification.component_decomposition,
      `CircleCohomologyVerification.actual_boundary_surjective,
      `CircleCohomologyVerification.actual_boundary_constant,
      `CircleCohomologyVerification.actual_upper_boundary_coordinate,
      `CircleCohomologyVerification.actual_generator_ne_zero,
      `CircleCohomologyVerification.actual_generator_spans] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
