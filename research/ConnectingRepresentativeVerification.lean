module

public import HodgeConjecture.Realization.Betti.SubcomplexDegreeZeroRepresentative
public import HodgeConjecture.Realization.Betti.SingularComponents
public import HodgeConjecture.Realization.Betti.TwoComponentBoundary
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The native homology class of an actual disconnected zero-cocycle retains
both original simplex values. This checks the new native representative
bridge independently of the circle's later connecting calculation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory HodgeConjecture
open SubcomplexConnectingRepresentative SubcomplexDegreeZeroRepresentative

namespace ConnectingRepresentativeVerification

def nativeSplitCocycle : Cocycle (TopCat.toSSet.obj (TopCat.of (ℝ ⊕ ℝ))) 0 :=
  (SingularCochains.kernelZeroCoordinates (ℝ ⊕ ℝ)).symm
    ((SingularComponents.sumEquiv ℝ ℝ 0 0).symm (TwoComponentBoundary.step 1))

def nativeSplitClass := cocycleClass _ 0 nativeSplitCocycle

theorem nativeSplitClass_model :
    (SingularCochains.cohomologyZeroIso (ℝ ⊕ ℝ)).hom nativeSplitClass =
      (SingularComponents.sumEquiv ℝ ℝ 0 0).symm (TwoComponentBoundary.step 1) := by
  apply Subtype.ext
  rw [nativeSplitClass, cohomologyZeroIso_cocycleClass]
  exact congrArg Subtype.val
    ((SingularCochains.kernelZeroCoordinates (ℝ ⊕ ℝ)).apply_symm_apply _)

theorem actual_native_class_left :
    SingularDegreeZero.eval (ℝ ⊕ ℝ)
      ((SingularCochains.cohomologyZeroIso (ℝ ⊕ ℝ)).hom nativeSplitClass) (Sum.inl 0) = 0 := by
  rw [nativeSplitClass_model]
  change SingularComponents.sumEquiv ℝ ℝ 0 0
    ((SingularComponents.sumEquiv ℝ ℝ 0 0).symm (TwoComponentBoundary.step 1)) false = 0
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem actual_native_class_right :
    SingularDegreeZero.eval (ℝ ⊕ ℝ)
      ((SingularCochains.cohomologyZeroIso (ℝ ⊕ ℝ)).hom nativeSplitClass) (Sum.inr 0) = 1 := by
  rw [nativeSplitClass_model]
  change SingularComponents.sumEquiv ℝ ℝ 0 0
    ((SingularComponents.sumEquiv ℝ ℝ 0 0).symm (TwoComponentBoundary.step 1)) true = 1
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem actual_native_class_ne_zero : nativeSplitClass ≠ 0 := by
  intro hz
  have h := actual_native_class_right
  rw [hz] at h
  change SingularDegreeZero.eval (ℝ ⊕ ℝ)
    ((SingularCochains.cohomologyZeroIso (ℝ ⊕ ℝ)).hom
      (0 : SingularCochains.Cohomology (TopCat.of (ℝ ⊕ ℝ)) 0)) (Sum.inr 0) = 1 at h
  rw [map_zero] at h
  exact zero_ne_one h

end ConnectingRepresentativeVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SubcomplexConnectingRepresentative.cocycleClass,
      `HodgeConjecture.SubcomplexConnectingRepresentative.cocycleClass_surjective,
      `HodgeConjecture.SubcomplexConnectingRepresentative.cocyclePullback,
      `HodgeConjecture.SubcomplexConnectingRepresentative.cocycleClass_pullback,
      `HodgeConjecture.SubcomplexConnectingRepresentative.differential_eq_zero_of_restriction_eq,
      `HodgeConjecture.SubcomplexConnectingRepresentative.connecting_cocycleClass,
      `HodgeConjecture.SubcomplexConnectingRepresentative.exists_connecting_representative,
      `HodgeConjecture.SubcomplexDegreeZeroRepresentative.representative_cocycleClass,
      `HodgeConjecture.SubcomplexDegreeZeroRepresentative.cohomologyZeroIso_cocycleClass,
      `HodgeConjecture.SubcomplexDegreeZeroRepresentative.eval_cocycleClass,
      `ConnectingRepresentativeVerification.nativeSplitCocycle,
      `ConnectingRepresentativeVerification.nativeSplitClass,
      `ConnectingRepresentativeVerification.nativeSplitClass_model,
      `ConnectingRepresentativeVerification.actual_native_class_left,
      `ConnectingRepresentativeVerification.actual_native_class_right,
      `ConnectingRepresentativeVerification.actual_native_class_ne_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
