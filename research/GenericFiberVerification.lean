module

import HodgeConjecture.Boundary.Normalization.GenericFiber
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP97 focused checks for the actual generic fiber of a finite dominant morphism.
Run with `lake env lean research/GenericFiberVerification.lean`.

The affine tests retain the original section pullback, both generic germs,
and the actual generic-stalk field map. They exercise the resulting algebra
pushout and its tensor equivalence. The scheme tests use the actual generic
point morphisms and the actual spectrum of the upstairs function field,
including the canonical pullback comparison and its universal property.
No étaleness, normality, separability, or Noetherianity is supplied. The exact
two-declaration audit enforces the standard-three Lean axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open scoped TensorProduct

noncomputable section

universe u

#check functionFieldMapOfDominant_isPushout_of_affine
#check functionFieldMapOfDominant_isPullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

section ActualAffineSquare

variable (U : X.Opens) [Nonempty U]

example :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap Γ(X, U) Γ(Y, p ⁻¹ᵁ U) = (p.app U).hom ∧
      algebraMap Γ(X, U) Y.functionField =
        (Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom ∧
      algebraMap X.functionField Y.functionField = (functionFieldMapOfDominant p).hom :=
  ⟨rfl, rfl, rfl⟩

example (b : Γ(X, U)) :
    letI := nonempty_preimage_of_isDominant p U
    (functionFieldMapOfDominant p).hom ((X.germToFunctionField U).hom b) =
      (Y.germToFunctionField (p ⁻¹ᵁ U)).hom ((p.app U).hom b) := by
  letI := nonempty_preimage_of_isDominant p U
  exact congrArg (fun f : Γ(X, U) ⟶ Y.functionField => f.hom b)
    (functionFieldMapOfDominant_germ p U)

example (hU : IsAffineOpen U) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    Algebra.IsPushout Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField := by
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  exact functionFieldMapOfDominant_isPushout_of_affine p U hU

example (hU : IsAffineOpen U) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    Nonempty ((Γ(Y, p ⁻¹ᵁ U) ⊗[Γ(X, U)] X.functionField) ≃ₐ[Γ(Y, p ⁻¹ᵁ U)]
      Y.functionField) := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI := functionFieldMapOfDominant_isPushout_of_affine p U hU
  exact ⟨Algebra.IsPushout.equiv Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField⟩

example (hU : IsAffineOpen U) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI := functionFieldMapOfDominant_isPushout_of_affine p U hU
    ∀ (a : Γ(Y, p ⁻¹ᵁ U)) (k : X.functionField),
      Algebra.IsPushout.equiv Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField
          (a ⊗ₜ[Γ(X, U)] k) =
        (Y.germToFunctionField (p ⁻¹ᵁ U)).hom a * (functionFieldMapOfDominant p).hom k := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI := functionFieldMapOfDominant_isPushout_of_affine p U hU
  intro a k
  exact Algebra.IsPushout.equiv_tmul Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField a k

example (hU : IsAffineOpen U) :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI := functionFieldMapOfDominant_isPushout_of_affine p U hU
    ∀ (a : Γ(Y, p ⁻¹ᵁ U)) (k : X.functionField),
      (Algebra.IsPushout.equiv Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField).symm
          ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom a) = a ⊗ₜ[Γ(X, U)] 1 ∧
      (Algebra.IsPushout.equiv Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField).symm
          ((functionFieldMapOfDominant p).hom k) = 1 ⊗ₜ[Γ(X, U)] k := by
  letI := nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI := functionFieldMapOfDominant_isPushout_of_affine p U hU
  intro a k
  exact ⟨Algebra.IsPushout.equiv_symm_algebraMap_left
      Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField a,
    Algebra.IsPushout.equiv_symm_algebraMap_right
      Γ(X, U) Γ(Y, p ⁻¹ᵁ U) X.functionField Y.functionField k⟩

end ActualAffineSquare

section ActualGenericFiber

example : IsPullback (Y.fromSpecStalk (genericPoint Y))
    (Spec.map (functionFieldMapOfDominant p)) p (X.fromSpecStalk (genericPoint X)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField Y.functionField := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  fail_if_success
    have _ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun _ => inferInstance
  exact functionFieldMapOfDominant_isPullback p

example : Y.fromSpecStalk (genericPoint Y) ≫ p =
    Spec.map (functionFieldMapOfDominant p) ≫ X.fromSpecStalk (genericPoint X) :=
  (functionFieldMapOfDominant_isPullback p).w

example (z : Spec Y.functionField) :
    p.base ((Y.fromSpecStalk (genericPoint Y)).base z) =
      (X.fromSpecStalk (genericPoint X)).base ((Spec.map (functionFieldMapOfDominant p)).base z) := by
  exact congrArg (fun f : Spec Y.functionField ⟶ X => f.base z)
    (functionFieldMapOfDominant_isPullback p).w

example : Nonempty (Spec Y.functionField ≅ pullback p (X.fromSpecStalk (genericPoint X))) :=
  ⟨(functionFieldMapOfDominant_isPullback p).isoPullback⟩

example : (functionFieldMapOfDominant_isPullback p).isoPullback.hom ≫
    pullback.fst p (X.fromSpecStalk (genericPoint X)) = Y.fromSpecStalk (genericPoint Y) :=
  (functionFieldMapOfDominant_isPullback p).isoPullback_hom_fst

example : (functionFieldMapOfDominant_isPullback p).isoPullback.hom ≫
    pullback.snd p (X.fromSpecStalk (genericPoint X)) = Spec.map (functionFieldMapOfDominant p) :=
  (functionFieldMapOfDominant_isPullback p).isoPullback_hom_snd

example : (functionFieldMapOfDominant_isPullback p).isoPullback.inv ≫
    Y.fromSpecStalk (genericPoint Y) = pullback.fst p (X.fromSpecStalk (genericPoint X)) :=
  (functionFieldMapOfDominant_isPullback p).isoPullback_inv_fst

example : (functionFieldMapOfDominant_isPullback p).isoPullback.inv ≫
    Spec.map (functionFieldMapOfDominant p) = pullback.snd p (X.fromSpecStalk (genericPoint X)) :=
  (functionFieldMapOfDominant_isPullback p).isoPullback_inv_snd

example {W : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ Spec X.functionField)
    (h : a ≫ p = b ≫ X.fromSpecStalk (genericPoint X)) :
    (functionFieldMapOfDominant_isPullback p).lift a b h ≫
        Y.fromSpecStalk (genericPoint Y) = a ∧
      (functionFieldMapOfDominant_isPullback p).lift a b h ≫
        Spec.map (functionFieldMapOfDominant p) = b :=
  ⟨(functionFieldMapOfDominant_isPullback p).lift_fst a b h,
    (functionFieldMapOfDominant_isPullback p).lift_snd a b h⟩

example {W : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ Spec X.functionField)
    (h : a ≫ p = b ≫ X.fromSpecStalk (genericPoint X)) :
    ∃! k : W ⟶ Spec Y.functionField,
      k ≫ Y.fromSpecStalk (genericPoint Y) = a ∧
        k ≫ Spec.map (functionFieldMapOfDominant p) = b := by
  let square := functionFieldMapOfDominant_isPullback p
  refine ⟨square.lift a b h, ⟨square.lift_fst a b h, square.lift_snd a b h⟩, ?_⟩
  intro k hk
  exact square.hom_ext (hk.1.trans (square.lift_fst a b h).symm)
    (hk.2.trans (square.lift_snd a b h).symm)

example {W : Scheme.{u}} (a b : W ⟶ Spec Y.functionField)
    (hY : a ≫ Y.fromSpecStalk (genericPoint Y) = b ≫ Y.fromSpecStalk (genericPoint Y))
    (hK : a ≫ Spec.map (functionFieldMapOfDominant p) =
      b ≫ Spec.map (functionFieldMapOfDominant p)) : a = b :=
  (functionFieldMapOfDominant_isPullback p).hom_ext hY hK

example : (functionFieldMapOfDominant_isPullback p).isoPullback.hom ≫
      (functionFieldMapOfDominant_isPullback p).isoPullback.inv = 𝟙 (Spec Y.functionField) ∧
    (functionFieldMapOfDominant_isPullback p).isoPullback.inv ≫
      (functionFieldMapOfDominant_isPullback p).isoPullback.hom =
        𝟙 (pullback p (X.fromSpecStalk (genericPoint X))) :=
  ⟨(functionFieldMapOfDominant_isPullback p).isoPullback.hom_inv_id,
    (functionFieldMapOfDominant_isPullback p).isoPullback.inv_hom_id⟩

end ActualGenericFiber

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_isPushout_of_affine,
    `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_isPullback]
  unless declarations.length == 2 && declarations.eraseDups.length == 2 do
    throwError "Expected exactly two distinct SP97 declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP97 audit registry: two distinct public declarations"
