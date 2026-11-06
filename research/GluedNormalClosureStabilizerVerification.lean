module

import HodgeConjecture.Boundary.Normalization.GluedNormalClosureStabilizer
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP96 focused checks for the exact stabilizer of the original marked refinement.
Run with `lake env lean research/GluedNormalClosureStabilizerVerification.lean`.

The input is the same finite dominant map of integral schemes and normal
stalks upstairs. The fixtures retain the actual embedding and marked action.
No étaleness, separability, perfectness, normal base or finite normalization
premise is supplied. A full marked deck group is not a fiber/torsor statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open HodgeConjecture.SchemeCorrespondence

noncomputable section

universe u

#check gluedNormalizationAutomorphism_comp_toCover_iff
#check gluedNormalClosureDeckTransformation_comp_toCover_iff
#check gluedNormalClosureMarkedDeckAction_injective
#check gluedNormalClosureMarkedDeckAction_surjective
#check gluedNormalClosureMarkedDeckEquiv
#check gluedNormalClosureMarkedDeckEquiv_symm_apply

local instance verificationOverIntegral {A B : Scheme.{u}} [IsIntegral A] (f : A ⟶ B) :
    IsIntegral (Over.mk f).left := inferInstanceAs (IsIntegral A)

local instance verificationBaseSurjective (X : Scheme.{u}) [IsIntegral X]
    (N : Type u) [Field N] [Algebra X.functionField N]
    [FiniteDimensional X.functionField N] : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance verificationBaseFieldAlgebra (X : Scheme.{u}) [IsIntegral X]
    (N : Type u) [Field N] [Algebra X.functionField N]
    [FiniteDimensional X.functionField N] :
    Algebra X.functionField (gluedNormalizationModel X N).functionField :=
  (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).galoisGroup,
      (gluedNormalizationAutomorphism X Nₚ σ).hom ≫ gluedNormalClosureToCover p hY =
          gluedNormalClosureToCover p hY ↔
        σ ∈ (functionFieldNormalClosureData p).intermediateFixingSubgroup :=
  gluedNormalizationAutomorphism_comp_toCover_iff p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).galoisGroup,
      (gluedNormalizationAutomorphism X Nₚ σ).hom ≫ gluedNormalClosureToCover p hY =
          gluedNormalClosureToCover p hY →
        σ ∈ (functionFieldNormalClosureData p).intermediateFixingSubgroup := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ h
  exact (gluedNormalizationAutomorphism_comp_toCover_iff p hY σ).mp h

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).galoisGroup,
      σ ∈ (functionFieldNormalClosureData p).intermediateFixingSubgroup →
        (gluedNormalizationAutomorphism X Nₚ σ).hom ≫ gluedNormalClosureToCover p hY =
          gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ h
  exact (gluedNormalizationAutomorphism_comp_toCover_iff p hY σ).mpr h

-- The stabilizer refers to the original embedding, not another conjugate field.
example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).galoisGroup,
      (gluedNormalizationAutomorphism X Nₚ σ).hom ≫ gluedNormalClosureToCover p hY =
          gluedNormalClosureToCover p hY ↔
        ∀ c : Y.functionField,
          σ ((functionFieldNormalClosureData p).embedding c) =
            (functionFieldNormalClosureData p).embedding c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  rw [gluedNormalizationAutomorphism_comp_toCover_iff p hY]
  constructor
  · intro h c
    exact (IntermediateField.mem_fixingSubgroup_iff
      (functionFieldNormalClosureData p).intermediateField σ).mp h _ ⟨c, rfl⟩
  · intro h
    apply (IntermediateField.mem_fixingSubgroup_iff
      (functionFieldNormalClosureData p).intermediateField σ).mpr
    rintro z ⟨c, rfl⟩
    exact h c

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ (σ : (functionFieldNormalClosureData p).galoisGroup)
      (_h : (gluedNormalizationAutomorphism X Nₚ σ).hom ≫ gluedNormalClosureToCover p hY =
        gluedNormalClosureToCover p hY) (c : Y.functionField),
      σ.symm ((functionFieldNormalClosureData p).embedding c) =
        (functionFieldNormalClosureData p).embedding c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ h c
  have hs := (gluedNormalizationAutomorphism_comp_toCover_iff p hY σ).mp h
  exact (IntermediateField.mem_fixingSubgroup_iff
    (functionFieldNormalClosureData p).intermediateField σ⁻¹).mp
    ((functionFieldNormalClosureData p).intermediateFixingSubgroup.inv_mem hs) _ ⟨c, rfl⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ d : DeckTransformation (gluedNormalizationToBase X Nₚ),
      d.hom.left ≫ gluedNormalClosureToCover p hY = gluedNormalClosureToCover p hY ↔
        gluedNormalizationDeckFieldAutomorphism X Nₚ d ∈
          (functionFieldNormalClosureData p).intermediateFixingSubgroup :=
  gluedNormalClosureDeckTransformation_comp_toCover_iff p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ d : DeckTransformation (gluedNormalizationToBase X Nₚ),
      d.hom.left ≫ gluedNormalClosureToCover p hY = gluedNormalClosureToCover p hY →
        gluedNormalizationDeckFieldAutomorphism X Nₚ d ∈
          (functionFieldNormalClosureData p).intermediateFixingSubgroup := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro d h
  exact (gluedNormalClosureDeckTransformation_comp_toCover_iff p hY d).mp h

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Function.Injective (gluedNormalClosureMarkedDeckAction p hY) :=
  gluedNormalClosureMarkedDeckAction_injective p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Function.Surjective (gluedNormalClosureMarkedDeckAction p hY) :=
  gluedNormalClosureMarkedDeckAction_surjective p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ τ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      gluedNormalClosureMarkedDeckAction p hY σ = gluedNormalClosureMarkedDeckAction p hY τ ↔
        σ = τ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ τ
  exact (gluedNormalClosureMarkedDeckAction_injective p hY).eq_iff

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureData p).intermediateFixingSubgroup ≃*
      DeckTransformation (gluedNormalClosureToCover p hY) :=
  gluedNormalClosureMarkedDeckEquiv p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (gluedNormalClosureMarkedDeckEquiv p hY).toMonoidHom =
      gluedNormalClosureMarkedDeckAction p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rfl

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalClosureMarkedDeckEquiv p hY σ).hom.left =
        (gluedNormalizationAutomorphism X Nₚ σ.val).hom := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  exact gluedNormalClosureMarkedDeckAction_hom p hY σ

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalClosureMarkedDeckEquiv p hY).symm
        (gluedNormalClosureMarkedDeckAction p hY σ) = σ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  exact (gluedNormalClosureMarkedDeckEquiv p hY).symm_apply_apply σ

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ d : DeckTransformation (gluedNormalClosureToCover p hY),
      gluedNormalClosureMarkedDeckAction p hY ((gluedNormalClosureMarkedDeckEquiv p hY).symm d) =
        d := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro d
  exact (gluedNormalClosureMarkedDeckEquiv p hY).apply_symm_apply d

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ τ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      gluedNormalClosureMarkedDeckEquiv p hY (σ * τ) =
        gluedNormalClosureMarkedDeckEquiv p hY σ * gluedNormalClosureMarkedDeckEquiv p hY τ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ τ
  exact (gluedNormalClosureMarkedDeckEquiv p hY).map_mul σ τ

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureMarkedDeckEquiv p hY 1 = 1 := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact (gluedNormalClosureMarkedDeckEquiv p hY).map_one

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      gluedNormalClosureMarkedDeckEquiv p hY σ⁻¹ = (gluedNormalClosureMarkedDeckEquiv p hY σ)⁻¹ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  exact map_inv (gluedNormalClosureMarkedDeckEquiv p hY) σ

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ d e : DeckTransformation (gluedNormalClosureToCover p hY),
      (gluedNormalClosureMarkedDeckEquiv p hY).symm (d * e) =
        (gluedNormalClosureMarkedDeckEquiv p hY).symm d *
          (gluedNormalClosureMarkedDeckEquiv p hY).symm e := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro d e
  exact (gluedNormalClosureMarkedDeckEquiv p hY).symm.map_mul d e

-- Every inverse image belongs to the subgroup fixing the original embedding.
example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ (d : DeckTransformation (gluedNormalClosureToCover p hY)) (c : Y.functionField),
      ((gluedNormalClosureMarkedDeckEquiv p hY).symm d).val
          ((functionFieldNormalClosureData p).embedding c) =
        (functionFieldNormalClosureData p).embedding c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro d c
  exact (IntermediateField.mem_fixingSubgroup_iff
    (functionFieldNormalClosureData p).intermediateField
    ((gluedNormalClosureMarkedDeckEquiv p hY).symm d).val).mp
    ((gluedNormalClosureMarkedDeckEquiv p hY).symm d).property _ ⟨c, rfl⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ (d : DeckTransformation (gluedNormalClosureToCover p hY)) (x : Nₚ),
      ((gluedNormalClosureMarkedDeckEquiv p hY).symm d).val x =
        gluedNormalizationFunctionFieldEquiv X Nₚ
          (functionFieldMapOfDominant d.inv.left
            ((gluedNormalizationFunctionFieldEquiv X Nₚ).symm x)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro d x
  exact gluedNormalClosureMarkedDeckEquiv_symm_apply p hY d x

-- The exact scope still has no geometric or field-theoretic strengthening.
example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureData p).intermediateFixingSubgroup ≃*
      DeckTransformation (gluedNormalClosureToCover p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField Y.functionField := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsFinite (gluedNormalizationToBase X Nₚ) := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact gluedNormalClosureMarkedDeckEquiv p hY

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.gluedNormalizationAutomorphism_comp_toCover_iff,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureDeckTransformation_comp_toCover_iff,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureMarkedDeckAction_injective,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureMarkedDeckAction_surjective,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureMarkedDeckEquiv,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureMarkedDeckEquiv_symm_apply]
  unless declarations.length == 6 && declarations.eraseDups.length == 6 do
    throwError "Expected exactly six distinct SP96 declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP96 audit registry: six distinct public declarations"
