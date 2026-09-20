import HodgeConjecture.Boundary.Normalization.GluedNormalClosureAction
import Lean.Util.CollectAxioms

/-!
SP90 regressions for the compatible action on the original glued normalization.
Run with `lake env lean research/GluedNormalizationActionVerification.lean`.

The generic action retains the original germ scalars, affine automorphisms,
restriction maps, and glued scheme. Tests check the inverse-ring convention,
identity and multiplication, actual chart formulas, and invariance over the
base without finite-extension, algebraicity, or normal-base assumptions.
The marked specialization tests only the subgroup fixing the original copy
of the upstairs function field for invariance over the original cover.
No faithfulness, torsor property, or stabilizer converse is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open HodgeConjecture.NormalizationInertia HodgeConjecture.SchemeCorrespondence

noncomputable section

universe u

section ArbitraryFieldExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance actionVerificationAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

local instance actionVerificationScalarTower (U : NonemptyAffineChart X) :
    IsScalarTower Γ(X, U.val) X.functionField N :=
  IsScalarTower.of_algebraMap_eq' rfl

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    algebraMap Γ(X, U.val) N b =
      algebraMap X.functionField N ((X.germToFunctionField U.val).hom b) := rfl

example (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X) :
    affineNormalizationChartAutomorphism X N σ U =
      normalClosureNormalizationSchemeIso (B := Γ(X, U.val)) σ := rfl

example (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X) :
    (affineNormalizationDiagramAutomorphism X N σ).hom.app U =
      (affineNormalizationChartAutomorphism X N σ U).hom := rfl

example (σ : N ≃ₐ[X.functionField] N) {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫
        (affineNormalizationChartAutomorphism X N σ V).hom =
      (affineNormalizationChartAutomorphism X N σ U).hom ≫
        (affineNormalizationDiagram X N).map f :=
  affineNormalizationChartAutomorphism_naturality X N σ f

example (σ : N ≃ₐ[X.functionField] N) {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫
        (affineNormalizationChartAutomorphism X N σ V).inv =
      (affineNormalizationChartAutomorphism X N σ U).inv ≫
        (affineNormalizationDiagram X N).map f := by
  apply (cancel_mono (affineNormalizationChartAutomorphism X N σ V).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    affineNormalizationChartAutomorphism_naturality, Iso.inv_hom_id_assoc]

example (σ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationAutomorphism X N σ =
      HasColimit.isoOfNatIso (affineNormalizationDiagramAutomorphism X N σ) := rfl

example (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X) :
    normalizationChartToGlued X N U ≫ (gluedNormalizationAutomorphism X N σ).hom =
      (affineNormalizationChartAutomorphism X N σ U).hom ≫
        normalizationChartToGlued X N U := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsAlgebraic X.functionField N := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U.val) := inferInstance
  exact normalizationChartToGlued_comp_automorphism X N σ U

example (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X)
    (a : (affineNormalizationDiagram X N).obj U) :
    (gluedNormalizationAutomorphism X N σ).hom.base
        ((normalizationChartToGlued X N U).base a) =
      (normalizationChartToGlued X N U).base
        ((affineNormalizationChartAutomorphism X N σ U).hom.base a) := by
  rw [← Scheme.comp_base_apply, normalizationChartToGlued_comp_automorphism]
  rfl

example (σ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationAutomorphism X N σ).hom ≫ gluedNormalizationToBase X N =
      gluedNormalizationToBase X N :=
  gluedNormalizationAutomorphism_comp_toBase X N σ

example (σ : N ≃ₐ[X.functionField] N) (z : gluedNormalizationModel X N) :
    (gluedNormalizationToBase X N).base ((gluedNormalizationAutomorphism X N σ).hom.base z) =
      (gluedNormalizationToBase X N).base z := by
  rw [← Scheme.comp_base_apply, gluedNormalizationAutomorphism_comp_toBase]

example : (gluedNormalizationAutomorphism X N 1).hom = 𝟙 _ :=
  gluedNormalizationAutomorphism_one X N

example (σ τ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationAutomorphism X N (σ * τ)).hom =
      (gluedNormalizationAutomorphism X N τ).hom ≫
        (gluedNormalizationAutomorphism X N σ).hom :=
  gluedNormalizationAutomorphism_mul X N σ τ

example (σ τ : N ≃ₐ[X.functionField] N) (z : gluedNormalizationModel X N) :
    (gluedNormalizationAutomorphism X N (σ * τ)).hom.base z =
      (gluedNormalizationAutomorphism X N σ).hom.base
        ((gluedNormalizationAutomorphism X N τ).hom.base z) := by
  rw [← Scheme.comp_base_apply, ← gluedNormalizationAutomorphism_mul]

example (σ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationAutomorphism X N σ).hom ≫
      (gluedNormalizationAutomorphism X N σ⁻¹).hom = 𝟙 _ := by
  rw [← gluedNormalizationAutomorphism_mul, inv_mul_cancel,
    gluedNormalizationAutomorphism_one]

example (σ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationDeckAction X N σ).hom.left =
      (gluedNormalizationAutomorphism X N σ).hom :=
  gluedNormalizationDeckAction_hom X N σ

example : gluedNormalizationDeckAction X N 1 = 1 :=
  (gluedNormalizationDeckAction X N).map_one

example (σ τ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationDeckAction X N (σ * τ) =
      gluedNormalizationDeckAction X N σ * gluedNormalizationDeckAction X N τ :=
  (gluedNormalizationDeckAction X N).map_mul σ τ

example (σ : N ≃ₐ[X.functionField] N) (V : X.Opens) (z : gluedNormalizationModel X N) :
    (gluedNormalizationAutomorphism X N σ).hom.base z ∈
        (gluedNormalizationToBase X N) ⁻¹ᵁ V ↔
      z ∈ (gluedNormalizationToBase X N) ⁻¹ᵁ V := by
  change (gluedNormalizationToBase X N).base
      ((gluedNormalizationAutomorphism X N σ).hom.base z) ∈ V ↔
    (gluedNormalizationToBase X N).base z ∈ V
  rw [← Scheme.comp_base_apply, gluedNormalizationAutomorphism_comp_toBase]

end ArbitraryFieldExtension

section MarkedAffineLeg

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

example (D : NormalClosureData K L N) (σ : D.intermediateFixingSubgroup) :
    (normalClosureNormalizationSchemeIso (B := B) (σ : D.galoisGroup)).hom ≫
        normalClosureToIntermediateNormalization (B := B) D =
      normalClosureToIntermediateNormalization (B := B) D := by
  fail_if_success have _ : IsFractionRing B K := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact normalClosureNormalizationSchemeIso_comp_toIntermediate (B := B) D σ

end MarkedAffineLeg

section ActualMarkedRefinement

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example (U : NonemptyAffineChart X) (b : Γ(X, U.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U.val) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
    algebraMap Γ(X, U.val) Nₚ b =
      algebraMap X.functionField Nₚ ((X.germToFunctionField U.val).hom b) := rfl

example (a : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding a : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) a :=
  functionFieldNormalClosureData_embedding_apply p a

example (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (affineNormalizationChartAutomorphism X Nₚ σ.val U).hom ≫
          finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) =
        finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
          (fun y => hY y.val) := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U.val) := inferInstance
  exact affineNormalizationChartAutomorphism_comp_toPreimage p hY U

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalizationAutomorphism X Nₚ σ.val).hom ≫ gluedNormalClosureToCover p hY =
        gluedNormalClosureToCover p hY := by
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact gluedNormalizationAutomorphism_comp_toCover p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ (σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup)
      (z : gluedNormalizationModel X Nₚ),
      (gluedNormalClosureToCover p hY).base
          ((gluedNormalizationAutomorphism X Nₚ σ.val).hom.base z) =
        (gluedNormalClosureToCover p hY).base z := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ z
  rw [← Scheme.comp_base_apply, gluedNormalizationAutomorphism_comp_toCover]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalClosureMarkedDeckAction p hY σ).hom.left =
        (gluedNormalizationAutomorphism X Nₚ σ.val).hom :=
  gluedNormalClosureMarkedDeckAction_hom p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalClosureMarkedDeckAction p hY σ).hom.left =
        (gluedNormalizationDeckAction X Nₚ σ.val).hom.left := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  rw [gluedNormalClosureMarkedDeckAction_hom, gluedNormalizationDeckAction_hom]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureMarkedDeckAction p hY 1 = 1 :=
  (gluedNormalClosureMarkedDeckAction p hY).map_one

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ τ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      gluedNormalClosureMarkedDeckAction p hY (σ * τ) =
        gluedNormalClosureMarkedDeckAction p hY σ *
          gluedNormalClosureMarkedDeckAction p hY τ :=
  (gluedNormalClosureMarkedDeckAction p hY).map_mul

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalClosureMarkedDeckAction p hY σ).hom.left ≫ gluedNormalClosureToCover p hY =
        gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  rw [gluedNormalClosureMarkedDeckAction_hom, gluedNormalizationAutomorphism_comp_toCover]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).galoisGroup,
      (gluedNormalizationDeckAction X Nₚ σ).hom.left ≫ gluedNormalizationToBase X Nₚ =
        gluedNormalizationToBase X Nₚ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  rw [gluedNormalizationDeckAction_hom, gluedNormalizationAutomorphism_comp_toBase]

end ActualMarkedRefinement

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.affineNormalizationChartAutomorphism,
    `HodgeConjecture.CollisionFoundations.affineNormalizationChartAutomorphism_naturality,
    `HodgeConjecture.CollisionFoundations.affineNormalizationDiagramAutomorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationAutomorphism,
    `HodgeConjecture.CollisionFoundations.normalizationChartToGlued_comp_automorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationAutomorphism_comp_toBase,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationAutomorphism_one,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationAutomorphism_mul,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckAction,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckAction_hom,
    `HodgeConjecture.CollisionFoundations.normalClosureNormalizationSchemeIso_comp_toIntermediate,
    `HodgeConjecture.CollisionFoundations.affineNormalizationChartAutomorphism_comp_toPreimage,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationAutomorphism_comp_toCover,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureMarkedDeckAction,
    `HodgeConjecture.CollisionFoundations.gluedNormalClosureMarkedDeckAction_hom]
  unless declarations.length == 15 do
    throwError "Expected exactly 15 SP90 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP90 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP90 audit registry: 15 distinct public declarations"
