import HodgeConjecture.Boundary.Normalization.GluedNormalizationFunctionField
import HodgeConjecture.Boundary.Normalization.GluedNormalizationAction

/-!
# Comparing the original glued action with field pullback

The existing inverse-ring convention sends a field automorphism to a
scheme automorphism whose generic pullback is its inverse. Under the
original field identification this proves faithfulness of the glued action.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles NormalizationInertia

noncomputable section

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable [FiniteDimensional X.functionField N]

local instance actionComparisonAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

local instance actionComparisonScalarTower (U : NonemptyAffineChart X) :
    IsScalarTower Γ(X, U.val) X.functionField N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance actionComparisonChartIntegral (U : NonemptyAffineChart X) :
    IsIntegral ((affineNormalizationDiagram X N).obj U) := by
  change IsIntegral (normalizedAffineModel Γ(X, U.val) N)
  unfold normalizedAffineModel
  infer_instance

local instance actionComparisonChartFieldAlgebra (U : NonemptyAffineChart X) :
    Algebra (normalizedCoordinateRing Γ(X, U.val) N)
      ((affineNormalizationDiagram X N).obj U).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (.of (normalizedCoordinateRing Γ(X, U.val) N))

local instance actionComparisonChartFieldFractionRing (U : NonemptyAffineChart X) :
    IsFractionRing (normalizedCoordinateRing Γ(X, U.val) N)
      ((affineNormalizationDiagram X N).obj U).functionField :=
  functionField_isFractionRing_of_affine (.of (normalizedCoordinateRing Γ(X, U.val) N))

/-- On the original chart, generic pullback is the inverse field automorphism. -/
theorem affineNormalizationFunctionFieldEquiv_automorphism
    (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X)
    (a : ((affineNormalizationDiagram X N).obj U).functionField) :
    affineNormalizationFunctionFieldEquiv X N U
        (functionFieldMapOfDominant (affineNormalizationChartAutomorphism X N σ U).hom a) =
      σ.symm (affineNormalizationFunctionFieldEquiv X N U a) := by
  let r := (normalClosureNormalizationRingEquiv (B := Γ(X, U.val)) σ).toRingEquiv.toCommRingCatIso.inv
  letI : IsDominant (Spec.map r) :=
    inferInstanceAs (IsDominant (affineNormalizationChartAutomorphism X N σ U).hom)
  have h : (affineNormalizationFunctionFieldEquiv X N U).toRingHom.comp
      (functionFieldMapOfDominant (affineNormalizationChartAutomorphism X N σ U).hom).hom =
      σ.symm.toRingHom.comp (affineNormalizationFunctionFieldEquiv X N U).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := normalizedCoordinateRing Γ(X, U.val) N)
    intro t
    change affineNormalizationFunctionFieldEquiv X N U
      (functionFieldMapOfDominant (affineNormalizationChartAutomorphism X N σ U).hom
        (algebraMap (normalizedCoordinateRing Γ(X, U.val) N) _ t)) =
      σ.symm (affineNormalizationFunctionFieldEquiv X N U (algebraMap _ _ t))
    erw [functionFieldMapOfDominant_spec_algebraMap r t]
    erw [affineNormalizationFunctionFieldEquiv_algebraMap X N U (r t),
      affineNormalizationFunctionFieldEquiv_algebraMap X N U t]
    rfl
  exact DFunLike.congr_fun h a

/-- The same inverse-pullback formula holds through every original chart. -/
theorem gluedNormalizationFunctionFieldEquivAt_automorphism
    (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X)
    (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquivAt X N U
        (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom a) =
      σ.symm (gluedNormalizationFunctionFieldEquivAt X N U a) := by
  have he : functionFieldMapOfDominant
      (normalizationChartToGlued X N U ≫ (gluedNormalizationAutomorphism X N σ).hom) =
      functionFieldMapOfDominant
        ((affineNormalizationChartAutomorphism X N σ U).hom ≫
          normalizationChartToGlued X N U) := by
    congr 1
    exact normalizationChartToGlued_comp_automorphism X N σ U
  rw [functionFieldMapOfDominant_comp, functionFieldMapOfDominant_comp] at he
  have h := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) a
  change functionFieldMapOfDominant (normalizationChartToGlued X N U)
      (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom a) =
    functionFieldMapOfDominant (affineNormalizationChartAutomorphism X N σ U).hom
      (functionFieldMapOfDominant (normalizationChartToGlued X N U) a) at h
  rw [gluedNormalizationFunctionFieldEquivAt_apply_chart,
    gluedNormalizationFunctionFieldEquivAt_apply_chart, h,
    affineNormalizationFunctionFieldEquiv_automorphism]

/-- The canonical global comparison intertwines actual pullback with the inverse action. -/
theorem gluedNormalizationFunctionFieldEquiv_automorphism
    (σ : N ≃ₐ[X.functionField] N) (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom a) =
      σ.symm (gluedNormalizationFunctionFieldEquiv X N a) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  let A : NonemptyAffineChart X := ⟨U, hU, ⟨⟨genericPoint X, hx⟩⟩⟩
  rw [gluedNormalizationFunctionFieldEquiv_apply_chart X N A,
    gluedNormalizationFunctionFieldEquiv_apply_chart X N A]
  exact gluedNormalizationFunctionFieldEquivAt_automorphism X N σ A a

/-- The original deck action is faithful for a finite ambient extension. -/
theorem gluedNormalizationDeckAction_injective :
    Function.Injective (gluedNormalizationDeckAction X N) := by
  intro σ τ h
  have hm : (gluedNormalizationAutomorphism X N σ).hom =
      (gluedNormalizationAutomorphism X N τ).hom :=
    congrArg (fun d => d.hom.left) h
  have hf : functionFieldMapOfDominant (gluedNormalizationAutomorphism X N σ).hom =
      functionFieldMapOfDominant (gluedNormalizationAutomorphism X N τ).hom := by
    congr 1
  apply inv_injective
  apply AlgEquiv.ext
  intro x
  letI : Surjective (gluedNormalizationToBase X N) :=
    gluedNormalizationToBase_surjective X N
  letI : Algebra X.functionField (gluedNormalizationModel X N).functionField :=
    (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra
  obtain ⟨a, rfl⟩ := (gluedNormalizationFunctionFieldEquiv X N).surjective x
  change σ.symm (gluedNormalizationFunctionFieldEquiv X N a) =
    τ.symm (gluedNormalizationFunctionFieldEquiv X N a)
  rw [← gluedNormalizationFunctionFieldEquiv_automorphism X N σ,
    ← gluedNormalizationFunctionFieldEquiv_automorphism X N τ, hf]

end

end HodgeConjecture.CollisionFoundations
