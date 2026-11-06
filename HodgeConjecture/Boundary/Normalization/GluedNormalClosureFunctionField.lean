module

public import HodgeConjecture.Boundary.Normalization.GluedNormalizationFunctionField

@[expose] public section

/-!
# The original marked refinement on function fields

The function-field comparison for the original glued normalization sends
pullback through its refinement to the original marked embedding. The proof
uses the actual whole affine inverse image and cancels its canonical
normalization isomorphism; no replacement embedding is chosen.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles NormalizationInertia

noncomputable section

universe u

local instance markedComparisonAffineIntegral
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] :
    IsIntegral (normalizedAffineModel B E) := by
  unfold normalizedAffineModel
  infer_instance

local instance markedComparisonAffineAlgebra
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] :
    Algebra (normalizedCoordinateRing B E)
      (normalizedAffineModel B E).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec
    (.of (normalizedCoordinateRing B E))

local instance markedComparisonAffineFractionRing
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] :
    IsFractionRing (normalizedCoordinateRing B E)
      (normalizedAffineModel B E).functionField :=
  functionField_isFractionRing_of_affine (.of (normalizedCoordinateRing B E))

local instance markedComparisonNormalClosureIntegral
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] :
    IsIntegral (normalClosureNormalization (B := B) (N := E)) :=
  markedComparisonAffineIntegral B E

local instance markedComparisonIntermediateIntegral
    (B E : Type u) [CommRing B] [Field E] [Algebra B E] :
    IsIntegral (intermediateNormalization (B := B) (L := E)) :=
  markedComparisonAffineIntegral B E

section IntermediateComparison

variable {Y : Scheme.{u}} [IsIntegral Y]
variable (V : Y.Opens) [Nonempty V] (hV : IsAffineOpen V)
variable (B : Type u) [CommRing B]
variable [Algebra B Γ(Y, V)] [Algebra B Y.functionField]
variable [IsScalarTower B Γ(Y, V) Y.functionField]
variable [Module.Finite B Γ(Y, V)] [IsIntegrallyClosed Γ(Y, V)]
variable [IsFractionRing Γ(Y, V) Y.functionField]

/-- Cancel the actual intermediate normalization isomorphism on generic
coordinates, using its forward map rather than choosing an inverse marking. -/
private theorem intermediateNormalizationInverse_functionField_algebraMap
    (t : normalizedCoordinateRing B Y.functionField) :
    functionFieldMapOfDominant
        ((hV.isoSpec ≪≫ intermediateNormalizationIso
          (B := B) (A := Γ(Y, V)) (E := Y.functionField)).inv ≫ V.ι)
        (t : Y.functionField) =
      algebraMap (normalizedCoordinateRing B Y.functionField)
        (normalizedAffineModel B Y.functionField).functionField t := by
  let e := intermediateNormalizationIso
    (B := B) (A := Γ(Y, V)) (E := Y.functionField)
  let f := (hV.isoSpec ≪≫ e).inv ≫ V.ι
  let r₀ := CommRingCat.ofHom (normalizationToIntermediate
    (B := B) (A := Γ(Y, V)) (E := Y.functionField)).toRingHom
  letI : IsDominant (Spec.map r₀) :=
    specMap_isDominant_of_injective r₀
      (normalizationToIntermediate_injective (B := B) (A := Γ(Y, V))
        (E := Y.functionField))
  have hf : e.hom ≫ f = hV.fromSpec := by
    simp only [f, Iso.trans_inv, Category.assoc, Iso.hom_inv_id_assoc,
      IsAffineOpen.isoSpec_inv_ι]
  apply functionFieldMapOfDominant_injective e.hom
  have he : functionFieldMapOfDominant (e.hom ≫ f) =
      functionFieldMapOfDominant hV.fromSpec := by
    congr 1
  rw [functionFieldMapOfDominant_comp] at he
  have hc : functionFieldMapOfDominant e.hom
      (functionFieldMapOfDominant f (t : Y.functionField)) =
      functionFieldMapOfDominant hV.fromSpec (t : Y.functionField) :=
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) (t : Y.functionField)
  change functionFieldMapOfDominant e.hom
    (functionFieldMapOfDominant f (t : Y.functionField)) = _
  rw [hc]
  have ht : (t : Y.functionField) =
      Y.germToFunctionField V
        (normalizationToIntermediate (B := B) (A := Γ(Y, V))
          (E := Y.functionField) t) :=
    (algebraMap_normalizationToIntermediate (B := B) (A := Γ(Y, V))
      (E := Y.functionField) t).symm
  rw [ht, functionFieldMapOfDominant_fromSpec_germ]
  erw [functionFieldMapOfDominant_spec_algebraMap r₀ t]
  rfl

end IntermediateComparison

section ActualMarkedRefinement

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

/-- Every original chart comparison carries the actual marked refinement
to the embedding in the original normal-closure data. -/
theorem gluedNormalClosureFunctionFieldEquivAt_toCover
    (U : NonemptyAffineChart X) (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    gluedNormalizationFunctionFieldEquivAt X Nₚ U
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) =
      (functionFieldNormalClosureData p).embedding c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : FiniteDimensional X.functionField Y.functionField :=
    functionFieldMapOfDominant_finiteDimensional p
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  letI : Nonempty (p ⁻¹ᵁ U.val) := nonempty_preimage_of_isDominant p U.val
  letI : Algebra Γ(X, U.val) Γ(Y, p ⁻¹ᵁ U.val) := (p.app U.val).hom.toAlgebra
  letI : Algebra Γ(X, U.val) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U.val)).hom.comp (p.app U.val).hom).toAlgebra
  letI : Algebra Γ(X, U.val) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U.val).hom).toAlgebra
  letI : IsScalarTower Γ(X, U.val) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U.val
  letI : IsScalarTower Γ(X, U.val) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U.val) Γ(Y, p ⁻¹ᵁ U.val) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U.val) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U.val U.property.1
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U.val) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (U.property.1.preimage p)
  letI : IsFractionRing (normalizedCoordinateRing Γ(X, U.val) Y.functionField)
      Y.functionField :=
    integralClosure.isFractionRing_of_finite_extension X.functionField Y.functionField
  letI : Module.Finite Γ(X, U.val) Γ(Y, p ⁻¹ᵁ U.val) :=
    finiteAffinePreimage_moduleFinite p U.val U.property.1
  letI : IsIntegrallyClosed Γ(Y, p ⁻¹ᵁ U.val) :=
    affineSections_isIntegrallyClosed_of_stalks (U.property.1.preimage p)
      (fun y => hY y.val)
  letI : IsIntegral ((affineNormalizationDiagram X Nₚ).obj U) := by
    change IsIntegral (normalizedAffineModel Γ(X, U.val) Nₚ)
    infer_instance
  let η := finiteAffinePreimageNormalizationIso p U.val U.property.1
    (fun y => hY y.val)
  let f := η.inv ≫ (p ⁻¹ᵁ U.val).ι
  let r := normalClosureToIntermediateNormalization (B := Γ(X, U.val))
    (functionFieldNormalClosureData p)
  let r₀ := CommRingCat.ofHom (normalizationMap Nₚ
    (normalClosureEmbeddingOverBase (B := Γ(X, U.val))
      (functionFieldNormalClosureData p))).toRingHom
  letI : IsDominant (Spec.map r₀) :=
    specMap_isDominant_of_injective r₀
      (normalizationMap_injective _ _
        (normalClosureEmbeddingOverBase (B := Γ(X, U.val))
          (functionFieldNormalClosureData p)).injective)
  letI : IsDominant r := inferInstanceAs (IsDominant (Spec.map r₀))
  have hchart : normalizationChartToGlued X Nₚ U ≫
      gluedNormalClosureToCover p hY = r ≫ f := by
    rw [normalizationChartToGlued_comp_toCover]
    simp only [finiteEtaleAffineNormalClosureToPreimage, r, f, η, Category.assoc]
  have h : (gluedNormalizationFunctionFieldEquivAt X Nₚ U).toRingHom.comp
      (functionFieldMapOfDominant (gluedNormalClosureToCover p hY)).hom =
      (functionFieldNormalClosureData p).embedding.toRingHom := by
    apply IsFractionRing.ringHom_ext
      (A := normalizedCoordinateRing Γ(X, U.val) Y.functionField)
    intro t
    change gluedNormalizationFunctionFieldEquivAt X Nₚ U
      (functionFieldMapOfDominant (gluedNormalClosureToCover p hY)
        (t : Y.functionField)) = _
    rw [gluedNormalizationFunctionFieldEquivAt_apply_chart]
    have he : functionFieldMapOfDominant
        (normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY) =
        functionFieldMapOfDominant (r ≫ f) := by
      congr 1
    rw [functionFieldMapOfDominant_comp, functionFieldMapOfDominant_comp] at he
    have hc : functionFieldMapOfDominant (normalizationChartToGlued X Nₚ U)
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY)
          (t : Y.functionField)) =
        functionFieldMapOfDominant r (functionFieldMapOfDominant f (t : Y.functionField)) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) (t : Y.functionField)
    rw [hc]
    have ht : functionFieldMapOfDominant f (t : Y.functionField) =
        algebraMap (normalizedCoordinateRing Γ(X, U.val) Y.functionField)
          (normalizedAffineModel Γ(X, U.val) Y.functionField).functionField t :=
      intermediateNormalizationInverse_functionField_algebraMap
        (p ⁻¹ᵁ U.val) (U.property.1.preimage p) Γ(X, U.val) t
    rw [ht]
    erw [functionFieldMapOfDominant_spec_algebraMap r₀ t]
    erw [affineNormalizationFunctionFieldEquiv_algebraMap X Nₚ U (r₀ t)]
    rfl
  exact DFunLike.congr_fun h c

/-- The canonical global comparison retains the original marked embedding
of the upstairs function field, without an étaleness hypothesis. -/
theorem gluedNormalClosureFunctionFieldEquiv_toCover (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    gluedNormalizationFunctionFieldEquiv X Nₚ
        (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c) =
      (functionFieldNormalClosureData p).embedding c := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := genericPoint X) (by trivial)
  let A : NonemptyAffineChart X := ⟨U, hU, ⟨⟨genericPoint X, hx⟩⟩⟩
  rw [gluedNormalizationFunctionFieldEquiv_apply_chart X Nₚ A]
  exact gluedNormalClosureFunctionFieldEquivAt_toCover p hY A c

end ActualMarkedRefinement

end

end HodgeConjecture.CollisionFoundations
