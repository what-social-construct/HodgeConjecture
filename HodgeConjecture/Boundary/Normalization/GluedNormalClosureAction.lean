module

public import HodgeConjecture.Boundary.Normalization.GluedNormalizationAction
public import HodgeConjecture.Boundary.Normalization.GluedNormalClosureRefinement

@[expose] public section

/-!
# The marked subgroup action on the original glued refinement

The subgroup fixing the original embedded intermediate field preserves the
marked normalization leg. This identity passes through the original affine
inverse-image comparison and then through the exact glued chart formulas.
The resulting action lies over the original cover, with the same underlying
automorphisms as the full action over the base.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open NormalizationInertia SchemeCorrespondence SchemeCycles

noncomputable section

universe u

section MarkedAffineLeg

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

/-- The original inverse-ring automorphism preserves the marked intermediate
normalization leg when its field automorphism fixes the marked field. -/
theorem normalClosureNormalizationSchemeIso_comp_toIntermediate
    (D : NormalClosureData K L N) (σ : D.intermediateFixingSubgroup) :
    (normalClosureNormalizationSchemeIso (B := B) (σ : D.galoisGroup)).hom ≫
        normalClosureToIntermediateNormalization (B := B) D =
      normalClosureToIntermediateNormalization (B := B) D := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext x
  change (σ : D.galoisGroup).symm (D.embedding (x : L)) = D.embedding (x : L)
  exact (IntermediateField.mem_fixingSubgroup_iff D.intermediateField
    ((σ : D.galoisGroup)⁻¹)).mp
      (D.intermediateFixingSubgroup.inv_mem σ.property)
      (D.embedding (x : L)) ⟨x, rfl⟩

end MarkedAffineLeg

section ActualMarkedRefinement

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

/-- The marked subgroup preserves the original refinement to each whole
affine inverse image, not only its composite to the base. -/
theorem affineNormalizationChartAutomorphism_comp_toPreimage
    (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (affineNormalizationChartAutomorphism X Nₚ σ.val U).hom ≫
          finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) =
        finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
          (fun y => hY y.val) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
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
  apply (cancel_mono
    (finiteAffinePreimageNormalizationIso p U.val U.property.1 (fun y => hY y.val)).hom).mp
  rw [Category.assoc, finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso]
  exact normalClosureNormalizationSchemeIso_comp_toIntermediate
    (B := Γ(X, U.val)) (functionFieldNormalClosureData p) σ

/-- The marked subgroup preserves the original global refinement to the cover. -/
theorem gluedNormalizationAutomorphism_comp_toCover :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalizationAutomorphism X Nₚ σ.val).hom ≫ gluedNormalClosureToCover p hY =
        gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  apply gluedNormalization_hom_ext X Nₚ
  intro U
  rw [← Category.assoc, normalizationChartToGlued_comp_automorphism,
    Category.assoc, normalizationChartToGlued_comp_toCover,
    ← Category.assoc, affineNormalizationChartAutomorphism_comp_toPreimage]

/-- The subgroup fixing the marked intermediate field acts over the same
global refinement, without requiring the original map to be étale. -/
def gluedNormalClosureMarkedDeckAction :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureData p).intermediateFixingSubgroup →*
      DeckTransformation (gluedNormalClosureToCover p hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  refine
    { toFun := fun σ => CategoryTheory.Aut.of <| Over.isoMk (gluedNormalizationAutomorphism X Nₚ σ.val)
        (gluedNormalizationAutomorphism_comp_toCover p hY σ)
      map_one' := ?_
      map_mul' := ?_ }
  · apply CategoryTheory.Aut.hom_ext
    apply Over.OverMorphism.ext
    exact gluedNormalizationAutomorphism_one X Nₚ
  · intro σ τ
    apply CategoryTheory.Aut.hom_ext
    apply Over.OverMorphism.ext
    exact gluedNormalizationAutomorphism_mul X Nₚ σ.val τ.val

/-- The marked action retains the underlying morphism of the full action. -/
theorem gluedNormalClosureMarkedDeckAction_hom :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ σ : (functionFieldNormalClosureData p).intermediateFixingSubgroup,
      (gluedNormalClosureMarkedDeckAction p hY σ).hom.left =
        (gluedNormalizationAutomorphism X Nₚ σ.val).hom := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro σ
  rfl

end ActualMarkedRefinement

end

end HodgeConjecture.CollisionFoundations
