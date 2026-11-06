module

public import HodgeConjecture.Boundary.Normalization.GluedNormalization
public import HodgeConjecture.Boundary.Normalization.DeckAction

@[expose] public section

/-!
# Gluing the original normalization action

Automorphisms of the fixed extension over the original function field
preserve every original normalization chart and commute with its actual
restriction maps. Their natural automorphisms descend to the same glued
scheme, with the inverse-ring convention of the existing affine deck action.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NormalizationInertia SchemeCorrespondence

noncomputable section

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance normalizationActionAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

local instance normalizationActionScalarTower (U : NonemptyAffineChart X) :
    IsScalarTower Γ(X, U.val) X.functionField N :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The existing inverse-ring deck automorphism on an original affine chart. -/
def affineNormalizationChartAutomorphism (σ : N ≃ₐ[X.functionField] N)
    (U : NonemptyAffineChart X) :
    (affineNormalizationDiagram X N).obj U ≅ (affineNormalizationDiagram X N).obj U :=
  normalClosureNormalizationSchemeIso (B := Γ(X, U.val)) σ

/-- The original affine automorphisms commute with the actual restriction maps. -/
theorem affineNormalizationChartAutomorphism_naturality
    (σ : N ≃ₐ[X.functionField] N) {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫
        (affineNormalizationChartAutomorphism X N σ V).hom =
      (affineNormalizationChartAutomorphism X N σ U).hom ≫
        (affineNormalizationDiagram X N).map f := by
  letI : Algebra Γ(X, V.val) Γ(X, U.val) :=
    (X.presheaf.map (homOfLE (leOfHom f)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, V.val) Γ(X, U.val) N :=
    sectionRestriction_ambientScalarTower V.val U.val N (leOfHom f)
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

/-- The original chart automorphisms form an automorphism of the original diagram. -/
def affineNormalizationDiagramAutomorphism (σ : N ≃ₐ[X.functionField] N) :
    affineNormalizationDiagram X N ≅ affineNormalizationDiagram X N :=
  NatIso.ofComponents (affineNormalizationChartAutomorphism X N σ)
    (fun f => affineNormalizationChartAutomorphism_naturality X N σ f)

/-- Descent acts on the original glued scheme, not a replacement normalization. -/
def gluedNormalizationAutomorphism (σ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationModel X N ≅ gluedNormalizationModel X N :=
  HasColimit.isoOfNatIso (affineNormalizationDiagramAutomorphism X N σ)

/-- The global automorphism restricts to the same original affine deck map. -/
theorem normalizationChartToGlued_comp_automorphism
    (σ : N ≃ₐ[X.functionField] N) (U : NonemptyAffineChart X) :
    normalizationChartToGlued X N U ≫ (gluedNormalizationAutomorphism X N σ).hom =
      (affineNormalizationChartAutomorphism X N σ U).hom ≫
        normalizationChartToGlued X N U :=
  HasColimit.isoOfNatIso_ι_hom (affineNormalizationDiagramAutomorphism X N σ) U

/-- The descended automorphism lies over the original base scheme. -/
theorem gluedNormalizationAutomorphism_comp_toBase (σ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationAutomorphism X N σ).hom ≫ gluedNormalizationToBase X N =
      gluedNormalizationToBase X N := by
  apply gluedNormalization_hom_ext X N
  intro U
  rw [← Category.assoc, normalizationChartToGlued_comp_automorphism,
    Category.assoc, normalizationChartToGlued_comp_toBase]
  change (normalClosureNormalizationSchemeIso (B := Γ(X, U.val)) σ).hom ≫
      normalClosureNormalizationToBase (B := Γ(X, U.val)) (N := N) ≫
        U.property.1.fromSpec =
    normalClosureNormalizationToBase (B := Γ(X, U.val)) (N := N) ≫ U.property.1.fromSpec
  rw [← Category.assoc, normalClosureNormalizationSchemeIso_hom_comp_toBase]

/-- The identity field automorphism descends to the identity morphism. -/
theorem gluedNormalizationAutomorphism_one :
    (gluedNormalizationAutomorphism X N 1).hom = 𝟙 _ := by
  apply gluedNormalization_hom_ext X N
  intro U
  rw [normalizationChartToGlued_comp_automorphism, Category.comp_id]
  have h : (affineNormalizationChartAutomorphism X N 1 U).hom = 𝟙 _ := by
    change Spec.map _ = 𝟙 _
    rw [← Spec.map_id]
    congr 1
  rw [h, Category.id_comp]

/-- Multiplication follows the existing inverse-ring/automorphism convention. -/
theorem gluedNormalizationAutomorphism_mul (σ τ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationAutomorphism X N (σ * τ)).hom =
      (gluedNormalizationAutomorphism X N τ).hom ≫
        (gluedNormalizationAutomorphism X N σ).hom := by
  apply gluedNormalization_hom_ext X N
  intro U
  rw [normalizationChartToGlued_comp_automorphism,
    ← Category.assoc, normalizationChartToGlued_comp_automorphism,
    Category.assoc, normalizationChartToGlued_comp_automorphism, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The fixed field-extension automorphisms act over the original structural map. -/
def gluedNormalizationDeckAction :
    (N ≃ₐ[X.functionField] N) →* DeckTransformation (gluedNormalizationToBase X N) where
  toFun σ := CategoryTheory.Aut.of <| Over.isoMk (gluedNormalizationAutomorphism X N σ)
    (gluedNormalizationAutomorphism_comp_toBase X N σ)
  map_one' := by
    apply CategoryTheory.Aut.hom_ext
    apply Over.OverMorphism.ext
    exact gluedNormalizationAutomorphism_one X N
  map_mul' σ τ := by
    apply CategoryTheory.Aut.hom_ext
    apply Over.OverMorphism.ext
    exact gluedNormalizationAutomorphism_mul X N σ τ

/-- The packaged deck action retains exactly the constructed global morphism. -/
theorem gluedNormalizationDeckAction_hom (σ : N ≃ₐ[X.functionField] N) :
    (gluedNormalizationDeckAction X N σ).hom.left =
      (gluedNormalizationAutomorphism X N σ).hom := rfl

end

end HodgeConjecture.CollisionFoundations
