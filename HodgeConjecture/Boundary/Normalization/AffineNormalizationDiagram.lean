module

public import HodgeConjecture.Boundary.Normalization.AffineNormalizationOpenImmersion
public import Mathlib.AlgebraicGeometry.Gluing

@[expose] public section

/-!
# The locally directed diagram of actual normalization charts

Nonempty affine opens index the existing normalization models in one fixed
extension of the original function field. Their actual restriction morphisms
form a locally directed diagram of open immersions over the original scheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/-- The inclusion-ordered index of actual nonempty affine opens. -/
abbrev NonemptyAffineChart (X : Scheme.{u}) :=
  {U : X.Opens // IsAffineOpen U ∧ Nonempty U}

/-- Nonemptiness is retained from the original chart, not separately chosen. -/
instance nonemptyAffineChart_nonempty {X : Scheme.{u}} (U : NonemptyAffineChart X) :
    Nonempty U.val := U.property.2

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance normalizationDiagramAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

/-- The diagram uses the existing models and actual restriction maps. -/
def affineNormalizationDiagram : NonemptyAffineChart X ⥤ Scheme.{u} where
  obj U := normalizedAffineModel Γ(X, U.val) N
  map f := affineNormalizationRestriction _ _ N (leOfHom f)
  map_id U := affineNormalizationRestriction_self U.val N
  map_comp f g := (affineNormalizationRestriction_trans _ _ _ N
    (leOfHom g) (leOfHom f)).symm

/-- The original structural maps form a cocone to X. -/
def affineNormalizationBaseCocone : Cocone (affineNormalizationDiagram X N) where
  pt := X
  ι :=
    { app := fun U => normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.fromSpec
      naturality := fun U V f => by
        simpa only [affineNormalizationDiagram, Functor.const_obj_map,
          Functor.const_obj_obj, Category.comp_id] using
          (affineNormalizationRestriction_comp_toX V.val U.val N
            (leOfHom f) V.property.1 U.property.1) }

/-- Every arrow in the actual chart diagram is an open immersion. -/
instance affineNormalizationDiagram_isOpenImmersion
    {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    IsOpenImmersion ((affineNormalizationDiagram X N).map f) :=
  affineNormalizationRestriction_isOpenImmersion V.val U.val N
    (leOfHom f) V.property.1 U.property.1

/-- Its image is the actual inverse image of the smaller base chart. -/
theorem affineNormalizationDiagram_range
    {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    Set.range ((affineNormalizationDiagram X N).map f).base =
      ((affineNormalizationBaseCocone X N).ι.app V).base ⁻¹' (U.val : Set X) :=
  affineNormalizationRestriction_range V.val U.val N
    (leOfHom f) V.property.1 U.property.1

/-- Equal images in an upper chart lift through one common smaller affine chart. -/
instance affineNormalizationDiagram_isLocallyDirected :
    ((affineNormalizationDiagram X N) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro U V T f g a b hab
  let μU : (affineNormalizationDiagram X N).obj U ⟶ X := (affineNormalizationBaseCocone X N).ι.app U
  let μV : (affineNormalizationDiagram X N).obj V ⟶ X := (affineNormalizationBaseCocone X N).ι.app V
  let μT : (affineNormalizationDiagram X N).obj T ⟶ X := (affineNormalizationBaseCocone X N).ι.app T
  have hU : (affineNormalizationDiagram X N).map f ≫ μT = μU :=
    (affineNormalizationBaseCocone X N).w f
  have hV : (affineNormalizationDiagram X N).map g ≫ μT = μV :=
    (affineNormalizationBaseCocone X N).w g
  change ((affineNormalizationDiagram X N).map f).base a =
    ((affineNormalizationDiagram X N).map g).base b at hab
  have hx : μU.base a = μV.base b := by
    simpa only [← Scheme.Hom.comp_apply, hU, hV] using congrArg μT.base hab
  have hxU : μU.base a ∈ U.val := by
    change μU.base a ∈ (U.val : Set X)
    rw [← U.property.1.range_fromSpec]
    exact ⟨_, rfl⟩
  have hxV : μU.base a ∈ V.val := by
    rw [hx]
    change μV.base b ∈ (V.val : Set X)
    rw [← V.property.1.range_fromSpec]
    exact ⟨_, rfl⟩
  obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter
    U.property.1 V.property.1 (μU.base a) ⟨hxU, hxV⟩
  let W : NonemptyAffineChart X :=
    ⟨X.basicOpen r, U.property.1.basicOpen r, ⟨⟨μU.base a, hxr⟩⟩⟩
  let fWU : W ⟶ U := homOfLE (X.basicOpen_le r)
  let fWV : W ⟶ V := homOfLE (hrs.trans_le (X.basicOpen_le s))
  have ha : a ∈ Set.range ((affineNormalizationDiagram X N).map fWU).base := by
    rw [affineNormalizationDiagram_range]
    exact hxr
  obtain ⟨w, hw⟩ := ha
  refine ⟨W, fWU, fWV, w, hw, ?_⟩
  change ((affineNormalizationDiagram X N).map fWV).base w = b
  apply ((affineNormalizationDiagram X N).map g).isOpenEmbedding.injective
  calc
    ((affineNormalizationDiagram X N).map g).base
        (((affineNormalizationDiagram X N).map fWV).base w) =
        ((affineNormalizationDiagram X N).map f).base
          (((affineNormalizationDiagram X N).map fWU).base w) := by
      simp only [← Scheme.Hom.comp_apply, ← Functor.map_comp]
      congr 2
    _ = ((affineNormalizationDiagram X N).map g).base b := by rw [hw, hab]

end

end HodgeConjecture.CollisionFoundations
