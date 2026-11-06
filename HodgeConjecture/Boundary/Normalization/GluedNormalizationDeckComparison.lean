module

public import HodgeConjecture.Boundary.Normalization.GluedNormalizationFunctionFieldAction
public import HodgeConjecture.Cycles.FunctionFieldExtensionality

@[expose] public section

/-!
# The full deck group of the original glued normalization

Generic pullback detects deck transformations because the original
normalization is integral and affine over its base. For a finite ambient
extension, the original field comparison reconstructs every deck
transformation from a field automorphism. The inverse deck map is used
to retain the existing inverse-pullback convention and group law.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open SchemeCycles SchemeCorrespondence

noncomputable section

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

local instance deckComparisonOverIntegral :
    IsIntegral (Over.mk (gluedNormalizationToBase X N)).left :=
  inferInstanceAs (IsIntegral (gluedNormalizationModel X N))

/-- Actual generic pullback determines a deck transformation of the same
normalization; no finite-extension hypothesis is needed for uniqueness. -/
theorem gluedNormalizationDeckTransformation_ext
    (d e : DeckTransformation (gluedNormalizationToBase X N))
    (h : functionFieldMapOfDominant d.hom.left =
      functionFieldMapOfDominant e.hom.left) : d = e := by
  apply CategoryTheory.Aut.hom_ext
  apply Over.OverMorphism.ext
  exact eq_of_functionFieldMapOfDominant_eq d.hom.left e.hom.left
    (gluedNormalizationToBase X N) ((Over.w d.hom).trans (Over.w e.hom).symm) h

variable [FiniteDimensional X.functionField N]

local instance deckComparisonBaseSurjective : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance deckComparisonFieldAlgebra :
    Algebra X.functionField (gluedNormalizationModel X N).functionField :=
  (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra

/-- Reconstruct the field automorphism using inverse deck pullback and the
original field marking. This direction preserves the original group law. -/
def gluedNormalizationDeckFieldAutomorphism
    (d : DeckTransformation (gluedNormalizationToBase X N)) :
    N ≃ₐ[X.functionField] N where
  toRingEquiv := (gluedNormalizationFunctionFieldEquiv X N).toRingEquiv.symm.trans
    ((functionFieldEquivOfOpenImmersion d.inv.left).trans
      (gluedNormalizationFunctionFieldEquiv X N).toRingEquiv)
  commutes' := by
    intro a
    have h : functionFieldMapOfDominant (gluedNormalizationToBase X N) ≫
        functionFieldMapOfDominant d.inv.left =
        functionFieldMapOfDominant (gluedNormalizationToBase X N) := by
      rw [← functionFieldMapOfDominant_comp]
      congr 1
      exact Over.w d.inv
    have ha := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a
    change functionFieldMapOfDominant d.inv.left
      (functionFieldMapOfDominant (gluedNormalizationToBase X N) a) =
        functionFieldMapOfDominant (gluedNormalizationToBase X N) a at ha
    change gluedNormalizationFunctionFieldEquiv X N
      (functionFieldMapOfDominant d.inv.left
        ((gluedNormalizationFunctionFieldEquiv X N).symm
          (algebraMap X.functionField N a))) = algebraMap X.functionField N a
    rw [(gluedNormalizationFunctionFieldEquiv X N).symm.commutes]
    change gluedNormalizationFunctionFieldEquiv X N
      (functionFieldMapOfDominant d.inv.left
        (functionFieldMapOfDominant (gluedNormalizationToBase X N) a)) = _
    rw [ha]
    exact (gluedNormalizationFunctionFieldEquiv X N).commutes a

/-- The reconstructed automorphism has the actual inverse-pullback formula. -/
theorem gluedNormalizationDeckFieldAutomorphism_apply
    (d : DeckTransformation (gluedNormalizationToBase X N)) (x : N) :
    gluedNormalizationDeckFieldAutomorphism X N d x =
      gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant d.inv.left
          ((gluedNormalizationFunctionFieldEquiv X N).symm x)) := rfl

/-- The original action recovers every deck transformation, with no change
to the glued scheme, its structural map or the field marking. -/
theorem gluedNormalizationDeckAction_fieldAutomorphism
    (d : DeckTransformation (gluedNormalizationToBase X N)) :
    gluedNormalizationDeckAction X N (gluedNormalizationDeckFieldAutomorphism X N d) = d := by
  have h : gluedNormalizationDeckAction X N
      (gluedNormalizationDeckFieldAutomorphism X N d)⁻¹ = d⁻¹ := by
    apply gluedNormalizationDeckTransformation_ext X N
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply (gluedNormalizationFunctionFieldEquiv X N).injective
    change gluedNormalizationFunctionFieldEquiv X N
      (functionFieldMapOfDominant
        (gluedNormalizationAutomorphism X N
          (gluedNormalizationDeckFieldAutomorphism X N d)⁻¹).hom a) =
      gluedNormalizationFunctionFieldEquiv X N (functionFieldMapOfDominant d.inv.left a)
    rw [gluedNormalizationFunctionFieldEquiv_automorphism]
    change gluedNormalizationDeckFieldAutomorphism X N d
      (gluedNormalizationFunctionFieldEquiv X N a) = _
    rw [gluedNormalizationDeckFieldAutomorphism_apply, AlgEquiv.symm_apply_apply]
  apply inv_injective
  simpa only [map_inv] using h

/-- Every automorphism over the original base comes from a field automorphism. -/
theorem gluedNormalizationDeckAction_surjective :
    Function.Surjective (gluedNormalizationDeckAction X N) :=
  fun d => ⟨gluedNormalizationDeckFieldAutomorphism X N d,
    gluedNormalizationDeckAction_fieldAutomorphism X N d⟩

/-- The full deck group, with the original action as forward map and the
explicit inverse-deck pullback as inverse. -/
def gluedNormalizationDeckEquiv :
    (N ≃ₐ[X.functionField] N) ≃* DeckTransformation (gluedNormalizationToBase X N) where
  toFun := gluedNormalizationDeckAction X N
  invFun := gluedNormalizationDeckFieldAutomorphism X N
  left_inv σ := (gluedNormalizationDeckAction_injective X N)
    (gluedNormalizationDeckAction_fieldAutomorphism X N (gluedNormalizationDeckAction X N σ))
  right_inv := gluedNormalizationDeckAction_fieldAutomorphism X N
  map_mul' := (gluedNormalizationDeckAction X N).map_mul

end

end HodgeConjecture.CollisionFoundations
