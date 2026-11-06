module

public import HodgeConjecture.Boundary.Normalization.GluedNormalization
public import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosureRestriction

@[expose] public section

/-!
# Gluing the original marked normal-closure refinement

The original chartwise maps to the whole inverse images of affine base opens
form a cocone to the original cover. Its descent retains the actual generic
field marking and has the original structural map as its composite to the
base. Uniqueness is relative to the marked chart formulas, not the triangle
alone. Only normal stalks on the cover and a finite dominant map are used.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles NormalizationInertia

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

/-- The original marked refinement maps, followed by the actual open
inclusions, form a cocone to the original cover. -/
def affineNormalClosureRefinementCocone :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Cocone (affineNormalizationDiagram X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  refine
    { pt := Y
      ι :=
        { app := fun U => finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
            (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι
          naturality := ?_ } }
  intro U V f
  simpa only [affineNormalizationDiagram, Functor.const_obj_map,
    Functor.const_obj_obj, Category.comp_id, Category.assoc, Scheme.homOfLE_ι] using
    congrArg (fun k => k ≫ (p ⁻¹ᵁ V.val).ι)
      (finiteEtaleAffineNormalClosureToPreimage_restriction p V.val U.val
        (leOfHom f) V.property.1 U.property.1
        (fun y => hY y.val) (fun y => hY y.val))

/-- The actual marked chart maps descend to the original cover. -/
def gluedNormalClosureToCover :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalizationModel X Nₚ ⟶ Y := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact colimit.desc (affineNormalizationDiagram X Nₚ)
    (affineNormalClosureRefinementCocone p hY)

/-- On each original chart, the descended map is exactly the original
marked refinement followed by the inclusion of the actual inverse image. -/
theorem normalizationChartToGlued_comp_toCover (U : NonemptyAffineChart X) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    normalizationChartToGlued X Nₚ U ≫ gluedNormalClosureToCover p hY =
      finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
        (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact colimit.ι_desc (affineNormalClosureRefinementCocone p hY) U

/-- The global refinement retains the original structural map to the base. -/
theorem gluedNormalClosureToCover_comp_toBase :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    gluedNormalClosureToCover p hY ≫ p = gluedNormalizationToBase X Nₚ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  apply gluedNormalization_hom_ext X Nₚ
  intro U
  rw [← Category.assoc, normalizationChartToGlued_comp_toCover,
    normalizationChartToGlued_comp_toBase]
  exact finiteEtaleAffineNormalClosureToPreimage_comp_toBase p U.val U.property.1
    (fun y => hY y.val)

/-- The original marked chart formulas determine the refinement uniquely.
Commutativity over the base alone is not the uniqueness hypothesis. -/
theorem gluedNormalClosureToCover_unique :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ f : gluedNormalizationModel X Nₚ ⟶ Y,
      (∀ U : NonemptyAffineChart X, normalizationChartToGlued X Nₚ U ≫ f =
        finiteEtaleAffineNormalClosureToPreimage p U.val U.property.1
          (fun y => hY y.val) ≫ (p ⁻¹ᵁ U.val).ι) →
      f = gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro f hf
  apply gluedNormalization_hom_ext X Nₚ
  intro U
  exact (hf U).trans (normalizationChartToGlued_comp_toCover p hY U).symm

end

end HodgeConjecture.CollisionFoundations
