module

public import HodgeConjecture.Boundary.Normalization.GluedNormalization

@[expose] public section

/-!
# The original charts as actual global inverse images

Each original normalization chart is exactly the inverse image of its base
open in the glued scheme. The resulting scheme isomorphisms preserve the
original structural maps and commute with the actual chart restrictions.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable (X : Scheme.{u}) [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

/-- The image of an original chart is its actual inverse image in the glued scheme. -/
theorem normalizationChartToGlued_range (U : NonemptyAffineChart X) :
    Set.range (normalizationChartToGlued X N U).base =
      (gluedNormalizationToBase X N).base ⁻¹' (U.val : Set X) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    change (gluedNormalizationToBase X N).base
      ((normalizationChartToGlued X N U).base a) ∈ (U.val : Set X)
    rw [← Scheme.Hom.comp_apply, normalizationChartToGlued_comp_toBase]
    rw [← U.property.1.range_fromSpec]
    exact ⟨_, rfl⟩
  · intro hz
    obtain ⟨V, b, rfl⟩ := (gluedNormalizationOpenCover X N).exists_eq z
    change (gluedNormalizationToBase X N).base
      ((normalizationChartToGlued X N V).base b) ∈ (U.val : Set X) at hz
    rw [← Scheme.Hom.comp_apply, normalizationChartToGlued_comp_toBase] at hz
    let μV := (affineNormalizationBaseCocone X N).ι.app V
    have hxV : μV.base b ∈ (V.val : Set X) := by
      rw [← V.property.1.range_fromSpec]
      exact ⟨_, rfl⟩
    obtain ⟨r, s, hrs, hxr⟩ := exists_basicOpen_le_affine_inter
      U.property.1 V.property.1 (μV.base b) ⟨hz, hxV⟩
    let W : NonemptyAffineChart X :=
      ⟨X.basicOpen r, U.property.1.basicOpen r, ⟨⟨μV.base b, hxr⟩⟩⟩
    let fWU : W ⟶ U := homOfLE (X.basicOpen_le r)
    let fWV : W ⟶ V := homOfLE (hrs.trans_le (X.basicOpen_le s))
    have hb : b ∈ Set.range ((affineNormalizationDiagram X N).map fWV).base := by
      rw [affineNormalizationDiagram_range]
      exact hxr
    obtain ⟨w, hw⟩ := hb
    refine ⟨((affineNormalizationDiagram X N).map fWU).base w, ?_⟩
    change (normalizationChartToGlued X N U).base
      (((affineNormalizationDiagram X N).map fWU).base w) =
      (normalizationChartToGlued X N V).base b
    rw [← hw]
    simp only [← Scheme.Hom.comp_apply, normalizationChartToGlued_naturality]

/-- The corresponding equality holds as actual opens of the glued scheme. -/
theorem normalizationChartToGlued_opensRange (U : NonemptyAffineChart X) :
    (normalizationChartToGlued X N U).opensRange =
      (gluedNormalizationToBase X N) ⁻¹ᵁ U.val := by
  ext z
  exact Set.ext_iff.mp (normalizationChartToGlued_range X N U) z

/-- The original chart is isomorphic to the actual global inverse-image open subscheme. -/
def normalizationChartPreimageIso (U : NonemptyAffineChart X) :
    (affineNormalizationDiagram X N).obj U ≅
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).toScheme :=
  (normalizationChartToGlued X N U).isoOpensRange ≪≫
    (gluedNormalizationModel X N).isoOfEq (normalizationChartToGlued_opensRange X N U)

/-- The inverse-image isomorphism retains the original global chart inclusion. -/
theorem normalizationChartPreimageIso_hom_comp_inclusion (U : NonemptyAffineChart X) :
    (normalizationChartPreimageIso X N U).hom ≫
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι =
      normalizationChartToGlued X N U := by
  simp [normalizationChartPreimageIso]

/-- The inverse comparison also commutes with the original inclusions. -/
theorem normalizationChartPreimageIso_inv_comp_chart (U : NonemptyAffineChart X) :
    (normalizationChartPreimageIso X N U).inv ≫ normalizationChartToGlued X N U =
      ((gluedNormalizationToBase X N) ⁻¹ᵁ U.val).ι := by
  rw [← normalizationChartPreimageIso_hom_comp_inclusion X N U]
  simp

local instance normalizationPreimageAmbientAlgebra (U : NonemptyAffineChart X) :
    Algebra Γ(X, U.val) N :=
  ((algebraMap X.functionField N).comp (X.germToFunctionField U.val).hom).toAlgebra

/-- The actual restricted global map is the original normalization map to the base chart. -/
theorem normalizationChartPreimageIso_hom_comp_restrict (U : NonemptyAffineChart X) :
    (normalizationChartPreimageIso X N U).hom ≫
      (gluedNormalizationToBase X N ∣_ U.val) =
      normalizedModelToBase Γ(X, U.val) N ≫ U.property.1.isoSpec.inv := by
  apply (cancel_mono U.val.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    normalizationChartPreimageIso_hom_comp_inclusion,
    normalizationChartToGlued_comp_toBase]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  rfl

/-- The actual global inverse-image comparisons commute with restriction to a smaller chart. -/
theorem normalizationChartPreimageIso_naturality
    {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫
      (normalizationChartPreimageIso X N V).hom =
      (normalizationChartPreimageIso X N U).hom ≫
        (gluedNormalizationModel X N).homOfLE
          (show (gluedNormalizationToBase X N) ⁻¹ᵁ U.val ≤
              (gluedNormalizationToBase X N) ⁻¹ᵁ V.val from by
            intro z hz
            exact (show U.val ≤ V.val from leOfHom f) hz) := by
  apply (cancel_mono ((gluedNormalizationToBase X N) ⁻¹ᵁ V.val).ι).mp
  simp only [Category.assoc, normalizationChartPreimageIso_hom_comp_inclusion,
    Scheme.homOfLE_ι, normalizationChartToGlued_naturality]

end

end HodgeConjecture.CollisionFoundations
