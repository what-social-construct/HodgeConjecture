import HodgeConjecture.Boundary.Normalization.AffineNormalizationDiagram

/-!
# Gluing the original normalization charts

The locally directed diagram glues the original same-field normalization
models into a scheme. Its canonical chart inclusions form an open cover,
and the original structural maps descend to the original base scheme.
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

/-- The scheme obtained by gluing the existing normalization chart diagram. -/
def gluedNormalizationModel : Scheme.{u} :=
  colimit (affineNormalizationDiagram X N)

/-- The canonical inclusion of an original affine normalization chart. -/
def normalizationChartToGlued (U : NonemptyAffineChart X) :
    (affineNormalizationDiagram X N).obj U ⟶ gluedNormalizationModel X N :=
  colimit.ι (affineNormalizationDiagram X N) U

/-- Each original chart embeds as an open subscheme of the glued scheme. -/
instance normalizationChartToGlued_isOpenImmersion (U : NonemptyAffineChart X) :
    IsOpenImmersion (normalizationChartToGlued X N U) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (affineNormalizationDiagram X N) U))

/-- The original normalization charts cover the glued scheme. -/
def gluedNormalizationOpenCover : (gluedNormalizationModel X N).OpenCover :=
  Scheme.IsLocallyDirected.openCover (affineNormalizationDiagram X N)

/-- The original structural cocone descends to the original base scheme. -/
def gluedNormalizationToBase : gluedNormalizationModel X N ⟶ X :=
  colimit.desc (affineNormalizationDiagram X N) (affineNormalizationBaseCocone X N)

/-- Restriction of the descended map is exactly the original structural map. -/
theorem normalizationChartToGlued_comp_toBase (U : NonemptyAffineChart X) :
    normalizationChartToGlued X N U ≫ gluedNormalizationToBase X N =
      (affineNormalizationBaseCocone X N).ι.app U :=
  colimit.ι_desc (affineNormalizationBaseCocone X N) U

/-- The actual restriction maps are the transition maps of the glued charts. -/
theorem normalizationChartToGlued_naturality
    {U V : NonemptyAffineChart X} (f : U ⟶ V) :
    (affineNormalizationDiagram X N).map f ≫ normalizationChartToGlued X N V =
      normalizationChartToGlued X N U :=
  colimit.w (affineNormalizationDiagram X N) f

/-- Two original chart points agree globally exactly when they agree in a
common smaller affine normalization chart. -/
theorem normalizationChartToGlued_eq_iff
    {U V : NonemptyAffineChart X}
    (a : (affineNormalizationDiagram X N).obj U)
    (b : (affineNormalizationDiagram X N).obj V) :
    (normalizationChartToGlued X N U).base a =
        (normalizationChartToGlued X N V).base b ↔
      ∃ (W : NonemptyAffineChart X) (f : W ⟶ U) (g : W ⟶ V)
        (w : (affineNormalizationDiagram X N).obj W),
        ((affineNormalizationDiagram X N).map f).base w = a ∧
        ((affineNormalizationDiagram X N).map g).base w = b :=
  Scheme.IsLocallyDirected.ι_eq_ι_iff (affineNormalizationDiagram X N)

/-- Morphisms from the glued scheme are determined by their original chart restrictions. -/
theorem gluedNormalization_hom_ext {Y : Scheme.{u}}
    (f g : gluedNormalizationModel X N ⟶ Y)
    (h : ∀ U : NonemptyAffineChart X,
      normalizationChartToGlued X N U ≫ f = normalizationChartToGlued X N U ≫ g) :
    f = g := by
  apply colimit.hom_ext (F := affineNormalizationDiagram X N)
  exact h

end

end HodgeConjecture.CollisionFoundations
