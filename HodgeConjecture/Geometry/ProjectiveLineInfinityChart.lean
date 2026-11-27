module

public import HodgeConjecture.Geometry.ProjectiveLineAffineChart

@[expose] public section

/-!
# Actual reciprocal normal charts at the original infinity point

Scaling the affine coordinate by a unit and following the original
second chart gives an actual scheme normal chart at infinity. Its open
range and base structure are the original second-chart data. Evaluation
sections have exactly the reciprocal coordinate `u * z`; evaluation at
zero has the original scheme point `projectiveLineInfinity` as image.

This is local scheme chart data. No global projective-line inversion or
new Chow quotient or infinity class is defined.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineInfinityChart

open AlgebraicGeometry CategoryTheory

universe u

section CommRing

variable (k : Type u) [CommRing k]

/-- The actual unit-scaled reciprocal chart of the original glued scheme. -/
def normalChart (v : kˣ) : Spec (.of (Polynomial k)) ⟶ projectiveLine k :=
  (ProjectiveLineAffineChart.affineIso k 0 v).hom ≫ projectiveLineYChart k

instance normalChart_isOpenImmersion (v : kˣ) : IsOpenImmersion (normalChart k v) := by
  unfold normalChart
  infer_instance

/-- The actual scheme-point range is the original second affine-chart range. -/
theorem normalChart_range (v : kˣ) :
    Set.range (normalChart k v).base = Set.range (projectiveLineYChart k).base := by
  unfold normalChart
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    ((ProjectiveLineAffineChart.affineIso k 0 v).hom.surjective).range_comp]

theorem normalChart_opensRange (v : kˣ) :
    (normalChart k v).opensRange = (projectiveLineYChart k).opensRange := by
  ext x
  change x ∈ Set.range (normalChart k v).base ↔
    x ∈ Set.range (projectiveLineYChart k).base
  rw [normalChart_range]

/-- The reciprocal normal chart retains the actual original base structure. -/
@[simp, reassoc]
theorem normalChart_over_base (v : kˣ) :
    normalChart k v ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineAffineStructureMorphism k := by
  unfold normalChart
  rw [Category.assoc, projectiveLineYChart_comp_structureMorphism,
    ProjectiveLineAffineChart.affineIso_over_base]

/-- The actual evaluation section in the original second affine scheme chart. -/
def reciprocalSection (z : k) : Spec (.of k) ⟶ projectiveLine k :=
  ProjectiveLineAffineChart.affineSection k z ≫ projectiveLineYChart k

@[simp, reassoc]
theorem reciprocalSection_over_base (z : k) :
    reciprocalSection k z ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) := by
  unfold reciprocalSection
  rw [Category.assoc, projectiveLineYChart_comp_structureMorphism,
    ProjectiveLineAffineChart.affineSection_over_base]

/-- Normal-coordinate evaluation retains the same actual reciprocal scheme section. -/
@[simp, reassoc]
theorem affineSection_normalChart (z : k) (v : kˣ) :
    ProjectiveLineAffineChart.affineSection k z ≫ normalChart k v =
      reciprocalSection k ((v : k) * z) := by
  unfold normalChart reciprocalSection
  rw [← Category.assoc, ProjectiveLineAffineChart.affineSection_affineIso]
  simp only [zero_add]

/-- Evaluation at zero in the original second chart, as an actual section. -/
abbrev infinitySection : Spec (.of k) ⟶ projectiveLine k := reciprocalSection k 0

@[simp, reassoc]
theorem infinitySection_over_base :
    infinitySection k ≫ (projectiveLine k ↘ Spec (.of k)) = 𝟙 (Spec (.of k)) :=
  reciprocalSection_over_base k 0

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The original zero evaluation has exactly the original scheme infinity point as image. -/
@[simp]
theorem reciprocalSection_base_zero (q : Spec (.of k)) :
    reciprocalSection k 0 q = projectiveLineInfinity k := by
  unfold reciprocalSection
  rw [Scheme.Hom.comp_apply, ProjectiveLineAffineChart.affineSection_base,
    ProjectiveLineAffineChart.affineCenter_zero]
  rfl

@[simp]
theorem infinitySection_base (q : Spec (.of k)) :
    infinitySection k q = projectiveLineInfinity k := reciprocalSection_base_zero k q

/-- Every scaled reciprocal normal chart centers at the same original scheme point. -/
@[simp]
theorem normalChart_origin (v : kˣ) :
    normalChart k v (affineLineOrigin k) = projectiveLineInfinity k := by
  have h := congrArg (fun f : Spec (.of k) ⟶ projectiveLine k =>
    f (default : Spec (.of k))) (affineSection_normalChart k 0 v)
  simpa only [Scheme.Hom.comp_apply, ProjectiveLineAffineChart.affineSection_base,
    ProjectiveLineAffineChart.affineCenter_zero, mul_zero,
    reciprocalSection_base_zero] using h

/-- Reciprocal evaluation sections are actual closed-point immersions over the field. -/
instance reciprocalSection_isClosedImmersion (z : k) :
    IsClosedImmersion (reciprocalSection k z) :=
  isClosedImmersion_of_comp_eq_id
    (projectiveLine k ↘ Spec (.of k)) (reciprocalSection k z)
    (reciprocalSection_over_base k z)

theorem reciprocalSection_zero_range :
    Set.range (reciprocalSection k 0).base = {projectiveLineInfinity k} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact Set.mem_singleton_iff.mpr (reciprocalSection_base_zero k q)
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨default, (reciprocalSection_base_zero k default).trans hx.symm⟩

/-- This is the existing infinity point of the original scheme, with its actual closed support. -/
theorem infinity_isClosed : IsClosed ({projectiveLineInfinity k} : Set (projectiveLine k)) := by
  rw [← reciprocalSection_zero_range]
  exact (reciprocalSection k 0).isClosedEmbedding.isClosed_range

end Field

end HodgeConjecture.ProjectiveLineInfinityChart

end
