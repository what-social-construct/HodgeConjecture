module

public import HodgeConjecture.Geometry.ProjectiveLineProductSections

/-!
# The two zero coordinate fibers are projective lines

The product maps obtained by fixing one coordinate at the rational zero
section identify `P¹` with the corresponding base-changed zero fibers.
As base changes of a closed immersion, both maps are closed immersions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The first zero-coordinate map realizes `P¹` as the base change of the
zero section along the first projection. -/
def projectiveLineProductZeroFirstPullbackIso :
    projectiveLine k ≅
      pullback (projectiveLineProductFst k) (projectiveLineZeroSection k) := by
  let p : projectiveLine k ⟶ Spec (.of k) := projectiveLine k ↘ Spec (.of k)
  let s : Spec (.of k) ⟶ projectiveLine k := projectiveLineZeroSection k
  let π₁ : projectiveLineProduct k ⟶ projectiveLine k := projectiveLineProductFst k
  let π₂ : projectiveLineProduct k ⟶ projectiveLine k := projectiveLineProductSnd k
  let j : projectiveLine k ⟶ projectiveLineProduct k := projectiveLineProductZeroFirst k
  let u : pullback π₁ s ⟶ projectiveLineProduct k := pullback.fst π₁ s
  let v : pullback π₁ s ⟶ Spec (.of k) := pullback.snd π₁ s
  have hju : j ≫ π₁ = p ≫ s := projectiveLineProductZeroFirst_fst k
  have hjv : j ≫ π₂ = 𝟙 _ := projectiveLineProductZeroFirst_snd k
  have hπ : π₂ ≫ p = π₁ ≫ p := projectiveLineProductSnd_comp_structureMorphism k
  have hpb : u ≫ π₁ = v ≫ s := pullback.condition
  have hv : (u ≫ π₂) ≫ p = v := by
    calc
      (u ≫ π₂) ≫ p = (u ≫ π₁) ≫ p := by simp [Category.assoc, hπ]
      _ = (v ≫ s) ≫ p := by rw [hpb]
      _ = v := by simp [s, p, Category.assoc]
  have hu : (u ≫ π₂) ≫ j = u := by
    apply projectiveLineProduct_hom_ext k
    · calc
        ((u ≫ π₂) ≫ j) ≫ π₁ = ((u ≫ π₂) ≫ p) ≫ s := by
          simp [Category.assoc, hju]
        _ = v ≫ s := by rw [hv]
        _ = u ≫ π₁ := hpb.symm
    · change ((u ≫ π₂) ≫ j) ≫ π₂ = u ≫ π₂
      simp [Category.assoc, hjv]
  refine ⟨pullback.lift j p hju, u ≫ π₂, ?_, ?_⟩
  · change (pullback.lift j p hju ≫ u) ≫ π₂ = 𝟙 _
    dsimp [u]
    rw [pullback.lift_fst]
    exact hjv
  · apply pullback.hom_ext
    · change ((u ≫ π₂) ≫ pullback.lift j p hju) ≫ u = 𝟙 _ ≫ u
      dsimp [u]
      simpa only [Category.assoc, pullback.lift_fst, Category.id_comp] using hu
    · change ((u ≫ π₂) ≫ pullback.lift j p hju) ≫ v = 𝟙 _ ≫ v
      dsimp [v]
      simpa only [Category.assoc, pullback.lift_snd, Category.id_comp] using hv

/-- The second zero-coordinate map realizes `P¹` as the base change of the
zero section along the second projection. -/
def projectiveLineProductZeroSecondPullbackIso :
    projectiveLine k ≅
      pullback (projectiveLineProductSnd k) (projectiveLineZeroSection k) := by
  let p : projectiveLine k ⟶ Spec (.of k) := projectiveLine k ↘ Spec (.of k)
  let s : Spec (.of k) ⟶ projectiveLine k := projectiveLineZeroSection k
  let π₁ : projectiveLineProduct k ⟶ projectiveLine k := projectiveLineProductFst k
  let π₂ : projectiveLineProduct k ⟶ projectiveLine k := projectiveLineProductSnd k
  let j : projectiveLine k ⟶ projectiveLineProduct k := projectiveLineProductZeroSecond k
  let u : pullback π₂ s ⟶ projectiveLineProduct k := pullback.fst π₂ s
  let v : pullback π₂ s ⟶ Spec (.of k) := pullback.snd π₂ s
  have hju : j ≫ π₂ = p ≫ s := projectiveLineProductZeroSecond_snd k
  have hjv : j ≫ π₁ = 𝟙 _ := projectiveLineProductZeroSecond_fst k
  have hπ : π₁ ≫ p = π₂ ≫ p := projectiveLineProductFst_comp_structureMorphism k |>.trans
    (projectiveLineProductSnd_comp_structureMorphism k).symm
  have hpb : u ≫ π₂ = v ≫ s := pullback.condition
  have hv : (u ≫ π₁) ≫ p = v := by
    calc
      (u ≫ π₁) ≫ p = (u ≫ π₂) ≫ p := by simp [Category.assoc, hπ]
      _ = (v ≫ s) ≫ p := by rw [hpb]
      _ = v := by simp [s, p, Category.assoc]
  have hu : (u ≫ π₁) ≫ j = u := by
    apply projectiveLineProduct_hom_ext k
    · change ((u ≫ π₁) ≫ j) ≫ π₁ = u ≫ π₁
      simp [Category.assoc, hjv]
    · calc
        ((u ≫ π₁) ≫ j) ≫ π₂ = ((u ≫ π₁) ≫ p) ≫ s := by
          simp [Category.assoc, hju]
        _ = v ≫ s := by rw [hv]
        _ = u ≫ π₂ := hpb.symm
  refine ⟨pullback.lift j p hju, u ≫ π₁, ?_, ?_⟩
  · change (pullback.lift j p hju ≫ u) ≫ π₁ = 𝟙 _
    dsimp [u]
    rw [pullback.lift_fst]
    exact hjv
  · apply pullback.hom_ext
    · change ((u ≫ π₁) ≫ pullback.lift j p hju) ≫ u = 𝟙 _ ≫ u
      dsimp [u]
      simpa only [Category.assoc, pullback.lift_fst, Category.id_comp] using hu
    · change ((u ≫ π₁) ≫ pullback.lift j p hju) ≫ v = 𝟙 _ ≫ v
      dsimp [v]
      simpa only [Category.assoc, pullback.lift_snd, Category.id_comp] using hv

/-- Fixing the first coordinate at zero gives an actual closed immersion. -/
instance projectiveLineProductZeroFirst_isClosedImmersion :
    IsClosedImmersion (projectiveLineProductZeroFirst k) := by
  let e := projectiveLineProductZeroFirstPullbackIso k
  have h : e.hom ≫ pullback.fst (projectiveLineProductFst k)
      (projectiveLineZeroSection k) = projectiveLineProductZeroFirst k := by
    simp [e, projectiveLineProductZeroFirstPullbackIso]
  rw [← h]
  infer_instance

/-- Fixing the second coordinate at zero gives an actual closed immersion. -/
instance projectiveLineProductZeroSecond_isClosedImmersion :
    IsClosedImmersion (projectiveLineProductZeroSecond k) := by
  let e := projectiveLineProductZeroSecondPullbackIso k
  have h : e.hom ≫ pullback.fst (projectiveLineProductSnd k)
      (projectiveLineZeroSection k) = projectiveLineProductZeroSecond k := by
    simp [e, projectiveLineProductZeroSecondPullbackIso]
  rw [← h]
  infer_instance

end AlgebraicGeometry

end
