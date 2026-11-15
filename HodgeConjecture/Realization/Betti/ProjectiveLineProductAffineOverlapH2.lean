module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductAffineChartH2

/-!
# Degree-two restriction to the product-chart overlap

A first-coordinate point with affine coordinate one lies in both standard
charts. Holding this coordinate fixed embeds the entire second projective
line in their overlap. Pulling the second projection class back along this
section recovers the nonzero projective-line generator. Since the class
generates degree-two cohomology on either chart, restriction to the overlap
is injective.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductAffineOverlapH2

open AlgebraicGeometry CategoryTheory Topology
open HodgeConjecture.ProjectiveLineProductComplexPoints
open HodgeConjecture.ProjectiveLineProductBetti
open HodgeConjecture.ProjectiveLineProductAffineChartH2
open HodgeConjecture.SingularSubcomplexes

/-- The complex affine point with first coordinate one. -/
def unitAffine : AffinePoint := AffineLineComplexPoints.evalPoint 1

/-- The coordinate-one point lies in both original projective-line charts. -/
theorem unitChart_agree :
    ProjectiveLineComplexPoints.canonicalXChart unitAffine =
      ProjectiveLineComplexPoints.canonicalYChart unitAffine := by
  have h := ProjectiveLineComplexPoints.finite_eq_reciprocal_inv 1 (by norm_num)
  have hc := congrArg ProjectiveLineComplexPoints.canonicalEquiv h
  simpa [unitAffine, ProjectiveLineComplexPoints.finite,
    ProjectiveLineComplexPoints.reciprocal] using hc

abbrev U : Set ProductSpace := chartSet false
abbrev V : Set ProductSpace := chartSet true
abbrev W : Set ProductSpace := U ∩ V

/-- Fixing the first affine coordinate at one gives a continuous section
from the second projective line into the actual chart overlap. -/
def overlapSection (p : LinePoint) : W :=
  ⟨pointsHomeomorph.symm (ProjectiveLineComplexPoints.canonicalXChart unitAffine, p), by
    constructor
    · change _ ∈ Set.range (chartMap false)
      exact ⟨(unitAffine, p), rfl⟩
    · change _ ∈ Set.range (chartMap true)
      refine ⟨(unitAffine, p), ?_⟩
      simp [chartMap, firstChart, unitChart_agree]⟩

theorem continuous_overlapSection : Continuous overlapSection := by
  apply Continuous.subtype_mk
  exact pointsHomeomorph.symm.continuous.comp
    (continuous_const.prodMk continuous_id)

/-- The topological map used for singular-cohomology pullback. -/
def overlapSectionMap : TopCat.of LinePoint ⟶ TopCat.of W :=
  TopCat.ofHom ⟨overlapSection, continuous_overlapSection⟩

/-- The second actual scheme projection is the identity along the fixed
first-coordinate section. -/
theorem overlapSection_secondProjection :
    overlapSectionMap ≫
      SingularMayerVietoris.intersectionToRight ProductSpace U V ≫
        subsetInclusion ProductSpace V ≫
          SchemeBetti.map (projectiveLineProductSnd ℂ)
            (projectiveLineProductSnd_comp_structureMorphism ℂ) =
      𝟙 (TopCat.of LinePoint) := by
  ext p : 1
  change (pointsHomeomorph (pointsHomeomorph.symm
    (ProjectiveLineComplexPoints.canonicalXChart unitAffine, p))).2 = p
  simp

/-- Pullback of the restricted second class along the overlap section is
the nonzero projective-line generator. -/
theorem overlapSection_pullback_secondClass :
    SingularCochains.cohomologyPullback overlapSectionMap 2
      (SingularCochains.cohomologyPullback
        (SingularMayerVietoris.intersectionToRight ProductSpace U V) 2
        (SingularCochains.cohomologyPullback
          (subsetInclusion ProductSpace V) 2 secondClass)) =
      lineGenerator := by
  have h := congrArg
    (fun f : TopCat.of LinePoint ⟶ TopCat.of LinePoint =>
      SingularCochains.cohomologyPullback f 2 lineGenerator)
    overlapSection_secondProjection
  rw [SingularCochains.cohomologyPullback_comp,
    SingularCochains.cohomologyPullback_comp,
    SingularCochains.cohomologyPullback_comp] at h
  simpa only [secondClass, SchemeBetti.pullback,
    SingularCochains.cohomologyPullback_id, CategoryTheory.comp_apply,
    ModuleCat.id_apply] using h

/-- Restriction from the second affine-first-factor chart to the actual
overlap is injective on rational singular degree-two cohomology. -/
theorem overlapRestriction_injective : Function.Injective
    (SingularCochains.cohomologyPullback
      (SingularMayerVietoris.intersectionToRight ProductSpace U V) 2) := by
  intro x y hxy
  let r := SingularCochains.cohomologyPullback
    (SingularMayerVietoris.intersectionToRight ProductSpace U V) 2
  let g := SingularCochains.cohomologyPullback
    (subsetInclusion ProductSpace V) 2 secondClass
  have hzero : r (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨a, ha⟩ := chartH2_generated true (x - y)
  have hg : a • lineGenerator = 0 := by
    have h := congrArg (fun z =>
      SingularCochains.cohomologyPullback overlapSectionMap 2 (r z)) ha
    change SingularCochains.cohomologyPullback overlapSectionMap 2 (r (x - y)) =
      SingularCochains.cohomologyPullback overlapSectionMap 2 (r (a • g)) at h
    rw [hzero, map_zero, map_smul, map_smul,
      overlapSection_pullback_secondClass] at h
    exact h.symm
  have ha0 : a = 0 := (smul_eq_zero.mp hg).resolve_right lineGenerator_ne_zero
  have hsub : x - y = 0 := by rw [ha, ha0, zero_smul]
  exact sub_eq_zero.mp hsub

end HodgeConjecture.ProjectiveLineProductAffineOverlapH2

end
