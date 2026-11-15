module

public import HodgeConjecture.Geometry.ProjectiveLineProductTopology
public import HodgeConjecture.Realization.Betti.ProductContractibleFactor
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanningCriterion
public import Mathlib.Analysis.Convex.Contractible

/-!
# Degree-two cohomology on a projective-line product chart

The inverse image of either standard affine chart in the first factor of
`P¹(ℂ) × P¹(ℂ)` is homeomorphic to `A¹(ℂ) × P¹(ℂ)`. Projection to the second
factor identifies its rational singular `H²` with that of `P¹(ℂ)`, and
the actual second scheme-projection class restricts to the generator.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductAffineChartH2

open AlgebraicGeometry CategoryTheory Topology HodgeConjecture.ProjectiveLineProductComplexPoints
open HodgeConjecture.ProjectiveLineProductBetti HodgeConjecture.SingularSubcomplexes

abbrev AffinePoint := AffineLineComplexPoints.Point
abbrev LinePoint := Scheme.ComplexPoints lineBase
abbrev ProductPoint := Scheme.ComplexPoints productBase

/-- Either original affine coordinate chart of the canonical projective line. -/
def firstChart (i : Bool) : AffinePoint → LinePoint :=
  if i then ProjectiveLineComplexPoints.canonicalYChart
  else ProjectiveLineComplexPoints.canonicalXChart

theorem firstChart_isOpenEmbedding (i : Bool) : IsOpenEmbedding (firstChart i) := by
  cases i
  · simpa [firstChart] using ProjectiveLineComplexPoints.isOpenEmbedding_canonicalXChart
  · simpa [firstChart] using ProjectiveLineComplexPoints.isOpenEmbedding_canonicalYChart

/-- The actual points of the affine-first-coordinate chart in the scheme product. -/
def chartMap (i : Bool) : AffinePoint × LinePoint → ProductPoint :=
  pointsHomeomorph.symm ∘ Prod.map (firstChart i) id

theorem chartMap_isOpenEmbedding (i : Bool) : IsOpenEmbedding (chartMap i) := by
  exact pointsHomeomorph.symm.isOpenEmbedding.comp
    ((firstChart_isOpenEmbedding i).prodMap (Homeomorph.refl LinePoint).isOpenEmbedding)

/-- The first-factor affine chart as an open subset of the actual scheme product points. -/
def chartSet (i : Bool) : Set ProductSpace := Set.range (chartMap i)

theorem chartSet_isOpen (i : Bool) : IsOpen (chartSet i) :=
  (chartMap_isOpenEmbedding i).isOpen_range

/-- Affine chart coordinates, retaining the original analytic topology on scheme points. -/
def chartHomeomorph (i : Bool) : AffinePoint × LinePoint ≃ₜ chartSet i :=
  (chartMap_isOpenEmbedding i).isEmbedding.toHomeomorph

@[simp] theorem chartHomeomorph_apply_coe (i : Bool) (p : AffinePoint × LinePoint) :
    ((chartHomeomorph i p : chartSet i) : ProductPoint) = chartMap i p := rfl

/-- The second scheme projection is the ordinary second coordinate on this chart. -/
theorem chartMap_snd (i : Bool) (p : AffinePoint × LinePoint) :
    Scheme.ComplexPoints.map (projectiveLineProductSnd ℂ)
      (projectiveLineProductSnd_comp_structureMorphism ℂ) (chartMap i p) = p.2 := by
  change (pointsHomeomorph (chartMap i p)).2 = p.2
  simp [chartMap]

/-- The first scheme projection is the chosen affine coordinate chart
on the first factor. -/
theorem chartMap_fst (i : Bool) (p : AffinePoint × LinePoint) :
    Scheme.ComplexPoints.map (projectiveLineProductFst ℂ)
      (projectiveLineProductFst_comp_structureMorphism ℂ) (chartMap i p) =
        firstChart i p.1 := by
  change (pointsHomeomorph (chartMap i p)).1 = firstChart i p.1
  simp [chartMap]

/-- The two affine-first-factor product charts cover the actual product points. -/
theorem chartSet_cover : chartSet false ∪ chartSet true = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro p
  obtain ⟨a, ha⟩ := ProjectiveLineComplexPoints.canonicalCharts_surjective
    (pointsHomeomorph p).1
  change p ∈ chartSet false ∨ p ∈ chartSet true
  cases a with
  | inl a =>
      change ProjectiveLineComplexPoints.canonicalXChart a = (pointsHomeomorph p).1 at ha
      left
      change p ∈ Set.range (chartMap false)
      refine ⟨(a, (pointsHomeomorph p).2), ?_⟩
      apply pointsHomeomorph.injective
      have hpair :
          (ProjectiveLineComplexPoints.canonicalXChart a, (pointsHomeomorph p).2) =
            pointsHomeomorph p := Prod.ext ha rfl
      simpa [chartMap, firstChart] using hpair
  | inr a =>
      change ProjectiveLineComplexPoints.canonicalYChart a = (pointsHomeomorph p).1 at ha
      right
      change p ∈ Set.range (chartMap true)
      refine ⟨(a, (pointsHomeomorph p).2), ?_⟩
      apply pointsHomeomorph.injective
      have hpair :
          (ProjectiveLineComplexPoints.canonicalYChart a, (pointsHomeomorph p).2) =
            pointsHomeomorph p := Prod.ext ha rfl
      simpa [chartMap, firstChart] using hpair

instance affinePointContractible : ContractibleSpace AffinePoint := by
  letI : ContractibleSpace ℂ := inferInstance
  exact AffineLineComplexPoints.coordinateHomeomorph.contractibleSpace

/-- Every rational singular degree-two class on the canonical projective line
is a multiple of its established cycle class. -/
theorem lineH2_generated (z : LineH2) : ∃ a : ℚ, z = a • lineGenerator := by
  refine ⟨lineCoordinate z, ?_⟩
  apply lineCoordinate.injective
  rw [map_smul, lineCoordinate_generator, smul_eq_mul, mul_one]

/-- The chart homeomorphism and actual second scheme projection compose to
the ordinary second-coordinate projection. -/
theorem chart_secondProjection_map (i : Bool) :
    TopCat.ofHom (chartHomeomorph i).toHomotopyEquiv.toFun ≫
      subsetInclusion ProductSpace (chartSet i) ≫
        SchemeBetti.map (projectiveLineProductSnd ℂ)
          (projectiveLineProductSnd_comp_structureMorphism ℂ) =
      TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(AffinePoint × LinePoint, LinePoint)) := by
  ext p : 1
  exact chartMap_snd i p

/-- The first scheme projection on the chart factors through its
contractible affine coordinate. -/
theorem chart_firstProjection_map (i : Bool) :
    TopCat.ofHom (chartHomeomorph i).toHomotopyEquiv.toFun ≫
      subsetInclusion ProductSpace (chartSet i) ≫
        SchemeBetti.map (projectiveLineProductFst ℂ)
          (projectiveLineProductFst_comp_structureMorphism ℂ) =
      TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(AffinePoint × LinePoint, AffinePoint)) ≫
        TopCat.ofHom (⟨firstChart i, (firstChart_isOpenEmbedding i).continuous⟩ :
          C(AffinePoint, LinePoint)) := by
  ext p : 1
  exact chartMap_fst i p

/-- The chart homeomorphism transports rational singular cohomology to the
ordinary topological product in degree two. -/
def chartH2Iso (i : Bool) :
    SingularCochains.Cohomology (TopCat.of (chartSet i)) 2 ≅
      SingularCochains.Cohomology (TopCat.of (AffinePoint × LinePoint)) 2 :=
  SingularHomotopy.homeomorphIso (chartHomeomorph i) 2

/-- The restricted second scheme-projection class is the projection pullback
of the established projective-line generator in chart coordinates. -/
theorem chartH2Iso_secondClass (i : Bool) :
    (chartH2Iso i).hom
      (SingularCochains.cohomologyPullback
        (subsetInclusion ProductSpace (chartSet i)) 2 secondClass) =
      (ProductContractibleFactor.cohomologyIso AffinePoint LinePoint 2).hom
        lineGenerator := by
  rw [ProductContractibleFactor.cohomologyIso_hom]
  have h := congrArg
    (fun f : TopCat.of (AffinePoint × LinePoint) ⟶ TopCat.of LinePoint =>
      SingularCochains.cohomologyPullback f 2 lineGenerator)
    (chart_secondProjection_map i)
  rw [SingularCochains.cohomologyPullback_comp,
    SingularCochains.cohomologyPullback_comp] at h
  simpa only [chartH2Iso, SingularHomotopy.homeomorphIso,
    SingularHomotopy.homotopyEquivIso, secondClass, SchemeBetti.pullback,
    CategoryTheory.comp_apply] using h

/-- The first projection class vanishes after transporting the chart to
`A¹(ℂ) × P¹(ℂ)`, because `H²(A¹(ℂ), ℚ) = 0`. -/
theorem chartH2Iso_firstClass_eq_zero (i : Bool) :
    (chartH2Iso i).hom
      (SingularCochains.cohomologyPullback
        (subsetInclusion ProductSpace (chartSet i)) 2 firstClass) = 0 := by
  let f : C(AffinePoint, LinePoint) :=
    ⟨firstChart i, (firstChart_isOpenEmbedding i).continuous⟩
  have h := congrArg
    (fun g : TopCat.of (AffinePoint × LinePoint) ⟶ TopCat.of LinePoint =>
      SingularCochains.cohomologyPullback g 2 lineGenerator)
    (chart_firstProjection_map i)
  simp only [SingularCochains.cohomologyPullback_comp,
    CategoryTheory.comp_apply] at h
  have hz : SingularCochains.cohomologyPullback (TopCat.ofHom f) 2 lineGenerator = 0 :=
    SingularContractible.cohomology_eq_zero AffinePoint 2 (by decide) _
  rw [hz, map_zero] at h
  simpa only [chartH2Iso, SingularHomotopy.homeomorphIso,
    SingularHomotopy.homotopyEquivIso, firstClass, SchemeBetti.pullback,
    CategoryTheory.comp_apply] using h

/-- Restriction of the actual first scheme-projection class to either open
affine-first-factor chart is zero. -/
theorem chart_firstClass_eq_zero (i : Bool) :
    SingularCochains.cohomologyPullback
      (subsetInclusion ProductSpace (chartSet i)) 2 firstClass = 0 := by
  have h := chartH2Iso_firstClass_eq_zero i
  have h' := congrArg (chartH2Iso i).inv h
  simpa only [map_zero, Iso.hom_inv_id_apply] using h'

/-- The restriction of the actual second scheme-projection class spans
rational singular `H²` on either affine-first-factor product chart. -/
theorem chartH2_generated (i : Bool)
    (y : SingularCochains.Cohomology (TopCat.of (chartSet i)) 2) :
    ∃ b : ℚ, y = b •
      SingularCochains.cohomologyPullback
        (subsetInclusion ProductSpace (chartSet i)) 2 secondClass := by
  let e := chartH2Iso i
  let g := SingularCochains.cohomologyPullback
    (subsetInclusion ProductSpace (chartSet i)) 2 secondClass
  obtain ⟨b, hb⟩ := ProductContractibleFactor.cohomology_generated
    AffinePoint LinePoint 2 lineGenerator lineH2_generated (e.hom y)
  refine ⟨b, ?_⟩
  have hgen : e.hom g =
      (ProductContractibleFactor.cohomologyIso AffinePoint LinePoint 2).hom
        lineGenerator := chartH2Iso_secondClass i
  have hb' : e.hom y = b • e.hom g := by rw [hgen]; exact hb
  calc
    y = e.inv (e.hom y) := (Iso.hom_inv_id_apply e y).symm
    _ = e.inv (b • e.hom g) := by rw [hb']
    _ = b • e.inv (e.hom g) := by rw [map_smul]
    _ = b • g := by rw [Iso.hom_inv_id_apply]

end HodgeConjecture.ProjectiveLineProductAffineChartH2

end
