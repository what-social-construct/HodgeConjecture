module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
public import HodgeConjecture.Geometry.AffineComplexPoints
public import Mathlib.Topology.Compactness.Paracompact

@[expose] public section

/-!
# The original P¹ point space is the canonical analytic point space

The map retains each original scheme morphism Spec ℂ → P¹. The analytic
topology built from all affine-open regular functions is proved to agree
with the existing topology from the two original evaluation charts.
Neither topology is redefined by transport from the other.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineComplexPoints

open AlgebraicGeometry CategoryTheory Topology
open scoped Polynomial

/-- The identity on the underlying actual scheme sections. -/
def canonicalEquiv : Point ≃
    Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ)) where
  toFun p := ⟨schemeMorphism p, schemeMorphism_toBase p⟩
  invFun p := ⟨p.hom, p.hom_comp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original first chart in the canonical analytic topology. -/
def canonicalXChart (a : AffineLineComplexPoints.Point) :
    Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ)) :=
  Scheme.ComplexPoints.map (projectiveLineXChart ℂ)
    (projectiveLineXChart_comp_structureMorphism ℂ)
    (AffineComplexPoints.ofAlgHom ℂ[X] a)

/-- The original second chart in the canonical analytic topology. -/
def canonicalYChart (a : AffineLineComplexPoints.Point) :
    Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ)) :=
  Scheme.ComplexPoints.map (projectiveLineYChart ℂ)
    (projectiveLineYChart_comp_structureMorphism ℂ)
    (AffineComplexPoints.ofAlgHom ℂ[X] a)

@[simp]
theorem canonicalEquiv_xChart (a : AffineLineComplexPoints.Point) :
    canonicalEquiv (xChart a) = canonicalXChart a := rfl

@[simp]
theorem canonicalEquiv_yChart (a : AffineLineComplexPoints.Point) :
    canonicalEquiv (yChart a) = canonicalYChart a := rfl

theorem isOpenEmbedding_canonicalXChart : IsOpenEmbedding canonicalXChart :=
  (Scheme.ComplexPoints.isOpenEmbedding_map_of_isOpenImmersion
    (projectiveLineXChart ℂ) (projectiveLineXChart_comp_structureMorphism ℂ)).comp
      (AffineComplexPoints.homeomorph ℂ[X]).symm.isOpenEmbedding

theorem isOpenEmbedding_canonicalYChart : IsOpenEmbedding canonicalYChart :=
  (Scheme.ComplexPoints.isOpenEmbedding_map_of_isOpenImmersion
    (projectiveLineYChart ℂ) (projectiveLineYChart_comp_structureMorphism ℂ)).comp
      (AffineComplexPoints.homeomorph ℂ[X]).symm.isOpenEmbedding

theorem continuous_canonicalEquiv : Continuous canonicalEquiv := by
  rw [continuous_iff_charts]
  exact ⟨isOpenEmbedding_canonicalXChart.continuous, isOpenEmbedding_canonicalYChart.continuous⟩

theorem canonicalCharts_surjective :
    Function.Surjective (Sum.elim canonicalXChart canonicalYChart) := by
  intro p
  rcases charts_cover (canonicalEquiv.symm p) with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨Sum.inl a, ?_⟩
    change canonicalEquiv (xChart a) = p
    rw [ha, Equiv.apply_symm_apply]
  · refine ⟨Sum.inr a, ?_⟩
    change canonicalEquiv (yChart a) = p
    rw [ha, Equiv.apply_symm_apply]

/-- The canonical space is also the quotient of the same two original affine point charts. -/
theorem canonicalCharts_isQuotientMap :
    IsQuotientMap (Sum.elim canonicalXChart canonicalYChart) :=
  (isOpenEmbedding_canonicalXChart.isOpenMap.sumElim
    isOpenEmbedding_canonicalYChart.isOpenMap).isQuotientMap
      (isOpenEmbedding_canonicalXChart.continuous.sumElim
        isOpenEmbedding_canonicalYChart.continuous) canonicalCharts_surjective

theorem continuous_canonicalEquiv_symm : Continuous canonicalEquiv.symm := by
  apply canonicalCharts_isQuotientMap.continuous_iff.mpr
  have h : canonicalEquiv.symm ∘ Sum.elim canonicalXChart canonicalYChart =
      Sum.elim xChart yChart := by
    funext a
    cases a with
    | inl a => exact canonicalEquiv.symm_apply_apply (xChart a)
    | inr a => exact canonicalEquiv.symm_apply_apply (yChart a)
  rw [h]
  exact continuous_xChart.sumElim continuous_yChart

/-- A proved comparison of the two independently constructed topologies on the same scheme points. -/
def canonicalHomeomorph : Point ≃ₜ
    Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ)) where
  toEquiv := canonicalEquiv
  continuous_toFun := continuous_canonicalEquiv
  continuous_invFun := continuous_canonicalEquiv_symm

@[simp]
theorem canonicalHomeomorph_schemeMorphism (p : Point) :
    (canonicalHomeomorph p).hom = schemeMorphism p := rfl

/-- Hausdorffness is transferred through the already proved original point comparisons. -/
theorem canonicalT2Space :
    T2Space (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
  (canonicalHomeomorph.symm.trans onePointHomeomorph).isEmbedding.t2Space

/-- The actual canonical projective-line point topology is paracompact. -/
theorem canonicalParacompactSpace :
    ParacompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
  (canonicalHomeomorph.symm.trans onePointHomeomorph).paracompactSpace_iff.mpr inferInstance

/-- The original two affine charts give an open quotient map onto canonical points. -/
theorem canonicalCharts_isOpenQuotientMap :
    IsOpenQuotientMap (Sum.elim canonicalXChart canonicalYChart) :=
  ⟨canonicalCharts_surjective,
    isOpenEmbedding_canonicalXChart.continuous.sumElim isOpenEmbedding_canonicalYChart.continuous,
    isOpenMap_sumElim.mpr
      ⟨isOpenEmbedding_canonicalXChart.isOpenMap, isOpenEmbedding_canonicalYChart.isOpenMap⟩⟩

/-- Local compactness follows from the existing comparison of the original point topologies. -/
theorem canonicalLocallyCompactSpace :
    LocallyCompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
  (canonicalHomeomorph.symm.trans onePointHomeomorph).isOpenEmbedding.locallyCompactSpace

/-- A countable basis descends along those same two original charts. -/
theorem canonicalSecondCountableTopology :
    SecondCountableTopology (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) := by
  let : SecondCountableTopology AffineLineComplexPoints.Point :=
    AffineLineComplexPoints.coordinateHomeomorph.isEmbedding.secondCountableTopology
  exact canonicalCharts_isOpenQuotientMap.secondCountableTopology

end HodgeConjecture.ProjectiveLineComplexPoints
