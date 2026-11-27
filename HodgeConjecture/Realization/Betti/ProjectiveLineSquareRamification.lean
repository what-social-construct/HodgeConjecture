module

public import HodgeConjecture.Realization.Betti.RelativeCochainsNaturality
public import HodgeConjecture.Realization.Betti.Examples.ComplexSquareThom
public import HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin

@[expose] public section

/-!
# Actual ramified point-Gysin pullback for the projective-line square

The original map acts on the actual pair consisting of P¹ and the complement
of zero. Restricting its original relative cochains to the original finite
normal chart intertwines this map with the actual complex square. Native
excision identifies that restriction with the inverse of the existing local
Thom-to-support isomorphism. The independent local ramification calculation
therefore gives the supported and absolute Gysin pullback formula with factor
two. The old absolute H² square calculation is not used in this proof.

The singleton is a topological support. Its reduced point square is not
asserted to be a cartesian square of schemes; the actual fiber is nonreduced.
Geometric identification of the factor with the original local multiplicity
is made separately, without introducing Chow groups into this native module.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquareRamification

open CategoryTheory HomologicalComplex Opposite Simplicial
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

abbrev space : TopCat := TopCat.of Point
abbrev complement := ProjectiveLinePointGysin.complementSubcomplex
abbrev SupportedH2 := ProjectiveLinePointGysin.SupportedH2
abbrev PointH0 := ProjectiveLinePointGysin.PointH0
abbrev Betti := ProjectiveLinePointGysin.AbsoluteH2
abbrev pointMap := ProjectiveLineSquarePullback.pointMap

/-- The original global square preserves the actual complement of zero. -/
theorem pairCondition : complement ≤ complement.preimage (TopCat.toSSet.map pointMap) :=
  RelativeCochains.subsetCondition pointMap reciprocalOpen reciprocalOpen
    ProjectiveLineSquarePullback.mapsTo_reciprocalOpen

/-- Original precomposition on the actual relative kernel, with no chosen coordinates. -/
def relativePullback : RelativeCochains.complex complement ⟶
    RelativeCochains.complex complement :=
  RelativeCochains.pullback (TopCat.toSSet.map pointMap) pairCondition

def supportedPull (n : ℕ) : RelativeCochains.Cohomology complement n ⟶
    RelativeCochains.Cohomology complement n := homologyMap relativePullback n

/-- The same actual pair map commutes with original forgetting of support. -/
theorem supportedPull_forget (n : ℕ) :
    supportedPull n ≫ RelativeCochains.forget complement n =
      RelativeCochains.forget complement n ≫
        SingularCochains.cohomologyPullback pointMap n :=
  RelativeCochains.cohomologyPullback_forget (TopCat.toSSet.map pointMap) pairCondition n

/-- The original continuous finite coordinate chart. -/
def finiteChartMap : TopCat.of ℂ ⟶ space := TopCat.ofHom ⟨finite, continuous_finite⟩

/-- This is the literal normal-chart diagram of the actual scheme-induced square map. -/
theorem finiteChart_naturality :
    ComplexSquareThom.squareMap ≫ finiteChartMap = finiteChartMap ≫ pointMap := by
  ext z : 1
  exact (ProjectiveLineSquarePullback.pointMap_finite z).symm

theorem chartCondition : ComplexPointThom.puncturedSubcomplex ≤
    complement.preimage (TopCat.toSSet.map finiteChartMap) := by
  intro n σ hσ t
  exact (finite_mem_reciprocal_iff _).mpr (hσ t)

/-- Actual relative restriction along the original finite coordinate chart. -/
def chartPullback : RelativeCochains.complex complement ⟶
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map finiteChartMap) chartCondition

/-- The original excision restriction and normal chart are exactly this pair pullback. -/
theorem chartPullback_eq_original :
    RelativeExcision.restriction ProjectiveLineNormalChart.first ProjectiveLineNormalChart.second ≫
        ProjectiveLineNormalChart.normalPullbackIso.hom = chartPullback := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

/-- Original excision followed by original normal-coordinate pullback, in every degree. -/
def chartComparison (n : ℕ) : RelativeCochains.Cohomology complement n ≅
    RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n :=
  RelativeExcision.excisionIso space finiteOpen reciprocalOpen isOpen_finiteOpen
    isOpen_reciprocalOpen cover n ≪≫ (ProjectiveLineNormalChart.normalClassIso n).symm

theorem chartComparison_hom (n : ℕ) :
    (chartComparison n).hom = homologyMap chartPullback n := by
  rw [chartComparison, Iso.trans_hom, RelativeExcision.excisionIso_hom]
  change homologyMap
      (RelativeExcision.restriction ProjectiveLineNormalChart.first
        ProjectiveLineNormalChart.second) n ≫
    homologyMap ProjectiveLineNormalChart.normalPullbackIso.hom n = _
  rw [← homologyMap_comp, chartPullback_eq_original]

/-- In degree two this retains precisely the existing local-to-supported Thom comparison. -/
theorem chartComparison_two_hom :
    (chartComparison 2).hom = ProjectiveLinePointGysin.thomToSupportIso.inv := rfl

/-- Naturality already holds on the original relative cochain complexes. -/
theorem relativePullback_chart :
    relativePullback ≫ chartPullback = chartPullback ≫ ComplexSquareThom.localRelativePullback := by
  have h : TopCat.toSSet.map finiteChartMap ≫ TopCat.toSSet.map pointMap =
      TopCat.toSSet.map ComplexSquareThom.squareMap ≫ TopCat.toSSet.map finiteChartMap := by
    rw [← Functor.map_comp, ← Functor.map_comp, finiteChart_naturality]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val ((TopCat.toSSet.map finiteChartMap ≫ TopCat.toSSet.map pointMap).app
      (op ⦋n⦌) σ) =
    φ.val ((TopCat.toSSet.map ComplexSquareThom.squareMap ≫
      TopCat.toSSet.map finiteChartMap).app (op ⦋n⦌) σ)
  rw [h]

/-- Local-to-global compatibility is induced by the actual original cochain square. -/
theorem chartComparison_naturality (n : ℕ) :
    supportedPull n ≫ (chartComparison n).hom =
      (chartComparison n).hom ≫ ComplexSquareThom.localPull n := by
  rw [chartComparison_hom]
  change homologyMap relativePullback n ≫ homologyMap chartPullback n =
    homologyMap chartPullback n ≫ homologyMap ComplexSquareThom.localRelativePullback n
  rw [← homologyMap_comp, ← homologyMap_comp, relativePullback_chart]

/-- The local relative ramification calculation determines the original supported map. -/
theorem supportedPull_square (z : SupportedH2) : supportedPull 2 z = (2 : ℚ) • z := by
  apply (ModuleCat.mono_iff_injective (chartComparison 2).hom).mp inferInstance
  have h := congrArg (fun f ↦ f z) (chartComparison_naturality 2)
  change (chartComparison 2).hom (supportedPull 2 z) =
    ComplexSquareThom.localPull 2 ((chartComparison 2).hom z) at h
  rw [ComplexSquareThom.localPull_square] at h
  simpa only [map_smul] using h

theorem supportedPull_thomClass :
    supportedPull 2 ProjectiveLinePointGysin.supportedThomClass =
      (2 : ℚ) • ProjectiveLinePointGysin.supportedThomClass :=
  supportedPull_square _

/-- Actual singleton-support H⁰ pullback, distinct from its ramified Gysin pullback. -/
def pointPull : PointH0 →ₗ[ℚ] PointH0 :=
  (SingularCochains.cohomologyPullback ProjectiveLineSquareGysin.supportMap 0).hom

theorem pointPull_eq_id : pointPull = LinearMap.id := by
  change (SingularCochains.cohomologyPullback ProjectiveLineSquareGysin.supportMap 0).hom = _
  rw [ProjectiveLineSquareGysin.supportMap_eq_id, SingularCochains.cohomologyPullback_id]
  rfl

/-- Ramification contributes two even though the actual singleton pullback is identity. -/
theorem supportedGysin_pullback (z : PointH0) :
    supportedPull 2 (ProjectiveLinePointGysin.supportedGysin z) =
      (2 : ℚ) • ProjectiveLinePointGysin.supportedGysin (pointPull z) := by
  rw [supportedPull_square, pointPull_eq_id, LinearMap.id_apply]

/-- Forgetting the proved supported formula gives the actual absolute Gysin pullback formula. -/
theorem gysin_pullback (z : PointH0) :
    SingularCochains.cohomologyPullback pointMap 2 (ProjectiveLinePointGysin.gysin z) =
      (2 : ℚ) • ProjectiveLinePointGysin.gysin (pointPull z) := by
  have h := congrArg (fun f ↦ f (ProjectiveLinePointGysin.supportedGysin z))
    (supportedPull_forget 2)
  change RelativeCochains.forget complement 2
      (supportedPull 2 (ProjectiveLinePointGysin.supportedGysin z)) =
    SingularCochains.cohomologyPullback pointMap 2 (ProjectiveLinePointGysin.gysin z) at h
  rw [supportedGysin_pullback, map_smul] at h
  exact h.symm

/-- Native absolute degree is recovered from the local ramification proof and geometric Gysin iso. -/
theorem cohomologyPullback_square (z : Betti) :
    SingularCochains.cohomologyPullback pointMap 2 z = (2 : ℚ) • z := by
  obtain ⟨w, rfl⟩ := ProjectiveLinePointGysin.gysin_bijective.surjective z
  rw [gysin_pullback, pointPull_eq_id, LinearMap.id_apply]

theorem cohomologyPullback_square_eq :
    (SingularCochains.cohomologyPullback pointMap 2).hom = (2 : ℚ) • LinearMap.id := by
  apply LinearMap.ext
  exact cohomologyPullback_square

/-- The existing supported push and new local ramification proof supply the degree law. -/
def degreeTransfer : RationalDegreeTransfer Betti Betti where
  pull := (SingularCochains.cohomologyPullback pointMap 2).hom
  push := ProjectiveLineSquareGysin.push
  degree := 2
  degree_ne_zero := by decide
  push_comp_pull := by
    rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_comp]
    exact cohomologyPullback_square_eq

end HodgeConjecture.ProjectiveLineSquareRamification

end
