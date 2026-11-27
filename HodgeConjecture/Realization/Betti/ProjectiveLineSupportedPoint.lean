module

public import HodgeConjecture.Realization.Betti.ProjectiveLineInfinityGysin
public import HodgeConjecture.Realization.Betti.SingularFiniteSupport

@[expose] public section

/-!
# Original point-supported Thom isomorphisms with one common support interface

The actual finite or reciprocal normal chart selects the already constructed
local Thom/excision isomorphism. Infinity's complement is identified with its
literal singleton complement by original identity-pair pullback. No absolute
cohomology coordinate defines any supported map.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSupportedPoint

open CategoryTheory HomologicalComplex
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

abbrev space : TopCat := TopCat.of Point
abbrev PointH0 (p : Point) := SingularFiniteSupport.PointH0 p
abbrev complement (p : Point) := SingularSubcomplexes.subsetSingular space ({p} : Set Point)ᶜ
abbrev SupportedH2 (p : Point) := RelativeCochains.Cohomology (complement p) 2
abbrev AbsoluteH2 := ProjectiveLinePointGysin.AbsoluteH2
abbrev pointUnit (p : Point) := SingularFiniteSupport.pointUnit p

def forget (p : Point) : SupportedH2 p →ₗ[ℚ] AbsoluteH2 :=
  (RelativeCochains.forget (complement p) 2).hom

/-- Data selecting an actual original normal chart, rather than an absolute class. -/
inductive Chart : Point → Type
  | finite (a : ℂ) : Chart (ProjectiveLineComplexPoints.finite a)
  | infinity : Chart ProjectiveLineComplexPoints.infinity

theorem chart_nonempty (p : Point) : Nonempty (Chart p) := by
  rcases finite_or_infinity p with ⟨a, rfl⟩ | rfl
  · exact ⟨Chart.finite a⟩
  · exact ⟨Chart.infinity⟩

def chart (p : Point) : Chart p := Classical.choice (chart_nonempty p)

theorem infinity_condition : complement infinity =
    ProjectiveLineInfinityGysin.second.preimage (𝟙 (TopCat.toSSet.obj space)) := by
  ext n σ
  change (∀ t, SingularSubcomplexes.simplexMap space n σ t ∈ ({infinity} : Set Point)ᶜ) ↔
    ∀ t, SingularSubcomplexes.simplexMap space n σ t ∈ finiteOpen
  rw [show finiteOpen = ({infinity} : Set Point)ᶜ from range_finite]

/-- Original identity pullback changes only the proved equal descriptions of the infinity complement. -/
def infinityCochainIso : RelativeCochains.complex ProjectiveLineInfinityGysin.second ≅
    RelativeCochains.complex (complement infinity) :=
  RelativeCochains.pullbackIso (Iso.refl _) infinity_condition

def infinitySupportIso : ProjectiveLineInfinityGysin.SupportedH2 ≅ SupportedH2 infinity :=
  homologyMapIso infinityCochainIso 2

theorem infinitySupportIso_forget :
    infinitySupportIso.hom ≫ RelativeCochains.forget (complement infinity) 2 =
      RelativeCochains.forget ProjectiveLineInfinityGysin.second 2 := by
  change RelativeCochains.cohomologyPullback (𝟙 _) infinity_condition.le 2 ≫
    RelativeCochains.forget (complement infinity) 2 = _
  rw [RelativeCochains.cohomologyPullback_forget]
  change RelativeCochains.forget ProjectiveLineInfinityGysin.second 2 ≫
    homologyMap (SimplicialCochains.pullback (𝟙 _)) 2 = _
  rw [SimplicialCochains.pullback_id, homologyMap_id]
  exact Category.comp_id _

/-- Both cases are the actual point H⁰→local Thom→original chart/excision maps. -/
def isoOfChart {p : Point} (c : Chart p) : PointH0 p ≅ SupportedH2 p := by
  cases c with
  | finite a =>
      change ProjectiveLineFinitePointGysin.PointH0 a ≅ ProjectiveLineFinitePointGysin.SupportedH2 a
      exact ProjectiveLineFinitePointGysin.pointPullbackIso a ≪≫
        ComplexPointThom.thomIso.toModuleIso ≪≫ ProjectiveLineFinitePointGysin.thomToSupportIso a 1
  | infinity =>
      change ProjectiveLineInfinityGysin.PointH0 ≅ SupportedH2 infinity
      exact ProjectiveLineInfinityGysin.pointPullbackIso ≪≫
        ComplexPointThom.thomIso.toModuleIso ≪≫ ProjectiveLineInfinityGysin.thomToSupportIso 1 ≪≫
          infinitySupportIso

theorem forget_isoOfChart_unit {p : Point} (c : Chart p) :
    forget p ((isoOfChart c).hom (pointUnit p)) = ProjectiveLineBettiCohomology.coverGenerator := by
  cases c with
  | finite a =>
      change RelativeCochains.forget (ProjectiveLineFinitePointGysin.second a) 2
        ((ProjectiveLineFinitePointGysin.thomToSupportIso a 1).hom
          (ComplexPointThom.thomIso ((ProjectiveLineFinitePointGysin.pointPullbackIso a).hom
            (ProjectiveLineFinitePointSupport.pointUnit a)))) = _
      rw [ComplexPointThom.thomIso_apply, ProjectiveLineFinitePointGysin.pointPullbackIso_pointUnit,
        ComplexPointThom.localGysin_pointUnit]
      exact ProjectiveLineFinitePointGysin.forget_supportedThomClass a 1
  | infinity =>
      change RelativeCochains.forget (complement infinity) 2
        (infinitySupportIso.hom ((ProjectiveLineInfinityGysin.thomToSupportIso 1).hom
          (ComplexPointThom.thomIso (ProjectiveLineInfinityGysin.pointPullbackIso.hom
            ProjectiveLineInfinitySupport.pointUnit)))) = _
      rw [ComplexPointThom.thomIso_apply, ProjectiveLineInfinityGysin.pointPullbackIso_pointUnit,
        ComplexPointThom.localGysin_pointUnit]
      change (infinitySupportIso.hom ≫ RelativeCochains.forget (complement infinity) 2)
        (ProjectiveLineInfinityGysin.supportedThomClass 1) = _
      rw [infinitySupportIso_forget]
      exact ProjectiveLineInfinityGysin.forget_supportedThomClass 1

/-- A single source/target interface for the actual selected normal-chart construction. -/
def gysinIso (p : Point) : PointH0 p ≅ SupportedH2 p := isoOfChart (chart p)

def supportedGysin (p : Point) : PointH0 p →ₗ[ℚ] SupportedH2 p := (gysinIso p).hom.hom

def gysin (p : Point) : PointH0 p →ₗ[ℚ] AbsoluteH2 := (forget p).comp (supportedGysin p)

theorem gysin_pointUnit (p : Point) :
    gysin p (pointUnit p) = ProjectiveLineBettiCohomology.coverGenerator :=
  forget_isoOfChart_unit (chart p)

theorem gysin_apply (p : Point) (z : PointH0 p) :
    gysin p z = SingularFiniteSupport.pointCoordinates p z •
      ProjectiveLineBettiCohomology.coverGenerator := by
  have h := congrArg (gysin p) (SingularFiniteSupport.point_eq_smul_unit p z)
  simpa only [map_smul, gysin_pointUnit] using h

theorem supportedGysin_bijective (p : Point) : Function.Bijective (supportedGysin p) :=
  (gysinIso p).toLinearEquiv.bijective

end HodgeConjecture.ProjectiveLineSupportedPoint

end
