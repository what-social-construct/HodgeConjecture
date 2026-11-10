module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLinePointSupport
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChartBoundary
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology

@[expose] public section

/-!
# The oriented Gysin map for the original projective-line zero point

Original point H⁰ maps to the oriented local relative Thom class in the
complex chart. Inverse actual excision places that class in cohomology
supported at the original zero point; forgetting support gives actual
singular H² of P¹. Native boundary naturality identifies its unit image
with the previously constructed positive cover generator.

The source, relative support, chart orientation and maps are explicit.
This constructs the Gysin map for this distinguished point and chart;
general point transport, coordinate independence and higher-codimension
Gysin constructions are separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLinePointGysin

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover ProjectiveLinePointSupport

abbrev space : TopCat := TopCat.of Point
abbrev complementSubcomplex := SingularSubcomplexes.subsetSingular space reciprocalOpen

/-- Actual rational cohomology with support in the singleton zero point. -/
abbrev SupportedH2 := RelativeCochains.Cohomology complementSubcomplex 2

/-- Original degree-zero singular cohomology of the actual singleton support. -/
abbrev PointH0 := SingularCochains.Cohomology (TopCat.of PointSupport) 0

abbrev AbsoluteH2 := SingularCochains.Cohomology space 2

/-- The original normal-coordinate map on the point's actual H⁰. -/
def pointPullbackIso : PointH0 ≅ SingularCochains.Cohomology (TopCat.of ComplexPointThom.Point) 0 :=
  SingularHomotopy.homeomorphIso pointHomeomorph 0

theorem pointPullbackIso_pointUnit : pointPullbackIso.hom pointUnit = ComplexPointThom.pointUnit := by
  change SingularCochains.cohomologyPullback
    (TopCat.ofHom (⟨pointHomeomorph, pointHomeomorph.continuous⟩ :
      C(ComplexPointThom.Point, PointSupport))) 0
    (SingularDegreeZeroNaturality.constantClass PointSupport 1) =
      SingularDegreeZeroNaturality.constantClass ComplexPointThom.Point 1
  exact SingularDegreeZeroNaturality.pullback_constantClass _ 1

/-- The actual chart comparison and inverse relative excision place the local class at its support. -/
def thomToSupportIso : ComplexPointThom.LocalH2 ≅ SupportedH2 :=
  ProjectiveLineNormalChart.normalClassIso 2 ≪≫
    (RelativeExcision.excisionIso space finiteOpen reciprocalOpen isOpen_finiteOpen
      isOpen_reciprocalOpen cover 2).symm

/-- The local orientation class in actual projective-line cohomology with support. -/
def supportedThomClass : SupportedH2 := thomToSupportIso.hom ComplexPointThom.thomClass

theorem supportedThomClass_ne_zero : supportedThomClass ≠ 0 := by
  intro h
  apply ComplexPointThom.thomClass_ne_zero
  apply thomToSupportIso.toLinearEquiv.injective
  change thomToSupportIso.hom ComplexPointThom.thomClass = thomToSupportIso.hom 0
  rw [map_zero]
  exact h

/-- Actual cohomology of the complement vanishes in positive degree. -/
theorem complementCohomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((SubcomplexCochains.complex complementSubcomplex.toSSet).homology n) :=
  (SingularContractible.isZero_cohomology reciprocalOpen n hn).of_iso
    (SingularMayerVietoris.chartCohomologyIso space reciprocalOpen n)

/-- Forgetting the support is itself an isomorphism here, by actual complement vanishing. -/
instance forget_isIso : IsIso (RelativeCochains.forget complementSubcomplex 2) := by
  have : Mono (RelativeCochains.forget complementSubcomplex 2) := by
    have h := (RelativeCochains.unionSequence_exact complementSubcomplex 1).mono_g
      ((complementCohomology_isZero 1 (by decide)).eq_of_src _ _)
    exact h
  have : Epi (RelativeCochains.forget complementSubcomplex 2) := by
    have h := (RelativeCochains.pairSequence_exact complementSubcomplex 2).epi_f
      ((complementCohomology_isZero 2 (by decide)).eq_of_tgt _ _)
    exact h
  exact isIso_of_mono_of_epi _

def forgetIso : SupportedH2 ≅ AbsoluteH2 := asIso (RelativeCochains.forget complementSubcomplex 2)

/-- The geometric supported class has the original positive absolute normalization. -/
theorem forget_supportedThomClass :
    RelativeCochains.forget complementSubcomplex 2 supportedThomClass =
      ProjectiveLineBettiCohomology.coverGenerator := by
  change RelativeCochains.forget complementSubcomplex 2
    ((RelativeExcision.excisionIso space finiteOpen reciprocalOpen isOpen_finiteOpen
      isOpen_reciprocalOpen cover 2).inv
        ((ProjectiveLineNormalChart.normalClassIso 2).hom ComplexPointThom.thomClass)) = _
  rw [ProjectiveLineNormalChart.normalClassIso_thomClass]
  have h := congrArg (fun f ↦ f
    (SingularCochains.cohomologyPullback
      (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1 CircleCohomology.coverGenerator))
    (RelativeMayerVietoris.connecting_excision_forget space finiteOpen reciprocalOpen
      isOpen_finiteOpen isOpen_reciprocalOpen cover 1)
  change RelativeCochains.forget complementSubcomplex 2
    ((RelativeExcision.excisionIso space finiteOpen reciprocalOpen isOpen_finiteOpen
      isOpen_reciprocalOpen cover 2).inv
        (RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
          (SingularCochains.cohomologyPullback
            (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1 CircleCohomology.coverGenerator))) =
    ProjectiveLineSingularCohomology.connecting
      (SingularCochains.cohomologyPullback
        (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1 CircleCohomology.coverGenerator) at h
  exact h.trans ProjectiveLineBettiCohomology.coverGenerator_eq_connecting.symm

/-- The actual supported point Gysin map, before forgetting support. -/
def supportedGysin : PointH0 →ₗ[ℚ] SupportedH2 :=
  thomToSupportIso.hom.hom.comp
    (ComplexPointThom.localGysin.comp pointPullbackIso.hom.hom)

/-- The geometric point Gysin map is local Thom, inverse excision, then original forgetting. -/
def gysin : PointH0 →ₗ[ℚ] AbsoluteH2 :=
  (RelativeCochains.forget complementSubcomplex 2).hom.comp supportedGysin

theorem supportedGysin_pointUnit : supportedGysin pointUnit = supportedThomClass := by
  change thomToSupportIso.hom (ComplexPointThom.localGysin (pointPullbackIso.hom pointUnit)) = _
  rw [pointPullbackIso_pointUnit, ComplexPointThom.localGysin_pointUnit]
  rfl

/-- The original point unit has exactly the computed positive projective-line class. -/
@[simp]
theorem gysin_pointUnit : gysin pointUnit = ProjectiveLineBettiCohomology.coverGenerator := by
  change RelativeCochains.forget complementSubcomplex 2 (supportedGysin pointUnit) = _
  rw [supportedGysin_pointUnit, forget_supportedThomClass]

/-- The geometric point Gysin isomorphism retains the original local and global maps. -/
def gysinIso : PointH0 ≅ AbsoluteH2 :=
  pointPullbackIso ≪≫ ComplexPointThom.thomIso.toModuleIso ≪≫ thomToSupportIso ≪≫ forgetIso

theorem gysinIso_apply (z : PointH0) : gysinIso.hom z = gysin z := by
  change RelativeCochains.forget complementSubcomplex 2
    (thomToSupportIso.hom (ComplexPointThom.thomIso (pointPullbackIso.hom z))) = _
  rw [ComplexPointThom.thomIso_apply]
  rfl

theorem gysin_bijective : Function.Bijective gysin := by
  have h : (gysin : PointH0 → AbsoluteH2) = gysinIso.hom := funext (fun z ↦ (gysinIso_apply z).symm)
  rw [h]
  exact gysinIso.toLinearEquiv.bijective

end HodgeConjecture.ProjectiveLinePointGysin
