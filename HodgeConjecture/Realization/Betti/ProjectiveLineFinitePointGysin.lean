module

public import HodgeConjecture.Geometry.ProjectiveLineAffineChart
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineFinitePointSupport
public import HodgeConjecture.Realization.Betti.ProjectiveLinePointGysin
public import HodgeConjecture.Realization.Betti.RelativeCochainsNaturality

@[expose] public section

/-!
# Actual Gysin maps at every finite point of the original projective line

Each normal coordinate is the original scheme map induced by the polynomial
automorphism X ↦ uX+a. Original relative pullback, normal-coordinate comparison,
excision and forgetting construct the supported and absolute Gysin maps.
Actual affine homotopy on the fixed point topology gives positive normalization.
Faithful support forgetting then proves independence of the unit u.

These are finite-point constructions and independence under affine complex
normal coordinates. A global algebraic affine automorphism of the glued P¹,
arbitrary analytic-coordinate independence and general proper trace are not
assumed or constructed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFinitePointGysin

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

abbrev space : TopCat := TopCat.of Point
abbrev PointH0 (a : ℂ) := ProjectiveLineFinitePointSupport.PointH0 a
abbrev complement (a : ℂ) := ProjectiveLineFinitePointSupport.complement a
abbrev first := SingularSubcomplexes.subsetSingular space finiteOpen
abbrev second (a : ℂ) := SingularSubcomplexes.subsetSingular space (complement a)
abbrev localBoundary (a : ℂ) := RelativeUnion.localBoundary first (second a)
abbrev SupportedH2 (a : ℂ) := RelativeCochains.Cohomology (second a) 2
abbrev AbsoluteH2 := ProjectiveLinePointGysin.AbsoluteH2

/-- The actual original scheme section evaluated in the actual affine scheme normal chart. -/
def normalChartPoint (a : ℂ) (u : ℂˣ) (z : ℂ) : Point :=
  ⟨ProjectiveLineAffineChart.affineSection ℂ z ≫
    ProjectiveLineAffineChart.normalChart ℂ a u, by
      rw [Category.assoc, ProjectiveLineAffineChart.normalChart_over_base,
        ProjectiveLineAffineChart.affineSection_over_base]⟩

theorem normalChartPoint_schemeMorphism (a : ℂ) (u : ℂˣ) (z : ℂ) :
    schemeMorphism (normalChartPoint a u z) =
      ProjectiveLineAffineChart.affineSection ℂ z ≫
        ProjectiveLineAffineChart.normalChart ℂ a u := rfl

@[simp]
theorem normalChartPoint_finite (a : ℂ) (u : ℂˣ) (z : ℂ) :
    normalChartPoint a u z = finite (a + (u : ℂ) * z) := by
  apply ProjectiveLineComplexPoints.ext
  change ProjectiveLineAffineChart.affineSection ℂ z ≫
      ProjectiveLineAffineChart.normalChart ℂ a u = _
  rw [ProjectiveLineAffineChart.affineSection_normalChart]
  rfl

theorem continuous_normalChartPoint (a : ℂ) (u : ℂˣ) : Continuous (normalChartPoint a u) := by
  have h : normalChartPoint a u = finite ∘ ProjectiveLineAffine.complexAffineHomeomorph a u :=
    funext (normalChartPoint_finite a u)
  rw [h]
  exact continuous_finite.comp (ProjectiveLineAffine.complexAffineHomeomorph a u).continuous

def normalChartMap (a : ℂ) (u : ℂˣ) : TopCat.of ℂ ⟶ space :=
  TopCat.ofHom ⟨normalChartPoint a u, continuous_normalChartPoint a u⟩

/-- The normal chart retains the actual underlying closed scheme point at its center. -/
theorem normalChart_center_base (a : ℂ) (u : ℂˣ) (q : Spec (.of ℂ)) :
    schemeMorphism (normalChartPoint a u 0) q = ProjectiveLineAffineChart.center ℂ a := by
  rw [normalChartPoint_finite]
  simp only [mul_zero, add_zero]
  exact ProjectiveLineAffineChart.finiteSection_base ℂ a q

/-- Every actual point of the singleton support has this same original closed scheme image. -/
theorem pointSupport_scheme_base (a : ℂ)
    (p : ProjectiveLineFinitePointSupport.PointSupport a) (q : Spec (.of ℂ)) :
    schemeMorphism p.val q = ProjectiveLineAffineChart.center ℂ a := by
  have hp : p.val = finite a := Set.mem_singleton_iff.mp p.property
  rw [hp]
  exact ProjectiveLineAffineChart.finiteSection_base ℂ a q

def normalHomeomorph (a : ℂ) (u : ℂˣ) : ℂ ≃ₜ finiteOpen :=
  (ProjectiveLineAffine.complexAffineHomeomorph a u).trans finiteHomeomorph

def normalSSetIso (a : ℂ) (u : ℂˣ) : TopCat.toSSet.obj (TopCat.of ℂ) ≅ first.toSSet :=
  TopCat.toSSet.mapIso
      (TopCat.isoOfHomeo (X := TopCat.of ℂ) (Y := TopCat.of finiteOpen) (normalHomeomorph a u)) ≪≫
    (SingularSubcomplexes.subsetSingularIso space finiteOpen).symm

/-- The topological normal chart is bound to the original scheme normal-chart map. -/
theorem normalSSetIso_inclusion (a : ℂ) (u : ℂˣ) :
    (normalSSetIso a u).hom ≫ first.ι = TopCat.toSSet.map (normalChartMap a u) := by
  change TopCat.toSSet.map
      (TopCat.ofHom (⟨normalHomeomorph a u, (normalHomeomorph a u).continuous⟩ :
        C(ℂ, finiteOpen))) ≫
      SingularSubcomplexes.subtypeToSubset space finiteOpen ≫ first.ι = _
  rw [Category.assoc, SingularSubcomplexes.subtypeToSubset_ι, ← Functor.map_comp]
  apply congrArg TopCat.toSSet.map
  ext z : 1
  exact (normalChartPoint_finite a u z).symm

theorem punctured_preimage (a : ℂ) (u : ℂˣ) :
    ComplexPointThom.puncturedSubcomplex = (localBoundary a).preimage (normalSSetIso a u).hom := by
  ext n σ
  change (∀ t, SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t ≠ 0) ↔
    ∀ t, finite (a + (u : ℂ) * SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) ∈ complement a
  simp only [ProjectiveLineFinitePointSupport.finite_mem_complement_iff,
    add_eq_left, mul_eq_zero, u.ne_zero, false_or]

def normalPullbackIso (a : ℂ) (u : ℂˣ) : RelativeCochains.complex (localBoundary a) ≅
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullbackIso (normalSSetIso a u) (punctured_preimage a u)

def normalClassIso (a : ℂ) (u : ℂˣ) (n : ℕ) :
    RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n ≅
      RelativeCochains.Cohomology (localBoundary a) n :=
  (homologyMapIso (normalPullbackIso a u) n).symm

theorem chartCondition (a : ℂ) (u : ℂˣ) : ComplexPointThom.puncturedSubcomplex ≤
    (second a).preimage (TopCat.toSSet.map (normalChartMap a u)) := by
  intro n σ hσ t
  change normalChartPoint a u (SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) ∈ complement a
  rw [normalChartPoint_finite, ProjectiveLineFinitePointSupport.finite_mem_complement_iff]
  simpa only [add_eq_left, mul_eq_zero, u.ne_zero, false_or] using hσ t

def chartPullback (a : ℂ) (u : ℂˣ) : RelativeCochains.complex (second a) ⟶
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map (normalChartMap a u)) (chartCondition a u)

theorem chartPullback_eq_original (a : ℂ) (u : ℂˣ) :
    RelativeExcision.restriction first (second a) ≫ (normalPullbackIso a u).hom =
      chartPullback a u := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val (((normalSSetIso a u).hom ≫ first.ι).app (op ⦋n⦌) σ) =
    φ.val ((TopCat.toSSet.map (normalChartMap a u)).app (op ⦋n⦌) σ)
  rw [normalSSetIso_inclusion]

def excisionIso (a : ℂ) (n : ℕ) : RelativeCochains.Cohomology (second a) n ≅
    RelativeCochains.Cohomology (localBoundary a) n :=
  RelativeExcision.excisionIso space finiteOpen (complement a) isOpen_finiteOpen
    (ProjectiveLineFinitePointSupport.complement_isOpen a)
    (ProjectiveLineFinitePointSupport.cover a) n

def chartComparison (a : ℂ) (u : ℂˣ) (n : ℕ) : RelativeCochains.Cohomology (second a) n ≅
    RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n :=
  excisionIso a n ≪≫ (normalClassIso a u n).symm

theorem chartComparison_hom (a : ℂ) (u : ℂˣ) (n : ℕ) :
    (chartComparison a u n).hom = homologyMap (chartPullback a u) n := by
  rw [chartComparison, Iso.trans_hom]
  change homologyMap (RelativeExcision.restriction first (second a)) n ≫
    homologyMap (normalPullbackIso a u).hom n = _
  rw [← homologyMap_comp, chartPullback_eq_original]

def pointPullbackIso (a : ℂ) : PointH0 a ≅
    SingularCochains.Cohomology (TopCat.of ComplexPointThom.Point) 0 :=
  SingularHomotopy.homeomorphIso (ProjectiveLineFinitePointSupport.pointNormalHomeomorph a) 0

theorem pointPullbackIso_pointUnit (a : ℂ) :
    (pointPullbackIso a).hom (ProjectiveLineFinitePointSupport.pointUnit a) =
      ComplexPointThom.pointUnit :=
  SingularDegreeZeroNaturality.pullback_constantClass _ 1

def thomToSupportIso (a : ℂ) (u : ℂˣ) : ComplexPointThom.LocalH2 ≅ SupportedH2 a :=
  normalClassIso a u 2 ≪≫ (excisionIso a 2).symm

theorem chartComparison_two_hom (a : ℂ) (u : ℂˣ) :
    (chartComparison a u 2).hom = (thomToSupportIso a u).inv := rfl

def supportedThomClass (a : ℂ) (u : ℂˣ) : SupportedH2 a :=
  (thomToSupportIso a u).hom ComplexPointThom.thomClass

theorem complementCohomology_isZero (a : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsZero ((SubcomplexCochains.complex (second a).toSSet).homology n) :=
  (SingularContractible.isZero_cohomology (complement a) n hn).of_iso
    (SingularMayerVietoris.chartCohomologyIso space (complement a) n)

instance forget_isIso (a : ℂ) : IsIso (RelativeCochains.forget (second a) 2) := by
  have : Mono (RelativeCochains.forget (second a) 2) :=
    (RelativeCochains.unionSequence_exact (second a) 1).mono_g
      ((complementCohomology_isZero a 1 (by decide)).eq_of_src _ _)
  have : Epi (RelativeCochains.forget (second a) 2) :=
    (RelativeCochains.pairSequence_exact (second a) 2).epi_f
      ((complementCohomology_isZero a 2 (by decide)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

def forgetIso (a : ℂ) : SupportedH2 a ≅ AbsoluteH2 := asIso (RelativeCochains.forget (second a) 2)

def supportedGysin (a : ℂ) (u : ℂˣ) : PointH0 a →ₗ[ℚ] SupportedH2 a :=
  (thomToSupportIso a u).hom.hom.comp
    (ComplexPointThom.localGysin.comp (pointPullbackIso a).hom.hom)

def gysin (a : ℂ) (u : ℂˣ) : PointH0 a →ₗ[ℚ] AbsoluteH2 :=
  (RelativeCochains.forget (second a) 2).hom.comp (supportedGysin a u)

theorem supportedGysin_pointUnit (a : ℂ) (u : ℂˣ) :
    supportedGysin a u (ProjectiveLineFinitePointSupport.pointUnit a) = supportedThomClass a u := by
  change (thomToSupportIso a u).hom (ComplexPointThom.localGysin
    ((pointPullbackIso a).hom (ProjectiveLineFinitePointSupport.pointUnit a))) = _
  rw [pointPullbackIso_pointUnit, ComplexPointThom.localGysin_pointUnit]
  rfl

/-! Comparison with the original zero chart, retaining the original relative restriction. -/

def zeroChartMap : TopCat.of ℂ ⟶ space := TopCat.ofHom ⟨finite, continuous_finite⟩

theorem zeroChartCondition : ComplexPointThom.puncturedSubcomplex ≤
    ProjectiveLinePointGysin.complementSubcomplex.preimage (TopCat.toSSet.map zeroChartMap) := by
  intro n σ hσ t
  exact (finite_mem_reciprocal_iff _).mpr (hσ t)

def zeroChartPullback : RelativeCochains.complex ProjectiveLinePointGysin.complementSubcomplex ⟶
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map zeroChartMap) zeroChartCondition

def zeroChartComparison (n : ℕ) :
    RelativeCochains.Cohomology ProjectiveLinePointGysin.complementSubcomplex n ≅
      RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n :=
  RelativeExcision.excisionIso space finiteOpen reciprocalOpen isOpen_finiteOpen
    isOpen_reciprocalOpen ProjectiveLineAnalyticCover.cover n ≪≫
      (ProjectiveLineNormalChart.normalClassIso n).symm

theorem zeroChartComparison_hom (n : ℕ) :
    (zeroChartComparison n).hom = homologyMap zeroChartPullback n := by
  rw [zeroChartComparison, Iso.trans_hom, RelativeExcision.excisionIso_hom]
  change homologyMap (RelativeExcision.restriction ProjectiveLineNormalChart.first
    ProjectiveLineNormalChart.second) n ≫
    homologyMap ProjectiveLineNormalChart.normalPullbackIso.hom n = _
  rw [← homologyMap_comp]
  rfl

theorem zeroChartComparison_two_hom :
    (zeroChartComparison 2).hom = ProjectiveLinePointGysin.thomToSupportIso.inv := rfl

def affinePairCondition (a : ℂ) (u : ℂˣ) :
    ProjectiveLinePointGysin.complementSubcomplex ≤
      (second a).preimage (TopCat.toSSet.map (ProjectiveLineAffine.affineMap a u)) :=
  RelativeCochains.subsetCondition (ProjectiveLineAffine.affineMap a u) reciprocalOpen
    (complement a) (ProjectiveLineFinitePointSupport.mapsTo_complement a u)

def affineRelativePullback (a : ℂ) (u : ℂˣ) : RelativeCochains.complex (second a) ⟶
    RelativeCochains.complex ProjectiveLinePointGysin.complementSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map (ProjectiveLineAffine.affineMap a u))
    (affinePairCondition a u)

def affineSupportedPull (a : ℂ) (u : ℂˣ) (n : ℕ) :
    RelativeCochains.Cohomology (second a) n ⟶
      RelativeCochains.Cohomology ProjectiveLinePointGysin.complementSubcomplex n :=
  homologyMap (affineRelativePullback a u) n

theorem affine_normalChart (a : ℂ) (u : ℂˣ) :
    zeroChartMap ≫ ProjectiveLineAffine.affineMap a u = normalChartMap a u := by
  ext z : 1
  change ProjectiveLineAffine.affineMap a u (finite z) = normalChartPoint a u z
  rw [ProjectiveLineAffine.affineMap_finite, normalChartPoint_finite]

theorem affineRelativePullback_chart (a : ℂ) (u : ℂˣ) :
    affineRelativePullback a u ≫ zeroChartPullback = chartPullback a u := by
  have h : TopCat.toSSet.map zeroChartMap ≫ TopCat.toSSet.map (ProjectiveLineAffine.affineMap a u) =
      TopCat.toSSet.map (normalChartMap a u) := by rw [← Functor.map_comp, affine_normalChart]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val ((TopCat.toSSet.map zeroChartMap ≫
    TopCat.toSSet.map (ProjectiveLineAffine.affineMap a u)).app (op ⦋n⦌) σ) =
    φ.val ((TopCat.toSSet.map (normalChartMap a u)).app (op ⦋n⦌) σ)
  rw [h]

theorem affineSupportedPull_chart (a : ℂ) (u : ℂˣ) (n : ℕ) :
    affineSupportedPull a u n ≫ (zeroChartComparison n).hom = (chartComparison a u n).hom := by
  rw [zeroChartComparison_hom, chartComparison_hom]
  change homologyMap (affineRelativePullback a u) n ≫ homologyMap zeroChartPullback n = _
  rw [← homologyMap_comp, affineRelativePullback_chart]

theorem affineSupportedPull_forget (a : ℂ) (u : ℂˣ) (n : ℕ) :
    affineSupportedPull a u n ≫
        RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex n =
      RelativeCochains.forget (second a) n ≫
        SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap a u) n :=
  RelativeCochains.cohomologyPullback_forget _ (affinePairCondition a u) n

theorem affineSupportedPull_thomClass (a : ℂ) (u : ℂˣ) :
    affineSupportedPull a u 2 (supportedThomClass a u) =
      ProjectiveLinePointGysin.supportedThomClass := by
  apply (ModuleCat.mono_iff_injective (zeroChartComparison 2).hom).mp inferInstance
  have h := congrArg (fun f ↦ f (supportedThomClass a u)) (affineSupportedPull_chart a u 2)
  change (zeroChartComparison 2).hom (affineSupportedPull a u 2 (supportedThomClass a u)) =
    (chartComparison a u 2).hom (supportedThomClass a u) at h
  rw [chartComparison_two_hom, supportedThomClass, ← ModuleCat.comp_apply,
    Iso.hom_inv_id, ModuleCat.id_apply] at h
  rw [h, zeroChartComparison_two_hom, ProjectiveLinePointGysin.supportedThomClass,
    ← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply]

/-- The native affine homotopy, not a chosen absolute coordinate, fixes positive normalization. -/
theorem forget_supportedThomClass (a : ℂ) (u : ℂˣ) :
    RelativeCochains.forget (second a) 2 (supportedThomClass a u) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  have h := congrArg (fun f ↦ f (supportedThomClass a u)) (affineSupportedPull_forget a u 2)
  change RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2
      (affineSupportedPull a u 2 (supportedThomClass a u)) =
    SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap a u) 2
      (RelativeCochains.forget (second a) 2 (supportedThomClass a u)) at h
  rw [affineSupportedPull_thomClass, ProjectiveLinePointGysin.forget_supportedThomClass,
    ProjectiveLineAffine.cohomologyPullback_affine] at h
  exact h.symm

theorem gysin_pointUnit (a : ℂ) (u : ℂˣ) :
    gysin a u (ProjectiveLineFinitePointSupport.pointUnit a) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  change RelativeCochains.forget (second a) 2
    (supportedGysin a u (ProjectiveLineFinitePointSupport.pointUnit a)) = _
  rw [supportedGysin_pointUnit, forget_supportedThomClass]

def gysinIso (a : ℂ) (u : ℂˣ) : PointH0 a ≅ AbsoluteH2 :=
  pointPullbackIso a ≪≫ ComplexPointThom.thomIso.toModuleIso ≪≫
    thomToSupportIso a u ≪≫ forgetIso a

theorem gysinIso_apply (a : ℂ) (u : ℂˣ) (z : PointH0 a) : (gysinIso a u).hom z = gysin a u z := by
  change RelativeCochains.forget (second a) 2
    ((thomToSupportIso a u).hom (ComplexPointThom.thomIso ((pointPullbackIso a).hom z))) = _
  rw [ComplexPointThom.thomIso_apply]
  rfl

theorem point_eq_smul_unit (a : ℂ) (z : PointH0 a) :
    z = ProjectiveLineFinitePointSupport.pointCoordinates a z •
      ProjectiveLineFinitePointSupport.pointUnit a := by
  apply (ProjectiveLineFinitePointSupport.pointCoordinates a).injective
  rw [map_smul, ProjectiveLineFinitePointSupport.pointCoordinates_pointUnit, smul_eq_mul, mul_one]

/-- Every invertible affine complex normal coordinate gives the same absolute Gysin map. -/
theorem gysin_coordinate_independent (a : ℂ) (u v : ℂˣ) : gysin a u = gysin a v := by
  apply LinearMap.ext
  intro z
  rw [point_eq_smul_unit a z, map_smul, map_smul, gysin_pointUnit, gysin_pointUnit]

/-- Faithful original support forgetting upgrades independence to the supported maps themselves. -/
theorem supportedGysin_coordinate_independent (a : ℂ) (u v : ℂˣ) :
    supportedGysin a u = supportedGysin a v := by
  apply LinearMap.ext
  intro z
  apply (ModuleCat.mono_iff_injective (RelativeCochains.forget (second a) 2)).mp inferInstance
  exact LinearMap.congr_fun (gysin_coordinate_independent a u v) z

theorem supportedThomClass_coordinate_independent (a : ℂ) (u v : ℂˣ) :
    supportedThomClass a u = supportedThomClass a v := by
  rw [← supportedGysin_pointUnit a u, ← supportedGysin_pointUnit a v,
    supportedGysin_coordinate_independent a u v]

end HodgeConjecture.ProjectiveLineFinitePointGysin

end
