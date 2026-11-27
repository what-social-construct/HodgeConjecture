module

public import HodgeConjecture.Geometry.ProjectiveLineInfinityChart
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineInfinitySupport
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineReciprocal
public import HodgeConjecture.Realization.Betti.ProjectiveLineFinitePointGysin

@[expose] public section

/-!
# Original relative Thom and Gysin maps at infinity

The original second scheme chart, scaled by a complex unit, defines the actual
normal-coordinate map. Original relative pullback, excision and forgetting
construct supported and absolute Gysin. The native reciprocal map transports
the original zero chart to this chart. Its independently computed positive
H² action fixes the orientation; no cycle map defines the native classes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineInfinityGysin

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite Simplicial
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover

abbrev space : TopCat := TopCat.of Point
abbrev PointH0 := ProjectiveLineInfinitySupport.PointH0
abbrev complement := ProjectiveLineInfinitySupport.complement
abbrev first := SingularSubcomplexes.subsetSingular space reciprocalOpen
abbrev second := SingularSubcomplexes.subsetSingular space complement
abbrev localBoundary := RelativeUnion.localBoundary first second
abbrev SupportedH2 := RelativeCochains.Cohomology second 2
abbrev AbsoluteH2 := ProjectiveLinePointGysin.AbsoluteH2

/-- Literal evaluation of the actual unit-scaled second scheme chart. -/
def normalChartPoint (u : ℂˣ) (z : ℂ) : Point :=
  ⟨ProjectiveLineAffineChart.affineSection ℂ z ≫
    ProjectiveLineInfinityChart.normalChart ℂ u, by
      rw [Category.assoc, ProjectiveLineInfinityChart.normalChart_over_base,
        ProjectiveLineAffineChart.affineSection_over_base]⟩

theorem normalChartPoint_schemeMorphism (u : ℂˣ) (z : ℂ) :
    schemeMorphism (normalChartPoint u z) =
      ProjectiveLineAffineChart.affineSection ℂ z ≫
        ProjectiveLineInfinityChart.normalChart ℂ u := rfl

@[simp]
theorem normalChartPoint_reciprocal (u : ℂˣ) (z : ℂ) :
    normalChartPoint u z = reciprocal ((u : ℂ) * z) := by
  apply ProjectiveLineComplexPoints.ext
  change ProjectiveLineAffineChart.affineSection ℂ z ≫
      ProjectiveLineInfinityChart.normalChart ℂ u = _
  rw [ProjectiveLineInfinityChart.affineSection_normalChart]
  rfl

theorem continuous_normalChartPoint (u : ℂˣ) : Continuous (normalChartPoint u) := by
  have h : normalChartPoint u = reciprocal ∘ ProjectiveLineAffine.complexAffineHomeomorph 0 u := by
    funext z
    simp only [Function.comp_apply, ProjectiveLineAffine.complexAffineHomeomorph_apply,
      normalChartPoint_reciprocal, zero_add]
  rw [h]
  exact continuous_reciprocal.comp (ProjectiveLineAffine.complexAffineHomeomorph 0 u).continuous

def normalChartMap (u : ℂˣ) : TopCat.of ℂ ⟶ space :=
  TopCat.ofHom ⟨normalChartPoint u, continuous_normalChartPoint u⟩

theorem normalChart_center_base (u : ℂˣ) (q : Spec (.of ℂ)) :
    schemeMorphism (normalChartPoint u 0) q = projectiveLineInfinity ℂ := by
  rw [normalChartPoint_reciprocal, mul_zero]
  exact infinity_base q

def normalHomeomorph (u : ℂˣ) : ℂ ≃ₜ reciprocalOpen :=
  (ProjectiveLineAffine.complexAffineHomeomorph 0 u).trans reciprocalHomeomorph

def normalSSetIso (u : ℂˣ) : TopCat.toSSet.obj (TopCat.of ℂ) ≅ first.toSSet :=
  TopCat.toSSet.mapIso
      (TopCat.isoOfHomeo (X := TopCat.of ℂ) (Y := TopCat.of reciprocalOpen) (normalHomeomorph u)) ≪≫
    (SingularSubcomplexes.subsetSingularIso space reciprocalOpen).symm

theorem normalSSetIso_inclusion (u : ℂˣ) :
    (normalSSetIso u).hom ≫ first.ι = TopCat.toSSet.map (normalChartMap u) := by
  change TopCat.toSSet.map
      (TopCat.ofHom (⟨normalHomeomorph u, (normalHomeomorph u).continuous⟩ :
        C(ℂ, reciprocalOpen))) ≫
      SingularSubcomplexes.subtypeToSubset space reciprocalOpen ≫ first.ι = _
  rw [SingularSubcomplexes.subtypeToSubset_ι, ← Functor.map_comp]
  apply congrArg TopCat.toSSet.map
  ext z : 1
  change reciprocal (0 + (u : ℂ) * z) = normalChartPoint u z
  rw [zero_add, normalChartPoint_reciprocal]

theorem punctured_preimage (u : ℂˣ) :
    ComplexPointThom.puncturedSubcomplex = localBoundary.preimage (normalSSetIso u).hom := by
  ext n σ
  change (∀ t, SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t ≠ 0) ↔
    ∀ t, reciprocal (0 + (u : ℂ) * SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) ∈ complement
  simp only [zero_add, ProjectiveLineInfinitySupport.reciprocal_mem_complement_iff]
  constructor
  · intro h t
    exact mul_ne_zero u.ne_zero (h t)
  · intro h t
    exact (mul_ne_zero_iff.mp (h t)).2

def normalPullbackIso (u : ℂˣ) : RelativeCochains.complex localBoundary ≅
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullbackIso (normalSSetIso u) (punctured_preimage u)

def normalClassIso (u : ℂˣ) (n : ℕ) :
    RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n ≅
      RelativeCochains.Cohomology localBoundary n :=
  (homologyMapIso (normalPullbackIso u) n).symm

theorem chartCondition (u : ℂˣ) : ComplexPointThom.puncturedSubcomplex ≤
    second.preimage (TopCat.toSSet.map (normalChartMap u)) := by
  intro n σ hσ t
  change normalChartPoint u (SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) ∈ complement
  rw [normalChartPoint_reciprocal, ProjectiveLineInfinitySupport.reciprocal_mem_complement_iff]
  exact mul_ne_zero u.ne_zero (hσ t)

def chartPullback (u : ℂˣ) : RelativeCochains.complex second ⟶
    RelativeCochains.complex ComplexPointThom.puncturedSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map (normalChartMap u)) (chartCondition u)

theorem chartPullback_eq_original (u : ℂˣ) :
    RelativeExcision.restriction first second ≫ (normalPullbackIso u).hom = chartPullback u := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val (((normalSSetIso u).hom ≫ first.ι).app (op ⦋n⦌) σ) =
    φ.val ((TopCat.toSSet.map (normalChartMap u)).app (op ⦋n⦌) σ)
  rw [normalSSetIso_inclusion]

def excisionIso (n : ℕ) : RelativeCochains.Cohomology second n ≅
    RelativeCochains.Cohomology localBoundary n :=
  RelativeExcision.excisionIso space reciprocalOpen complement isOpen_reciprocalOpen
    ProjectiveLineInfinitySupport.complement_isOpen ProjectiveLineInfinitySupport.cover n

def chartComparison (u : ℂˣ) (n : ℕ) : RelativeCochains.Cohomology second n ≅
    RelativeCochains.Cohomology ComplexPointThom.puncturedSubcomplex n :=
  excisionIso n ≪≫ (normalClassIso u n).symm

theorem chartComparison_hom (u : ℂˣ) (n : ℕ) :
    (chartComparison u n).hom = homologyMap (chartPullback u) n := by
  rw [chartComparison, Iso.trans_hom, excisionIso, RelativeExcision.excisionIso_hom]
  change homologyMap (RelativeExcision.restriction first second) n ≫
    homologyMap (normalPullbackIso u).hom n = _
  rw [← homologyMap_comp, chartPullback_eq_original]

def pointPullbackIso : PointH0 ≅ SingularCochains.Cohomology (TopCat.of ComplexPointThom.Point) 0 :=
  SingularHomotopy.homeomorphIso ProjectiveLineInfinitySupport.pointNormalHomeomorph 0

theorem pointPullbackIso_pointUnit :
    pointPullbackIso.hom ProjectiveLineInfinitySupport.pointUnit = ComplexPointThom.pointUnit :=
  SingularDegreeZeroNaturality.pullback_constantClass _ 1

def thomToSupportIso (u : ℂˣ) : ComplexPointThom.LocalH2 ≅ SupportedH2 :=
  normalClassIso u 2 ≪≫ (excisionIso 2).symm

theorem chartComparison_two_hom (u : ℂˣ) :
    (chartComparison u 2).hom = (thomToSupportIso u).inv := rfl

def supportedThomClass (u : ℂˣ) : SupportedH2 :=
  (thomToSupportIso u).hom ComplexPointThom.thomClass

theorem complementCohomology_isZero (n : ℕ) (hn : n ≠ 0) :
    IsZero ((SubcomplexCochains.complex second.toSSet).homology n) :=
  (SingularContractible.isZero_cohomology complement n hn).of_iso
    (SingularMayerVietoris.chartCohomologyIso space complement n)

instance forget_isIso : IsIso (RelativeCochains.forget second 2) := by
  have : Mono (RelativeCochains.forget second 2) :=
    (RelativeCochains.unionSequence_exact second 1).mono_g
      ((complementCohomology_isZero 1 (by decide)).eq_of_src _ _)
  have : Epi (RelativeCochains.forget second 2) :=
    (RelativeCochains.pairSequence_exact second 2).epi_f
      ((complementCohomology_isZero 2 (by decide)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

def forgetIso : SupportedH2 ≅ AbsoluteH2 := asIso (RelativeCochains.forget second 2)

def supportedGysin (u : ℂˣ) : PointH0 →ₗ[ℚ] SupportedH2 :=
  (thomToSupportIso u).hom.hom.comp
    (ComplexPointThom.localGysin.comp pointPullbackIso.hom.hom)

def gysin (u : ℂˣ) : PointH0 →ₗ[ℚ] AbsoluteH2 :=
  (RelativeCochains.forget second 2).hom.comp (supportedGysin u)

theorem supportedGysin_pointUnit (u : ℂˣ) :
    supportedGysin u ProjectiveLineInfinitySupport.pointUnit = supportedThomClass u := by
  change (thomToSupportIso u).hom
    (ComplexPointThom.localGysin (pointPullbackIso.hom ProjectiveLineInfinitySupport.pointUnit)) = _
  rw [pointPullbackIso_pointUnit, ComplexPointThom.localGysin_pointUnit]
  rfl

/-- Actual native scaling followed by the original reciprocal chart switch. -/
def transportHomeomorph (u : ℂˣ) : Point ≃ₜ Point :=
  (ProjectiveLineAffine.affineHomeomorph 0 u).trans ProjectiveLineReciprocal.reciprocalHomeomorph

def transportMap (u : ℂˣ) : space ⟶ space :=
  TopCat.ofHom ⟨transportHomeomorph u, (transportHomeomorph u).continuous⟩

theorem transportMap_eq (u : ℂˣ) : transportMap u =
    ProjectiveLineAffine.affineMap 0 u ≫ ProjectiveLineReciprocal.reciprocalMap := rfl

theorem transportMap_finite (u : ℂˣ) (z : ℂ) :
    transportMap u (finite z) = reciprocal ((u : ℂ) * z) := by
  change ProjectiveLineReciprocal.reciprocalMap (ProjectiveLineAffine.affineMap 0 u (finite z)) = _
  rw [ProjectiveLineAffine.affineMap_finite, zero_add,
    ProjectiveLineReciprocal.reciprocalMap_finite]

theorem mapsTo_complement (u : ℂˣ) :
    Set.MapsTo (transportMap u) reciprocalOpen complement := by
  intro p hp
  rw [ProjectiveLinePointSupport.reciprocalOpen_eq_puncturedOpen] at hp
  have hzero : transportHomeomorph u (finite 0) = infinity := by
    change transportMap u (finite 0) = infinity
    rw [transportMap_finite, mul_zero]
    rfl
  change transportHomeomorph u p ∈ ProjectiveLineInfinitySupport.complement
  rw [ProjectiveLineInfinitySupport.complement_eq]
  change transportHomeomorph u p ≠ infinity
  rw [← hzero]
  exact (not_congr (transportHomeomorph u).injective.eq_iff).mpr hp

theorem pairCondition (u : ℂˣ) : ProjectiveLinePointGysin.complementSubcomplex ≤
    second.preimage (TopCat.toSSet.map (transportMap u)) :=
  RelativeCochains.subsetCondition (transportMap u) reciprocalOpen complement (mapsTo_complement u)

def relativePullback (u : ℂˣ) : RelativeCochains.complex second ⟶
    RelativeCochains.complex ProjectiveLinePointGysin.complementSubcomplex :=
  RelativeCochains.pullback (TopCat.toSSet.map (transportMap u)) (pairCondition u)

def supportedPull (u : ℂˣ) (n : ℕ) : RelativeCochains.Cohomology second n ⟶
    RelativeCochains.Cohomology ProjectiveLinePointGysin.complementSubcomplex n :=
  homologyMap (relativePullback u) n

theorem transport_normalChart (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.zeroChartMap ≫ transportMap u = normalChartMap u := by
  ext z : 1
  change transportMap u (finite z) = normalChartPoint u z
  rw [transportMap_finite, normalChartPoint_reciprocal]

theorem relativePullback_chart (u : ℂˣ) :
    relativePullback u ≫ ProjectiveLineFinitePointGysin.zeroChartPullback = chartPullback u := by
  have h : TopCat.toSSet.map ProjectiveLineFinitePointGysin.zeroChartMap ≫
      TopCat.toSSet.map (transportMap u) = TopCat.toSSet.map (normalChartMap u) := by
    rw [← Functor.map_comp, transport_normalChart]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  funext σ
  change φ.val ((TopCat.toSSet.map ProjectiveLineFinitePointGysin.zeroChartMap ≫
    TopCat.toSSet.map (transportMap u)).app (op ⦋n⦌) σ) =
    φ.val ((TopCat.toSSet.map (normalChartMap u)).app (op ⦋n⦌) σ)
  rw [h]

theorem supportedPull_chart (u : ℂˣ) (n : ℕ) :
    supportedPull u n ≫ (ProjectiveLineFinitePointGysin.zeroChartComparison n).hom =
      (chartComparison u n).hom := by
  rw [ProjectiveLineFinitePointGysin.zeroChartComparison_hom, chartComparison_hom]
  change homologyMap (relativePullback u) n ≫
    homologyMap ProjectiveLineFinitePointGysin.zeroChartPullback n = _
  rw [← homologyMap_comp, relativePullback_chart]

theorem supportedPull_forget (u : ℂˣ) (n : ℕ) :
    supportedPull u n ≫ RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex n =
      RelativeCochains.forget second n ≫ SingularCochains.cohomologyPullback (transportMap u) n :=
  RelativeCochains.cohomologyPullback_forget _ (pairCondition u) n

theorem supportedPull_thomClass (u : ℂˣ) :
    supportedPull u 2 (supportedThomClass u) = ProjectiveLinePointGysin.supportedThomClass := by
  apply (ModuleCat.mono_iff_injective (ProjectiveLineFinitePointGysin.zeroChartComparison 2).hom).mp
    inferInstance
  have h := congrArg (fun f ↦ f (supportedThomClass u)) (supportedPull_chart u 2)
  change (ProjectiveLineFinitePointGysin.zeroChartComparison 2).hom
      (supportedPull u 2 (supportedThomClass u)) =
    (chartComparison u 2).hom (supportedThomClass u) at h
  rw [chartComparison_two_hom] at h
  have hinv := congrArg (fun f ↦ f ComplexPointThom.thomClass) (thomToSupportIso u).hom_inv_id
  change (thomToSupportIso u).inv ((thomToSupportIso u).hom ComplexPointThom.thomClass) =
    ComplexPointThom.thomClass at hinv
  rw [show (thomToSupportIso u).inv (supportedThomClass u) = ComplexPointThom.thomClass from hinv] at h
  have hz : (ProjectiveLineFinitePointGysin.zeroChartComparison 2).hom
      ProjectiveLinePointGysin.supportedThomClass = ComplexPointThom.thomClass := by
    rw [ProjectiveLineFinitePointGysin.zeroChartComparison_two_hom]
    exact congrArg (fun f ↦ f ComplexPointThom.thomClass) ProjectiveLinePointGysin.thomToSupportIso.hom_inv_id
  exact h.trans hz.symm

/-- Two native orientation signs cancel in reciprocal pullback; affine scaling is homotopic to identity. -/
theorem cohomologyPullback_transport_two (u : ℂˣ) :
    SingularCochains.cohomologyPullback (transportMap u) 2 = 𝟙 _ := by
  rw [transportMap_eq, SingularCochains.cohomologyPullback_comp,
    ProjectiveLineReciprocal.cohomologyPullback_reciprocal_two,
    ProjectiveLineAffine.cohomologyPullback_affine, Category.id_comp]

theorem forget_supportedThomClass (u : ℂˣ) :
    RelativeCochains.forget second 2 (supportedThomClass u) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  have h := congrArg (fun f ↦ f (supportedThomClass u)) (supportedPull_forget u 2)
  change RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2
      (supportedPull u 2 (supportedThomClass u)) =
    SingularCochains.cohomologyPullback (transportMap u) 2
      (RelativeCochains.forget second 2 (supportedThomClass u)) at h
  rw [supportedPull_thomClass, ProjectiveLinePointGysin.forget_supportedThomClass,
    cohomologyPullback_transport_two] at h
  exact h.symm

@[simp]
theorem gysin_pointUnit (u : ℂˣ) :
    gysin u ProjectiveLineInfinitySupport.pointUnit = ProjectiveLineBettiCohomology.coverGenerator := by
  change RelativeCochains.forget second 2 (supportedGysin u ProjectiveLineInfinitySupport.pointUnit) = _
  rw [supportedGysin_pointUnit, forget_supportedThomClass]

def gysinIso (u : ℂˣ) : PointH0 ≅ AbsoluteH2 :=
  pointPullbackIso ≪≫ ComplexPointThom.thomIso.toModuleIso ≪≫ thomToSupportIso u ≪≫ forgetIso

theorem gysinIso_apply (u : ℂˣ) (z : PointH0) : (gysinIso u).hom z = gysin u z := by
  change RelativeCochains.forget second 2
    ((thomToSupportIso u).hom (ComplexPointThom.thomIso (pointPullbackIso.hom z))) = _
  rw [ComplexPointThom.thomIso_apply]
  rfl

theorem point_eq_smul_unit (z : PointH0) :
    z = ProjectiveLineInfinitySupport.pointCoordinates z • ProjectiveLineInfinitySupport.pointUnit := by
  apply ProjectiveLineInfinitySupport.pointCoordinates.injective
  rw [map_smul, ProjectiveLineInfinitySupport.pointCoordinates_pointUnit, smul_eq_mul, mul_one]

theorem gysin_coordinate_independent (u v : ℂˣ) : gysin u = gysin v := by
  apply LinearMap.ext
  intro z
  rw [point_eq_smul_unit z, map_smul, map_smul, gysin_pointUnit, gysin_pointUnit]

theorem supportedGysin_coordinate_independent (u v : ℂˣ) : supportedGysin u = supportedGysin v := by
  apply LinearMap.ext
  intro z
  apply (ModuleCat.mono_iff_injective (RelativeCochains.forget second 2)).mp inferInstance
  exact LinearMap.congr_fun (gysin_coordinate_independent u v) z

theorem supportedThomClass_coordinate_independent (u v : ℂˣ) :
    supportedThomClass u = supportedThomClass v := by
  rw [← supportedGysin_pointUnit u, ← supportedGysin_pointUnit v,
    supportedGysin_coordinate_independent u v]

/-- The same original singleton H⁰, for any actual complex-valued point. -/
abbrev PointH0At (p : Point) :=
  SingularCochains.Cohomology (TopCat.of ↥({p} : Set Point)) 0

def pointUnitAt (p : Point) : PointH0At p :=
  SingularDegreeZeroNaturality.constantClass ↥({p} : Set Point) 1

/-- The actual two-chart point dichotomy supplies an original geometric Gysin
isomorphism at every complex-valued point. The witnesses are the finite and
reciprocal Thom/excision constructions, with their original positive unit. -/
theorem every_point_gysinIso (p : Point) (u : ℂˣ) :
    ∃ e : PointH0At p ≅ AbsoluteH2,
      e.hom (pointUnitAt p) = ProjectiveLineBettiCohomology.coverGenerator := by
  rcases finite_or_infinity p with ⟨a, rfl⟩ | rfl
  · change ∃ e : ProjectiveLineFinitePointGysin.PointH0 a ≅ AbsoluteH2,
      e.hom (ProjectiveLineFinitePointSupport.pointUnit a) = _
    refine ⟨ProjectiveLineFinitePointGysin.gysinIso a u, ?_⟩
    exact (ProjectiveLineFinitePointGysin.gysinIso_apply a u
      (ProjectiveLineFinitePointSupport.pointUnit a)).trans
        (ProjectiveLineFinitePointGysin.gysin_pointUnit a u)
  · change ∃ e : PointH0 ≅ AbsoluteH2, e.hom ProjectiveLineInfinitySupport.pointUnit = _
    refine ⟨gysinIso u, ?_⟩
    exact (gysinIso_apply u ProjectiveLineInfinitySupport.pointUnit).trans (gysin_pointUnit u)

/-- Each actual point admits a family of original geometric maps independent
of the nonzero scale in its selected finite or reciprocal normal chart. -/
theorem every_point_scale_independent (p : Point) :
    ∃ g : ℂˣ → (PointH0At p →ₗ[ℚ] AbsoluteH2),
      (∀ u, g u (pointUnitAt p) = ProjectiveLineBettiCohomology.coverGenerator) ∧
      (∀ u v, g u = g v) := by
  rcases finite_or_infinity p with ⟨a, rfl⟩ | rfl
  · exact ⟨ProjectiveLineFinitePointGysin.gysin a,
      ProjectiveLineFinitePointGysin.gysin_pointUnit a,
      ProjectiveLineFinitePointGysin.gysin_coordinate_independent a⟩
  · exact ⟨gysin, gysin_pointUnit, gysin_coordinate_independent⟩

end HodgeConjecture.ProjectiveLineInfinityGysin

end
