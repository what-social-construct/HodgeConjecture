-- Legacy imports expose checked private proof bodies for the dependency gates.
import HodgeConjecture.Realization.DeRham.ProjectiveLineFinitePointComparison
import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
import HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
import HodgeConjecture.MathlibCompat.DeclarationDependencies
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Finite-point Gysin controls retain the actual scheme normal chart,
original relative maps, positive complex orientation and original ordinary
point classes. Old fixtures are available but excluded from the audited
new proof closures. Global square rank is distinguished from local length. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFinitePointGysinVerification

open AlgebraicGeometry CategoryTheory HomologicalComplex Opposite Simplicial SchemeCycles
open ProjectiveLineComplexPoints ProjectiveLineAnalyticCover ProjectiveLineBettiCohomology
open ProjectiveLineFinitePointComparison

abbrev sampleCenter : ℂ := 1 + Complex.I

def negativeUnit : ℂˣ := Units.mk0 (-1 : ℂ) (by norm_num)
def imaginaryUnit : ℂˣ := Units.mk0 Complex.I (by norm_num)

private theorem class_coordinate (a : ℂ) : h2Equiv (model.cycleClass (pointClass a)) = 1 := by
  rw [pointClass_cycleClass, h2Equiv_coverGenerator]

theorem unchanged_model_basis_source_and_original_maps :
    model = ProjectiveLineCoverageCertificate.model ∧
    basis = ProjectiveLineCoverageCertificate.basis ∧
    CoverChow = RationalChowGroup
      (DimensionFunction.ofLocallyOfFiniteType ℂ (projectiveLine ℂ)
        (cover ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)))) 0 ∧
    actualPull = rationalChowFiniteFlatPullback ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 ∧
    actualPush = rationalChowFinitePushforward ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem actual_affine_scheme_iso_keeps_original_chart_range
    (a : ℂ) (u : ℂˣ) (z : ℂ) :
    IsIso (ProjectiveLineAffineChart.affineIso ℂ a u).hom ∧
    (ProjectiveLineAffineChart.normalChart ℂ a u).opensRange =
      (projectiveLineXChart ℂ).opensRange ∧
    ProjectiveLineAffineChart.affineSection ℂ z ≫
        ProjectiveLineAffineChart.normalChart ℂ a u =
      ProjectiveLineAffineChart.finiteSection ℂ (a + (u : ℂ) * z) :=
  ⟨inferInstance, ProjectiveLineAffineChart.normalChart_opensRange ℂ a u,
    ProjectiveLineAffineChart.affineSection_normalChart ℂ a z u⟩

theorem native_chart_is_the_same_actual_scheme_section
    (a : ℂ) (u : ℂˣ) (z : ℂ) :
    schemeMorphism (ProjectiveLineFinitePointGysin.normalChartPoint a u z) =
        ProjectiveLineAffineChart.affineSection ℂ z ≫
          ProjectiveLineAffineChart.normalChart ℂ a u ∧
    ProjectiveLineFinitePointGysin.normalChartPoint a u z = finite (a + (u : ℂ) * z) ∧
    schemeMorphism (ProjectiveLineFinitePointGysin.normalChartPoint a u 0)
        (default : Spec (.of ℂ)) = ProjectiveLineAffineChart.center ℂ a :=
  ⟨rfl, ProjectiveLineFinitePointGysin.normalChartPoint_finite a u z,
    ProjectiveLineFinitePointGysin.normalChart_center_base a u _⟩

theorem nontrivial_negative_and_imaginary_chart_samples :
    ProjectiveLineFinitePointGysin.normalChartPoint sampleCenter negativeUnit 1 = finite Complex.I ∧
    ProjectiveLineFinitePointGysin.normalChartPoint sampleCenter imaginaryUnit 1 =
      finite (1 + 2 * Complex.I) ∧
    ProjectiveLineAffine.affineMap sampleCenter imaginaryUnit infinity = infinity := by
  refine ⟨?_, ?_, ProjectiveLineAffine.affineMap_infinity _ _⟩
  · rw [ProjectiveLineFinitePointGysin.normalChartPoint_finite]
    congr 1
    norm_num [sampleCenter, negativeUnit] <;> ring
  · rw [ProjectiveLineFinitePointGysin.normalChartPoint_finite]
    congr 1
    norm_num [sampleCenter, imaginaryUnit] <;> ring

theorem actual_affine_homotopy_keeps_finite_endpoints_and_infinity
    (a : ℂ) (u : ℂˣ) (t : unitInterval) (z : ℂ) :
    ProjectiveLineAffine.affineHomotopy a u (0, finite z) = finite z ∧
    ProjectiveLineAffine.affineHomotopy a u (1, finite z) = finite (a + (u : ℂ) * z) ∧
    ProjectiveLineAffine.affineHomotopy a u (t, infinity) = infinity := by
  constructor
  · exact (ProjectiveLineAffine.affineHomotopy a u).map_zero_left (finite z)
  constructor
  · have h := (ProjectiveLineAffine.affineHomotopy a u).map_one_left (finite z)
    simpa only [ProjectiveLineAffine.affineContinuousMap,
      ProjectiveLineAffine.affineHomeomorph_finite] using h
  · exact ProjectiveLineAffine.affineHomotopyFun_infinity a u t

theorem rotated_affine_samples_act_identically_in_every_native_degree
    (n : ℕ) (z : SingularCochains.Cohomology ProjectiveLineAffine.space n) :
    SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap sampleCenter negativeUnit) n z = z ∧
    SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap sampleCenter imaginaryUnit) n z = z :=
  ⟨ProjectiveLineAffine.cohomologyPullback_affine_apply _ _ _ _,
    ProjectiveLineAffine.cohomologyPullback_affine_apply _ _ _ _⟩

theorem actual_complement_and_normal_point_maps_agree
    (a : ℂ) (u : ℂˣ) (x : ComplexPointThom.Point) :
    ProjectiveLineAffine.affineMap a u ⁻¹' ProjectiveLineFinitePointSupport.complement a =
      reciprocalOpen ∧
    (ProjectiveLineFinitePointSupport.pointNormalHomeomorph a x : Point) =
      ProjectiveLineFinitePointGysin.normalChartPoint a u x.val := by
  refine ⟨ProjectiveLineFinitePointSupport.preimage_complement a u, ?_⟩
  rw [ProjectiveLineFinitePointSupport.pointNormalHomeomorph_coe,
    ProjectiveLineFinitePointGysin.normalChartPoint_finite,
    Set.mem_singleton_iff.mp x.property, mul_zero, add_zero]

theorem actual_singleton_unit_and_scheme_image_are_retained (a : ℂ) :
    ContractibleSpace ↥(ProjectiveLineFinitePointSupport.complement a) ∧
    ProjectiveLineFinitePointSupport.pointCoordinates a
        (ProjectiveLineFinitePointSupport.pointUnit a) = 1 ∧
    schemeMorphism (ProjectiveLineFinitePointSupport.point a).val
        (default : Spec (.of ℂ)) = ProjectiveLineAffineChart.center ℂ a :=
  ⟨inferInstance, ProjectiveLineFinitePointSupport.pointCoordinates_pointUnit a,
    ProjectiveLineFinitePointGysin.pointSupport_scheme_base a _ _⟩

theorem original_relative_chart_excision_and_forget_maps_are_retained
    (a : ℂ) (u : ℂˣ) :
    RelativeExcision.restriction ProjectiveLineFinitePointGysin.first
        (ProjectiveLineFinitePointGysin.second a) ≫
        (ProjectiveLineFinitePointGysin.normalPullbackIso a u).hom =
      ProjectiveLineFinitePointGysin.chartPullback a u ∧
    (ProjectiveLineFinitePointGysin.chartComparison a u 2).hom =
      homologyMap (ProjectiveLineFinitePointGysin.chartPullback a u) 2 ∧
    ProjectiveLineFinitePointGysin.affineSupportedPull a u 2 ≫
        RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2 =
      RelativeCochains.forget (ProjectiveLineFinitePointGysin.second a) 2 ≫
        SingularCochains.cohomologyPullback (ProjectiveLineAffine.affineMap a u) 2 :=
  ⟨ProjectiveLineFinitePointGysin.chartPullback_eq_original a u,
    ProjectiveLineFinitePointGysin.chartComparison_hom a u 2,
    ProjectiveLineFinitePointGysin.affineSupportedPull_forget a u 2⟩

theorem actual_gysin_iso_has_positive_original_unit (a : ℂ) (u : ℂˣ) :
    (ProjectiveLineFinitePointGysin.gysinIso a u).hom
        (ProjectiveLineFinitePointSupport.pointUnit a) = coverGenerator ∧
    RelativeCochains.forget (ProjectiveLineFinitePointGysin.second a) 2
        (ProjectiveLineFinitePointGysin.supportedThomClass a u) = coverGenerator ∧
    ProjectiveLineFinitePointGysin.supportedGysin a u
        (ProjectiveLineFinitePointSupport.pointUnit a) =
      ProjectiveLineFinitePointGysin.supportedThomClass a u := by
  refine ⟨?_, ProjectiveLineFinitePointGysin.forget_supportedThomClass a u,
    ProjectiveLineFinitePointGysin.supportedGysin_pointUnit a u⟩
  rw [ProjectiveLineFinitePointGysin.gysinIso_apply, ProjectiveLineFinitePointGysin.gysin_pointUnit]

theorem complex_negative_and_imaginary_units_preserve_positive_orientation :
    ProjectiveLineFinitePointGysin.supportedGysin sampleCenter negativeUnit =
      ProjectiveLineFinitePointGysin.supportedGysin sampleCenter imaginaryUnit ∧
    ProjectiveLineFinitePointGysin.gysin sampleCenter imaginaryUnit =
      ProjectiveLineFinitePointGysin.gysin sampleCenter 1 ∧
    h2Equiv (ProjectiveLineFinitePointGysin.gysin sampleCenter negativeUnit
      (ProjectiveLineFinitePointSupport.pointUnit sampleCenter)) = 1 := by
  refine ⟨ProjectiveLineFinitePointGysin.supportedGysin_coordinate_independent _ _ _,
    ProjectiveLineFinitePointGysin.gysin_coordinate_independent _ _ _, ?_⟩
  rw [ProjectiveLineFinitePointGysin.gysin_pointUnit, h2Equiv_coverGenerator]

theorem zero_coefficient_is_not_an_invertible_normal_coordinate :
    (¬ ∃ u : ℂˣ, (u : ℂ) = 0) ∧
    ¬ Function.Injective (fun z : ℂ ↦ sampleCenter + (0 : ℂ) * z) := by
  constructor
  · rintro ⟨u, hu⟩
    exact u.ne_zero hu
  · intro h
    have hzero : (0 : ℂ) = 1 := h (by simp)
    norm_num at hzero

theorem original_support_image_and_ordinary_point_class_are_the_same (a : ℂ) :
    schemePoint a = ProjectiveLineAffineChart.center ℂ a ∧
    pointClass a = ProjectiveLineFinitePointChow.pointClass ℂ a ∧
    ProjectiveLineCycles.rationalChowDegree ℂ (pointClass a) = 1 ∧
    pointClass a ≠ 0 := by
  refine ⟨schemePoint_eq_center a, pointClass_eq_original a, ?_, pointClass_ne_zero a⟩
  rw [pointClass_eq_original]
  exact ProjectiveLineFinitePointChow.pointClass_degree ℂ a

theorem original_point_cycle_has_the_same_geometric_gysin_unit (a : ℂ) (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin a u (ProjectiveLineFinitePointSupport.pointUnit a) =
      model.cycleClass (pointClass a) ∧
    h2Equiv (model.cycleClass (pointClass a)) = 1 :=
  ⟨gysin_pointUnit_eq_cycleClass a u, class_coordinate a⟩

theorem negative_point_unit_does_not_have_positive_normalization (a : ℂ) (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin a u (ProjectiveLineFinitePointSupport.pointUnit a) ≠ 0 ∧
    ProjectiveLineFinitePointGysin.gysin a u (-ProjectiveLineFinitePointSupport.pointUnit a) ≠
      coverGenerator := by
  constructor
  · intro h
    have hc := congrArg h2Equiv h
    rw [ProjectiveLineFinitePointGysin.gysin_pointUnit, h2Equiv_coverGenerator, map_zero] at hc
    norm_num at hc
  · intro h
    have hc := congrArg h2Equiv h
    rw [map_neg, ProjectiveLineFinitePointGysin.gysin_pointUnit,
      map_neg, h2Equiv_coverGenerator] at hc
    norm_num at hc

theorem transfer_degree_is_actual_global_rank_at_the_selected_target (a : ℂ) :
    (transfer a).degree = cover.finrank (schemePoint a) ∧
    (transfer a).degree = 2 ∧
    ∀ x : scheme, (transfer a).degree = cover.finrank x :=
  ⟨rfl, degree_eq_two a, degree_eq_geometric_rank a⟩

theorem every_finite_point_has_the_same_full_target_certificate (a : ℂ) :
    FiniteCoverageCertificate.check (certificate a) = true ∧
    (certificate a).cycles () = ProjectiveLineFinitePointChow.pointClass ℂ a ∧
    RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model :=
  ⟨accepted a, normalized_cycles a (), model_satisfies_from_finite_point a⟩

theorem nonzero_center_sample_keeps_its_actual_point_and_original_class :
    (ProjectiveLineFinitePointSupport.point sampleCenter).val = finite sampleCenter ∧
    (ProjectiveLineFinitePointSupport.point sampleCenter).val ≠ finite 0 ∧
    (certificate sampleCenter).cycles () =
      ProjectiveLineFinitePointChow.pointClass ℂ sampleCenter := by
  refine ⟨rfl, ?_, normalized_cycles sampleCenter ()⟩
  intro h
  have hc := finite_injective h
  have hr := congrArg Complex.re hc
  norm_num [sampleCenter] at hr

theorem unnormalized_push_fails_the_original_full_target_column (a : ℂ) :
    model.cycleClass (actualPush (upstairsCycles a ())) ≠
      (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : Betti) := by
  intro h
  have hc := congrArg h2Equiv h
  change h2Equiv (model.cycleClass (actualPush (actualPull (pointClass a)))) = _ at hc
  rw [geometric_chow_push_pull a, map_smul, map_smul, class_coordinate,
    degree_eq_two, target_column, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem degree_one_is_false_and_normalization_recovers_same_point (a : ℂ) :
    (¬ ∀ z : Betti, (transfer a).push ((transfer a).pull z) = (1 : ℚ) • z) ∧
    (((transfer a).degree : ℚ)⁻¹ • actualPush (actualPull (pointClass a)) = pointClass a) := by
  constructor
  · intro h
    have htwo : (transfer a).push ((transfer a).pull (model.cycleClass (pointClass a))) =
        ((transfer a).degree : ℚ) • model.cycleClass (pointClass a) := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] using
        LinearMap.congr_fun (transfer a).push_comp_pull (model.cycleClass (pointClass a))
    have hc := congrArg h2Equiv (h (model.cycleClass (pointClass a)))
    rw [htwo, one_smul, map_smul, class_coordinate, degree_eq_two] at hc
    norm_num at hc
  · rw [geometric_chow_push_pull a, smul_smul, degree_eq_two]
    norm_num

theorem zero_center_gysin_unit_agrees_with_original_zero_construction (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin 0 u (ProjectiveLineFinitePointSupport.pointUnit 0) =
      ProjectiveLinePointGysin.gysin ProjectiveLinePointSupport.pointUnit := by
  rw [ProjectiveLineFinitePointGysin.gysin_pointUnit, ProjectiveLinePointGysin.gysin_pointUnit]

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.OnePointHomotopy.continuous_map_family_of_leftInverse,
    `HodgeConjecture.OnePointHomotopy.continuous_onePointCongr_family,
    `HodgeConjecture.ProjectiveLineAffineChart.coordinateEquiv,
    `HodgeConjecture.ProjectiveLineAffineChart.coordinateEquiv_X,
    `HodgeConjecture.ProjectiveLineAffineChart.affineIso_hom,
    `HodgeConjecture.ProjectiveLineAffineChart.normalChart_opensRange,
    `HodgeConjecture.ProjectiveLineAffineChart.affineSection_normalChart,
    `HodgeConjecture.ProjectiveLineAffineChart.affineCenter_asIdeal,
    `HodgeConjecture.ProjectiveLineAffineChart.center_isClosed,
    `HodgeConjecture.ProjectiveLineAffineChart.center_ne_genericPoint,
    `HodgeConjecture.ProjectiveLineAffine.coefficient_ne_zero,
    `HodgeConjecture.ProjectiveLineAffine.inverseFamily_affineFamily,
    `HodgeConjecture.ProjectiveLineAffine.affineHomotopy,
    `HodgeConjecture.ProjectiveLineAffine.affineHomotopyFun_infinity,
    `HodgeConjecture.ProjectiveLineAffine.cohomologyPullback_affine,
    `HodgeConjecture.ProjectiveLineAffine.affineMap_finite,
    `HodgeConjecture.ProjectiveLineFinitePointSupport.preimage_complement,
    `HodgeConjecture.ProjectiveLineFinitePointSupport.complementContractibleSpace,
    `HodgeConjecture.ProjectiveLineFinitePointSupport.pointNormalHomeomorph,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.normalChartPoint_finite,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.pointSupport_scheme_base,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.normalSSetIso_inclusion,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.chartPullback_eq_original,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.chartComparison_hom,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.thomToSupportIso,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.forget_isIso,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.affineSupportedPull_thomClass,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.forget_supportedThomClass,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysinIso_apply,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_coordinate_independent,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.supportedGysin_coordinate_independent,
    `HodgeConjecture.ProjectiveLineFinitePointChow.pointRepresentative_val,
    `HodgeConjecture.ProjectiveLineFinitePointChow.pointClass_degree,
    `HodgeConjecture.ProjectiveLineFinitePointChow.pointClass_ne_zero,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.schemePoint_eq_center,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.pointClass_eq_original,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.gysin_pointUnit_eq_cycleClass,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.pointClass_cycleClass,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.transfer,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.degree_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.pull_comparison,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.push_comparison,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.upstairs_columns,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.normalized_cycles,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.accepted,
    `HodgeConjecture.ProjectiveLineFinitePointComparison.model_satisfies_from_finite_point,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.unchanged_model_basis_source_and_original_maps,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_affine_scheme_iso_keeps_original_chart_range,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.native_chart_is_the_same_actual_scheme_section,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.nontrivial_negative_and_imaginary_chart_samples,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_affine_homotopy_keeps_finite_endpoints_and_infinity,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.rotated_affine_samples_act_identically_in_every_native_degree,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_complement_and_normal_point_maps_agree,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_singleton_unit_and_scheme_image_are_retained,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.original_relative_chart_excision_and_forget_maps_are_retained,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.actual_gysin_iso_has_positive_original_unit,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.complex_negative_and_imaginary_units_preserve_positive_orientation,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.zero_coefficient_is_not_an_invertible_normal_coordinate,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.original_support_image_and_ordinary_point_class_are_the_same,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.original_point_cycle_has_the_same_geometric_gysin_unit,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.negative_point_unit_does_not_have_positive_normalization,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.transfer_degree_is_actual_global_rank_at_the_selected_target,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.every_finite_point_has_the_same_full_target_certificate,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.nonzero_center_sample_keeps_its_actual_point_and_original_class,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.unnormalized_push_fails_the_original_full_target_column,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.degree_one_is_false_and_normalization_recovers_same_point,
    `HodgeConjecture.ProjectiveLineFinitePointGysinVerification.zero_center_gysin_unit_agrees_with_original_zero_construction]
  unless declarations.length = 68 do
    throwError "Expected exactly 68 finite-point Gysin audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing finite-point Gysin audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbiddenCoreModules := [
    `HodgeConjecture.Geometry.ProjectiveLineSquare,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquarePullback,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin,
    `HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification,
    `HodgeConjecture.Realization.Betti.Examples.ComplexSquareThom,
    `HodgeConjecture.Realization.Betti.Examples.CircleSquare]
  let coreEndpoints := [
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.supportedGysin_coordinate_independent]
  unless forbiddenCoreModules.length = 6 ∧ coreEndpoints.length = 2 do
    throwError "Expected six forbidden core origins and two native Gysin endpoints"
  for endpoint in coreEndpoints do
    unless env.contains endpoint do
      throwError "Missing finite-point core endpoint {endpoint}"
    let closure := HodgeConjecture.Research.declarationDependencies env endpoint
    let forbiddenUses := closure.toList.filter fun name ↦
      match env.getModuleIdxFor? name with
      | some idx =>
          let origin := env.header.moduleNames[idx]!
          forbiddenCoreModules.contains origin ||
            (`HodgeConjecture.Realization.Chow).isPrefixOf origin ||
            (`HodgeConjecture.Realization.DeRham).isPrefixOf origin
      | none => false
    unless forbiddenUses.isEmpty do
      throwError "Old square/ramification or realization layer entered native core {endpoint}: {forbiddenUses}"
    logInfo m!"PASS independent affine finite-point Gysin core: {endpoint}"
  let forbiddenOldResults := [
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square_eq,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonical_cohomologyPullback_square]
  let forbiddenFinalModules := [
    `HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage,
    `HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison]
  unless forbiddenOldResults.length = 3 ∧ forbiddenFinalModules.length = 2 do
    throwError "Expected three old global results and both old fixture origins"
  for name in forbiddenOldResults ++
      [`HodgeConjecture.ProjectiveLineSquareCoverage.model_satisfies_from_square_cover,
       `HodgeConjecture.ProjectiveLineRamificationComparison.model_satisfies_from_ramification] do
    unless env.contains name do
      throwError "Missing old-result witness for finite-point dependency guard {name}"
  let finalEndpoint :=
    `HodgeConjecture.ProjectiveLineFinitePointComparison.model_satisfies_from_finite_point
  unless env.contains finalEndpoint do
    throwError "Missing finite-point family endpoint {finalEndpoint}"
  let finalClosure := HodgeConjecture.Research.declarationDependencies env finalEndpoint
  for name in forbiddenOldResults do
    if finalClosure.contains name then
      throwError "Old absolute square proof {name} entered finite-point endpoint"
  let oldFixtureUses := finalClosure.toList.filter fun name ↦
    match env.getModuleIdxFor? name with
    | some idx => forbiddenFinalModules.contains env.header.moduleNames[idx]!
    | none => false
  unless oldFixtureUses.isEmpty do
    throwError "Old fixture declarations entered finite-point family: {oldFixtureUses}"
  logInfo m!"PASS independent finite-point family endpoint: {finalEndpoint}"
  let required := [
    `HodgeConjecture.ProjectiveLineFinitePointGysin.pointSupport_scheme_base,
    `HodgeConjecture.ProjectiveLineAffineChart.affineSection_normalChart,
    `HodgeConjecture.OnePointHomotopy.continuous_map_family_of_leftInverse,
    `HodgeConjecture.ProjectiveLineAffine.affineHomotopy,
    `HodgeConjecture.ProjectiveLineAffine.cohomologyPullback_affine,
    `HodgeConjecture.ProjectiveLineFinitePointGysin.gysin_pointUnit,
    `HodgeConjecture.ProjectiveLineSquare.square_finrank]
  unless required.length = 7 do
    throwError "Expected seven actual support/chart/homotopy/Gysin/global-rank dependencies"
  for name in required do
    unless env.contains name do
      throwError "Missing finite-point required dependency {name}"
    unless finalClosure.contains name do
      throwError "Required actual finite-point dependency {name} missing from {finalEndpoint}"
    logInfo m!"PASS required finite-point dependency: {name}"

end HodgeConjecture.ProjectiveLineFinitePointGysinVerification

end
