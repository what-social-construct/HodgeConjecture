-- Legacy imports retain private checked proof bodies for the dependency gates below.
import HodgeConjecture.Realization.DeRham.ProjectiveLineRamificationComparison
import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
import HodgeConjecture.MathlibCompat.DeclarationDependencies
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-! Focused controls for ramification-weighted original point-Gysin pullback.
The final dependency gates inspect checked declaration bodies, not imports.
The old global-square result is deliberately available, then excluded from
all three new proof closures. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineRamificationVerification

open AlgebraicGeometry CategoryTheory HomologicalComplex Opposite Simplicial SchemeCycles
open ProjectiveLineRamificationComparison ProjectiveLineBettiCohomology

abbrev localThom := ComplexPointThom.thomClass
abbrev supportedThom := ProjectiveLinePointGysin.supportedThomClass
abbrev pointUnit := ProjectiveLinePointSupport.pointUnit

def supportedCoordinates : ProjectiveLineSquareRamification.SupportedH2 →ₗ[ℚ] ℚ :=
  ComplexPointThom.coordinates.toLinearMap.comp
    (ProjectiveLineSquareRamification.chartComparison 2).hom.hom

private theorem supported_coordinate : supportedCoordinates supportedThom = 1 := by
  change ComplexPointThom.coordinates
    ((ProjectiveLineSquareRamification.chartComparison 2).hom supportedThom) = 1
  rw [ProjectiveLineSquareRamification.chartComparison_two_hom]
  change ComplexPointThom.coordinates
    (ProjectiveLinePointGysin.thomToSupportIso.inv
      (ProjectiveLinePointGysin.thomToSupportIso.hom localThom)) = 1
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id]
  exact ComplexPointThom.coordinates_thomClass

private theorem zero_coordinate : h2Equiv (model.cycleClass zeroClass) = 1 := by
  rw [zeroClass_cycleClass, h2Equiv_coverGenerator]

theorem unchanged_target_source_and_original_maps :
    model = ProjectiveLineCoverageCertificate.model ∧
    basis = ProjectiveLineCoverageCertificate.basis ∧
    CoverChow = RationalChowGroup
      (DimensionFunction.ofLocallyOfFiniteType ℂ (projectiveLine ℂ)
        (cover ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)))) 0 ∧
    actualPull = rationalChowFiniteFlatPullback ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 ∧
    actualPush = rationalChowFinitePushforward ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem relative_pair_pull_is_original_simplex_precomposition
    (n : ℕ) (φ : RelativeCochains.Cochain ComplexPointThom.puncturedSubcomplex n)
    (σ : (TopCat.toSSet.obj ComplexPointThom.space).obj (op ⦋n⦌)) :
    ((ComplexSquareThom.localRelativePullback.f n) φ).val σ =
      φ.val ((TopCat.toSSet.map ComplexSquareThom.squareMap).app (op ⦋n⦌) σ) ∧
    ComplexSquareThom.puncturedSquareMap ≫
        SingularSubcomplexes.subsetInclusion ComplexPointThom.space ComplexPointThom.punctured =
      SingularSubcomplexes.subsetInclusion ComplexPointThom.space ComplexPointThom.punctured ≫
        ComplexSquareThom.squareMap := ⟨rfl, ComplexSquareThom.puncturedSquareMap_inclusion⟩

theorem local_point_identity_has_ramified_thom_coefficient_two :
    ComplexSquareThom.pointPull ComplexPointThom.pointUnit = ComplexPointThom.pointUnit ∧
    ComplexPointThom.coordinates
      (ComplexSquareThom.localPull 2 (ComplexPointThom.localGysin ComplexPointThom.pointUnit)) = 2 := by
  refine ⟨ComplexSquareThom.pointPull_pointUnit, ?_⟩
  rw [ComplexPointThom.localGysin_pointUnit, ComplexSquareThom.localPull_thomClass,
    map_smul, ComplexPointThom.coordinates_thomClass, smul_eq_mul, mul_one]

theorem local_ramification_is_nontrivial_and_cannot_annihilate_thom :
    ComplexSquareThom.localPull 2 localThom ≠ localThom ∧
      ComplexSquareThom.localPull 2 localThom ≠ 0 := by
  constructor
  · intro h
    have hc := congrArg ComplexPointThom.coordinates h
    rw [ComplexSquareThom.localPull_thomClass, map_smul,
      ComplexPointThom.coordinates_thomClass] at hc
    norm_num at hc
  · intro h
    have hc := congrArg ComplexPointThom.coordinates h
    rw [ComplexSquareThom.localPull_thomClass, map_smul,
      ComplexPointThom.coordinates_thomClass, map_zero] at hc
    norm_num at hc

theorem reversed_local_orientation_fails_positive_normalization :
    ComplexPointThom.boundaryPairing (-localThom) = -1 ∧
      ComplexPointThom.boundaryPairing (-localThom) ≠ 1 := by
  rw [map_neg, ComplexPointThom.boundaryPairing_thomClass]
  norm_num

theorem original_chart_excision_and_forget_maps_are_retained :
    RelativeExcision.restriction ProjectiveLineNormalChart.first ProjectiveLineNormalChart.second ≫
        ProjectiveLineNormalChart.normalPullbackIso.hom =
      ProjectiveLineSquareRamification.chartPullback ∧
    ProjectiveLineSquareRamification.supportedPull 2 ≫
        RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2 =
      RelativeCochains.forget ProjectiveLinePointGysin.complementSubcomplex 2 ≫
        SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2 :=
  ⟨ProjectiveLineSquareRamification.chartPullback_eq_original,
    ProjectiveLineSquareRamification.supportedPull_forget 2⟩

theorem supported_thom_uses_the_actual_normal_chart_and_local_coefficient :
    supportedCoordinates supportedThom = 1 ∧
    supportedCoordinates (ProjectiveLineSquareRamification.supportedPull 2 supportedThom) = 2 := by
  refine ⟨supported_coordinate, ?_⟩
  rw [ProjectiveLineSquareRamification.supportedPull_square,
    map_smul, supported_coordinate, smul_eq_mul, mul_one]

theorem global_point_identity_has_ramified_supported_gysin_coefficient :
    ProjectiveLineSquareRamification.pointPull pointUnit = pointUnit ∧
    supportedCoordinates
        (ProjectiveLineSquareRamification.supportedPull 2
          (ProjectiveLinePointGysin.supportedGysin pointUnit)) = 2 := by
  constructor
  · rw [ProjectiveLineSquareRamification.pointPull_eq_id]
    rfl
  · rw [ProjectiveLinePointGysin.supportedGysin_pointUnit]
    exact supported_thom_uses_the_actual_normal_chart_and_local_coefficient.2

theorem unweighted_absolute_gysin_pullback_is_false :
    SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2
        (ProjectiveLinePointGysin.gysin pointUnit) ≠
      ProjectiveLinePointGysin.gysin (ProjectiveLineSquareRamification.pointPull pointUnit) := by
  intro h
  rw [ProjectiveLineSquareRamification.gysin_pullback,
    ProjectiveLineSquareRamification.pointPull_eq_id, LinearMap.id_apply] at h
  have hc := congrArg h2Equiv h
  rw [map_smul, ProjectiveLinePointGysin.gysin_pointUnit, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem actual_local_length_is_the_geometric_cover_rank :
    ramificationIndex = 2 ∧
      ramificationIndex = finiteFiberMultiplicity cover (projectiveLineZero ℂ) ∧
      ∀ x : scheme, ramificationIndex = cover.finrank x :=
  ⟨ramificationIndex_eq_two, rfl, ramificationIndex_eq_geometric_rank⟩

theorem actual_raw_zero_pull_has_weight_two_and_no_infinity_component :
    finiteFiberPullback cover ℚ
        (fundamentalCycle ℚ (pointSupport scheme (projectiveLineZero ℂ)))
        (pointSupport scheme (projectiveLineZero ℂ)) = 2 ∧
    finiteFiberPullback cover ℚ
        (fundamentalCycle ℚ (pointSupport scheme (projectiveLineZero ℂ)))
        (pointSupport scheme (projectiveLineInfinity ℂ)) = 0 := by
  have hne : pointSupport scheme (projectiveLineZero ℂ) ≠
      pointSupport scheme (projectiveLineInfinity ℂ) := by
    intro h
    exact projectiveLineZero_ne_projectiveLineInfinity ℂ
      ((pointEquivIntegralClosedSubscheme scheme).injective h)
  rw [ProjectiveLineSquareRamifiedChow.finiteFiberPullback_zero_eq_two]
  simp [fundamentalCycle, hne]

theorem original_zero_chow_class_is_retained_with_its_actual_weight :
    zeroClass = ProjectiveLineGysinCycleClass.rationalZeroClass ∧
    sourceComparison (actualPull zeroClass) = (ramificationIndex : ℚ) • zeroClass ∧
    zeroClass ≠ 0 :=
  ⟨zeroClass_eq_original, actual_zero_pull, ProjectiveLineSquareRamifiedChow.zeroClass_ne_zero⟩

theorem original_zero_cycle_has_the_same_positive_gysin_unit :
    model.cycleClass zeroClass = ProjectiveLinePointGysin.gysin pointUnit ∧
      h2Equiv (model.cycleClass zeroClass) = 1 :=
  ⟨gysin_pointUnit_eq_zeroClass.symm, zero_coordinate⟩

theorem all_native_H2_pullback_follows_the_relative_proof :
    (∀ z : Betti,
      h2Equiv (SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2 z) =
        2 * h2Equiv z) ∧
    Function.Injective
      (SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2) := by
  constructor
  · intro z
    rw [ProjectiveLineSquareRamification.cohomologyPullback_square, map_smul, smul_eq_mul]
  · exact RationalDegreeTransfer.pull_injective ProjectiveLineSquareRamification.degreeTransfer

theorem unnormalized_zero_push_fails_the_original_target_column :
    model.cycleClass (actualPush (upstairsCycles ())) ≠
      (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : Betti) := by
  intro h
  have hc := congrArg h2Equiv h
  change h2Equiv (model.cycleClass (actualPush (actualPull zeroClass))) = _ at hc
  rw [geometric_chow_push_pull, map_smul, map_smul, zero_coordinate,
    ramificationIndex_eq_two, target_column, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem degree_one_law_is_false_and_normalization_recovers_the_original_zero :
    (¬ ∀ z : Betti, transfer.push (transfer.pull z) = (1 : ℚ) • z) ∧
    (2 : ℚ)⁻¹ • actualPush (actualPull zeroClass) = zeroClass := by
  constructor
  · intro h
    have hd : transfer.degree = ramificationIndex := rfl
    have htwo : transfer.push (transfer.pull (model.cycleClass zeroClass)) =
        (ramificationIndex : ℚ) • model.cycleClass zeroClass := by
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, hd] using
        LinearMap.congr_fun transfer.push_comp_pull (model.cycleClass zeroClass)
    have hc := congrArg h2Equiv (h (model.cycleClass zeroClass))
    rw [htwo, one_smul, map_smul, zero_coordinate, ramificationIndex_eq_two] at hc
    norm_num at hc
  · rw [geometric_chow_push_pull, ramificationIndex_eq_two, smul_smul]
    norm_num

theorem accepted_zero_aggregate_has_the_same_full_target_and_zero_representative :
    FiniteCoverageCertificate.check certificate = true ∧
      RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model ∧
      certificate.cycles () = ProjectiveLineGysinCycleClass.rationalZeroClass :=
  ⟨accepted, model_satisfies_from_ramification, (normalized_cycles ()).trans zeroClass_eq_original⟩

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.RelativeCochains.pullback_id,
    `HodgeConjecture.RelativeCochains.pullback_comp,
    `HodgeConjecture.RelativeCochains.pullback_congr,
    `HodgeConjecture.RelativeCochains.cohomologyPullback_comp,
    `HodgeConjecture.RelativeCochains.cohomologyPullback_forget,
    `HodgeConjecture.RelativeCochains.chartCohomologyIso_naturality,
    `HodgeConjecture.RelativeCochains.connecting_subtype_naturality,
    `HodgeConjecture.ComplexSquareThom.pairCondition,
    `HodgeConjecture.ComplexSquareThom.localRelativePullback,
    `HodgeConjecture.ComplexSquareThom.puncturedPull_square,
    `HodgeConjecture.ComplexSquareThom.connecting_square_naturality,
    `HodgeConjecture.ComplexSquareThom.localPull_square,
    `HodgeConjecture.ComplexSquareThom.localPull_thomClass,
    `HodgeConjecture.ComplexSquareThom.pointPull_eq_id,
    `HodgeConjecture.ComplexSquareThom.localGysin_pullback,
    `HodgeConjecture.ProjectiveLineSquareRamification.chartPullback_eq_original,
    `HodgeConjecture.ProjectiveLineSquareRamification.chartComparison_hom,
    `HodgeConjecture.ProjectiveLineSquareRamification.chartComparison_two_hom,
    `HodgeConjecture.ProjectiveLineSquareRamification.relativePullback_chart,
    `HodgeConjecture.ProjectiveLineSquareRamification.chartComparison_naturality,
    `HodgeConjecture.ProjectiveLineSquareRamification.supportedPull_forget,
    `HodgeConjecture.ProjectiveLineSquareRamification.supportedPull_square,
    `HodgeConjecture.ProjectiveLineSquareRamification.supportedGysin_pullback,
    `HodgeConjecture.ProjectiveLineSquareRamification.gysin_pullback,
    `HodgeConjecture.ProjectiveLineSquareRamification.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquareRamification.degreeTransfer,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.zeroClass_degree,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.finiteFiberPullback_zero,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.finiteFiberPullback_zero_eq_two,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.chowEquiv_pull_zero,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.chowEquiv_pull_zero_weighted,
    `HodgeConjecture.ProjectiveLineRamificationComparison.zeroClass_eq_original,
    `HodgeConjecture.ProjectiveLineRamificationComparison.ramificationIndex_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLineRamificationComparison.supportedGysin_ramification,
    `HodgeConjecture.ProjectiveLineRamificationComparison.gysin_ramification,
    `HodgeConjecture.ProjectiveLineRamificationComparison.actual_zero_pull,
    `HodgeConjecture.ProjectiveLineRamificationComparison.pull_comparison,
    `HodgeConjecture.ProjectiveLineRamificationComparison.push_comparison,
    `HodgeConjecture.ProjectiveLineRamificationComparison.upstairs_columns,
    `HodgeConjecture.ProjectiveLineRamificationComparison.normalized_cycles,
    `HodgeConjecture.ProjectiveLineRamificationComparison.accepted,
    `HodgeConjecture.ProjectiveLineRamificationComparison.model_satisfies_from_ramification,
    `HodgeConjecture.ProjectiveLineRamificationVerification.unchanged_target_source_and_original_maps,
    `HodgeConjecture.ProjectiveLineRamificationVerification.relative_pair_pull_is_original_simplex_precomposition,
    `HodgeConjecture.ProjectiveLineRamificationVerification.local_point_identity_has_ramified_thom_coefficient_two,
    `HodgeConjecture.ProjectiveLineRamificationVerification.local_ramification_is_nontrivial_and_cannot_annihilate_thom,
    `HodgeConjecture.ProjectiveLineRamificationVerification.reversed_local_orientation_fails_positive_normalization,
    `HodgeConjecture.ProjectiveLineRamificationVerification.original_chart_excision_and_forget_maps_are_retained,
    `HodgeConjecture.ProjectiveLineRamificationVerification.supported_thom_uses_the_actual_normal_chart_and_local_coefficient,
    `HodgeConjecture.ProjectiveLineRamificationVerification.global_point_identity_has_ramified_supported_gysin_coefficient,
    `HodgeConjecture.ProjectiveLineRamificationVerification.unweighted_absolute_gysin_pullback_is_false,
    `HodgeConjecture.ProjectiveLineRamificationVerification.actual_local_length_is_the_geometric_cover_rank,
    `HodgeConjecture.ProjectiveLineRamificationVerification.actual_raw_zero_pull_has_weight_two_and_no_infinity_component,
    `HodgeConjecture.ProjectiveLineRamificationVerification.original_zero_chow_class_is_retained_with_its_actual_weight,
    `HodgeConjecture.ProjectiveLineRamificationVerification.original_zero_cycle_has_the_same_positive_gysin_unit,
    `HodgeConjecture.ProjectiveLineRamificationVerification.all_native_H2_pullback_follows_the_relative_proof,
    `HodgeConjecture.ProjectiveLineRamificationVerification.unnormalized_zero_push_fails_the_original_target_column,
    `HodgeConjecture.ProjectiveLineRamificationVerification.degree_one_law_is_false_and_normalization_recovers_the_original_zero,
    `HodgeConjecture.ProjectiveLineRamificationVerification.accepted_zero_aggregate_has_the_same_full_target_and_zero_representative]
  unless declarations.length = 59 do
    throwError "Expected exactly 59 ramification audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing ramification audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let forbidden := [
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square_eq,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonical_cohomologyPullback_square]
  unless forbidden.length = 3 do
    throwError "Expected exactly three forbidden old global H² declarations"
  for name in forbidden ++
      [`HodgeConjecture.ProjectiveLineSquareCoverage.model_satisfies_from_square_cover] do
    unless env.contains name do
      throwError "Missing old-result witness needed by ramification dependency guard {name}"
  let finalEndpoint :=
    `HodgeConjecture.ProjectiveLineRamificationComparison.model_satisfies_from_ramification
  unless env.contains finalEndpoint do
    throwError "Missing final ramification dependency endpoint {finalEndpoint}"
  let finalClosure := HodgeConjecture.Research.declarationDependencies env finalEndpoint
  let endpoints := [
    `HodgeConjecture.ProjectiveLineSquareRamification.supportedPull_square,
    `HodgeConjecture.ProjectiveLineSquareRamification.degreeTransfer,
    finalEndpoint]
  unless endpoints.length = 3 do
    throwError "Expected exactly three independent ramification endpoints"
  for endpoint in endpoints do
    unless env.contains endpoint do
      throwError "Missing ramification dependency endpoint {endpoint}"
    let closure := if endpoint == finalEndpoint then finalClosure else
      HodgeConjecture.Research.declarationDependencies env endpoint
    for name in forbidden do
      if closure.contains name then
        throwError "Old global-square result {name} entered {endpoint}"
    let oldCoverageUses := closure.toList.filter fun name ↦
      match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]! ==
          `HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
      | none => false
    unless oldCoverageUses.isEmpty do
      throwError "Old square aggregate entered {endpoint}: {oldCoverageUses}"
    logInfo m!"PASS independent relative ramification closure: {endpoint}"
  let required := [
    `HodgeConjecture.ComplexSquareThom.localPull_square,
    `HodgeConjecture.RelativeCochains.connecting_naturality,
    `HodgeConjecture.ProjectiveLineSquareRamification.chartComparison_naturality,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.finiteFiberPullback_zero,
    `HodgeConjecture.ProjectiveLineSquareRamifiedChow.chowEquiv_pull_zero_weighted]
  unless required.length = 5 do
    throwError "Expected exactly five required local/ordinary ramification dependencies"
  for name in required do
    unless env.contains name do
      throwError "Missing required ramification declaration {name}"
    unless finalClosure.contains name do
      throwError "Required local/ordinary ramification dependency {name} missing from {finalEndpoint}"
    logInfo m!"PASS required ramification dependency: {name}"

end HodgeConjecture.ProjectiveLineRamificationVerification

end
