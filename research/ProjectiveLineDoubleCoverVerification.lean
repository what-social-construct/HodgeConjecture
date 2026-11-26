module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineDoubleCoverCoverage
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

@[expose] public section

/-! Controls for the actual split double cover of P¹. The native H²
decomposition is independent of Chow, while component cycles start in
the original ordinary Chow quotient of the original scheme coproduct. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineDoubleCoverVerification

open AlgebraicGeometry CategoryTheory ProjectiveLineDoubleCoverCoverage
open ProjectiveLineBettiCohomology

abbrev infinityClass : BaseChow := ProjectiveLineBettiCycleClass.rationalInfinityClass

def leftInfinity : CoverChow :=
  SplitDoubleCoverChow.leftPush ℂ baseStructure 0 infinityClass

def rightInfinity : CoverChow :=
  SplitDoubleCoverChow.rightPush ℂ baseStructure 0 infinityClass

def antiDiagonal : CoverChow := leftInfinity - rightInfinity

def baseNativeCoordinates : SplitDoubleCoverBetti.BaseBetti baseStructure 2 ≃ₗ[ℚ] ℚ :=
  baseComparison.symm.trans h2Equiv

def coordinates : CoverBetti ≃ₗ[ℚ] ℚ × ℚ :=
  bettiComparison.trans (baseNativeCoordinates.prodCongr baseNativeCoordinates)

instance : FiniteDimensional ℚ CoverBetti := coordinates.symm.finiteDimensional

private lemma infinity_coordinate : h2Equiv (model.cycleClass infinityClass) = 1 := by
  change h2Equiv (ProjectiveLineBettiCycleClass.cycleClass infinityClass) = 1
  rw [ProjectiveLineBettiCycleClass.cycleClass_infinity, h2Equiv_coverGenerator]

private lemma pull_coordinates (a : BaseBetti) :
    coordinates (transfer.pull a) = (h2Equiv a, h2Equiv a) := by
  change (baseNativeCoordinates
      (bettiComparison (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseComparison a))).1,
    baseNativeCoordinates
      (bettiComparison (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseComparison a))).2) = _
  rw [SplitDoubleCoverBetti.cohomologyEquiv_pull]
  change (h2Equiv (baseComparison.symm (baseComparison a)),
    h2Equiv (baseComparison.symm (baseComparison a))) = _
  rw [baseComparison.symm_apply_apply]

theorem unchanged_target_and_exact_original_maps :
    model = ProjectiveLineCoverageCertificate.model ∧
    basis = ProjectiveLineCoverageCertificate.basis ∧
    actualPull = SchemeCycles.rationalChowFiniteFlatPullback ℂ baseStructure cover 0 ∧
    actualPush = SchemeCycles.rationalChowFinitePushforward ℂ baseStructure cover 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem native_upstairs_H2_has_dimension_two : Module.finrank ℚ CoverBetti = 2 := by
  rw [coordinates.finrank_eq]
  simp

theorem upstairs_cycle_class_coordinates (z : CoverChow) :
    coordinates (upstairsCycleClass z) =
      (h2Equiv (model.cycleClass (chowComparison z).1),
        h2Equiv (model.cycleClass (chowComparison z).2)) := by
  change (baseNativeCoordinates (bettiComparison (upstairsCycleClass z)).1,
    baseNativeCoordinates (bettiComparison (upstairsCycleClass z)).2) = _
  rw [upstairsCycleClass_components]
  change (h2Equiv (baseComparison.symm (baseComparison (model.cycleClass (chowComparison z).1))),
    h2Equiv (baseComparison.symm (baseComparison (model.cycleClass (chowComparison z).2)))) = _
  rw [baseComparison.symm_apply_apply, baseComparison.symm_apply_apply]

theorem infinity_pull_has_both_native_components :
    coordinates (upstairsCycleClass (actualPull infinityClass)) = (1, 1) := by
  rw [upstairs_cycle_class_coordinates, SplitDoubleCoverChow.chowEquiv_pull]
  change (h2Equiv (model.cycleClass infinityClass),
    h2Equiv (model.cycleClass infinityClass)) = (1, 1)
  rw [infinity_coordinate]

theorem original_inclusion_infinity_components :
    coordinates (upstairsCycleClass leftInfinity) = (1, 0) ∧
    coordinates (upstairsCycleClass rightInfinity) = (0, 1) := by
  constructor
  · rw [upstairs_cycle_class_coordinates]
    change (h2Equiv (model.cycleClass (chowComparison
      (SplitDoubleCoverChow.leftPush ℂ baseStructure 0 infinityClass)).1),
      h2Equiv (model.cycleClass (chowComparison
      (SplitDoubleCoverChow.leftPush ℂ baseStructure 0 infinityClass)).2)) = _
    rw [SplitDoubleCoverChow.chowEquiv_leftPush]
    change (h2Equiv (model.cycleClass infinityClass), h2Equiv (model.cycleClass 0)) = (1, 0)
    rw [infinity_coordinate, map_zero, map_zero]
  · rw [upstairs_cycle_class_coordinates]
    change (h2Equiv (model.cycleClass (chowComparison
      (SplitDoubleCoverChow.rightPush ℂ baseStructure 0 infinityClass)).1),
      h2Equiv (model.cycleClass (chowComparison
      (SplitDoubleCoverChow.rightPush ℂ baseStructure 0 infinityClass)).2)) = _
    rw [SplitDoubleCoverChow.chowEquiv_rightPush]
    change (h2Equiv (model.cycleClass 0), h2Equiv (model.cycleClass infinityClass)) = (0, 1)
    rw [map_zero, map_zero, infinity_coordinate]

theorem one_component_fails_upstairs_generation :
    upstairsCycleClass leftInfinity ≠
      transfer.pull (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : BaseBetti) := by
  rw [target_column]
  intro h
  have hc := congrArg coordinates h
  rw [original_inclusion_infinity_components.1, pull_coordinates,
    h2Equiv_coverGenerator] at hc
  have hs := congrArg Prod.snd hc
  norm_num at hs

theorem unnormalized_original_push_doubles_class :
    model.cycleClass (actualPush (upstairsCycles ())) = (2 : ℚ) • coverGenerator := by
  change model.cycleClass (actualPush (actualPull infinityClass)) = _
  rw [geometric_chow_push_pull, map_smul]
  change (2 : ℚ) • ProjectiveLineBettiCycleClass.cycleClass infinityClass = _
  rw [ProjectiveLineBettiCycleClass.cycleClass_infinity]

theorem unnormalized_push_fails_original_target_column :
    model.cycleClass (actualPush (upstairsCycles ())) ≠
      (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i ()) : BaseBetti) := by
  rw [unnormalized_original_push_doubles_class, target_column]
  intro h
  have hc := congrArg h2Equiv h
  rw [map_smul, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem normalized_original_push_recovers_infinity :
    (2 : ℚ)⁻¹ • SchemeCycles.rationalChowFinitePushforward ℂ baseStructure cover 0
      (SchemeCycles.rationalChowFiniteFlatPullback ℂ baseStructure cover 0 infinityClass) =
        infinityClass := by
  change (2 : ℚ)⁻¹ • actualPush (actualPull infinityClass) = _
  rw [geometric_chow_push_pull, smul_smul]
  norm_num

theorem anti_diagonal_has_nonzero_native_class :
    coordinates (upstairsCycleClass antiDiagonal) = (1, -1) ∧
      upstairsCycleClass antiDiagonal ≠ 0 := by
  have hc : coordinates (upstairsCycleClass antiDiagonal) = (1, -1) := by
    change coordinates (upstairsCycleClass (leftInfinity - rightInfinity)) = _
    rw [map_sub, map_sub, original_inclusion_infinity_components.1,
      original_inclusion_infinity_components.2]
    change ((1 : ℚ) - 0, (0 : ℚ) - 1) = (1, -1)
    norm_num
  refine ⟨hc, ?_⟩
  intro hz
  rw [hz, map_zero] at hc
  have hf := congrArg Prod.fst hc
  norm_num at hf

theorem anti_diagonal_original_chow_push_zero : actualPush antiDiagonal = 0 := by
  change actualPush
    (SplitDoubleCoverChow.leftPush ℂ baseStructure 0 infinityClass -
      SplitDoubleCoverChow.rightPush ℂ baseStructure 0 infinityClass) = 0
  rw [map_sub, SplitDoubleCoverChow.actualPush_leftPush,
    SplitDoubleCoverChow.actualPush_rightPush, sub_self]

theorem anti_diagonal_native_push_zero :
    SplitDoubleCoverBetti.actualPush baseStructure 2 (upstairsCycleClass antiDiagonal) = 0 := by
  have hc : chowComparison antiDiagonal = (infinityClass, -infinityClass) := by
    change chowComparison
      (SplitDoubleCoverChow.leftPush ℂ baseStructure 0 infinityClass -
        SplitDoubleCoverChow.rightPush ℂ baseStructure 0 infinityClass) = _
    rw [map_sub, SplitDoubleCoverChow.chowEquiv_leftPush,
      SplitDoubleCoverChow.chowEquiv_rightPush]
    change (infinityClass - 0, 0 - infinityClass) = (infinityClass, -infinityClass)
    rw [sub_zero, zero_sub]
  rw [SplitDoubleCoverBetti.actualPush_eq_sum, upstairsCycleClass_components, hc]
  change baseCycleClass infinityClass + baseCycleClass (-infinityClass) = 0
  rw [map_neg, add_neg_cancel]

theorem native_fold_pull_is_injective : Function.Injective transfer.pull := by
  intro a b hab
  have hc := congrArg (fun z : CoverBetti ↦ (bettiComparison z).1) hab
  change (bettiComparison
    (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseComparison a))).1 =
      (bettiComparison
        (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseComparison b))).1 at hc
  rw [SplitDoubleCoverBetti.cohomologyEquiv_pull,
    SplitDoubleCoverBetti.cohomologyEquiv_pull] at hc
  exact baseComparison.injective hc

theorem accepted_aggregate_covers_unchanged_full_target :
    FiniteCoverageCertificate.check certificate = true ∧
      RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model := by
  refine ⟨accepted, ?_⟩
  exact FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SplitDoubleCover.fold_finrank,
    `HodgeConjecture.SplitDoubleCover.fold_stalkMap_isIso,
    `HodgeConjecture.SplitDoubleCover.source_isNoetherian,
    `AlgebraicGeometry.Scheme.ComplexPoints.coprodHomeomorph,
    `AlgebraicGeometry.Scheme.ComplexPoints.coprodHomeomorph_inl,
    `HodgeConjecture.SingularDoubleCover.simplexSheet_at,
    `HodgeConjecture.SingularDoubleCover.simplexSheet_face,
    `HodgeConjecture.SingularDoubleCover.differential_extension,
    `HodgeConjecture.SingularDoubleCover.cochain_reassembly,
    `HodgeConjecture.SingularDoubleCover.cochainPush_pullback,
    `HodgeConjecture.SingularDoubleCover.cohomologyEquiv,
    `HodgeConjecture.SplitDoubleCoverBetti.pointHomeomorph,
    `HodgeConjecture.SplitDoubleCoverBetti.cohomologyEquiv,
    `HodgeConjecture.SplitDoubleCoverBetti.actualPush_eq_homologyMap,
    `HodgeConjecture.SplitDoubleCoverBetti.cohomologyEquiv_pull,
    `HodgeConjecture.SplitDoubleCoverBetti.actualPush_eq_sum,
    `HodgeConjecture.SplitDoubleCoverBetti.degreeTransfer,
    `HodgeConjecture.SplitDoubleCoverChow.fold_finiteFiberMultiplicity,
    `HodgeConjecture.SplitDoubleCoverChow.leftRestriction_classMap,
    `HodgeConjecture.SplitDoubleCoverChow.rightRestriction_classMap,
    `HodgeConjecture.SplitDoubleCoverChow.chowEquiv,
    `HodgeConjecture.SplitDoubleCoverChow.chowEquiv_leftPush,
    `HodgeConjecture.SplitDoubleCoverChow.chowEquiv_rightPush,
    `HodgeConjecture.SplitDoubleCoverChow.chowEquiv_pull,
    `HodgeConjecture.SplitDoubleCoverChow.actualPush_eq_sum,
    `HodgeConjecture.ProjectiveLineCoverageCertificate.basis,
    `HodgeConjecture.ProjectiveLineBettiCycleClass.cycleClass_infinity,
    `HodgeConjecture.FiniteCoverageCertificate.of_degree_transfer,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.upstairsCycleClass_components,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.upstairsCycleClass_unique,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.pull_comparison,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.push_comparison,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.degree_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.upstairs_columns,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.normalized_cycles,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.accepted,
    `HodgeConjecture.ProjectiveLineDoubleCoverCoverage.model_satisfies_from_double_cover,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.unchanged_target_and_exact_original_maps,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.native_upstairs_H2_has_dimension_two,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.upstairs_cycle_class_coordinates,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.infinity_pull_has_both_native_components,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.original_inclusion_infinity_components,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.one_component_fails_upstairs_generation,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.unnormalized_original_push_doubles_class,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.unnormalized_push_fails_original_target_column,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.normalized_original_push_recovers_infinity,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.anti_diagonal_has_nonzero_native_class,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.anti_diagonal_original_chow_push_zero,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.anti_diagonal_native_push_zero,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.native_fold_pull_is_injective,
    `HodgeConjecture.ProjectiveLineDoubleCoverVerification.accepted_aggregate_covers_unchanged_full_target]
  unless declarations.length = 51 do
    throwError "Expected exactly 51 P¹ double-cover audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing P¹ double-cover audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end HodgeConjecture.ProjectiveLineDoubleCoverVerification

end
