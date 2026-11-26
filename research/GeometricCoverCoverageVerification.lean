module

public import HodgeConjecture.Realization.Betti.Examples.SplitGeometricCoverage
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

@[expose] public section

/-!
Focused controls for the rank-two geometric-cover aggregate. All Chow
sources below are the original ordinary quotients in the exact structural
gradings. Singular coordinates are evaluations on the original complex points.
The negative controls exercise normalization, missing target directions,
and the positive geometric degree gate.
-/

set_option autoImplicit false

namespace HodgeConjecture.GeometricCoverCoverageVerification

open AlgebraicGeometry CategoryTheory SplitGeometricCoverage

noncomputable section

-- These equalities enforce both exact original Chow domains and original maps.
theorem exact_ordinary_chow_domains :
    actualPull =
      SchemeCycles.rationalChowFiniteFlatPullback ℂ baseStructure cover 0 ∧
    actualPush =
      SchemeCycles.rationalChowFinitePushforward ℂ baseStructure cover 0 :=
  ⟨rfl, rfl⟩

theorem native_and_geometric_degree_two :
    transfer.degree = 2 ∧
      ∀ x : downstairs, cover.finrank x = transfer.degree ∧ 0 < cover.finrank x := by
  refine ⟨SplitBetti.twoSheetTransfer_degree, fun x ↦ ?_⟩
  have hx : cover.finrank x = 2 := SplitPointGeometry.twoSheetCover_finrank ℂ x
  refine ⟨hx.trans SplitBetti.twoSheetTransfer_degree.symm, ?_⟩
  rw [hx]
  norm_num

-- The normalization is checked directly on the original ordinary Chow maps,
-- independently of the certificate's stored column binding.
theorem normalized_original_push_recovers_point (j : BaseIndex) :
    (2 : ℚ)⁻¹ •
      SchemeCycles.rationalChowFinitePushforward ℂ baseStructure cover 0
        (SchemeCycles.rationalChowFiniteFlatPullback ℂ baseStructure cover 0
          (SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j)) =
      SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j := by
  change (2 : ℚ)⁻¹ • actualPush
    (actualPull (SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j)) = _
  rw [geometric_chow_push_pull, smul_smul]
  norm_num

-- Each actual upstairs fiber cycle has value one on both points of its
-- fiber and zero on both points of the other fiber.
theorem native_fiber_values (j i : BaseIndex) (sheet : Fin 2) :
    SplitBetti.coordinates CoverIndex (upstairsCycleClass (upstairsCycles j))
      (i, sheet) = if j = i then 1 else 0 := by
  rw [upstairs_columns, target_column]
  change SplitBetti.coordinates CoverIndex
    (SplitBetti.pullback (Prod.fst : CoverIndex → BaseIndex)
      (basis j : BaseBetti)) (i, sheet) = _
  rw [SplitBetti.coordinates_pullback]
  have h := SplitOrdinaryBetti.coordinates_fullHodgeBasis BaseIndex j i
  by_cases hij : j = i
  · simpa only [basis, hij, ↓reduceIte] using h
  · simpa only [basis, hij, ↓reduceIte] using h

theorem first_fiber_has_two_points_and_omits_second_fiber :
    SplitBetti.coordinates CoverIndex (upstairsCycleClass (upstairsCycles 0)) (0, 0) = 1 ∧
    SplitBetti.coordinates CoverIndex (upstairsCycleClass (upstairsCycles 0)) (0, 1) = 1 ∧
    SplitBetti.coordinates CoverIndex (upstairsCycleClass (upstairsCycles 0)) (1, 0) = 0 ∧
    SplitBetti.coordinates CoverIndex (upstairsCycleClass (upstairsCycles 0)) (1, 1) = 0 := by
  simp only [native_fiber_values]
  norm_num

-- This follows through the original Chow-to-singular push comparison and
-- native transfer, separately from the ordinary Chow push--pull calculation.
theorem raw_push_doubles_target (j : BaseIndex) :
    model.cycleClass (actualPush (upstairsCycles j)) =
      (2 : ℚ) • (basis j : BaseBetti) := by
  calc
    model.cycleClass (actualPush (upstairsCycles j)) =
        transfer.push (upstairsCycleClass (upstairsCycles j)) :=
      LinearMap.congr_fun push_comparison (upstairsCycles j)
    _ = transfer.push (transfer.pull (basis j : BaseBetti)) := by
      rw [upstairs_columns, target_column]
    _ = (2 : ℚ) • (basis j : BaseBetti) := by
      have h := LinearMap.congr_fun transfer.push_comp_pull (basis j : BaseBetti)
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        SplitBetti.twoSheetTransfer_degree, Nat.cast_ofNat] using h

-- An unnormalized cycle cannot be substituted for a normalized column.
theorem raw_push_cannot_bind_target_column (j : BaseIndex) :
    model.cycleClass (actualPush (upstairsCycles j)) ≠
      (basis.equivFun.symm
        (fun i ↦ (1 : Matrix BaseIndex BaseIndex ℚ) i j) : BaseBetti) := by
  rw [raw_push_doubles_target, target_column]
  intro h
  have hj : SplitBetti.coordinates BaseIndex (basis j : BaseBetti) j = 1 := by
    simpa only [basis, ↓reduceIte] using
      SplitOrdinaryBetti.coordinates_fullHodgeBasis BaseIndex j j
  have hc := congrArg (fun a : BaseBetti ↦ SplitBetti.coordinates BaseIndex a j) h
  have impossible : (2 : ℚ) * 1 = 1 := by
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul, hj] using hc
  norm_num at impossible

-- Repeating the first fiber retains correct geometry and degree, but it
-- cannot represent the second independently fixed Hodge basis direction.
theorem repeated_first_fiber_fails_second_column :
    upstairsCycleClass (upstairsCycles (0 : BaseIndex)) ≠
      transfer.pull
        (basis.equivFun.symm
          (fun i ↦ (1 : Matrix BaseIndex BaseIndex ℚ) i (1 : BaseIndex)) : BaseBetti) := by
  rw [target_column]
  intro h
  have hc := congrArg
    (fun a : CoverBetti ↦ SplitBetti.coordinates CoverIndex a (1, 0)) h
  change SplitBetti.coordinates CoverIndex (upstairsCycleClass (upstairsCycles 0)) (1, 0) =
    SplitBetti.coordinates CoverIndex
      (SplitBetti.pullback (Prod.fst : CoverIndex → BaseIndex) (basis 1 : BaseBetti))
        (1, 0) at hc
  rw [native_fiber_values, SplitBetti.coordinates_pullback] at hc
  change (if (0 : BaseIndex) = 1 then (1 : ℚ) else 0) =
    SplitBetti.coordinates BaseIndex (basis 1 : BaseBetti) 1 at hc
  have hright : SplitBetti.coordinates BaseIndex (basis 1 : BaseBetti) 1 = 1 := by
    simpa only [basis, ↓reduceIte] using
      SplitOrdinaryBetti.coordinates_fullHodgeBasis BaseIndex (1 : BaseIndex) 1
  rw [hright] at hc
  norm_num at hc

-- The actual native pullback preserves every nonzero class. Evaluation on
-- the chosen first sheet proves this without adding an injectivity premise.
theorem positive_cover_cannot_kill_nonzero (a : BaseBetti) (ha : a ≠ 0) :
    transfer.pull a ≠ 0 := by
  intro vanished
  apply ha
  apply (SplitBetti.coordinates BaseIndex).injective
  ext i
  have hc := congrArg
    (fun b : CoverBetti ↦ SplitBetti.coordinates CoverIndex b (i, 0)) vanished
  change SplitBetti.coordinates CoverIndex
    (SplitBetti.pullback (Prod.fst : CoverIndex → BaseIndex) a) (i, 0) =
      SplitBetti.coordinates CoverIndex 0 (i, 0) at hc
  simpa only [SplitBetti.coordinates_pullback, map_zero, Pi.zero_apply] using hc

theorem empty_sheet_rank_zero (x : downstairs) :
    (SplitPointGeometry.coverProjection ℂ BaseIndex (Fin 0)).finrank x = 0 := by
  simpa only [Fintype.card_fin] using
    SplitPointGeometry.coverProjection_finrank ℂ BaseIndex (Fin 0) x

-- A finite étale projection with no sheets does not pass the positive
-- transfer-degree gate. Existence of a scheme map alone cannot supply it.
theorem empty_sheet_cannot_supply_positive_geometric_transfer :
    ¬ ∃ T : RationalDegreeTransfer
        (SplitBetti.Cohomology (BaseIndex × Fin 0)) BaseBetti,
      T.degree = (SplitPointGeometry.coverProjection ℂ BaseIndex (Fin 0)).finrank
        (SplitPointGeometry.labelEquivScheme ℂ BaseIndex 0) := by
  rintro ⟨T, hdegree⟩
  apply T.degree_ne_zero
  exact hdegree.trans (empty_sheet_rank_zero _)

-- Fail immediately on missing public declarations or an axiom beyond the
-- standard three. This includes constructor gates and local negative controls.
open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SplitZeroCycles.ordinaryChowEquivOfStructure,
    `HodgeConjecture.SplitZeroCycles.ordinaryChowEquivOfStructure_rationalClassMap,
    `HodgeConjecture.SplitZeroCycles.ordinaryRationalPrincipalRelations_eq_bot,
    `HodgeConjecture.SplitZeroCycles.finiteFiberMultiplicity_eq_one,
    `HodgeConjecture.SplitZeroCycles.finitePushforward_eq_split,
    `HodgeConjecture.SplitZeroCycles.finiteFiberPullback_eq_split,
    `HodgeConjecture.SplitZeroCycles.ordinaryChowEquivOfStructure_finitePushforward,
    `HodgeConjecture.SplitZeroCycles.ordinaryChowEquivOfStructure_finiteFlatPullback,
    `HodgeConjecture.SplitPointGeometry.coverProjection_finrank,
    `HodgeConjecture.SplitPointGeometry.twoSheetCover_isFiniteEtaleSurjective,
    `HodgeConjecture.SplitComplexPoints.schemePointHomeomorph,
    `HodgeConjecture.SplitComplexPoints.schemePointHomeomorph_map,
    `HodgeConjecture.SplitBetti.pushforward_pullback_of_card,
    `HodgeConjecture.SplitBetti.projectionTransfer,
    `HodgeConjecture.SplitBetti.projectionTransfer_degree_eq_finrank,
    `HodgeConjecture.SplitOrdinaryBetti.cycleClassOfStructure,
    `HodgeConjecture.SplitOrdinaryBetti.fullHodgeEquiv,
    `HodgeConjecture.SplitOrdinaryBetti.fullHodgeBasis,
    `HodgeConjecture.FiniteCoverageCertificate.normalizedCoverCycles,
    `HodgeConjecture.FiniteCoverageCertificate.of_degree_transfer,
    `HodgeConjecture.FiniteCoverageCertificate.of_degree_transfer_harmonic,
    `HodgeConjecture.SplitGeometricCoverage.pull_comparison,
    `HodgeConjecture.SplitGeometricCoverage.push_comparison,
    `HodgeConjecture.SplitGeometricCoverage.degree_eq_geometric_rank,
    `HodgeConjecture.SplitGeometricCoverage.upstairs_columns,
    `HodgeConjecture.SplitGeometricCoverage.geometric_chow_push_pull,
    `HodgeConjecture.SplitGeometricCoverage.accepted,
    `HodgeConjecture.SplitGeometricCoverage.normalized_cycles,
    `HodgeConjecture.SplitGeometricCoverage.model_satisfies_from_geometric_cover,
    `HodgeConjecture.GeometricCoverCoverageVerification.exact_ordinary_chow_domains,
    `HodgeConjecture.GeometricCoverCoverageVerification.native_and_geometric_degree_two,
    `HodgeConjecture.GeometricCoverCoverageVerification.normalized_original_push_recovers_point,
    `HodgeConjecture.GeometricCoverCoverageVerification.native_fiber_values,
    `HodgeConjecture.GeometricCoverCoverageVerification.first_fiber_has_two_points_and_omits_second_fiber,
    `HodgeConjecture.GeometricCoverCoverageVerification.raw_push_doubles_target,
    `HodgeConjecture.GeometricCoverCoverageVerification.raw_push_cannot_bind_target_column,
    `HodgeConjecture.GeometricCoverCoverageVerification.repeated_first_fiber_fails_second_column,
    `HodgeConjecture.GeometricCoverCoverageVerification.positive_cover_cannot_kill_nonzero,
    `HodgeConjecture.GeometricCoverCoverageVerification.empty_sheet_rank_zero,
    `HodgeConjecture.GeometricCoverCoverageVerification.empty_sheet_cannot_supply_positive_geometric_transfer]
  unless declarations.length = 40 do
    throwError "Expected exactly 40 geometric-cover audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing geometric-cover audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end

end HodgeConjecture.GeometricCoverCoverageVerification

end
