module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineSquareCoverage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

@[expose] public section

/-! Controls for the connected, branched, actual P¹ square map. The ordinary
Chow maps retain their original exact grading; native singular pullback is
calculated independently, and the push is the degree-specific point-Gysin trace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquareVerification

open AlgebraicGeometry CategoryTheory SchemeCycles ProjectiveLineSquareCoverage
open ProjectiveLineBettiCohomology

abbrev infinityClass : BaseChow := ProjectiveLineBettiCycleClass.rationalInfinityClass

private theorem infinity_coordinate : h2Equiv (model.cycleClass infinityClass) = 1 := by
  change h2Equiv (ProjectiveLineBettiCycleClass.cycleClass infinityClass) = 1
  rw [ProjectiveLineBettiCycleClass.cycleClass_infinity, h2Equiv_coverGenerator]

private theorem pulled_coordinate :
    h2Equiv (upstairsCycleClass (actualPull infinityClass)) = 2 := by
  change h2Equiv (ProjectiveLineBettiCycleClass.cycleClass
    (sourceComparison (actualPull infinityClass))) = 2
  rw [ProjectiveLineBettiCycleClass.coordinate_cycleClass,
    ProjectiveLineSquareChow.degree_pull,
    ProjectiveLineBettiCycleClass.rationalChowDegree_infinity]
  norm_num

theorem unchanged_model_basis_and_original_maps :
    model = ProjectiveLineCoverageCertificate.model ∧
    basis = ProjectiveLineCoverageCertificate.basis ∧
    actualPull = rationalChowFiniteFlatPullback ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 ∧
    actualPush = rationalChowFinitePushforward ℂ
      (projectiveLine ℂ ↘ Spec (.of ℂ)) cover 0 := ⟨rfl, rfl, rfl, rfl⟩

theorem source_group_has_exact_composite_grading :
    CoverChow = RationalChowGroup
      (DimensionFunction.ofLocallyOfFiniteType ℂ (projectiveLine ℂ)
        (cover ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)))) 0 := rfl

theorem connected_finite_flat_geometric_degree_two :
    ConnectedSpace scheme ∧ IsFinite cover ∧ Flat cover ∧
      ∀ x : scheme, cover.finrank x = 2 :=
  ⟨inferInstance, inferInstance, inferInstance, ProjectiveLineSquare.square_finrank ℂ⟩

theorem both_single_point_branch_fibers_have_length_two :
    (∃! x : scheme, cover x = projectiveLineZero ℂ) ∧
      finiteFiberMultiplicity cover (projectiveLineZero ℂ) = 2 ∧
    (∃! x : scheme, cover x = projectiveLineInfinity ℂ) ∧
      finiteFiberMultiplicity cover (projectiveLineInfinity ℂ) = 2 := by
  refine ⟨⟨projectiveLineZero ℂ, ProjectiveLineSquare.zero_fixed ℂ,
    fun x hx => (ProjectiveLineSquare.square_eq_zero_iff ℂ x).mp hx⟩,
    ProjectiveLineSquareChow.zero_finiteFiberMultiplicity ℂ,
    ⟨projectiveLineInfinity ℂ, ProjectiveLineSquare.infinity_fixed ℂ,
    fun x hx => (ProjectiveLineSquare.square_eq_infinity_iff ℂ x).mp hx⟩,
    ProjectiveLineSquareChow.infinity_finiteFiberMultiplicity ℂ⟩

theorem actual_zero_quotient_contains_nonzero_nilpotent :
    ∃ x : PolynomialSquare.zeroFiber ℂ, x ≠ 0 ∧ x ^ 2 = 0 ∧
      Module.length ℂ (PolynomialSquare.zeroFiber ℂ) = 2 :=
  ⟨AdjoinRoot.root (Polynomial.X ^ 2 : Polynomial ℂ),
    PolynomialSquare.zeroFiber_root_ne_zero ℂ, PolynomialSquare.zeroFiber_root_sq ℂ,
    PolynomialSquare.zeroFiber_length_over_base ℂ⟩

theorem actual_cover_is_branched : ¬ Etale cover ∧ ¬ FormallyUnramified cover :=
  ⟨ProjectiveLineSquareChow.square_not_etale ℂ,
    ProjectiveLineSquareChow.square_not_formallyUnramified ℂ⟩

theorem original_point_pull_keeps_weight_two :
    sourceComparison (actualPull infinityClass) = (2 : ℚ) • infinityClass ∧
      h2Equiv (upstairsCycleClass (actualPull infinityClass)) = 2 :=
  ⟨ProjectiveLineSquareChow.chowEquiv_pull_infinity ℂ, pulled_coordinate⟩

theorem ordinary_degree_preserves_push_and_doubles_pull (q : ℚ) :
    ProjectiveLineCycles.rationalChowDegree ℂ
        (actualPush (q • sourceComparison.symm infinityClass)) = q ∧
    ProjectiveLineCycles.rationalChowDegree ℂ
        (sourceComparison (actualPull (q • infinityClass))) = 2 * q := by
  constructor
  · rw [ProjectiveLineSquareChow.degree_push]
    simp only [map_smul, LinearEquiv.apply_symm_apply,
      ProjectiveLineBettiCycleClass.rationalChowDegree_infinity, smul_eq_mul, mul_one]
  · rw [ProjectiveLineSquareChow.degree_pull]
    simp only [map_smul, ProjectiveLineBettiCycleClass.rationalChowDegree_infinity,
      smul_eq_mul, mul_one]

theorem original_scheme_binding_of_native_square
    (z : ProjectiveLineComplexPoints.Point) :
    ProjectiveLineComplexPoints.schemeMorphism
        (ProjectiveLineSquarePullback.pointSquareFun z) =
      ProjectiveLineComplexPoints.schemeMorphism z ≫ cover ∧
    ProjectiveLineSquarePullback.canonicalMap ≫
        ProjectiveLineSquarePullback.canonicalSquareMap =
      ProjectiveLineSquarePullback.pointMap ≫ ProjectiveLineSquarePullback.canonicalMap :=
  ⟨rfl, ProjectiveLineSquarePullback.canonicalSquare_naturality⟩

theorem independent_circle_and_projective_line_native_degrees
    (a : SingularCochains.Cohomology CircleCohomology.space 1) (b : Betti) :
    CircleCohomology.h1Equiv
        (SingularCochains.cohomologyPullback CircleSquare.squareMap 1 a) =
      2 * CircleCohomology.h1Equiv a ∧
    h2Equiv (SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2 b) =
      2 * h2Equiv b := by
  constructor
  · rw [CircleSquare.cohomologyPullback_square, map_smul, smul_eq_mul]
  · rw [ProjectiveLineSquarePullback.cohomologyPullback_square, map_smul, smul_eq_mul]

theorem supported_gysin_trace_preserves_original_point_class :
    ProjectiveLineSquareGysin.supportMap ≫
        SingularSubcomplexes.subsetInclusion
          (TopCat.of ProjectiveLineComplexPoints.Point) ProjectiveLinePointSupport.support =
      SingularSubcomplexes.subsetInclusion
          (TopCat.of ProjectiveLineComplexPoints.Point) ProjectiveLinePointSupport.support ≫
        ProjectiveLineSquarePullback.pointMap ∧
    h2Equiv (transfer.push (model.cycleClass infinityClass)) = 1 := by
  refine ⟨ProjectiveLineSquareGysin.supportMap_inclusion, ?_⟩
  change h2Equiv (ProjectiveLineSquareGysin.push (model.cycleClass infinityClass)) = 1
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply]
  exact infinity_coordinate

theorem original_unnormalized_push_doubles_and_changes_infinity :
    actualPush (actualPull infinityClass) = (2 : ℚ) • infinityClass ∧
      actualPush (actualPull infinityClass) ≠ infinityClass := by
  refine ⟨geometric_chow_push_pull infinityClass, ?_⟩
  intro h
  have hd := congrArg (ProjectiveLineCycles.rationalChowDegree ℂ) h
  rw [geometric_chow_push_pull, map_smul,
    ProjectiveLineBettiCycleClass.rationalChowDegree_infinity] at hd
  norm_num at hd

theorem unnormalized_push_fails_the_original_full_target_column :
    model.cycleClass (actualPush (upstairsCycles ())) ≠
      (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i ()) : Betti) := by
  intro h
  have hc := congrArg h2Equiv h
  change h2Equiv (model.cycleClass (actualPush (actualPull infinityClass))) = _ at hc
  rw [geometric_chow_push_pull, map_smul, map_smul, infinity_coordinate,
    target_column, h2Equiv_coverGenerator] at hc
  norm_num at hc

theorem normalized_original_push_recovers_infinity_with_degree_one :
    (2 : ℚ)⁻¹ • actualPush (actualPull infinityClass) = infinityClass ∧
      ProjectiveLineCycles.rationalChowDegree ℂ (certificate.cycles ()) = 1 := by
  constructor
  · rw [geometric_chow_push_pull, smul_smul]
    norm_num
  · rw [normalized_cycles]
    exact ProjectiveLineBettiCycleClass.rationalChowDegree_infinity

theorem native_pull_cannot_kill_a_nonzero_class (z : Betti) (hz : z ≠ 0) :
    transfer.pull z ≠ 0 := by
  intro h
  change SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2 z = 0 at h
  rw [ProjectiveLineSquarePullback.cohomologyPullback_square] at h
  exact hz ((smul_eq_zero.mp h).resolve_left (by norm_num))

theorem degree_one_cannot_satisfy_the_native_push_pull_law :
    ¬ ∀ z : Betti, transfer.push (transfer.pull z) = (1 : ℚ) • z := by
  intro h
  have hc := congrArg h2Equiv (h (model.cycleClass infinityClass))
  dsimp only [transfer, ProjectiveLineSquareGysin.degreeTransfer] at hc
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply,
    ProjectiveLineSquarePullback.cohomologyPullback_square,
    one_smul, map_smul, infinity_coordinate] at hc
  norm_num at hc

theorem accepted_aggregate_uses_unchanged_full_target :
    FiniteCoverageCertificate.check certificate = true ∧
      RationalHodgeConjectureAt ProjectiveLineCoverageCertificate.model ∧
      certificate.cycles () = infinityClass :=
  ⟨accepted, model_satisfies_from_square_cover, normalized_cycles ()⟩

theorem actual_polynomial_square_mixes_even_and_odd_components :
    PolynomialSquare.assemble ℂ
      ![3 * Polynomial.X + 7, Polynomial.X ^ 2] =
        Polynomial.X ^ 5 + 3 * Polynomial.X ^ 2 + 7 := by
  simp [PolynomialSquare.assemble, PolynomialSquare.squareHom, map_add, map_mul, map_pow]
  ring

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.PolynomialSquare.assemble_coefficients,
    `HodgeConjecture.PolynomialSquare.oneXBasis,
    `HodgeConjecture.PolynomialSquare.squareHom_finite,
    `HodgeConjecture.PolynomialSquare.squareHom_flat,
    `HodgeConjecture.PolynomialSquare.squareHom_finrank,
    `HodgeConjecture.PolynomialSquare.zeroFiber_length_over_base,
    `HodgeConjecture.PolynomialSquare.zeroFiber_root_sq,
    `HodgeConjecture.PolynomialSquare.zeroFiber_root_ne_zero,
    `HodgeConjecture.ProjectiveLineSquare.square,
    `HodgeConjecture.ProjectiveLineSquare.chart_x_isPullback,
    `HodgeConjecture.ProjectiveLineSquare.square_finrank,
    `HodgeConjecture.ProjectiveLineSquare.source_connected,
    `HodgeConjecture.ProjectiveLineSquare.square_eq_zero_iff,
    `HodgeConjecture.ProjectiveLineSquare.square_eq_infinity_iff,
    `HodgeConjecture.ProjectiveLineSquare.over_base,
    `HodgeConjecture.ProjectiveLineSquareChow.sourceDimension_eq,
    `HodgeConjecture.ProjectiveLineSquareChow.chowEquiv_classMap,
    `HodgeConjecture.ProjectiveLineSquareChow.chowEquiv_symm_classMap,
    `HodgeConjecture.ProjectiveLineSquareChow.actualPull,
    `HodgeConjecture.ProjectiveLineSquareChow.actualPush,
    `HodgeConjecture.ProjectiveLineSquareChow.degree_push,
    `HodgeConjecture.ProjectiveLineSquareChow.degree_pull,
    `HodgeConjecture.ProjectiveLineSquareChow.push_pull,
    `HodgeConjecture.ProjectiveLineSquareChow.zero_finiteFiberMultiplicity,
    `HodgeConjecture.ProjectiveLineSquareChow.infinity_finiteFiberMultiplicity,
    `HodgeConjecture.ProjectiveLineSquareChow.square_not_etale,
    `HodgeConjecture.ProjectiveLineSquareChow.chowEquiv_pull_infinity,
    `HodgeConjecture.CircleSquare.angularSimplex_face,
    `HodgeConjecture.CircleSquare.edge_add,
    `HodgeConjecture.CircleSquare.fullLoop_independent,
    `HodgeConjecture.CircleSquare.cohomologyPullback_square,
    `HodgeConjecture.SingularMayerVietorisNaturality.connecting_naturality,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonicalSquare_naturality,
    `HodgeConjecture.ProjectiveLineSquarePullback.circleInclusion_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquarePullback.canonical_cohomologyPullback_square,
    `HodgeConjecture.ProjectiveLineSquareGysin.supportMap_inclusion,
    `HodgeConjecture.ProjectiveLineSquareGysin.push_gysin,
    `HodgeConjecture.ProjectiveLineSquareGysin.push_eq_id,
    `HodgeConjecture.ProjectiveLineSquareGysin.degreeTransfer,
    `HodgeConjecture.ProjectiveLineCoverageCertificate.basis,
    `HodgeConjecture.FiniteCoverageCertificate.of_degree_transfer,
    `HodgeConjecture.ProjectiveLineSquareCoverage.pull_comparison,
    `HodgeConjecture.ProjectiveLineSquareCoverage.push_comparison,
    `HodgeConjecture.ProjectiveLineSquareCoverage.degree_eq_geometric_rank,
    `HodgeConjecture.ProjectiveLineSquareCoverage.upstairs_columns,
    `HodgeConjecture.ProjectiveLineSquareCoverage.normalized_cycles,
    `HodgeConjecture.ProjectiveLineSquareCoverage.accepted,
    `HodgeConjecture.ProjectiveLineSquareCoverage.model_satisfies_from_square_cover,
    `HodgeConjecture.ProjectiveLineSquareVerification.unchanged_model_basis_and_original_maps,
    `HodgeConjecture.ProjectiveLineSquareVerification.source_group_has_exact_composite_grading,
    `HodgeConjecture.ProjectiveLineSquareVerification.connected_finite_flat_geometric_degree_two,
    `HodgeConjecture.ProjectiveLineSquareVerification.both_single_point_branch_fibers_have_length_two,
    `HodgeConjecture.ProjectiveLineSquareVerification.actual_zero_quotient_contains_nonzero_nilpotent,
    `HodgeConjecture.ProjectiveLineSquareVerification.actual_cover_is_branched,
    `HodgeConjecture.ProjectiveLineSquareVerification.original_point_pull_keeps_weight_two,
    `HodgeConjecture.ProjectiveLineSquareVerification.ordinary_degree_preserves_push_and_doubles_pull,
    `HodgeConjecture.ProjectiveLineSquareVerification.original_scheme_binding_of_native_square,
    `HodgeConjecture.ProjectiveLineSquareVerification.independent_circle_and_projective_line_native_degrees,
    `HodgeConjecture.ProjectiveLineSquareVerification.supported_gysin_trace_preserves_original_point_class,
    `HodgeConjecture.ProjectiveLineSquareVerification.original_unnormalized_push_doubles_and_changes_infinity,
    `HodgeConjecture.ProjectiveLineSquareVerification.unnormalized_push_fails_the_original_full_target_column,
    `HodgeConjecture.ProjectiveLineSquareVerification.normalized_original_push_recovers_infinity_with_degree_one,
    `HodgeConjecture.ProjectiveLineSquareVerification.native_pull_cannot_kill_a_nonzero_class,
    `HodgeConjecture.ProjectiveLineSquareVerification.degree_one_cannot_satisfy_the_native_push_pull_law,
    `HodgeConjecture.ProjectiveLineSquareVerification.accepted_aggregate_uses_unchanged_full_target,
    `HodgeConjecture.ProjectiveLineSquareVerification.actual_polynomial_square_mixes_even_and_odd_components]
  unless declarations.length = 67 do
    throwError "Expected exactly 67 connected P¹ square audit declarations"
  for declaration in declarations do
    unless env.contains declaration do
      throwError "Missing connected P¹ square audit declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end HodgeConjecture.ProjectiveLineSquareVerification

end
