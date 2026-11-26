module
import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverHodgeComparison
import Lean.Util.CollectAxioms

set_option autoImplicit false
noncomputable section
open HodgeConjecture CircleCoverHarmonicComparison

-- The geometric finite model has a nonzero exact cochain killed by projection.
example : coverSheaf.harmonicOneProjection (realize (TwoComponentBoundary.diagonal 1)) = 0 ∧
    realize (TwoComponentBoundary.diagonal 1) ≠ 0 := by
  have hd : rationalCoboundary (fun b => if b then 0 else 1) =
      TwoComponentBoundary.diagonal 1 := by
    ext b
    simp [rationalCoboundary_apply, TwoComponentBoundary.diagonal]
  constructor
  · apply coverSheaf.harmonicOneProjection_of_exact
    refine ⟨realize (fun b => if b then 0 else 1), ?_⟩
    rw [← realize_coboundary, hd]
  · intro hz
    have h := congrArg (fun c : coverSheaf.C1 => c ⟨false, (0 : Fin 1)⟩) hz
    simp [realize_apply, TwoComponentBoundary.diagonal] at h

-- The original signed cover generator survives with its exact normalization.
example : realJump (projectedRealization (TwoComponentBoundary.step 1)) = 1 := by
  change realJump (coverSheaf.harmonicOneProjection (realize (TwoComponentBoundary.step 1))) = 1
  rw [realJump_projection, realJump_realize, TwoComponentBoundary.jump_step]
  norm_num

-- The finite harmonic test does not identify the actual projective-line generator with zero.
example : ¬ coverSheaf.IsExactOneCochain
    ((ProjectiveLineCoverHarmonicComparison.witness ProjectiveLineProductBetti.lineGenerator :
      coverSheaf.C1) - (ProjectiveLineCoverHarmonicComparison.witness 0 : coverSheaf.C1)) := by
  intro certificate
  exact ProjectiveLineProductBetti.lineGenerator_ne_zero
    (coverSheaf.eq_of_exact_harmonicWitness_sub ProjectiveLineCoverHarmonicComparison.witness
      ProjectiveLineCoverHarmonicComparison.witness_injective certificate)

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CircleCoverHarmonicComparison.range_rationalCoboundary,
      `HodgeConjecture.CircleCoverHarmonicComparison.quotientCircleEquiv,
      `HodgeConjecture.CircleCoverHarmonicComparison.quotientCircleEquiv_mk,
      `HodgeConjecture.CircleCoverHarmonicComparison.delta0_apply,
      `HodgeConjecture.CircleCoverHarmonicComparison.realize_coboundary,
      `HodgeConjecture.CircleCoverHarmonicComparison.realJump_projection,
      `HodgeConjecture.CircleCoverHarmonicComparison.witness_injective,
      `HodgeConjecture.CircleCoverHarmonicComparison.witness_componentBoundary,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.quotientBettiEquiv,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.quotientBettiEquiv_mk,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.witness_injective,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.witness_original_boundaries,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.quotientBettiEquiv_step,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.witness_canonicalCycleClass,
      `HodgeConjecture.ProjectiveLineCoverHarmonicComparison.canonicalCycleClass_eq_iff_exact_witness_sub,
      `HodgeConjecture.ProjectiveLineCoverHodgeComparison.pureHodgeStructure,
      `HodgeConjecture.ProjectiveLineCoverHodgeComparison.filtration_eq_geometric_transport,
      `HodgeConjecture.ProjectiveLineCoverHodgeComparison.mem_rationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineCoverHodgeComparison.finiteCycleClass_commutes,
      `HodgeConjecture.ProjectiveLineCoverHodgeComparison.finiteCycleClass_has_hodge_type] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS cover comparison axiom boundary: {declaration}; {axioms.toList}"
end
