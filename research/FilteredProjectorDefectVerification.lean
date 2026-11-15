module

public import HodgeConjecture.Inputs.ChowLocalization
public import HodgeConjecture.LinearAlgebra.UniversalIdempotentAlgebra
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The polynomial control is a raw lift of the zero projector under evaluation
at zero, with a nonzero defect, a strictly growing first filtration step,
and zero annihilator. It distinguishes open restriction from localization
in the polynomial action parameter. The positive control reuses the
existing universal selector, without rebuilding a projector.
-/

set_option autoImplicit false

noncomputable section

namespace FilteredProjectorDefectVerification

open HodgeConjecture Polynomial ProjectorDefectModule

/-- A raw closure with an honest nonzero defect in its original algebra. -/
def polynomialClosure : AlgebraProjectorClosure ℚ ℚ[X] 0 where
  genericProjector_isIdempotent := by simp [IsIdempotentElem]
  restriction := aeval (0 : ℚ)
  Closure := Unit
  closureClass := fun _ ↦ X
  closureClass_restricts := by intro _; simp

theorem polynomialDefect_ne_zero : projectorIdempotenceDefect (X : ℚ[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 2) h
  norm_num [projectorIdempotenceDefect, Polynomial.coeff_X_mul, Polynomial.coeff_X] at hc

theorem polynomialDetector_nonzero : ¬ Subsingleton (polynomialClosure.DefectModule ()) := by
  change ¬ Subsingleton (Carrier (X : ℚ[X]))
  rw [subsingleton_iff_defect_eq_zero]
  exact polynomialDefect_ne_zero

example (z : polynomialClosure.DefectModule ()) :
    polynomialClosure.restriction (polynomialClosure.defectEmbedding () z) = 0 :=
  polynomialClosure.restriction_defectEmbedding () z

/-- The polynomial-action filtration is not a disguised constant filtration. -/
theorem firstStep_not_mem_zero :
    presentation (X : ℚ[X]) X ∉ filtration (X : ℚ[X]) 0 := by
  rw [filtration_zero, Submodule.mem_span_singleton]
  rintro ⟨a, ha⟩
  have he := congrArg (embedding (X : ℚ[X])) ha
  rw [map_smul, embedding_generator, embedding_presentation, aeval_X] at he
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 3) he
  norm_num [projectorIdempotenceDefect, mul_sub, Polynomial.coeff_X_mul,
    Polynomial.coeff_X] at hc

theorem firstStep_mem_one :
    presentation (X : ℚ[X]) X ∈ filtration (X : ℚ[X]) 1 := by
  exact (mem_filtration _ _ _).mpr ⟨X, by simp, rfl⟩

theorem polynomialFiltration_strict :
    filtration (X : ℚ[X]) 0 < filtration (X : ℚ[X]) 1 := by
  refine lt_of_le_of_ne (filtration_monotone _ (by decide : 0 ≤ 1)) ?_
  intro h
  exact firstStep_not_mem_zero (h ▸ firstStep_mem_one)

/-- Restriction-zero does not even imply torsion for the polynomial-action parameter. -/
theorem polynomialAnnihilator_eq_bot :
    Module.annihilator ℚ[X] (Carrier (X : ℚ[X])) = ⊥ := by
  ext p
  rw [mem_annihilator_iff, Ideal.mem_bot]
  simp [polynomialDefect_ne_zero]

/-- The old product-algebra boundary control also has a nonzero cyclic detector. -/
theorem productDetector_nonzero : ¬ Subsingleton (Carrier ((1, 2) : ℚ × ℚ)) := by
  rw [subsingleton_iff_defect_eq_zero]
  norm_num [projectorIdempotenceDefect, Prod.ext_iff]

/-- A nonzero parameter relation can annihilate a nonzero detector. -/
theorem productDetector_torsion :
    X - C 2 ∈ Module.annihilator ℚ[X] (Carrier ((1, 2) : ℚ × ℚ)) := by
  rw [mem_annihilator_iff]
  norm_num [projectorIdempotenceDefect, Algebra.algebraMap_eq_smul_one, Prod.ext_iff]

example : (X - C 2 : ℚ[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff 1) h
  norm_num at hc

example : Subsingleton
    (Carrier (UniversalIdempotentAlgebra.selector : UniversalIdempotentAlgebra ℚ)) :=
  (subsingleton_iff_isIdempotent _).mpr UniversalIdempotentAlgebra.selector_isIdempotent

/-- The construction also accepts the native noncommutative endomorphism algebra. -/
example (q : Module.End ℚ (ℚ × ℚ)) : Module.FinitePresentation ℚ[X] (Carrier q) :=
  inferInstance

example (q : Module.End ℚ (ℚ × ℚ)) (n : ℕ) : Module.Finite ℚ (filtration q n) :=
  inferInstance

instance controlLocalization : ChowLocalizationHypotheses
    (LinearMap.ker polynomialClosure.restriction.toLinearMap).subtype
    polynomialClosure.restriction.toLinearMap where
  range_eq_ker := Submodule.range_subtype _
  restriction_surjective := by
    intro a
    exact ⟨C a, by simp [polynomialClosure]⟩

example (n : ℕ) :
    (polynomialClosure.defectFiltration () n).map (polynomialClosure.defectEmbedding ()) ≤
      LinearMap.range (LinearMap.ker polynomialClosure.restriction.toLinearMap).subtype :=
  ChowLocalization.defectFiltration_map_le_range _ polynomialClosure () n

end FilteredProjectorDefectVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectorDefectModule.submodule,
      `HodgeConjecture.ProjectorDefectModule.embedding_injective,
      `HodgeConjecture.ProjectorDefectModule.embedding_generator,
      `HodgeConjecture.ProjectorDefectModule.presentation_surjective,
      `HodgeConjecture.ProjectorDefectModule.embedding_presentation,
      `HodgeConjecture.ProjectorDefectModule.finite,
      `HodgeConjecture.ProjectorDefectModule.finitePresentation,
      `HodgeConjecture.ProjectorDefectModule.subsingleton_iff_defect_eq_zero,
      `HodgeConjecture.ProjectorDefectModule.subsingleton_iff_isIdempotent,
      `HodgeConjecture.ProjectorDefectModule.mem_annihilator_iff,
      `HodgeConjecture.ProjectorDefectModule.presentation_ker,
      `HodgeConjecture.ProjectorDefectModule.filtration_eq_span,
      `HodgeConjecture.ProjectorDefectModule.filtration_fg,
      `HodgeConjecture.ProjectorDefectModule.filtration_exhaustive,
      `HodgeConjecture.ProjectorDefectModule.smul_mem_filtration,
      `HodgeConjecture.ProjectorDefectModule.polynomialDegreeFiltration,
      `HodgeConjecture.ProjectorDefectModule.isModuleFiltration,
      `HodgeConjecture.ProjectorDefectModule.filtration_eq_bot_iff,
      `HodgeConjecture.AlgebraProjectorClosure.defectModule_detects,
      `HodgeConjecture.AlgebraProjectorClosure.restriction_defectEmbedding,
      `HodgeConjecture.AlgebraProjectorClosure.defectFiltration_map_restriction,
      `HodgeConjecture.AlgebraProjectorClosure.zeroDefectWitness,
      `HodgeConjecture.ChowLocalization.defectModule_embedding_mem_range,
      `HodgeConjecture.ChowLocalization.defectFiltration_map_le_range,
      `FilteredProjectorDefectVerification.polynomialDefect_ne_zero,
      `FilteredProjectorDefectVerification.polynomialDetector_nonzero,
      `FilteredProjectorDefectVerification.polynomialFiltration_strict,
      `FilteredProjectorDefectVerification.polynomialAnnihilator_eq_bot,
      `FilteredProjectorDefectVerification.productDetector_nonzero,
      `FilteredProjectorDefectVerification.productDetector_torsion] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
