import HodgeConjecture.Boundary.Normalization.NormalClosureFactor
import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import HodgeConjecture.Boundary.Normalization.NormalizationBaseChange
import Lean.Util.CollectAxioms

/-!
SP79 regressions for the factor selected by the original tensor evaluation.
Run with `lake env lean research/NormalClosureFactorVerification.lean`.

The generic result retains an arbitrary commutative scalar ring and independent
universes. Concrete field and two-factor examples test the selecting element,
including the case where the complementary product has no factors. The marked
normal-closure tests retain the original evaluation as the first projection.
Actual finite dominant formally unramified morphisms supply separability with
their actual function-field scalar map. Base-change tests transport the element
only to the generic base change, not to the integral tensor algebra itself.
Every new public declaration has an enforced standard-three-axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open HodgeConjecture.CollisionFoundations
open scoped TensorProduct Classical

noncomputable section

universe uK uP uN u

section GenericFieldQuotient

variable {K : Type uK} {P : Type uP} {N : Type uN}
variable [CommRing K] [CommRing P] [Field N]
variable [Algebra K P] [Algebra K N] [IsArtinianRing P] [IsReduced P]
variable (f : P →ₐ[K] N) (hf : Function.Surjective f)

example : (AlgHom.fst K N _).comp (fieldQuotientProductEquiv f hf).toAlgHom = f :=
  fst_comp_fieldQuotientProductEquiv f hf

example (x : P) : (fieldQuotientProductEquiv f hf x).1 = f x :=
  fieldQuotientProductEquiv_fst f hf x

example (n : N) : f ((fieldQuotientProductEquiv f hf).symm (n, 0)) = n := by
  rw [← fieldQuotientProductEquiv_fst f hf, AlgEquiv.apply_symm_apply]

example : IsIdempotentElem (fieldQuotientIdempotent f hf) :=
  fieldQuotientIdempotent_isIdempotentElem f hf

example : f (fieldQuotientIdempotent f hf) = 1 :=
  fieldQuotientIdempotent_map f hf

example (x : P) : fieldQuotientIdempotent f hf * x = 0 ↔ f x = 0 :=
  fieldQuotientIdempotent_mul_eq_zero_iff f hf x

example : RingHom.ker f.toRingHom = Ideal.span {1 - fieldQuotientIdempotent f hf} :=
  fieldQuotient_ker_eq_span_one_sub f hf

example (e : P) (he : f e = 1) (hker : ∀ x, f x = 0 → e * x = 0) :
    e = fieldQuotientIdempotent f hf :=
  fieldQuotientIdempotent_unique f hf e he hker

end GenericFieldQuotient

-- No nonzero-complement premise excludes the identity quotient of a field.
example (K : Type uK) (N : Type uN) [CommRing K] [Field N] [Algebra K N] :
    fieldQuotientIdempotent (AlgHom.id K N) Function.surjective_id = 1 := by
  symm
  apply fieldQuotientIdempotent_unique (AlgHom.id K N) Function.surjective_id
  · rfl
  · intro x hx
    simpa using hx

example : fieldQuotientIdempotent (AlgHom.fst ℚ ℚ ℚ)
    (fun q => ⟨(q, 0), rfl⟩) = (1, 0) := by
  symm
  apply fieldQuotientIdempotent_unique (AlgHom.fst ℚ ℚ ℚ) (fun q => ⟨(q, 0), rfl⟩)
  · rfl
  · rintro ⟨a, b⟩ ha
    change a = 0 at ha
    simp [Prod.ext_iff, ha]

example : fieldQuotientIdempotent (AlgHom.snd ℚ ℚ ℚ)
    (fun q => ⟨(0, q), rfl⟩) = (0, 1) := by
  symm
  apply fieldQuotientIdempotent_unique (AlgHom.snd ℚ ℚ ℚ) (fun q => ⟨(0, q), rfl⟩)
  · rfl
  · rintro ⟨a, b⟩ hb
    change b = 0 at hb
    simp [Prod.ext_iff, hb]

section MarkedNormalClosure

variable {K L N : Type u} [Field K] [Field L] [Field N]
variable [Algebra K L] [Algebra K N] (D : NormalClosureData K L N)

example : Module.Finite K (⨂[K] _ : L →ₐ[K] N, L) := by
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.tensorSource_finite

variable [Algebra.IsSeparable K L]

example : Algebra.Etale K (⨂[K] _ : L →ₐ[K] N, L) := by
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.tensorSource_etale

example : (AlgHom.fst K N _).comp D.tensorEvaluationProductEquiv.toAlgHom =
    D.tensorEvaluation :=
  D.fst_comp_tensorEvaluationProductEquiv

example (x : ⨂[K] _ : L →ₐ[K] N, L) :
    (D.tensorEvaluationProductEquiv x).1 = D.tensorEvaluation x :=
  AlgHom.congr_fun D.fst_comp_tensorEvaluationProductEquiv x

example : IsIdempotentElem D.tensorEvaluationIdempotent ∧
    D.tensorEvaluation D.tensorEvaluationIdempotent = 1 ∧
    (∀ x, D.tensorEvaluationIdempotent * x = 0 ↔ D.tensorEvaluation x = 0) ∧
    RingHom.ker D.tensorEvaluation.toRingHom =
      Ideal.span {1 - D.tensorEvaluationIdempotent} :=
  D.tensorEvaluationIdempotent_spec

example : RingHom.ker D.tensorEvaluation.toRingHom =
    Ideal.span {1 - D.tensorEvaluationIdempotent} :=
  D.tensorEvaluationIdempotent_spec.2.2.2

example (e : ⨂[K] _ : L →ₐ[K] N, L) (he : D.tensorEvaluation e = 1)
    (hker : ∀ x, D.tensorEvaluation x = 0 → e * x = 0) :
    e = D.tensorEvaluationIdempotent :=
  D.tensorEvaluationIdempotent_unique e he hker

example : D.tensorEvaluationProductEquiv D.tensorEvaluationIdempotent = (1, 0) :=
  D.tensorEvaluationProductEquiv.apply_symm_apply (1, 0)

end MarkedNormalClosure

section ActualFunctionFields

open AlgebraicGeometry CategoryTheory HodgeConjecture.SchemeCycles

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Module.Finite X.functionField
      (⨂[X.functionField] _ : Y.functionField →ₐ[X.functionField]
        IntermediateField.normalClosure X.functionField Y.functionField
          (AlgebraicClosure Y.functionField), Y.functionField) := by
  fail_if_success have _ : FormallyUnramified p := inferInstance
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  exact (functionFieldNormalClosureData p).tensorSource_finite

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.Etale X.functionField
      (⨂[X.functionField] _ : Y.functionField →ₐ[X.functionField]
        IntermediateField.normalClosure X.functionField Y.functionField
          (AlgebraicClosure Y.functionField), Y.functionField) := by
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : IsEtale p := inferInstance
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  exact (functionFieldNormalClosureData p).tensorSource_etale

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    letI := functionFieldMapOfDominant_isSeparable p
    let D := functionFieldNormalClosureData p
    D.tensorEvaluation D.tensorEvaluationIdempotent = 1 := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  exact (functionFieldNormalClosureData p).tensorEvaluationIdempotent_spec.2.1

example [FormallyUnramified p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    letI := functionFieldMapOfDominant_isSeparable p
    let D := functionFieldNormalClosureData p
    RingHom.ker D.tensorEvaluation.toRingHom =
      Ideal.span {1 - D.tensorEvaluationIdempotent} := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  exact (functionFieldNormalClosureData p).tensorEvaluationIdempotent_spec.2.2.2

end ActualFunctionFields

section GenericBaseChange

variable {B K L N : Type u} [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B L]
variable [IsScalarTower B K L] [Algebra.IsSeparable K L]
variable (D : NormalClosureData K L N)

example : IsIdempotentElem ((D.normalizationTensorBaseChangeEquiv (B := B)).symm
    D.tensorEvaluationIdempotent) :=
  D.tensorEvaluationIdempotent_spec.1.map (D.normalizationTensorBaseChangeEquiv (B := B)).symm

example :
    (D.tensorEvaluation.comp (D.normalizationTensorBaseChangeEquiv (B := B)).toAlgHom)
      ((D.normalizationTensorBaseChangeEquiv (B := B)).symm D.tensorEvaluationIdempotent) = 1 := by
  change D.tensorEvaluation ((D.normalizationTensorBaseChangeEquiv (B := B))
    ((D.normalizationTensorBaseChangeEquiv (B := B)).symm D.tensorEvaluationIdempotent)) = 1
  rw [AlgEquiv.apply_symm_apply]
  exact D.tensorEvaluationIdempotent_spec.2.1

end GenericBaseChange

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.fieldQuotientProductEquiv,
      `HodgeConjecture.CollisionFoundations.fieldQuotientProductEquiv_fst,
      `HodgeConjecture.CollisionFoundations.fst_comp_fieldQuotientProductEquiv,
      `HodgeConjecture.CollisionFoundations.fieldQuotientIdempotent,
      `HodgeConjecture.CollisionFoundations.fieldQuotientIdempotent_isIdempotentElem,
      `HodgeConjecture.CollisionFoundations.fieldQuotientIdempotent_map,
      `HodgeConjecture.CollisionFoundations.fieldQuotientIdempotent_mul_eq_zero_iff,
      `HodgeConjecture.CollisionFoundations.fieldQuotientIdempotent_unique,
      `HodgeConjecture.CollisionFoundations.fieldQuotient_ker_eq_span_one_sub,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorSource_finite,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorSource_etale,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluationProductEquiv,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.fst_comp_tensorEvaluationProductEquiv,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluationIdempotent,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluationIdempotent_spec,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluationIdempotent_unique] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
