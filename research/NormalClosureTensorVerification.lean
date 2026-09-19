import HodgeConjecture.Boundary
import Lean.Util.CollectAxioms

/-!
SP77 regressions for finite tensor evaluation into the marked normal closure.
Run with `lake env lean research/NormalClosureTensorVerification.lean`.

These tests retain the original scalar rings on the generic and integral
maps, identify the generic field as the actual evaluation-kernel quotient,
and verify finite/étale source algebras without asserting that their
integral image is already the whole normalization. The field construction
does not require separability or a characteristic-zero hypothesis.
Every new public declaration has an enforced standard-three-axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open HodgeConjecture.CollisionFoundations
open scoped TensorProduct Classical

noncomputable section

universe u

section FiniteTensorSources

variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]

example (ι : Type u) [Finite ι] [Module.Finite B A] :
    Module.Finite B (⨂[B] _ : ι, A) :=
  piTensorProduct_finite ι

example (ι : Type u) [Finite ι] [Algebra.Etale B A] :
    Algebra.Etale B (⨂[B] _ : ι, A) :=
  piTensorProduct_etale ι

example [Module.Finite B A] : Module.Finite B (⨂[B] _ : PEmpty.{u+1}, A) :=
  piTensorProduct_finite PEmpty

example [Algebra.Etale B A] : Algebra.Etale B (⨂[B] _ : PEmpty.{u+1}, A) :=
  piTensorProduct_etale PEmpty

example [Module.Finite B A] : Module.Finite B (⨂[B] _ : PUnit.{u+1}, A) :=
  piTensorProduct_finite PUnit

example [Algebra.Etale B A] : Algebra.Etale B (⨂[B] _ : PUnit.{u+1}, A) :=
  piTensorProduct_etale PUnit

end FiniteTensorSources

section GenericEvaluation

variable {ι B A S : Type u} [Fintype ι]
variable [CommRing B] [CommRing A] [CommRing S] [Algebra B A] [Algebra B S]
variable (f : ι → A →ₐ[B] S)

example (x : ι → A) :
    piTensorProductEvaluation f (PiTensorProduct.tprod B x) = ∏ i, f i (x i) :=
  piTensorProductEvaluation_tprod f x

example (i : ι) (x : A) :
    piTensorProductEvaluation f (PiTensorProduct.singleAlgHom i x) = f i x :=
  piTensorProductEvaluation_singleAlgHom f i x

example (x y : ⨂[B] _ : ι, A) :
    piTensorProductEvaluation f (x * y) =
      piTensorProductEvaluation f x * piTensorProductEvaluation f y :=
  map_mul (piTensorProductEvaluation f) x y

example (b : B) :
    piTensorProductEvaluation f (algebraMap B (⨂[B] _ : ι, A) b) =
      algebraMap B S b :=
  (piTensorProductEvaluation f).commutes b

end GenericEvaluation

section FieldEvaluation

variable {K L N : Type u} [Field K] [Field L] [Field N]
variable [Algebra K L] [Algebra K N]
variable (D : NormalClosureData K L N)

example : Function.Surjective D.tensorEvaluation := by
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.tensorEvaluation_surjective

example (σ : L →ₐ[K] N) (x : L) :
    D.tensorEvaluation (PiTensorProduct.singleAlgHom σ x) = σ x :=
  D.tensorEvaluation_singleAlgHom σ x

example (x : L) :
    D.tensorEvaluation (PiTensorProduct.singleAlgHom D.embedding x) = D.embedding x :=
  D.tensorEvaluation_singleAlgHom D.embedding x

example : (RingHom.ker D.tensorEvaluation.toRingHom).IsMaximal :=
  D.tensorEvaluation_ker_isMaximal

example : ((⨂[K] _ : L →ₐ[K] N, L) ⧸ RingHom.ker D.tensorEvaluation.toRingHom) ≃ₐ[K] N :=
  D.tensorEvaluationQuotientEquiv

example (x : ⨂[K] _ : L →ₐ[K] N, L) :
    D.tensorEvaluationQuotientEquiv
        (Ideal.Quotient.mk (RingHom.ker D.tensorEvaluation.toRingHom) x) =
      D.tensorEvaluation x :=
  D.tensorEvaluationQuotientEquiv_mk x

example (σ : L →ₐ[K] N) (x : L) :
    D.tensorEvaluationQuotientEquiv
        (Ideal.Quotient.mk (RingHom.ker D.tensorEvaluation.toRingHom)
          (PiTensorProduct.singleAlgHom σ x)) = σ x := by
  rw [D.tensorEvaluationQuotientEquiv_mk, D.tensorEvaluation_singleAlgHom]

example (k : K) :
    D.tensorEvaluationQuotientEquiv
        (algebraMap K ((⨂[K] _ : L →ₐ[K] N, L) ⧸
          RingHom.ker D.tensorEvaluation.toRingHom) k) = algebraMap K N k :=
  D.tensorEvaluationQuotientEquiv.commutes k

end FieldEvaluation

-- A finite extension in positive characteristic constructs its own marked
-- normal closure and its surjective tensor evaluation without separability.
example (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [CharP K 2] :
    Function.Surjective (NormalClosureData.ofAlgebraicClosure K L).tensorEvaluation := by
  fail_if_success have _ : CharZero K := inferInstance
  fail_if_success have _ : Algebra.IsSeparable K L := inferInstance
  exact (NormalClosureData.ofAlgebraicClosure K L).tensorEvaluation_surjective

example (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [CharP K 2] :
    Module.Finite K
      (⨂[K] _ : L →ₐ[K]
        IntermediateField.normalClosure K L (AlgebraicClosure L), L) :=
  piTensorProduct_finite _

section IntegralEvaluation

variable {B K L N : Type u} [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable (D : NormalClosureData K L N)

example (σ : L →ₐ[K] N) (x : normalizedCoordinateRing B L) :
    D.normalizationTensorEvaluation (PiTensorProduct.singleAlgHom σ x) =
      normalizationMap N (σ.restrictScalars B) x :=
  D.normalizationTensorEvaluation_singleAlgHom σ x

example (σ : L →ₐ[K] N) (x : normalizedCoordinateRing B L) :
    ((D.normalizationTensorEvaluation (PiTensorProduct.singleAlgHom σ x) :
      normalizedCoordinateRing B N) : N) = σ (x : L) :=
  D.normalizationTensorEvaluation_coe_singleAlgHom σ x

example (x : (L →ₐ[K] N) → normalizedCoordinateRing B L) :
    ((D.normalizationTensorEvaluation (PiTensorProduct.tprod B x) :
      normalizedCoordinateRing B N) : N) =
      D.tensorEvaluation (PiTensorProduct.tprod K (fun σ => (x σ : L))) :=
  D.normalizationTensorEvaluation_coe_tprod x

example (b : B) :
    D.normalizationTensorEvaluation
        (algebraMap B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) b) =
      algebraMap B (normalizedCoordinateRing B N) b :=
  D.normalizationTensorEvaluation.commutes b

example (b : B) :
    ((D.normalizationTensorEvaluation
        (algebraMap B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) b) :
      normalizedCoordinateRing B N) : N) = algebraMap B N b := by
  rw [D.normalizationTensorEvaluation.commutes]
  rfl

end IntegralEvaluation

section AffineSource

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N] [CommRing A]
variable [Algebra K L] [Algebra K N] [Algebra B L]
variable [Algebra B A] [Algebra A L]
variable [IsScalarTower B A L] [IsFractionRing A L] [IsIntegrallyClosed A]
variable [Module.Finite B A]
variable (D : NormalClosureData K L N)

example : Module.Finite B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Algebra B N := inferInstance
  fail_if_success have _ : Algebra B K := inferInstance
  exact D.normalizationTensor_finite (A := A)

example [Algebra.Etale B A] :
    Algebra.Etale B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) :=
  D.normalizationTensor_etale (A := A)

example [Algebra.Etale B A] :
    Module.Finite B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) ∧
      Algebra.Etale B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) :=
  ⟨D.normalizationTensor_finite (A := A), D.normalizationTensor_etale (A := A)⟩

end AffineSource

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.piTensorProduct_finite,
      `HodgeConjecture.CollisionFoundations.piTensorProduct_etale,
      `HodgeConjecture.CollisionFoundations.piTensorProductEvaluation,
      `HodgeConjecture.CollisionFoundations.piTensorProductEvaluation_tprod,
      `HodgeConjecture.CollisionFoundations.piTensorProductEvaluation_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluation,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluation_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluation_surjective,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluation_ker_isMaximal,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluationQuotientEquiv,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.tensorEvaluationQuotientEquiv_mk,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_coe_singleAlgHom,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_coe_tprod,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensor_finite,
      `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensor_etale] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
