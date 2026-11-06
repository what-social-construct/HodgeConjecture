module

public import HodgeConjecture.Boundary.Normalization.NormalizationBaseChange
public import HodgeConjecture.Boundary.Normalization.NormalClosureFactor
public import HodgeConjecture.CommutativeAlgebra.UnramifiedIntegralFactor
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

/-!
# The integral factor of normal-closure tensor evaluation

The integral trace and the separability tensor of the actual finite étale
source split its existing evaluation onto the marked normalization. The
selecting idempotent generates the complementary kernel ideal. Localization
at this idempotent then proves étaleness of that same normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct

universe u

namespace NormalClosureData

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N] [CommRing A]
variable [Algebra B K] [IsFractionRing B K] [IsIntegrallyClosed B]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [Algebra B A] [Algebra A L] [IsScalarTower B A L]
variable [IsFractionRing A L] [IsIntegrallyClosed A] [Module.Finite B A]
variable [Algebra.Etale B A]

/-- The integral trace section of the actual tensor evaluation. It is
linear over the base and respects the source action through evaluation. -/
def normalizationTensorSection (D : NormalClosureData K L N) :
    normalizedCoordinateRing B N →ₗ[B]
      (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI := D.normalizationTensor_finite (B := B) (A := A)
  letI := D.normalizationTensor_etale (B := B) (A := A)
  exact unramifiedIntegralSection (B := B) K N (D.normalizationTensorEvaluation (B := B))

/-- The trace section respects multiplication by any source element. -/
theorem normalizationTensorSection_mul (D : NormalClosureData K L N)
    (s : ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L)
    (x : normalizedCoordinateRing B N) :
    D.normalizationTensorSection (B := B) (A := A) (D.normalizationTensorEvaluation s * x) =
      s * D.normalizationTensorSection (B := B) (A := A) x := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI := D.normalizationTensor_finite (B := B) (A := A)
  letI := D.normalizationTensor_etale (B := B) (A := A)
  exact unramifiedIntegralSection_mul (B := B) K N (D.normalizationTensorEvaluation (B := B)) s x

/-- Evaluation after the constructed section is the identity on the
entire existing normal-closure normalization. -/
theorem normalizationTensorSection_rightInverse (D : NormalClosureData K L N)
    (x : normalizedCoordinateRing B N) :
    D.normalizationTensorEvaluation (B := B)
      (D.normalizationTensorSection (B := B) (A := A) x) = x := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI := D.normalizationTensor_finite (B := B) (A := A)
  letI := D.normalizationTensor_etale (B := B) (A := A)
  exact unramifiedIntegralSection_rightInverse (B := B) K N
    (D.normalizationTensorEvaluation (B := B))
    (D.normalizationTensorEvaluation_span (B := B)) x

include A in
/-- The integral evaluation is surjective, with no separately supplied
normal-closure model or normality hypothesis on the tensor source. -/
theorem normalizationTensorEvaluation_surjective (D : NormalClosureData K L N) :
    Function.Surjective (D.normalizationTensorEvaluation (B := B)) :=
  fun x => ⟨D.normalizationTensorSection (B := B) (A := A) x,
    D.normalizationTensorSection_rightInverse (B := B) (A := A) x⟩

/-- The integral selector is the trace section evaluated at one. -/
def normalizationTensorIdempotent (D : NormalClosureData K L N) :
    ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L :=
  D.normalizationTensorSection (B := B) (A := A) 1

/-- The selecting idempotent has value one, annihilates exactly the
evaluation kernel, and its complement generates that kernel. -/
theorem normalizationTensorIdempotent_spec (D : NormalClosureData K L N) :
    IsIdempotentElem (D.normalizationTensorIdempotent (B := B) (A := A)) ∧
      D.normalizationTensorEvaluation (B := B)
        (D.normalizationTensorIdempotent (B := B) (A := A)) = 1 ∧
      (∀ x, D.normalizationTensorIdempotent (B := B) (A := A) * x = 0 ↔
        D.normalizationTensorEvaluation x = 0) ∧
      RingHom.ker (D.normalizationTensorEvaluation (B := B)).toRingHom =
        Ideal.span {1 - D.normalizationTensorIdempotent (B := B) (A := A)} := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI := D.normalizationTensor_finite (B := B) (A := A)
  letI := D.normalizationTensor_etale (B := B) (A := A)
  exact ⟨unramifiedIntegralIdempotent_isIdempotentElem (B := B) K N
      (D.normalizationTensorEvaluation (B := B)) (D.normalizationTensorEvaluation_span (B := B)),
    unramifiedIntegralIdempotent_map (B := B) K N
      (D.normalizationTensorEvaluation (B := B)) (D.normalizationTensorEvaluation_span (B := B)),
    unramifiedIntegralIdempotent_mul_eq_zero_iff (B := B) K N
      (D.normalizationTensorEvaluation (B := B)) (D.normalizationTensorEvaluation_span (B := B)),
    unramifiedIntegralEvaluation_ker_eq_span_one_sub (B := B) K N
      (D.normalizationTensorEvaluation (B := B)) (D.normalizationTensorEvaluation_span (B := B))⟩

/-- Scalar extension sends the integral selector to the previously
constructed canonical generic selector, with the original comparison. -/
theorem normalizationTensorIdempotent_baseChange [Algebra.IsSeparable K L]
    (D : NormalClosureData K L N) :
    D.normalizationTensorBaseChangeEquiv (B := B)
        ((1 : K) ⊗ₜ[B] D.normalizationTensorIdempotent (B := B) (A := A)) =
      D.tensorEvaluationIdempotent := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI := D.normalizationTensor_finite (B := B) (A := A)
  letI := D.normalizationTensor_etale (B := B) (A := A)
  let β := D.normalizationTensorBaseChangeEquiv (B := B)
  let E := D.normalizationTensorIdempotent (B := B) (A := A)
  let F := Algebra.TensorProduct.map (AlgHom.id K K)
    (D.normalizationTensorEvaluation (B := B))
  have hvalue : D.tensorEvaluation (β ((1 : K) ⊗ₜ[B] E)) = 1 := by
    have h := AlgHom.congr_fun (D.normalizationTensorEvaluation_baseChange (B := B))
      ((1 : K) ⊗ₜ[B] E)
    change D.tensorEvaluation (β ((1 : K) ⊗ₜ[B] E)) =
      normalizedCoordinateRingBaseChangeEquiv B K N
        ((1 : K) ⊗ₜ[B] D.normalizationTensorEvaluation E) at h
    rw [(D.normalizationTensorIdempotent_spec (B := B) (A := A)).2.1,
      normalizedCoordinateRingBaseChangeEquiv_tmul] at h
    simpa using h
  apply D.tensorEvaluationIdempotent_unique _ hvalue
  intro x hx
  have hF : F (β.symm x) = 0 := by
    apply (normalizedCoordinateRingBaseChangeEquiv B K N).injective
    rw [map_zero]
    have h := AlgHom.congr_fun (D.normalizationTensorEvaluation_baseChange (B := B))
      (β.symm x)
    change D.tensorEvaluation (β (β.symm x)) =
      normalizedCoordinateRingBaseChangeEquiv B K N (F (β.symm x)) at h
    rw [AlgEquiv.apply_symm_apply, hx] at h
    exact h.symm
  change β ((1 : K) ⊗ₜ[B] E) * x = 0
  rw [← β.apply_symm_apply x, ← map_mul]
  have hmul := unramifiedIntegralIdempotent_baseChange_mul (B := B) K N
    (D.normalizationTensorEvaluation (B := B)) (β.symm x)
  change ((1 : K) ⊗ₜ[B] E) * β.symm x =
    TensorProduct.AlgebraTensorModule.map (LinearMap.id : K →ₗ[K] K)
      (D.normalizationTensorSection (B := B) (A := A)) (F (β.symm x)) at hmul
  rw [hmul, hF]
  let R := TensorProduct.AlgebraTensorModule.map (LinearMap.id : K →ₗ[K] K)
    (D.normalizationTensorSection (B := B) (A := A))
  change β (R 0) = 0
  exact (congrArg β R.toAddMonoidHom.map_zero).trans β.toRingEquiv.toRingHom.map_zero

/-- The complementary-idempotent quotient is the original normalization,
via the actual integral evaluation. -/
def normalizationTensorQuotientEquiv (D : NormalClosureData K L N) :
    ((⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) ⧸
      Ideal.span {1 - D.normalizationTensorIdempotent (B := B) (A := A)}) ≃ₐ[B]
      normalizedCoordinateRing B N :=
  (Ideal.quotientEquivAlgOfEq B
    (D.normalizationTensorIdempotent_spec (B := B) (A := A)).2.2.2.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (D.normalizationTensorEvaluation_surjective (B := B) (A := A)))

/-- The quotient comparison preserves the original evaluator on every
integral tensor element. -/
@[simp]
theorem normalizationTensorQuotientEquiv_mk (D : NormalClosureData K L N)
    (x : ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) :
    D.normalizationTensorQuotientEquiv (B := B) (A := A) (Ideal.Quotient.mk _ x) =
      D.normalizationTensorEvaluation x := rfl

include A in
/-- The normal-closure normalization is finite over the base because it
is the proved quotient of the actual finite tensor source. -/
theorem normalization_finite_of_etaleModel (D : NormalClosureData K L N) :
    Module.Finite B (normalizedCoordinateRing B N) := by
  letI := D.normalizationTensor_finite (B := B) (A := A)
  exact Module.Finite.of_surjective D.normalizationTensorEvaluation.toLinearMap
    (D.normalizationTensorEvaluation_surjective (B := B) (A := A))

include A in
/-- The whole normal-closure normalization is étale: its actual
evaluation identifies it with localization at the integral selector. -/
theorem normalization_etale_of_etaleModel (D : NormalClosureData K L N) :
    Algebra.Etale B (normalizedCoordinateRing B N) := by
  let P := ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L
  let f : P →ₐ[B] normalizedCoordinateRing B N := D.normalizationTensorEvaluation
  letI : Algebra P (normalizedCoordinateRing B N) := f.toRingHom.toAlgebra
  letI : IsScalarTower B P (normalizedCoordinateRing B N) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let e : P := D.normalizationTensorIdempotent (B := B) (A := A)
  letI : IsLocalization.Away e (normalizedCoordinateRing B N) :=
    IsLocalization.away_of_isIdempotentElem
      (D.normalizationTensorIdempotent_spec (B := B) (A := A)).1
      (D.normalizationTensorIdempotent_spec (B := B) (A := A)).2.2.2
      (D.normalizationTensorEvaluation_surjective (B := B) (A := A))
  letI : Algebra.Etale P (normalizedCoordinateRing B N) :=
    Algebra.Etale.of_isLocalizationAway e
  letI : Algebra.Etale B P := D.normalizationTensor_etale (B := B) (A := A)
  exact Algebra.Etale.comp B P (normalizedCoordinateRing B N)

end NormalClosureData

end

end HodgeConjecture.CollisionFoundations
