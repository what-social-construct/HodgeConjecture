import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Trace contraction of a separability tensor

A tensor commuting with the two copies of a finite-dimensional commutative
algebra has the same contraction by trace as its product. In particular,
the trace contraction of a separability tensor is one.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct

universe uK uA

variable (K : Type uK) (A : Type uA) [Field K] [CommRing A] [Algebra K A]

/-- Contract the second factor of an algebra tensor by the algebra trace. -/
def traceContraction : A ⊗[K] A →ₗ[K] A :=
  (TensorProduct.rid K A).toLinearMap.comp
    (TensorProduct.map LinearMap.id (Algebra.trace K A))

@[simp]
theorem traceContraction_tmul (a b : A) :
    traceContraction K A (a ⊗ₜ[K] b) = Algebra.trace K A b • a := by
  simp [traceContraction]

variable {K A} [FiniteDimensional K A]

/-- On a tensor commuting with the two algebra factors, contraction by
trace equals multiplication of the factors. -/
theorem traceContraction_eq_lmul_of_central (t : A ⊗[K] A)
    (hcentral : ∀ x : A, (1 ⊗ₜ[K] x) * t = (x ⊗ₜ[K] 1) * t) :
    traceContraction K A t = Algebra.TensorProduct.lmul' K t := by
  classical
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  have hdual (f : A →ₗ[K] K) :
      f (traceContraction K A t) = f (Algebra.TensorProduct.lmul' K t) := by
    let c : A ⊗[K] A →ₗ[K] A :=
      (TensorProduct.lid K A).toLinearMap.comp (TensorProduct.map f LinearMap.id)
    have hc (x : A) :
        (∑ p ∈ s, f p.1 • (x * p.2)) = ∑ p ∈ s, f (x * p.1) • p.2 := by
      have h := congrArg c (hcentral x)
      simpa [hs, c, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul] using h
    let m : A →ₗ[K] A :=
      ∑ p ∈ s, (f.comp (Algebra.lmul K A p.1)).smulRight p.2
    have hm : Algebra.lmul K A (∑ p ∈ s, f p.1 • p.2) = m := by
      ext x
      simpa [m, Finset.sum_mul, smul_mul_assoc, mul_comm] using hc x
    have htrace :
        (∑ p ∈ s, f p.1 * Algebra.trace K A p.2) = f (∑ p ∈ s, p.1 * p.2) := by
      calc
        _ = Algebra.trace K A (∑ p ∈ s, f p.1 • p.2) := by simp
        _ = LinearMap.trace K A m := by rw [Algebra.trace_apply, hm]
        _ = _ := by simp [m, LinearMap.trace_smulRight]
    simpa [hs, map_sum, traceContraction_tmul, map_smul,
      Algebra.TensorProduct.lmul'_apply_tmul, mul_comm] using htrace
  apply (Module.Free.chooseBasis K A).repr.injective
  ext i
  exact hdual ((Module.Free.chooseBasis K A).coord i)

/-- A separability tensor has trace contraction one. -/
theorem traceContraction_eq_one_of_central (t : A ⊗[K] A)
    (hcentral : ∀ x : A, (1 ⊗ₜ[K] x) * t = (x ⊗ₜ[K] 1) * t)
    (hmul : Algebra.TensorProduct.lmul' K t = 1) :
    traceContraction K A t = 1 :=
  (traceContraction_eq_lmul_of_central t hcentral).trans hmul

/-- Multiplying the second factor of a separability tensor by an element
and contracting by trace recovers that element. -/
theorem traceContraction_one_tmul_mul (t : A ⊗[K] A)
    (hcentral : ∀ x : A, (1 ⊗ₜ[K] x) * t = (x ⊗ₜ[K] 1) * t)
    (hmul : Algebra.TensorProduct.lmul' K t = 1) (x : A) :
    traceContraction K A ((1 ⊗ₜ[K] x) * t) = x := by
  have hleft (z : A ⊗[K] A) :
      traceContraction K A ((x ⊗ₜ[K] 1) * z) = x * traceContraction K A z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add a b ha hb => simp [mul_add, ha, hb]
  rw [hcentral x, hleft, traceContraction_eq_one_of_central t hcentral hmul, mul_one]

end

end HodgeConjecture.CollisionFoundations
