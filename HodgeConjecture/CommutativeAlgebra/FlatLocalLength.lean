module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.TensorProduct.Quotient

@[expose] public section

/-!
# Principal quotient lengths under flat local base change

The actual quotient by an extended ideal is the tensor base change of the
original quotient. Mathlib's local length formula then gives its length,
including infinite lengths. This is the local calculation used for flat
pullback of principal divisors (Stacks 02M1).
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-- Actual quotient lengths under the given flat local algebra map. -/
theorem length_quotient_map_of_flat (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) =
      Module.length A (A ⧸ I) *
        Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) := by
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq]
  exact IsLocalRing.length_baseChange A B (A ⧸ I)

/-- The principal-quotient specialization retains the original element. -/
theorem length_quotient_span_algebraMap_of_flat (a : A) :
    Module.length B (B ⧸ Ideal.span {algebraMap A B a}) =
      Module.length A (A ⧸ Ideal.span {a}) *
        Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) := by
  have h : (Ideal.span {a}).map (algebraMap A B) =
      Ideal.span {algebraMap A B a} := by rw [Ideal.map_span, Set.image_singleton]
  rw [← h]
  exact length_quotient_map_of_flat A B (Ideal.span {a})

end

end HodgeConjecture.CommutativeAlgebra
