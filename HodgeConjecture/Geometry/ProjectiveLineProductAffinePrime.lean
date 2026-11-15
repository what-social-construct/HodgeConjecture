module

public import HodgeConjecture.Geometry.ProjectiveLineProductAffineDimension
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

@[expose] public section

/-!
# A height-one coordinate prime in the affine product chart

In the two-variable polynomial ring identified with the affine product
chart, the first coordinate variable generates a prime ideal of height one.
Relating this prime to the product's zero-fiber generic point is a separate
geometric identification.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The first variable in the two-variable affine chart generates a
height-one ideal. -/
theorem projectiveLineAffineProduct_firstVariable_height_one :
    (Ideal.span {(MvPolynomial.X (Sum.inl (0 : Fin 1)) :
      MvPolynomial (Fin 1 ⊕ Fin 1) k)}).height = 1 := by
  have hp : Prime (MvPolynomial.X (Sum.inl (0 : Fin 1)) :
      MvPolynomial (Fin 1 ⊕ Fin 1) k) :=
    MvPolynomial.X_prime
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit

/-- The second variable in the same affine chart also generates a
height-one ideal. -/
theorem projectiveLineAffineProduct_secondVariable_height_one :
    (Ideal.span {(MvPolynomial.X (Sum.inr (0 : Fin 1)) :
      MvPolynomial (Fin 1 ⊕ Fin 1) k)}).height = 1 := by
  have hp : Prime (MvPolynomial.X (Sum.inr (0 : Fin 1)) :
      MvPolynomial (Fin 1 ⊕ Fin 1) k) :=
    MvPolynomial.X_prime
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit

end AlgebraicGeometry

end
