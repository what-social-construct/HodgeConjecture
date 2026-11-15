module

public import HodgeConjecture.Geometry.ProjectiveLineProductAffineChart
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

@[expose] public section

/-!
# Dimension of the affine product chart

The tensor-product coordinate ring of the first affine chart in each
projective-line factor is a polynomial ring in two variables. Thus this
specific affine chart has Krull dimension two over a field. Passing from
this local calculation to codimension of a global fiber carrier requires
identifying its prime in this chart.
-/

set_option autoImplicit false

noncomputable section

open TensorProduct

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- The coordinate ring `k[X] ⊗[k] k[X]` is a two-variable polynomial ring. -/
def projectiveLineAffineProductRingEquiv :
    (Polynomial k ⊗[k] Polynomial k) ≃ₐ[k]
      MvPolynomial (Fin 1 ⊕ Fin 1) k :=
  (Algebra.TensorProduct.congr
      (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm
      (MvPolynomial.uniqueAlgEquiv k (Fin 1)).symm).trans
    (MvPolynomial.tensorEquivSum k (Fin 1) (Fin 1) k)

/-- The actual affine-product coordinate ring has Krull dimension two. -/
theorem projectiveLineAffineProduct_ringKrullDim :
    ringKrullDim (Polynomial k ⊗[k] Polynomial k) = 2 := by
  rw [ringKrullDim_eq_of_ringEquiv
    (projectiveLineAffineProductRingEquiv k).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field]
  norm_num

end AlgebraicGeometry

end
