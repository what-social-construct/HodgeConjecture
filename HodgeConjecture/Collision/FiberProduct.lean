module

public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section

/-!
# Self-fiber-product algebra

This locally owned module lets the generic collision algebra evolve toward
arbitrary generically finite morphisms.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open Algebra
open scoped TensorProduct

universe u v

variable {B : Type u} {A : Type v}
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The coordinate algebra of the affine self-fiber product. -/
abbrev SelfFiberProductAlgebra :=
  A ⊗[B] A

/-- Multiplication is dual to the diagonal map into the self-fiber product. -/
def diagonalMultiplication :
    SelfFiberProductAlgebra (B := B) (A := A) →ₐ[B] A :=
  TensorProduct.lmul' B

@[simp]
theorem diagonalMultiplication_tmul (a b : A) :
    diagonalMultiplication (B := B) (A := A) (a ⊗ₜ[B] b) =
      a * b := by
  simp [diagonalMultiplication]

end

end HodgeConjecture.CollisionFoundations
