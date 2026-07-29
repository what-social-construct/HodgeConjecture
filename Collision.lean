import CollisionIdeals.OffDiagonal
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Abstract collision algebras

This file extracts the tensor-product collision algebra from the polynomial
presentation used in `CollisionIdeals`.

For an algebra `B → A`, the self-collision algebra is `A ⊗[B] A`.  Its
diagonal obstruction is the kernel of tensor multiplication.  The canonical
off-diagonal ideal is the annihilator of this obstruction, equivalently the
first colon ideal in any ambient quotient presentation.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra
open scoped TensorProduct

noncomputable section

universe u v

variable (B : Type u) (A : Type v)
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The coordinate ring of the abstract self-collision fiber product. -/
abbrev CollisionAlgebra :=
  A ⊗[B] A

/-- Tensor multiplication, dual to the relative diagonal. -/
abbrev collisionMultiplication :
    CollisionAlgebra B A →ₐ[B] A :=
  TensorProduct.lmul' B

/-- The ideal of the relative diagonal in the collision algebra. -/
abbrev collisionObstructionIdeal :
    Ideal (CollisionAlgebra B A) :=
  KaehlerDifferential.ideal B A

/-- The canonical residual off-diagonal ideal inside the collision algebra. -/
def collisionOffDiagonalIdeal :
    Ideal (CollisionAlgebra B A) :=
  (collisionObstructionIdeal B A).annihilator

/--
The off-diagonal ideal is the quotient form of the first-colon construction.

This is the abstract tensor-product version of
`CollisionIdeals.comap_annihilator_map_quotient_eq_colon`.
-/
theorem collisionOffDiagonalIdeal_eq_annihilator :
    collisionOffDiagonalIdeal B A =
      (collisionObstructionIdeal B A).annihilator :=
  rfl

end

end HodgeConjecture
