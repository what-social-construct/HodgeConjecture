import HodgeConjecture.Collision.FiberProduct
import HodgeConjecture.Collision.OffDiagonal
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Abstract collision algebras

This file develops the tensor-product collision algebra independently of a
particular polynomial presentation.

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
  CollisionFoundations.SelfFiberProductAlgebra (B := B) (A := A)

/-- Tensor multiplication, dual to the relative diagonal. -/
abbrev collisionMultiplication :
    CollisionAlgebra B A →ₐ[B] A :=
  CollisionFoundations.diagonalMultiplication

/-- Tensor multiplication is surjective, with section `a ↦ 1 ⊗ a`. -/
theorem collisionMultiplication_surjective :
    Function.Surjective
      (collisionMultiplication B A).toRingHom := by
  intro a
  refine ⟨(1 : A) ⊗ₜ[B] a, ?_⟩
  simp [collisionMultiplication]

/--
The ideal `I_{Δ/R_f}` of the relative diagonal in the collision algebra.

Despite the word “obstruction,” this ideal measures whether the collision
space has components beyond the diagonal.  It is distinct from the cokernel
obstruction to algebraically realizing a cohomological projector.
-/
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
`CollisionFoundations.comap_annihilator_map_quotient_eq_colon`.
-/
theorem collisionOffDiagonalIdeal_eq_annihilator :
    collisionOffDiagonalIdeal B A =
      (collisionObstructionIdeal B A).annihilator :=
  rfl

end

end HodgeConjecture
