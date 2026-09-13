import HodgeConjecture.Realization.Chow.MarkedAugmentedRealization

/-!
# Rigidity of a multiplicative residual realization

In a marked augmentation ideal, `q - 1` acts by minus the identity.
Consequently a linear, multiplicative residual realization sends this
class to minus the unit whenever the target unit lies in its image.
Surjectivity suffices. This separates the exact multiplicative bridge
from the broader linear residual interface used by class-coverage targets.
-/

set_option autoImplicit false

namespace HodgeConjecture.MarkedAugmentedAlgebra

noncomputable section

universe u v

variable {A : Type u} [CommRing A] [Algebra ℚ A]
variable (M : MarkedAugmentedAlgebra ℚ A)
variable {B : Type v} [Ring B] [Algebra ℚ B]

/-- The canonical residual class acts by minus the identity on the ideal. -/
theorem residualClass_mul_eq_neg (x : M.Residual) : M.residualClass * x = -x := by
  apply Subtype.ext
  change (M.selector - 1) * (x : A) = -(x : A)
  rw [sub_mul, M.selector_mul_residual, one_mul, zero_sub]

/-- Multiplicativity carries the intrinsic residual action law to the image. -/
theorem generatedClass_mul_image (θ : M.Residual →ₗ[ℚ] B)
    (hMul : ∀ x y, θ (x * y) = θ x * θ y) (x : M.Residual) :
    M.generatedClass θ * θ x = -θ x := by
  rw [generatedClass, ← hMul, M.residualClass_mul_eq_neg, map_neg]

/-- Even without surjectivity, a multiplicative residual image satisfies
the negative-idempotent equation. -/
theorem generatedClass_sq_eq_neg (θ : M.Residual →ₗ[ℚ] B)
    (hMul : ∀ x y, θ (x * y) = θ x * θ y) :
    M.generatedClass θ * M.generatedClass θ = -M.generatedClass θ :=
  M.generatedClass_mul_image θ hMul M.residualClass

/-- Meeting the target unit forces the generated class to be minus that unit. -/
theorem generatedClass_eq_neg_one_of_one_mem_range (θ : M.Residual →ₗ[ℚ] B)
    (hMul : ∀ x y, θ (x * y) = θ x * θ y)
    (hOne : (1 : B) ∈ LinearMap.range θ) :
    M.generatedClass θ = -1 := by
  obtain ⟨x, hx⟩ := hOne
  simpa only [hx, mul_one] using M.generatedClass_mul_image θ hMul x

/-- Surjective multiplicative residual maps cannot vary the generated class:
it is always minus the target unit, even though the interface is nonunital. -/
theorem generatedClass_eq_neg_one_of_surjective (θ : M.Residual →ₗ[ℚ] B)
    (hMul : ∀ x y, θ (x * y) = θ x * θ y)
    (hSurj : Function.Surjective θ) :
    M.generatedClass θ = -1 :=
  M.generatedClass_eq_neg_one_of_one_mem_range θ hMul (hSurj 1)

end

end HodgeConjecture.MarkedAugmentedAlgebra
