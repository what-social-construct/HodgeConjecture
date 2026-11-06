module

public import HodgeConjecture.Realization.Betti.SingularDegreeZero
public import HodgeConjecture.Realization.FiberSum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Degree-zero transfer on finite discrete spaces

Transfer sums a singular zero-cocycle over the actual point fiber of a
continuous map. Discreteness guarantees that the resulting zero-cochain
is a cocycle. The operation is constructed on singular cohomology before
any choice of labels or matrix coordinates.
-/

set_option autoImplicit false

namespace HodgeConjecture.SingularDegreeZero

noncomputable section

open Classical
open scoped BigOperators

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Summation over the actual fibers of a finite-domain map. -/
abbrev fiberSum [Fintype X] (f : X → Y) : (X → ℚ) →ₗ[ℚ] (Y → ℚ) :=
  finiteFiberSum ℚ f

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [DiscreteTopology Y] [DiscreteTopology Z]

/-- The degree-zero cohomological transfer, as a sum over actual point fibers. -/
def transfer [Fintype X] (f : C(X, Y)) : H0 X →ₗ[ℚ] H0 Y :=
  (equivFunctions Y).symm.toLinearMap.comp
    ((fiberSum f).comp (eval X).toLinearMap)

@[simp]
theorem eval_transfer [Fintype X] (f : C(X, Y)) (h : H0 X) (y : Y) :
    eval Y (transfer f h) y = ∑ x, if f x = y then eval X h x else 0 := by
  simp [transfer, fiberSum]

/-- Transfer satisfies the degree-zero projection formula for cup product. -/
theorem transfer_projectionFormula [Fintype X] (f : C(X, Y))
    (a : H0 Y) (b : H0 X) :
    transfer f (pullback f a * b) = a * transfer f b := by
  apply (equivFunctions Y).injective
  ext y
  change eval Y (transfer f (pullback f a * b)) y =
    eval Y (a * transfer f b) y
  simp only [eval_transfer, map_mul, Pi.mul_apply, eval_pullback]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = y <;> simp [h]

end

end HodgeConjecture.SingularDegreeZero
