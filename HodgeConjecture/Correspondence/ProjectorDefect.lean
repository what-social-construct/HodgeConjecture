import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Group.Idempotent

/-!
# The idempotence defect of a proposed projector

For an element `q` of a ring, the elementary defect `q * q - q` vanishes
exactly when `q` is idempotent.  Keeping this definition below the boundary
and realization layers gives raw closures and compactified graph images one
common API.
-/

set_option autoImplicit false

namespace HodgeConjecture

/-- The elementary multiplicative defect of a proposed projector. -/
def projectorIdempotenceDefect
    {A : Type*} [Ring A] (q : A) : A :=
  q * q - q

/-- Ring homomorphisms preserve the projector idempotence defect. -/
@[simp]
theorem map_projectorIdempotenceDefect
    {A B : Type*} [Ring A] [Ring B]
    (f : A →+* B) (q : A) :
    f (projectorIdempotenceDefect q) =
      projectorIdempotenceDefect (f q) := by
  simp [projectorIdempotenceDefect]

/-- Vanishing of the elementary defect is equivalent to idempotence. -/
theorem projectorIdempotenceDefect_eq_zero_iff
    {A : Type*} [Ring A] (q : A) :
    projectorIdempotenceDefect q = 0 ↔
      IsIdempotentElem q := by
  rw [projectorIdempotenceDefect, sub_eq_zero]
  rfl

/-- An idempotent element has zero elementary defect. -/
theorem projectorIdempotenceDefect_eq_zero
    {A : Type*} [Ring A] {q : A}
    (hq : IsIdempotentElem q) :
    projectorIdempotenceDefect q = 0 :=
  (projectorIdempotenceDefect_eq_zero_iff q).2 hq

end HodgeConjecture
