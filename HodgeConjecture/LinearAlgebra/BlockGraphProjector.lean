module

public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Block graph projectors

This file contains the linear-algebra core shared by marked-sheet and Tate-block
graph projectors.  A vector `α : M` determines the projector

`(t, x) ↦ (t, t • α)`

on `R × M`.  It is conjugate to the projector onto the scalar factor by the
lower-triangular shear `(t, x) ↦ (t, x + t • α)`.

There is no geometric content here: the construction only uses the module
structure on `M`.
-/

set_option autoImplicit false

namespace HodgeConjecture

universe u v

namespace BlockGraphProjector

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The linear map from the scalar line sending `t` to `t • α`. -/
def lineMap (α : M) : R →ₗ[R] M :=
  LinearMap.id.smulRight α

/-- The graph projector determined by `α`. -/
def operator (α : M) : Module.End R (R × M) :=
  (LinearMap.fst R R M).prod
    ((lineMap α).comp (LinearMap.fst R R M))

@[simp]
theorem operator_apply (α : M) (t : R) (x : M) :
    operator α (t, x) = (t, t • α) :=
  rfl

/-- Every graph operator is an idempotent endomorphism. -/
theorem operator_isIdempotent (α : M) :
    IsIdempotentElem (operator (R := R) α) := by
  change operator (R := R) α * operator (R := R) α =
    operator (R := R) α
  ext x <;> simp [operator, Module.End.mul_apply]

/-- The standard projector onto the scalar factor. -/
def diagonalOperator : Module.End R (R × M) :=
  (LinearMap.fst R R M).prod 0

@[simp]
theorem diagonalOperator_apply (t : R) (x : M) :
    diagonalOperator (R := R) (M := M) (t, x) = (t, 0) :=
  rfl

/-- The lower-triangular shear carrying the scalar line to the graph of `α`. -/
def shear (α : M) : (R × M) ≃ₗ[R] (R × M) where
  toFun z := (z.1, z.2 + z.1 • α)
  invFun z := (z.1, z.2 - z.1 • α)
  left_inv z := by
    ext <;> simp
  right_inv z := by
    ext <;> simp
  map_add' x y := by
    ext
    · rfl
    · simp only [Prod.fst_add, Prod.snd_add, add_smul]
      abel
  map_smul' c x := by
    ext <;> simp [mul_smul]

@[simp]
theorem shear_apply (α : M) (t : R) (x : M) :
    shear α (t, x) = (t, x + t • α) :=
  rfl

@[simp]
theorem shear_symm_apply (α : M) (t : R) (x : M) :
    (shear α).symm (t, x) = (t, x - t • α) :=
  rfl

/-- In graph-adapted coordinates, the graph projector is diagonal. -/
theorem operator_eq_shear_diagonal_shear_symm (α : M) :
    operator α =
      (shear α).toLinearMap * diagonalOperator (R := R) (M := M) *
        (shear α).symm.toLinearMap := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  simp [Module.End.mul_apply]

/-- Conjugating the diagonal projector by the lower shear gives the graph projector. -/
theorem shear_conj_diagonalOperator (α : M) :
    (shear α).conj (diagonalOperator (R := R) (M := M)) = operator α := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  simp [LinearEquiv.conj_apply]

end BlockGraphProjector

end HodgeConjecture
