import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FinCases

/-!
# Diagnostic: a full matrix correspondence algebra cannot restrict to sheets

The full two-by-two rational matrix algebra admits no unital ring map to a
nontrivial commutative ring. In particular, it admits no rational algebra map
to a nonempty pointwise rational sheet algebra.

This is a diagnostic theorem, not a claim that every correspondence algebra
in the project is a full matrix algebra. An extension interface targeting a
commutative sheet algebra cannot be instantiated with the full matrix algebra;
one must choose an appropriate smaller source, retain a noncommutative generic
correspondence target, or compare the chosen idempotents through the universal
one-idempotent algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture.MatrixRestrictionObstruction

private def matrixUnit (i j : Fin 2) : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.single i j 1

private theorem matrixUnit_mul_same (i j k : Fin 2) :
    matrixUnit i j * matrixUnit j k = matrixUnit i k := by
  simp [matrixUnit]

private theorem matrixUnit_diag_mul_diag :
    matrixUnit 0 0 * matrixUnit 1 1 = 0 := by
  simp [matrixUnit, Matrix.single_mul_single_of_ne]

private theorem matrixUnit_diag_sum :
    matrixUnit 0 0 + matrixUnit 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixUnit, Matrix.single]

/-- A nontrivial commutative target cannot receive a unital ring homomorphism
from the full rational two-by-two matrix algebra. -/
theorem no_ringHom_to_commutative
    (C : Type*) [CommRing C] [Nontrivial C]
    (f : Matrix (Fin 2) (Fin 2) ℚ →+* C) : False := by
  have hdiag : f (matrixUnit 0 0) = f (matrixUnit 1 1) := by
    calc
      f (matrixUnit 0 0) =
          f (matrixUnit 0 1) * f (matrixUnit 1 0) := by
        rw [← map_mul, matrixUnit_mul_same]
      _ = f (matrixUnit 1 0) * f (matrixUnit 0 1) := mul_comm _ _
      _ = f (matrixUnit 1 1) := by
        rw [← map_mul, matrixUnit_mul_same]
  have hzero : f (matrixUnit 0 0) = 0 := by
    calc
      f (matrixUnit 0 0) =
          f (matrixUnit 0 0) * f (matrixUnit 0 0) := by
        rw [← map_mul, matrixUnit_mul_same]
      _ = f (matrixUnit 0 0) * f (matrixUnit 1 1) := by rw [hdiag]
      _ = 0 := by rw [← map_mul, matrixUnit_diag_mul_diag, map_zero]
  have hone : (1 : C) = 0 := by
    calc
      (1 : C) = f (matrixUnit 0 0 + matrixUnit 1 1) := by
        rw [matrixUnit_diag_sum, map_one]
      _ = 0 := by rw [map_add, ← hdiag, hzero, zero_add]
  exact one_ne_zero hone

/-- In particular, the full two-by-two matrix algebra has no rational
algebra homomorphism to a nontrivial commutative rational algebra. -/
theorem no_algHom_to_commutative
    (C : Type*) [CommRing C] [Algebra ℚ C] [Nontrivial C]
    (f : Matrix (Fin 2) (Fin 2) ℚ →ₐ[ℚ] C) : False :=
  no_ringHom_to_commutative C f.toRingHom

/-- A nonempty pointwise sheet algebra is one such forbidden target. -/
theorem no_algHom_to_pointwise_sheets
    (S : Type*) [Nonempty S]
    (f : Matrix (Fin 2) (Fin 2) ℚ →ₐ[ℚ] (S → ℚ)) : False :=
  no_algHom_to_commutative (S → ℚ) f

/-- The one-sheet special case is already impossible. -/
theorem no_algHom_to_rationals
    (f : Matrix (Fin 2) (Fin 2) ℚ →ₐ[ℚ] ℚ) : False :=
  no_algHom_to_commutative ℚ f

end HodgeConjecture.MatrixRestrictionObstruction
