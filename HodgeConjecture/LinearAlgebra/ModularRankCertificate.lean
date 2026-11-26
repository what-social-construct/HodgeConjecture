module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Exact rational rank certificates checked modulo a prime

The executable checker binds an integer matrix to a supplied rational matrix
by an exact denominator-clearing equation, and checks a right inverse modulo
a prime. A nonzero modular determinant certifies a nonzero integer determinant;
this direction requires no bound on the integer entries. Modular equality by
itself is not used to infer rational equality: the binding equation is checked
over ℚ. Only the cleared integer matrix is reduced modulo the prime.

The first certificate uses a square family of selected columns. It proves
full rank for that family, not probabilistic batching or SNARK soundness.
-/

set_option autoImplicit false

namespace HodgeConjecture.ModularRankCertificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite arithmetic data, with the inverse typed over its declared modulus. -/
structure Certificate (ι : Type*) where
  denominator : ℤ
  integerMatrix : Matrix ι ι ℤ
  modulus : ℕ
  modularInverse : Matrix ι ι (ZMod modulus)

/-- All arithmetic gates are mandatory, including exact rational binding. -/
def check (A : Matrix ι ι ℚ) (C : Certificate ι) : Bool :=
  decide (C.denominator ≠ 0) &&
  decide (C.integerMatrix.map (fun z : ℤ => (z : ℚ)) = (C.denominator : ℚ) • A) &&
  decide C.modulus.Prime &&
  decide (C.integerMatrix.map (fun z : ℤ => (z : ZMod C.modulus)) * C.modularInverse = 1)

theorem check_eq_true_iff (A : Matrix ι ι ℚ) (C : Certificate ι) :
    check A C = true ↔
      C.denominator ≠ 0 ∧
      C.integerMatrix.map (fun z : ℤ => (z : ℚ)) = (C.denominator : ℚ) • A ∧
      C.modulus.Prime ∧
      C.integerMatrix.map (fun z : ℤ => (z : ZMod C.modulus)) * C.modularInverse = 1 := by
  simp only [check, Bool.and_eq_true_iff, decide_eq_true_eq]
  tauto

theorem integer_det_ne_zero_of_check (A : Matrix ι ι ℚ) (C : Certificate ι)
    (accepted : check A C = true) : C.integerMatrix.det ≠ 0 := by
  obtain ⟨_, _, prime, inverse⟩ := (check_eq_true_iff A C).mp accepted
  haveI : Fact C.modulus.Prime := ⟨prime⟩
  have hmod := Matrix.det_ne_zero_of_right_inverse inverse
  intro hzero
  apply hmod
  rw [← Int.cast_det, hzero, Int.cast_zero]

theorem rational_det_ne_zero_of_check (A : Matrix ι ι ℚ) (C : Certificate ι)
    (accepted : check A C = true) :
    (C.integerMatrix.map (fun z : ℤ => (z : ℚ))).det ≠ 0 := by
  rw [← Int.cast_det]
  exact_mod_cast integer_det_ne_zero_of_check A C accepted

/-- Acceptance certifies full rational rank of the exact bound matrix. -/
theorem mulVec_surjective_of_check (A : Matrix ι ι ℚ) (C : Certificate ι)
    (accepted : check A C = true) : Function.Surjective A.mulVec := by
  have hunit : IsUnit (C.integerMatrix.map (fun z : ℤ => (z : ℚ))) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (rational_det_ne_zero_of_check A C accepted))
  have honto := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  have binding := ((check_eq_true_iff A C).mp accepted).2.1
  intro y
  obtain ⟨v, hv⟩ := honto y
  refine ⟨(C.denominator : ℚ) • v, ?_⟩
  rw [binding, Matrix.smul_mulVec] at hv
  simpa only [Matrix.mulVec_smul] using hv

end HodgeConjecture.ModularRankCertificate
