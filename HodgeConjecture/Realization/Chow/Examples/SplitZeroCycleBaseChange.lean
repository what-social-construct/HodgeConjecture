module

public import HodgeConjecture.Realization.Chow.Examples.SplitZeroCycles
public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

/-!
# Rational scalar extension of split zero-cycles

The rational cycle module on the actual integral closed subschemes is the
extension of scalars of the integral cycle module. Its canonical equivalence
sends a pure tensor `q ⊗ z` to `q` times the coefficient extension of `z`.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

namespace SplitZeroCycles

open TensorProduct

variable (K : Type u) [Field K] (I : Type u) [Finite I]

/-- Rational zero-cycles are integral zero-cycles tensored with `ℚ`. -/
def rationalizationEquiv :
    (ℚ ⊗[ℤ] Cycles K I ℤ) ≃ₗ[ℚ] Cycles K I ℚ := by
  classical
  letI := Fintype.ofFinite I
  exact (LinearEquiv.baseChange ℤ ℚ _ _ (coordinates K I ℤ)).trans
    ((TensorProduct.piScalarRight ℤ ℚ ℚ I).trans (coordinates K I ℚ).symm)

@[simp]
theorem rationalizationEquiv_tmul (q : ℚ) (z : Cycles K I ℤ) :
    rationalizationEquiv K I (q ⊗ₜ[ℤ] z) = q • rationalize K I z := by
  apply (coordinates K I ℚ).injective
  simp only [rationalizationEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    LinearEquiv.apply_symm_apply, map_smul]
  ext i
  simp [mul_comm]

@[simp]
theorem rationalizationEquiv_one_tmul (z : Cycles K I ℤ) :
    rationalizationEquiv K I (1 ⊗ₜ[ℤ] z) = rationalize K I z := by
  simp

@[simp]
theorem rationalizationEquiv_tmul_pointCycle (q : ℚ) (i : I) :
    rationalizationEquiv K I (q ⊗ₜ[ℤ] pointCycle K I ℤ i) =
      q • pointCycle K I ℚ i := by
  simp

end SplitZeroCycles

end

end HodgeConjecture
