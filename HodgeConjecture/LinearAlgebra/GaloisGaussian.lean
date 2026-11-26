module

public import HodgeConjecture.LinearAlgebra.GaloisDescent
public import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# A nontrivial Galois coefficient extension over the rationals

The quadratic algebra with generator squared equal to `-1` is a field of
degree two over `ℚ`. Conjugation supplies an explicit automorphism that moves
its imaginary generator. Consequently, an imaginary coefficient in the
scalar extension of the rational line cannot pass the fixed-tensor descent
gate. These are coefficient fields, independently of any geometric base
change or modular rank computation.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.GaloisDescent.Gaussian

open scoped TensorProduct

/-- Gaussian rational coefficients, with the defining relation `ω² = -1`. -/
abbrev Coefficients := QuadraticAlgebra ℚ (-1) 0

/-- The defining quadratic polynomial has no rational root. -/
instance noRationalRoot : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) :=
  ⟨by
    intro r hr
    have hnonneg := sq_nonneg r
    nlinarith⟩

-- All field-theoretic structures are the existing Mathlib instances.
example : Field Coefficients := inferInstance
example : FiniteDimensional ℚ Coefficients := inferInstance
example : IsGalois ℚ Coefficients := inferInstance

/-- This coefficient extension is genuinely quadratic. -/
theorem finrank_eq_two : Module.finrank ℚ Coefficients = 2 :=
  QuadraticAlgebra.finrank_eq_two (-1 : ℚ) 0

/-- The imaginary generator of the quadratic coefficient field. -/
def omega : Coefficients := QuadraticAlgebra.omega

/-- The explicit nontrivial rational algebra automorphism is conjugation. -/
def conjugation : Coefficients ≃ₐ[ℚ] Coefficients :=
  { starRingAut (R := Coefficients) with
    commutes' := fun r =>
      (starRingAut (R := Coefficients)).toRingHom.map_rat_algebraMap r }

@[simp]
theorem conjugation_apply (z : Coefficients) : conjugation z = star z :=
  rfl

/-- Conjugation changes the sign of the imaginary generator. -/
theorem conjugation_omega_ne : conjugation omega ≠ omega := by
  intro h
  have him := congrArg QuadraticAlgebra.im h
  change (-1 : ℚ) = 1 at him
  norm_num at him

/-- The generator is not fixed by every coefficient-field automorphism. -/
theorem omega_not_fixed :
    ¬ ∀ g : Coefficients ≃ₐ[ℚ] Coefficients, g omega = omega := by
  intro h
  exact conjugation_omega_ne (h conjugation)

/-- An explicitly nonrational coefficient in the extended rational line. -/
def imaginaryTensor : Coefficients ⊗[ℚ] ℚ := omega ⊗ₜ[ℚ] (1 : ℚ)

/-- The descent gate rejects the imaginary coefficient already on the rational line. -/
theorem imaginaryTensor_not_fixed :
    ¬ ∀ g : Coefficients ≃ₐ[ℚ] Coefficients,
      scalarAction g imaginaryTensor = imaginaryTensor := by
  intro hfixed
  have h := congrArg (TensorProduct.rid ℚ Coefficients) (hfixed conjugation)
  apply conjugation_omega_ne
  simpa only [imaginaryTensor, scalarAction_tmul, TensorProduct.rid_tmul, one_smul] using h

/-- The rejected tensor cannot be supplied by a rational scalar. -/
theorem imaginaryTensor_not_in_range :
    imaginaryTensor ∉ Set.range (tensorInclude (K := ℚ) (N := Coefficients) (V := ℚ)) := by
  intro h
  exact imaginaryTensor_not_fixed ((mem_range_tensorInclude_iff_fixed imaginaryTensor).mp h)

end HodgeConjecture.GaloisDescent.Gaussian

end
