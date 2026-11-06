module

public import HodgeConjecture.Cycles.LocalOrder
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-!
# A computed nonzero signed order

For the actual fraction-ring structure `ℤ → ℚ`, the principal quotient
`ℤ / (2)` is a simple `ℤ`-module, hence has length one. Consequently the
existing signed order of `2` is `1`, and the order of its inverse is `-1`.
These values are proved from the quotient, not assumed as normalization.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles.Examples

noncomputable section

/-- The actual integer quotient by `(2)` has length one. -/
theorem int_two_quotient_length :
    Module.length ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) = 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  letI : IsSimpleModule ℤ (ℤ ⧸ Ideal.span {(2 : ℤ)}) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact Module.length_eq_one _ _

/-- The length-based order of `2` in the actual fraction field is one. -/
theorem localOrder_int_two :
    localOrder ℤ (Units.mk0 (2 : ℚ) two_ne_zero) = 1 := by
  simpa [int_two_quotient_length] using
    localOrder_algebraMap (K := ℚ) ℤ (2 : ℤ) two_ne_zero

/-- The actual inverse rational function has strictly negative order. -/
theorem localOrder_int_two_inv :
    localOrder ℤ (Units.mk0 (2 : ℚ) two_ne_zero)⁻¹ = -1 := by
  rw [localOrder_inv, localOrder_int_two]

end

end HodgeConjecture.SchemeCycles.Examples
