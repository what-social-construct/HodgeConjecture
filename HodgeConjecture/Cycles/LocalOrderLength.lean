module

public import HodgeConjecture.CommutativeAlgebra.LocalLength
public import HodgeConjecture.Cycles.LocalOrder

@[expose] public section

/-!
# Residue-degree weighting of the existing local order

Apply the local length comparison to principal quotients and their fraction
differences. These are the local length terms used in the norm-order formula
of Stacks 02MJ; the norm comparison itself is still a separate obligation.
The order is the existing `localOrder`, including for nonnormal domains.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v w

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B]
  [Algebra A B] [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
  [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  [IsDomain B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]
  {L : Type w} [Field L] [Algebra B L] [IsFractionRing B L]

/-- The residue-degree weighted order of a nonzero ring element is the
length of its actual principal quotient over the base ring. -/
theorem localOrder_algebraMap_length_restrictScalars (b : B) (hb : b ≠ 0) :
    (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) : ℤ) *
      localOrder B (Units.mk0 (algebraMap B L b)
        (by simpa only [map_zero] using (IsFractionRing.injective B L).ne hb)) =
      ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  rw [localOrder_algebraMap B b hb,
    length_restrictScalars_of_localHom A B (B ⧸ Ideal.span {b})
      (isFiniteLength_quotient_span_singleton B (mem_nonZeroDivisors_of_ne_zero hb))]
  simp only [ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul]

/-- The same weighted order for a fraction is the difference of the two
principal-quotient lengths over the base ring. -/
theorem localOrder_fraction_length_restrictScalars
    (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) : ℤ) *
      localOrder B
        (Units.mk0 (algebraMap B L a)
            (by simpa only [map_zero] using (IsFractionRing.injective B L).ne ha) /
          Units.mk0 (algebraMap B L b)
            (by simpa only [map_zero] using (IsFractionRing.injective B L).ne hb)) =
      ((Module.length A (B ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  rw [localOrder_div, mul_sub, localOrder_algebraMap_length_restrictScalars A B a ha,
    localOrder_algebraMap_length_restrictScalars A B b hb]

end

end HodgeConjecture.SchemeCycles
