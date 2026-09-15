import Mathlib.RingTheory.OrderOfVanishing

/-!
# Signed local orders from actual quotient lengths

Restrict Mathlib's fraction-field order to nonzero rational functions and
read its integer exponent. The resulting signed order has the usual
product, inverse, and fraction formulas. Its value on a nonzero ring
element is the finite length of the actual principal quotient.

No valuation-ring, normality, divisor-support, or cycle relation is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v

variable (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Integer-valued order of a nonzero rational function, from the actual
length-based fraction-field order. -/
def localOrder (f : Kˣ) : ℤ := WithZero.log (Ring.ordFrac R (f : K))

@[simp]
theorem localOrder_one : localOrder R (1 : Kˣ) = 0 := by
  simp [localOrder]

theorem localOrder_mul (f g : Kˣ) :
    localOrder R (f * g) = localOrder R f + localOrder R g := by
  simp only [localOrder, Units.val_mul, map_mul]
  exact WithZero.log_mul ((map_ne_zero _).mpr f.ne_zero) ((map_ne_zero _).mpr g.ne_zero)

@[simp]
theorem localOrder_inv (f : Kˣ) : localOrder R f⁻¹ = -localOrder R f := by
  simp [localOrder, WithZero.log_inv]

theorem localOrder_div (f g : Kˣ) :
    localOrder R (f / g) = localOrder R f - localOrder R g := by
  rw [div_eq_mul_inv, localOrder_mul, localOrder_inv, sub_eq_add_neg]

/-- A nonzero principal quotient really has finite length under the
Noetherian dimension-at-most-one hypotheses. -/
theorem principalQuotient_length_ne_top (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) ≠ ⊤ :=
  Module.length_ne_top_iff.mpr
    (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha))

/-- The integer order agrees with the actual finite principal-quotient length. -/
theorem localOrder_algebraMap (a : R) (ha : a ≠ 0) :
    localOrder R (Units.mk0 (algebraMap R K a)
      (by simpa only [map_zero] using (IsFractionRing.injective R K).ne ha)) =
      ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) := by
  classical
  rw [localOrder, Units.val_mk0, Ring.ordFrac_eq_ord R a ha]
  change WithZero.log (if a ∈ nonZeroDivisors R then
    WithZero.map' (Nat.castAddMonoidHom ℤ).toMultiplicative (Ring.ord R a) else 0) = _
  rw [if_pos (mem_nonZeroDivisors_of_ne_zero ha), Ring.ord]
  have h := principalQuotient_length_ne_top R a ha
  conv_lhs => rw [← ENat.coe_toNat h]
  rfl

/-- Numerator-minus-denominator is proved for actual nonzero ring elements,
so the signed order is independent of the chosen fraction presentation. -/
theorem localOrder_fraction (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    localOrder R
      (Units.mk0 (algebraMap R K a)
          (by simpa only [map_zero] using (IsFractionRing.injective R K).ne ha) /
        Units.mk0 (algebraMap R K b)
          (by simpa only [map_zero] using (IsFractionRing.injective R K).ne hb)) =
      ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) -
        ((Module.length R (R ⧸ Ideal.span {b})).toNat : ℤ) := by
  rw [localOrder_div, localOrder_algebraMap R a ha, localOrder_algebraMap R b hb]

/-- An invertible local element contributes zero to the divisor coefficient. -/
@[simp]
theorem localOrder_map_unit (a : Rˣ) :
    localOrder R (Units.map (algebraMap R K).toMonoidHom a) = 0 := by
  have hspan : Ideal.span {(a : R)} = ⊤ := Ideal.span_singleton_eq_top.mpr a.isUnit
  letI : Subsingleton (R ⧸ Ideal.span {(a : R)}) :=
    (Submodule.Quotient.subsingleton_iff _).mpr (fun x ↦ by rw [hspan]; trivial)
  have h := localOrder_algebraMap (K := K) R (a : R) a.ne_zero
  have he : Units.mk0 (algebraMap R K (a : R))
      (by simpa only [map_zero] using (IsFractionRing.injective R K).ne a.ne_zero) =
      Units.map (algebraMap R K).toMonoidHom a := Units.ext rfl
  rw [he, Module.length_eq_zero] at h
  simpa using h

end

end HodgeConjecture.SchemeCycles
