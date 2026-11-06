module

public import HodgeConjecture.Cycles.LocalOrder
public import HodgeConjecture.CommutativeAlgebra.LocalizedPrincipalQuotient
public import HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

/-!
# Localized principal quotients compute the existing local order

Apply the actual principal-quotient comparison (Stacks Tag 02C8,
https://stacks.math.columbia.edu/tag/02C8) at a prime. Over a Noetherian
domain of dimension at most one, its localized length is the existing
`localOrder` of the image of the original element in the same fraction field.
The localization's dimension bound and fraction-field property are derived.

The algebra on the fraction field is required to extend the original base
map through the localization. No normality or valuation-ring hypothesis is
used. This is the termwise identification in the proof of Stacks Tag 02MJ:
https://stacks.math.columbia.edu/tag/02MJ
-/

set_option autoImplicit false
namespace HodgeConjecture.SchemeCycles

noncomputable section

open HodgeConjecture.CommutativeAlgebra

variable (B L : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B]
  [Ring.KrullDimLE 1 B] [Field L] [Algebra B L] [IsFractionRing B L]
  (q : Ideal B) [q.IsPrime]
  [Algebra (Localization.AtPrime q) L] [IsScalarTower B (Localization.AtPrime q) L]

omit [IsNoetherianRing B] [Ring.KrullDimLE 1 B] in
theorem atPrimeFractionRing : IsFractionRing (Localization.AtPrime q) L :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl
    (Localization.AtPrime q) L

attribute [local instance] atPrime_krullDimLE_one atPrimeFractionRing

/-- The localized principal-quotient length is the local order of the original element. -/
theorem localOrder_atPrime_algebraMap_eq_localized_length (b : B) (hb : b ≠ 0) :
    localOrder (Localization.AtPrime q)
      (Units.mk0 (algebraMap B L b)
        ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb)) =
      ((Module.length (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (B ⧸ Ideal.span {b}))).toNat : ℤ) := by
  have hbq : algebraMap B (Localization.AtPrime q) b ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective (Localization.AtPrime q)
      q.primeCompl_le_nonZeroDivisors)).mpr hb
  have h := localOrder_algebraMap (K := L) (Localization.AtPrime q)
    (algebraMap B (Localization.AtPrime q) b) hbq
  rw [← length_localized_principalQuotient B q.primeCompl b] at h
  simpa only [← IsScalarTower.algebraMap_apply] using h

/-- The same comparison for a numerator and denominator in the original ring. -/
theorem localOrder_atPrime_fraction_eq_localized_length (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    localOrder (Localization.AtPrime q)
      (Units.mk0 (algebraMap B L a)
          ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr ha) /
        Units.mk0 (algebraMap B L b)
          ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb)) =
      ((Module.length (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (B ⧸ Ideal.span {a}))).toNat : ℤ) -
      ((Module.length (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (B ⧸ Ideal.span {b}))).toNat : ℤ) := by
  rw [localOrder_div, localOrder_atPrime_algebraMap_eq_localized_length B L q a ha,
    localOrder_atPrime_algebraMap_eq_localized_length B L q b hb]

/-- A generator outside the prime has zero local order. -/
theorem localOrder_atPrime_eq_zero_of_not_mem (b : B) (hb : b ≠ 0) (hbq : b ∉ q) :
    localOrder (Localization.AtPrime q)
      (Units.mk0 (algebraMap B L b)
        ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb)) = 0 := by
  rw [localOrder_atPrime_algebraMap_eq_localized_length B L q b hb,
    length_localized_principalQuotient_eq_zero B q.primeCompl b hbq]
  rfl

end

end HodgeConjecture.SchemeCycles
