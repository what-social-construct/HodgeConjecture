module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

@[expose] public section

/-!
# Local rings of a localization

This isolates the selected-prime local-ring equivalence from any group action
or normalization-specific algebra instances.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Localizing at a prime after a localization gives the local ring of its
contracted prime in the original ring. -/
def localizationAtPrimeEquivOfIsLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (q : Ideal S) [q.IsPrime] :
    letI : Algebra R (Localization.AtPrime q) :=
      ((algebraMap S (Localization.AtPrime q)).comp (algebraMap R S)).toAlgebra
    Localization.AtPrime (q.under R) ≃ₐ[R] Localization.AtPrime q := by
  letI : Algebra R (Localization.AtPrime q) :=
    ((algebraMap S (Localization.AtPrime q)).comp (algebraMap R S)).toAlgebra
  letI : SMul R S := (inferInstance : Algebra R S).toSMul
  letI : SMul S (Localization.AtPrime q) :=
    (inferInstance : Algebra S (Localization.AtPrime q)).toSMul
  letI : SMul R (Localization.AtPrime q) :=
    (inferInstance : Algebra R (Localization.AtPrime q)).toSMul
  letI : IsScalarTower R S (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization.AtPrime (Localization.AtPrime q) (q.under R) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime q) q
  exact IsLocalization.algEquiv (q.under R).primeCompl _ _

end

end HodgeConjecture.NormalizationInertia
