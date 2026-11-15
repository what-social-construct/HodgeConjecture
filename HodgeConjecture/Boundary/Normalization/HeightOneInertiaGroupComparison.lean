module

public import HodgeConjecture.Boundary.Normalization.LocalizationInertia
public import HodgeConjecture.Boundary.Normalization.PrimeInertia

@[expose] public section

/-!
# Prime inertia after normalization base localization

The project's named prime inertia group is the same group used in the DVR
fixed-inertia theorem after localizing the normalization at fixed base
denominators.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

theorem normalizationPrimeInertiaGroup_eq_localized_inertia
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [IsFractionRing B K] [Algebra C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N]
    (M : Submonoid B) [IsLocalization M C]
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime]
    (hdisjoint : Disjoint (M : Set B) (Q.under B : Set B)) :
    normalizationPrimeInertiaGroup (B := B) (K := K) Q =
      (Q.map
        (CollisionFoundations.normalizationBaseChangeMap
          (B := B) (C := C) (E := N)).toRingHom).inertia (N ≃ₐ[K] N) := by
  rw [normalizationPrimeInertiaGroup_eq_inertia]
  exact (normalization_inertia_map_of_isLocalization M Q hdisjoint).symm

end

end HodgeConjecture.NormalizationInertia
