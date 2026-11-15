module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Basic

@[expose] public section

/-!
# Formal unramifiedness from a localized étale model

An étale map after localizing the base supplies formal unramifiedness over
the original base. A local algebra equivalence carries that conclusion back
to the original target, and scalar restriction allows the source to be any
intermediate algebra. This is the last formal step needed once the selected
fixed-ring localizations have been identified.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Transport étaleness from a localized base through an equivalence of
selected local rings, then restrict scalars to the intended source ring. -/
theorem formallyUnramified_of_etale_localized_equiv
    {B C A V U : Type*}
    [CommRing B] [CommRing C] [CommRing A] [CommRing V] [CommRing U]
    [Algebra B C] [Algebra B A] [Algebra B V] [Algebra A V]
    [Algebra B U] [Algebra C U]
    [IsScalarTower B A V] [IsScalarTower B C U]
    (M : Submonoid B) [IsLocalization M C]
    (e : V ≃ₐ[B] U) (h : Algebra.Etale C U) :
    Algebra.FormallyUnramified A V := by
  letI : Algebra.FormallyUnramified B C :=
    Algebra.FormallyUnramified.of_isLocalization M
  letI : Algebra.Etale C U := h
  letI : Algebra.FormallyUnramified B U :=
    Algebra.FormallyUnramified.comp B C U
  letI : Algebra.FormallyUnramified B V :=
    (Algebra.FormallyUnramified.iff_of_equiv e).mpr inferInstance
  exact Algebra.FormallyUnramified.of_restrictScalars B A V

end

end HodgeConjecture.NormalizationInertia
