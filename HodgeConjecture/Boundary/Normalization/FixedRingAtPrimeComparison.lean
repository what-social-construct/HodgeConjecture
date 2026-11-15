module

public import HodgeConjecture.Boundary.Normalization.FixedRingLocalizationComparison
public import HodgeConjecture.Boundary.Normalization.LocalizationAtPrimeComparison

@[expose] public section

/-!
# Selected local rings of localized fixed rings

The equivariant fixed-ring localization theorem and the generic local-ring
comparison compose to identify the selected local rings. The source and
target algebra maps are the actual maps induced by the equivariant
localization.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Localizing a fixed ring at the prime below `q'` agrees with the local
ring of the localized fixed ring at `q'`. -/
def fixedSubalgebra_localizationAtPrimeEquiv
    {A S T G : Type*}
    [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] [Algebra S T] [IsScalarTower A S T]
    [Group G] [MulSemiringAction G S] [MulSemiringAction G T]
    [SMulCommClass G A S] [SMulCommClass G A T] [IsDomain T]
    (H : Subgroup G) (M : Submonoid A)
    [IsLocalization (Algebra.algebraMapSubmonoid S M) T]
    (hequiv : ∀ (g : G) (x : S),
      g • algebraMap S T x = algebraMap S T (g • x))
    (hinjective : Function.Injective (algebraMap S T))
    (q' : Ideal (FixedPoints.subalgebra A T H)) [q'.IsPrime] :
    let F := FixedPoints.subalgebra A S H
    let F' := FixedPoints.subalgebra A T H
    letI : Algebra F F' := (fixedSubalgebraLocalizationMap H hequiv).toAlgebra
    letI : Algebra F (Localization.AtPrime q') :=
      ((algebraMap F' (Localization.AtPrime q')).comp (algebraMap F F')).toAlgebra
    Localization.AtPrime (q'.under F) ≃ₐ[F] Localization.AtPrime q' := by
  dsimp only
  let F := FixedPoints.subalgebra A S H
  let F' := FixedPoints.subalgebra A T H
  letI : Algebra F F' := (fixedSubalgebraLocalizationMap H hequiv).toAlgebra
  letI : IsLocalization (Algebra.algebraMapSubmonoid F M) F' :=
    fixedSubalgebra_isLocalization_of_injective H M hequiv hinjective
  exact localizationAtPrimeEquivOfIsLocalization
    (R := F) (S := F') (Algebra.algebraMapSubmonoid F M) q'

end

end HodgeConjecture.NormalizationInertia
