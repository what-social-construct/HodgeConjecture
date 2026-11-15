module

public import HodgeConjecture.Boundary.Normalization.HeightOneDvrBase
public import HodgeConjecture.Boundary.Normalization.NormalizationLocalization

@[expose] public section

/-!
# The selected prime after normalization base localization

This applies the generic maximal-prime theorem to the existing normalization
base-change map. It keeps the localized algebra and both towers explicit to
avoid instance synthesis through the whole normalization diagram.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- The image of a selected prime over the localization center is maximal in
the normalization over that local base. -/
theorem normalizationBaseChange_selectedPrime_isMaximal
    {B C N : Type u}
    [CommRing B] [CommRing C] [Field N]
    [Algebra B C] [Algebra B N] [Algebra C N]
    [IsScalarTower B C N]
    (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime C p]
    (Q : Ideal (CollisionFoundations.normalizedCoordinateRing B N))
    [Q.IsPrime] [Q.LiesOver p] :
    (Q.map
      (CollisionFoundations.normalizationBaseChangeMap
        (B := B) (C := C) (E := N)).toRingHom).IsMaximal := by
  let S := CollisionFoundations.normalizedCoordinateRing B N
  let T := CollisionFoundations.normalizedCoordinateRing C N
  let f := CollisionFoundations.normalizationBaseChangeMap
    (B := B) (C := C) (E := N)
  letI : Algebra S T := f.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B C T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext b
    change algebraMap B N b = algebraMap C N (algebraMap B C b)
    exact IsScalarTower.algebraMap_apply B C N b
  letI : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C p
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid S p.primeCompl) T :=
    CollisionFoundations.normalizedCoordinateRing_isLocalization
      (B := B) (C := C) (E := N) p.primeCompl
  letI : Algebra.IsIntegral C T := ⟨fun x => integralClosure.isIntegral x⟩
  change (Q.map (algebraMap S T)).IsMaximal
  exact mappedPrime_isMaximal_of_integralLocalization
    (B := B) (S := S) (Bp := C) (Sp := T) p Q

end

end HodgeConjecture.NormalizationInertia
