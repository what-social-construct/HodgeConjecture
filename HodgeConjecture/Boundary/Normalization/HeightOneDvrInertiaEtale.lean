module

public import HodgeConjecture.Boundary.Normalization.DvrInertiaFixedRing
public import HodgeConjecture.Boundary.Normalization.HeightOneDvrBaseChange

@[expose] public section

/-!
# The DVR fixed-inertia theorem at a height-one normalization prime

The affine base is normal here, so its height-one localization is a DVR.
This module applies the selected-prime form of Stacks Tag `09EH` to that
localized normalization. The comparison back to the original fixed-ring
localization is kept separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

theorem normalization_heightOne_inertia_etale_atPrime
    {B K N : Type u}
    [CommRing B] [Field K] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [FiniteDimensional K N] [IsGalois K N]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] (hQ : Q.height = 1) :
    let p := Q.under B
    let C := Localization.AtPrime p
    letI : IsDomain B := (IsFractionRing.injective B K).isDomain
    letI : Algebra C K := localizationAtPrimeAlgebraFractionField (K := K) p
    letI : IsScalarTower B C K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le C K
        p.primeCompl (nonZeroDivisors B) p.primeCompl_le_nonZeroDivisors
    letI : IsFractionRing C K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl C K
    letI : Algebra C N :=
      ((algebraMap K N).comp (algebraMap C K)).toAlgebra
    letI : IsScalarTower C K N := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower B C N := IsScalarTower.of_algebraMap_eq' (by
      ext b
      change algebraMap B N b = algebraMap K N (algebraMap C K (algebraMap B C b))
      rw [← IsScalarTower.algebraMap_apply B C K,
        ← IsScalarTower.algebraMap_apply B K N])
    let T := integralClosure C N
    letI := IsIntegralClosure.MulSemiringAction C K N T
    letI : SMulCommClass (N ≃ₐ[K] N) C T :=
      ⟨fun g a b ↦ by
        simp only [Algebra.smul_def]
        change galRestrict C K N T g (algebraMap C T a * b) =
          algebraMap C T a * galRestrict C K N T g b
        rw [map_mul, AlgEquiv.commutes]⟩
    let P := Q.map
      (CollisionFoundations.normalizationBaseChangeMap
        (B := B) (C := C) (E := N)).toRingHom
    letI : Q.LiesOver p := ⟨rfl⟩
    letI : P.IsMaximal := normalizationBaseChange_selectedPrime_isMaximal p Q
    letI : P.IsPrime := inferInstance
    let I := P.inertia (N ≃ₐ[K] N)
    let F := FixedPoints.subalgebra C T I
    letI : CommRing F := inferInstance
    letI : (P.under F).IsPrime := inferInstance
    letI : CommRing (Localization.AtPrime (P.under F)) := inferInstance
    Algebra.Etale C (Localization.AtPrime (P.under F)) := by
  dsimp only
  let p := Q.under B
  let C := Localization.AtPrime p
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : Algebra C K := localizationAtPrimeAlgebraFractionField (K := K) p
  letI : IsScalarTower B C K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le C K
      p.primeCompl (nonZeroDivisors B) p.primeCompl_le_nonZeroDivisors
  letI : Algebra C N :=
    ((algebraMap K N).comp (algebraMap C K)).toAlgebra
  letI : IsScalarTower C K N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B C N := IsScalarTower.of_algebraMap_eq' (by
    ext b
    change algebraMap B N b = algebraMap K N (algebraMap C K (algebraMap B C b))
    rw [← IsScalarTower.algebraMap_apply B C K,
      ← IsScalarTower.algebraMap_apply B K N])
  letI : IsFractionRing C K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl C K
  letI : IsDiscreteValuationRing C :=
    integralClosure_baseLocalization_isDiscreteValuationRing
      (B := B) (K := K) (N := N) Q hQ
  let T := integralClosure C N
  letI := IsIntegralClosure.MulSemiringAction C K N T
  letI : SMulCommClass (N ≃ₐ[K] N) C T :=
    ⟨fun g a b ↦ by
      simp only [Algebra.smul_def]
      change galRestrict C K N T g (algebraMap C T a * b) =
        algebraMap C T a * galRestrict C K N T g b
      rw [map_mul, AlgEquiv.commutes]⟩
  let P := Q.map
    (CollisionFoundations.normalizationBaseChangeMap
      (B := B) (C := C) (E := N)).toRingHom
  letI : Q.LiesOver p := ⟨rfl⟩
  letI : P.IsMaximal := normalizationBaseChange_selectedPrime_isMaximal p Q
  letI : P.IsPrime := inferInstance
  let I := P.inertia (N ≃ₐ[K] N)
  let F := FixedPoints.subalgebra C T I
  letI : CommRing F := inferInstance
  letI : (P.under F).IsPrime := inferInstance
  letI : CommRing (Localization.AtPrime (P.under F)) := inferInstance
  simpa only [p, C, P, I, T, F] using
    (inertia_fixedSubalgebra_etale_atPrime C K N P)

end

end HodgeConjecture.NormalizationInertia
