module

public import HodgeConjecture.Boundary.Normalization.NormalizationFixedRingLocalization

@[expose] public section

/-!
# Selected fixed-ring primes under normalization base change

The image of a selected prime under normalization base localization contracts
to the original selected prime in each subgroup-fixed ring.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- The selected prime of the localized normalization contracts to the same
fixed-ring prime as the original selected prime. -/
theorem normalizationFixedRing_selectedPrime_under
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [Algebra C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N]
    (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime C p]
    (H : Subgroup (N ≃ₐ[K] N))
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] [Q.LiesOver p] :
    let S := NormalClosureNormalizationRing (B := B) (N := N)
    let T := NormalClosureNormalizationRing (B := C) (N := N)
    letI : Algebra S T :=
      (CollisionFoundations.normalizationBaseChangeMap
        (B := B) (C := C) (E := N)).toAlgebra
    letI : SMulCommClass (N ≃ₐ[K] N) B T :=
      normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
    let F := FixedPoints.subalgebra B S H
    let F' := FixedPoints.subalgebra B T H
    letI : Algebra F F' :=
      (fixedSubalgebraLocalizationMap (A := B) (S := S) (T := T)
        H (fun (σ : N ≃ₐ[K] N) (x : S) ↦ by
        apply Subtype.ext
        rfl)).toAlgebra
    ((Q.map (algebraMap S T)).under F').under F = Q.under F := by
  dsimp only
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let T := NormalClosureNormalizationRing (B := C) (N := N)
  let f := CollisionFoundations.normalizationBaseChangeMap
    (B := B) (C := C) (E := N)
  letI : Algebra S T := f.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass (N ≃ₐ[K] N) B T :=
    normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
  letI : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T :=
    CollisionFoundations.normalizedCoordinateRing_isLocalization
      (B := B) (C := C) (E := N) p.primeCompl
  have hequiv : ∀ (σ : N ≃ₐ[K] N) (x : S),
      σ • algebraMap S T x = algebraMap S T (σ • x) := by
    intro σ x
    apply Subtype.ext
    rfl
  have hdisjoint : Disjoint
      (Algebra.algebraMapSubmonoid S p.primeCompl : Set S)
      (Q : Set S) := Ideal.disjoint_primeCompl_of_liesOver Q p
  exact fixedSubalgebra_under_map_of_isLocalization H p.primeCompl
    hequiv Q hdisjoint

/-- The local fixed ring before base localization is equivalent to the local
fixed ring afterward, for the actual normalization base-change map. -/
def normalizationFixedRing_localizationAtPrimeEquiv
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [Algebra C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N]
    (p : Ideal B) [p.IsPrime] [IsLocalization.AtPrime C p]
    (H : Subgroup (N ≃ₐ[K] N)) :
    let S := NormalClosureNormalizationRing (B := B) (N := N)
    let T := NormalClosureNormalizationRing (B := C) (N := N)
    letI : Algebra S T :=
      (CollisionFoundations.normalizationBaseChangeMap
        (B := B) (C := C) (E := N)).toAlgebra
    letI : SMulCommClass (N ≃ₐ[K] N) B T :=
      normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
    let F := FixedPoints.subalgebra B S H
    let F' := FixedPoints.subalgebra B T H
    letI : Algebra F F' :=
      (fixedSubalgebraLocalizationMap (A := B) (S := S) (T := T)
        H (fun (σ : N ≃ₐ[K] N) (x : S) ↦ by
        apply Subtype.ext
        rfl)).toAlgebra
    ∀ (q' : Ideal F') (hq' : q'.IsPrime),
    letI : q'.IsPrime := hq'
    letI : Algebra F (Localization.AtPrime q') :=
      ((algebraMap F' (Localization.AtPrime q')).comp (algebraMap F F')).toAlgebra
    Localization.AtPrime (q'.under F) ≃ₐ[F] Localization.AtPrime q' := by
  dsimp only
  intro q' hq'
  letI : q'.IsPrime := hq'
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let T := NormalClosureNormalizationRing (B := C) (N := N)
  let f := CollisionFoundations.normalizationBaseChangeMap
    (B := B) (C := C) (E := N)
  letI : Algebra S T := f.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass (N ≃ₐ[K] N) B T :=
    normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
  letI : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) T :=
    CollisionFoundations.normalizedCoordinateRing_isLocalization
      (B := B) (C := C) (E := N) p.primeCompl
  have hequiv : ∀ (σ : N ≃ₐ[K] N) (x : S),
      σ • algebraMap S T x = algebraMap S T (σ • x) := by
    intro σ x
    apply Subtype.ext
    rfl
  exact fixedSubalgebra_localizationAtPrimeEquiv H p.primeCompl hequiv
    (CollisionFoundations.normalizationBaseChangeMap_injective
      (B := B) (C := C) (E := N)) q'

end

end HodgeConjecture.NormalizationInertia
