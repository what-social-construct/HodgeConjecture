module

public import HodgeConjecture.Boundary.Normalization.FixedRingAtPrimeComparison
public import HodgeConjecture.Boundary.Normalization.FixedRingPrimeLocalization
public import HodgeConjecture.Boundary.Normalization.LocalizationInertia

@[expose] public section

/-!
# Fixed rings under normalization base localization

This specializes the generic equivariant fixed-ring localization theorem to
the inclusion of integral closures in the same ambient Galois field.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- The Galois action on the integral closure over `C` fixes the original
base `B`, even when the fixed subalgebra is regarded as a `B`-algebra. -/
theorem normalizationBaseChangeSMulCommClass
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [Algebra C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N] :
    SMulCommClass (N ≃ₐ[K] N) B
      (NormalClosureNormalizationRing (B := C) (N := N)) where
  smul_comm σ b x := by
    change (normalClosureNormalizationRingEquiv (B := C) σ) (b • x) =
      b • (normalClosureNormalizationRingEquiv (B := C) σ) x
    simp only [Algebra.smul_def, map_mul]
    congr 1
    apply Subtype.ext
    change σ (algebraMap B N b) = algebraMap B N b
    rw [IsScalarTower.algebraMap_apply B K N b]
    exact σ.commutes (algebraMap B K b)

/-- Localizing the normalization at base denominators localizes every
subgroup-fixed ring at the same denominators. -/
theorem normalizationFixedRing_isLocalization
    {B C K N : Type u}
    [CommRing B] [CommRing C] [Field K] [Field N]
    [Algebra B C] [Algebra B K] [Algebra C K]
    [Algebra K N] [Algebra B N] [Algebra C N]
    [IsScalarTower B C K] [IsScalarTower B K N]
    [IsScalarTower C K N] [IsScalarTower B C N]
    (M : Submonoid B) [IsLocalization M C]
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
    IsLocalization (Algebra.algebraMapSubmonoid F M) F' := by
  dsimp only
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let T := NormalClosureNormalizationRing (B := C) (N := N)
  let f := CollisionFoundations.normalizationBaseChangeMap
    (B := B) (C := C) (E := N)
  letI : Algebra S T := f.toAlgebra
  letI : IsScalarTower B S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : SMulCommClass (N ≃ₐ[K] N) B T :=
    normalizationBaseChangeSMulCommClass (B := B) (C := C) (K := K) (N := N)
  letI : IsLocalization (Algebra.algebraMapSubmonoid S M) T :=
    CollisionFoundations.normalizedCoordinateRing_isLocalization
      (B := B) (C := C) (E := N) M
  have hequiv : ∀ (σ : N ≃ₐ[K] N) (x : S),
      σ • algebraMap S T x = algebraMap S T (σ • x) := by
    intro σ x
    apply Subtype.ext
    rfl
  exact fixedSubalgebra_isLocalization_of_injective H M hequiv
    (CollisionFoundations.normalizationBaseChangeMap_injective
      (B := B) (C := C) (E := N))

end

end HodgeConjecture.NormalizationInertia
