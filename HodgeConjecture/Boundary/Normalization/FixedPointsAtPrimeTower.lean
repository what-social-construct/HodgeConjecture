module

public import HodgeConjecture.Boundary.Normalization.FixedPointsBaseComparison

@[expose] public section

/-!
# Base-map coherence at a localized fixed-point ring

The canonical map from the original base into a local fixed-point ring agrees
with the map through the localized base. This makes the final étale transport
compatible with the original source algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- The original base acts on the selected localization through its fixed
subalgebra. -/
abbrev fixedPointsAtPrimeBaseAlgebra
    {B T G : Type*}
    [CommRing B] [CommRing T] [Algebra B T]
    [Group G] [MulSemiringAction G T] [SMulCommClass G B T]
    (H : Subgroup G) (P : Ideal T) [P.IsPrime] :
    Algebra B
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
  ((algebraMap (FixedPoints.subalgebra B T H)
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H)))).comp
    (algebraMap B (FixedPoints.subalgebra B T H))).toAlgebra

/-- The two base maps into the selected local fixed-point ring agree. -/
theorem fixedPointsAtPrime_isScalarTower
    {B C T G : Type*}
    [CommRing B] [CommRing C] [CommRing T]
    [Algebra B C] [Algebra B T] [Algebra C T]
    [IsScalarTower B C T]
    [Group G] [MulSemiringAction G T]
    [SMulCommClass G B T] [SMulCommClass G C T]
    (H : Subgroup G) (P : Ideal T) [P.IsPrime] :
    letI : Algebra B
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
      fixedPointsAtPrimeBaseAlgebra H P
    letI : Algebra C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
      fixedPointsBaseChangeAtPrimeAlgebra H P
    IsScalarTower B C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) := by
  letI : Algebra B
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
    fixedPointsAtPrimeBaseAlgebra H P
  letI : Algebra C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
    fixedPointsBaseChangeAtPrimeAlgebra H P
  let F := FixedPoints.subalgebra B T H
  let U := Localization.AtPrime (P.under F)
  have hF : ∀ b : B,
      (algebraMap B F b) =
        (algebraMap C (FixedPoints.subalgebra C T H)) (algebraMap B C b) := by
    intro b
    apply Subtype.ext
    change algebraMap B T b = algebraMap C T (algebraMap B C b)
    exact IsScalarTower.algebraMap_apply B C T b
  have hmap : ∀ b : B,
      algebraMap B U b = algebraMap C U (algebraMap B C b) := by
    intro b
    change algebraMap F U (algebraMap B F b) =
      algebraMap F U
        (algebraMap C (FixedPoints.subalgebra C T H) (algebraMap B C b))
    rw [hF b]
  have hB : ∀ b : B, ∀ v : U,
      b • v = algebraMap B U b * v := by
    intro b v
    calc
      b • v = (algebraMap B F b) • v :=
        (IsScalarTower.algebraMap_smul F b v).symm
      _ = algebraMap F U (algebraMap B F b) * v :=
        Algebra.smul_def _ _
      _ = algebraMap B U b * v := rfl
  refine ⟨fun b c u => ?_⟩
  simp only [Algebra.smul_def, map_mul, mul_assoc]
  rw [hB b, hmap b]

end

end HodgeConjecture.NormalizationInertia
