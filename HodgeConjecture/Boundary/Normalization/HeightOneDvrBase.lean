module

public import HodgeConjecture.Boundary.Normalization.FixedRingLocalization
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Localization.LocalizationLocalization

@[expose] public section

/-!
# The height-one DVR base of a normalization prime

For a normal Noetherian domain `B` with fraction field `K`, a height-one prime
of its integral closure in any extension field contracts to a height-one
prime of `B`. Its localization is therefore a discrete valuation ring.
No Galois or finiteness hypothesis on the extension is needed for this step.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u

/-- The canonical fraction-field map from a prime localization to an
arbitrary chosen fraction field of the original domain. -/
noncomputable abbrev localizationAtPrimeAlgebraFractionField
    {B K : Type*} [CommRing B] [IsDomain B] [Field K]
    [Algebra B K] [IsFractionRing B K]
    (p : Ideal B) [p.IsPrime] :
    Algebra (Localization.AtPrime p) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.AtPrime p) K p.primeCompl
    (nonZeroDivisors B) p.primeCompl_le_nonZeroDivisors

/-- Localizing a domain at a prime does not change its chosen fraction
field. The algebra structure is the canonical localization map above. -/
theorem localizationAtPrime_isFractionRing
    {B K : Type*} [CommRing B] [IsDomain B] [Field K]
    [Algebra B K] [IsFractionRing B K]
    (p : Ideal B) [p.IsPrime] :
    letI : Algebra (Localization.AtPrime p) K :=
      localizationAtPrimeAlgebraFractionField (K := K) p
    IsFractionRing (Localization.AtPrime p) K := by
  letI : Algebra (Localization.AtPrime p) K :=
    localizationAtPrimeAlgebraFractionField (K := K) p
  letI : IsScalarTower B (Localization.AtPrime p) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime p) K p.primeCompl
      (nonZeroDivisors B) p.primeCompl_le_nonZeroDivisors
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    p.primeCompl (Localization.AtPrime p) K

/-- A height-one prime in an integral closure contracts to height one in the
normal base. -/
theorem integralClosure_primeHeight_under_eq_one
    {B K N : Type u}
    [CommRing B] [Field K] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [IsDomain B]
    [IsIntegrallyClosed B]
    (Q : Ideal (integralClosure B N)) [Q.IsPrime]
    (hQ : Q.height = 1) :
    (Q.under B).height = 1 := by
  let S := integralClosure B N
  have hBN : Function.Injective (algebraMap B N) := by
    intro x y h
    apply IsFractionRing.injective B K
    apply (algebraMap K N).injective
    simpa only [IsScalarTower.algebraMap_apply B K N] using h
  have hBS : Function.Injective (algebraMap B S) := by
    intro x y h
    apply hBN
    exact congrArg (fun z : S => (z : N)) h
  letI : FaithfulSMul B S :=
    (faithfulSMul_iff_algebraMap_injective B S).mpr hBS
  letI : Algebra.IsIntegral B S := ⟨fun x => integralClosure.isIntegral x⟩
  letI : Algebra.HasGoingDown B S := inferInstance
  have hle : (Q.under B).height ≤ Q.height :=
    primeHeight_under_le_of_hasGoingDown Q
  have hQne : Q ≠ ⊥ := Q.ne_bot_of_height_eq_one hQ
  have hpne : Q.under B ≠ ⊥ := by
    intro hp
    exact hQne (Ideal.eq_bot_of_under_eq_bot hp)
  apply le_antisymm
  · simpa only [hQ] using hle
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro hzero
    have hmin := (Ideal.height_eq_zero_iff).mp hzero
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
    exact hpne hmin

/-- The contracted height-one prime has a discrete valuation ring as its
local ring. -/
theorem integralClosure_baseLocalization_isDiscreteValuationRing
    {B K N : Type u}
    [CommRing B] [Field K] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [IsDomain B]
    [IsNoetherianRing B] [IsIntegrallyClosed B]
    (Q : Ideal (integralClosure B N)) [Q.IsPrime]
    (hQ : Q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime (Q.under B)) := by
  exact localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one
    (Q.under B)
    (integralClosure_primeHeight_under_eq_one (B := B) (K := K) (N := N) Q hQ)

/-- In a localized integral extension, the image of the selected prime
over the localization center is maximal. This is the prime condition in the
local DVR fixed-inertia theorem. -/
theorem mappedPrime_isMaximal_of_integralLocalization
    {B S Bp Sp : Type u}
    [CommRing B] [CommRing S] [CommRing Bp] [CommRing Sp]
    [Algebra B S] [Algebra B Bp] [Algebra S Sp]
    [Algebra Bp Sp] [Algebra B Sp]
    [IsScalarTower B S Sp] [IsScalarTower B Bp Sp]
    (p : Ideal B) [p.IsPrime]
    [IsLocalization.AtPrime Bp p] [IsLocalRing Bp]
    [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sp]
    [Algebra.IsIntegral Bp Sp]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p] :
    (Q.map (algebraMap S Sp)).IsMaximal := by
  have hdisj :
      Disjoint
        ((Algebra.algebraMapSubmonoid S p.primeCompl : Submonoid S) : Set S)
        (Q : Set S) :=
    Ideal.disjoint_primeCompl_of_liesOver Q p
  haveI : (Q.map (algebraMap S Sp)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sp
      Q inferInstance hdisj
  have hOver :
      (Q.map (algebraMap S Sp)).LiesOver
        (p.map (algebraMap B Bp)) :=
    IsLocalization.liesOver_of_isPrime_of_disjoint
      p.primeCompl
      (Algebra.algebraMapSubmonoid S p.primeCompl)
      p (P := Q) hdisj
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := Bp) (S := Sp) (Q.map (algebraMap S Sp))
  rw [← hOver.over]
  infer_instance

end

end HodgeConjecture.NormalizationInertia
