module

public import HodgeConjecture.Boundary.Normalization.FixedRingUnramified
public import HodgeConjecture.Boundary.Normalization.InvariantIntermediate
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

/-!
# Height-one localization of fixed rings

This module supplies the commutative-algebra bridge behind the localized
fixed-ring descent.  For a finite group acting on a domain, it proves that a
height-one prime remains height one after contraction to a subgroup-fixed
ring.  The proof constructs going down for the invariant extension: lift a
chain by going up and then use transitivity of the subgroup on primes with
the same contraction to move its endpoint to the selected prime.

Consequently, a Noetherian integrally closed fixed ring has a discrete
valuation ring at the selected contraction.  The final theorem specializes
this observation to the fixed subrings of a normal-closure normalization.
The height-transfer and DVR bridge use no unramifiedness or purity theorem;
the closing descent statements consume the explicitly named unramifiedness
premise from `FixedRingUnramified.lean`.

Mathematical references: Stacks Project, Tag `0BRI` for integrality of
finite-group invariants and transitivity on primes over one contraction;
Tags `00GQ` and `00GU` for lying over and going up; and Tag `00PD` for the
characterization of discrete valuation rings as one-dimensional Noetherian
normal local domains.  The going-down theorem below is the displayed
combination of these inputs, not a citation of a separate going-down result
for arbitrary integral extensions.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture

noncomputable section

universe u

namespace NormalizationInertia

open scoped Pointwise

section Height

variable {A S G : Type*}
variable [CommRing A] [CommRing S] [Algebra A S] [IsDomain S]
variable [Group G] [Finite G] [MulSemiringAction G S]
variable [SMulCommClass G A S]

/-- A finite-group invariant extension has going down.  Integrality gives a
lift by going up, and invariant-prime transitivity conjugates the terminal
prime of that lift to the prescribed prime. -/
theorem fixedPoints_hasGoingDown (H : Subgroup G) :
    letI : Algebra (FixedPoints.subalgebra A S H) S := inferInstance
    Algebra.HasGoingDown (FixedPoints.subalgebra A S H) S := by
  let SH := FixedPoints.subalgebra A S H
  letI : SMulCommClass H SH S := by
    constructor
    intro h a x
    change h.1 • ((a : S) * x) = (a : S) * (h.1 • x)
    rw [smul_mul']
    congr 1
    exact a.property h
  letI : Algebra.IsInvariant SH S H := by
    constructor
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  letI : Algebra.IsIntegral SH S :=
    Algebra.IsInvariant.isIntegral SH S H
  constructor
  intro p hp Q hQ hpQ
  obtain ⟨P₀, hP₀prime, hP₀over⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (S := S) p (by simp)
  obtain ⟨Q', hP₀Q', hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (S := S) (Q.under SH) P₀ (by rw [hP₀over]; exact hpQ.le)
  letI : Q'.IsPrime := hQ'prime
  have hunder : Q'.under SH = Q.under SH := hQ'over
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq SH S H Q' Q hunder
  refine ⟨g • P₀, ?_, (hP₀prime.smul g), ?_⟩
  · rw [hg]
    exact smul_mono_right g hP₀Q'
  · constructor
    rw [Ideal.under_smul]
    exact hP₀over.symm

/-- Going down bounds the height of a contracted prime by its height
upstairs. -/
theorem primeHeight_under_le_of_hasGoingDown
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Algebra.HasGoingDown R T]
    (Q : Ideal T) [Q.IsPrime] :
    (Q.under R).height ≤ Q.height := by
  letI : Q.LiesOver (Q.under R) := ⟨rfl⟩
  change (⟨Q.under R, inferInstance⟩ : PrimeSpectrum R).asIdeal.height ≤
    (⟨Q, inferInstance⟩ : PrimeSpectrum T).asIdeal.height
  rw [PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.height_eq_orderHeight]
  apply Order.height_le
  intro l hl
  letI : Q.LiesOver l.last.asIdeal :=
    ⟨congrArg PrimeSpectrum.asIdeal hl⟩
  obtain ⟨L, hlen, hlast, _⟩ :=
    Ideal.exists_ltSeries_of_hasGoingDown l Q
  rw [← hlen]
  simpa [hlast] using (Order.length_le_height_last (p := L))

/-- Contraction from a domain with a finite group action cannot increase
prime height. -/
theorem fixedPoints_primeHeight_under_le
    (H : Subgroup G) (Q : Ideal S) [Q.IsPrime] :
    (Q.under (FixedPoints.subalgebra A S H)).height ≤
      Q.height := by
  let SH := FixedPoints.subalgebra A S H
  letI : Algebra.HasGoingDown SH S := fixedPoints_hasGoingDown H
  exact primeHeight_under_le_of_hasGoingDown Q

/-- A height-one prime of a domain contracts to a height-one prime in every
subgroup-fixed ring for a finite group action. -/
theorem fixedPoints_primeHeight_under_eq_one
    (H : Subgroup G) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.height = 1) :
    (Q.under (FixedPoints.subalgebra A S H)).height = 1 := by
  let SH := FixedPoints.subalgebra A S H
  letI : SMulCommClass H SH S := by
    constructor
    intro h a x
    change h.1 • ((a : S) * x) = (a : S) * (h.1 • x)
    rw [smul_mul']
    congr 1
    exact a.property h
  letI : Algebra.IsInvariant SH S H := by
    constructor
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  letI : Algebra.IsIntegral SH S :=
    Algebra.IsInvariant.isIntegral SH S H
  have hQne : Q ≠ ⊥ := by
    intro h
    subst h
    have hzero : (⊥ : Ideal S).height = 0 := by
      rw [Ideal.height_eq_zero_iff,
        IsDomain.minimalPrimes_eq_singleton_bot]
      simp
    rw [hzero] at hQ
    exact zero_ne_one hQ
  have hqne : Q.under SH ≠ ⊥ := by
    intro h
    exact hQne (Ideal.eq_bot_of_comap_eq_bot h)
  apply le_antisymm
  · simpa [hQ] using fixedPoints_primeHeight_under_le (A := A) H Q
  · rw [Order.one_le_iff_pos, pos_iff_ne_zero]
    intro hzero
    have hmin := (Ideal.height_eq_zero_iff).mp hzero
    rw [IsDomain.minimalPrimes_eq_singleton_bot] at hmin
    exact hqne hmin

end Height

section DVR

/-- A height-one localization of a Noetherian normal domain is a discrete
valuation ring.  This local form is what the fixed-ring descent needs; it
does not assert that the ambient ring is one-dimensional. -/
theorem localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one
    {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let T := Localization.AtPrime P
  letI : IsNoetherianRing T :=
    IsLocalization.isNoetherianRing P.primeCompl T inferInstance
  letI : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim T ≤ (1 : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P T,
      hP]
    exact_mod_cast le_rfl
  letI : Ring.KrullDimLE 1 T := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne T :=
    ⟨fun {Q} hQ hPrime ↦
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
        (inferInstance : Ring.KrullDimLE 1 T)) Q hQ hPrime⟩
  have hvalCriterion :
      IsIntegrallyClosed T ∧
        ∀ Q : Ideal T, Q ≠ ⊥ → Q.IsPrime →
          Q = IsLocalRing.maximalIdeal T :=
    ⟨inferInstance, fun Q hQ hPrime ↦
      IsLocalRing.eq_maximalIdeal
        (Ring.DimensionLEOne.maximalOfPrime hQ hPrime)⟩
  letI : ValuationRing T :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain T).out 4 2).mp
      hvalCriterion
  have hPne : P ≠ ⊥ := by
    intro h
    subst h
    have hzero : (⊥ : Ideal R).height = 0 := by
      rw [Ideal.height_eq_zero_iff,
        IsDomain.minimalPrimes_eq_singleton_bot]
      simp
    rw [hzero] at hP
    exact zero_ne_one hP
  have hnotfield : ¬ IsField T :=
    IsLocalization.AtPrime.not_isField R hPne T
  exact ((IsDiscreteValuationRing.TFAE T hnotfield).out 2 1).mp
    (inferInstance : ValuationRing T)

end DVR

section LocalizedDescentAtHeightOne

variable {A S G : Type*}
variable [CommRing A] [CommRing S] [Algebra A S] [IsDomain S]
variable [Group G] [Finite G] [MulSemiringAction G S]
variable [SMulCommClass G A S]

/-- Height one and normality of the selected fixed ring discharge the local
Dedekind hypothesis in the fixed-ring unramified descent. -/
theorem fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one
    [IsNoetherianRing A] [Module.Finite A S]
    (I H : Subgroup G) (hIH : I ≤ H)
    [IsIntegrallyClosed (FixedPoints.subalgebra A S H)]
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.height = 1)
    (hI : InertiaFixedRingUnramifiedAt (A := A) (S := S) I Q) :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S H)) := by
  let SH := FixedPoints.subalgebra A S H
  letI : Module.Finite A SH :=
    Module.Finite.of_injective SH.val.toLinearMap Subtype.val_injective
  letI : IsNoetherianRing SH := IsNoetherianRing.of_finite A SH
  have hq : (Q.under SH).height = 1 :=
    fixedPoints_primeHeight_under_eq_one (A := A) H Q hQ
  letI : IsDiscreteValuationRing
      (Localization.AtPrime (Q.under SH)) :=
    localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one
      (Q.under SH) hq
  exact fixedRing_isUnramifiedAt_of_inertia_le_localized I H hIH Q hI

end LocalizedDescentAtHeightOne

section NormalizationSpecialization

/-- At a height-one prime of a finite normal-closure normalization over a
Noetherian affine domain, every subgroup-fixed normalization has a DVR as
its selected local ring.  In particular, the local Dedekind hypothesis used
by `fixedRing_isUnramifiedAt_of_inertia_le_localized` is automatic here. -/
theorem fixedSubgroupNormalizationRing_localization_isDiscreteValuationRing
    {B K N : Type u}
    [CommRing B] [Field K] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [FiniteDimensional K N] [IsNoetherianRing B]
    [Module.Finite B
      (NormalClosureNormalizationRing (B := B) (N := N))]
    (H : Subgroup (N ≃ₐ[K] N))
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] (hQ : Q.height = 1) :
    IsDiscreteValuationRing
      (Localization.AtPrime
        (Q.under (FixedSubgroupNormalizationRing (B := B) H))) := by
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let SH := FixedSubgroupNormalizationRing (B := B) H
  let F := IntermediateField.fixedField H
  let R := integralClosure B F
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : IsDomain S := inferInstance
  letI : Module.Finite B SH :=
    Module.Finite.of_injective SH.val.toLinearMap Subtype.val_injective
  letI : IsNoetherianRing SH := IsNoetherianRing.of_finite B SH
  letI : IsIntegrallyClosed R :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let e : R ≃+* SH :=
    (fixedFieldNormalizationEquivFixedRing (B := B) H).toRingEquiv
  letI : IsIntegrallyClosed SH := IsIntegrallyClosed.of_equiv e
  have hq : (Q.under SH).height = 1 :=
    fixedPoints_primeHeight_under_eq_one (A := B) H Q hQ
  exact localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one
    (Q.under SH) hq

/-- In the normal-closure normalization, height one supplies the local DVR
needed by fixed-ring unramified descent.  This version is based over the
affine ring `B`; the fixed-inertia unramifiedness premise remains explicit. -/
theorem fixedSubgroupNormalizationRing_isUnramifiedAt_of_inertia_le
    {B K N : Type u}
    [CommRing B] [Field K] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [FiniteDimensional K N] [IsNoetherianRing B]
    [Module.Finite B
      (NormalClosureNormalizationRing (B := B) (N := N))]
    (I H : Subgroup (N ≃ₐ[K] N)) (hIH : I ≤ H)
    (Q : Ideal (NormalClosureNormalizationRing (B := B) (N := N)))
    [Q.IsPrime] (hQ : Q.height = 1)
    (hI : InertiaFixedRingUnramifiedAt
      (A := B)
      (S := NormalClosureNormalizationRing (B := B) (N := N)) I Q) :
    Algebra.IsUnramifiedAt B
      (Q.under (FixedSubgroupNormalizationRing (B := B) H)) := by
  let S := NormalClosureNormalizationRing (B := B) (N := N)
  let SH := FixedSubgroupNormalizationRing (B := B) H
  let F := IntermediateField.fixedField H
  let R := integralClosure B F
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : IsIntegrallyClosed R :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let e : R ≃+* SH :=
    (fixedFieldNormalizationEquivFixedRing (B := B) H).toRingEquiv
  letI : IsIntegrallyClosed SH := IsIntegrallyClosed.of_equiv e
  exact fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one
    I H hIH Q hQ hI

end NormalizationSpecialization

end NormalizationInertia

end

end HodgeConjecture
