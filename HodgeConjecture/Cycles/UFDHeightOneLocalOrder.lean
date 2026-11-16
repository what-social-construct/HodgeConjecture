module

public import HodgeConjecture.Cycles.LocalOrder
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Local orders of principal height-one primes

The length-based local order of a generator of the maximal ideal is one,
while a local unit has order zero. Applied at a height-one prime generated
by an element of a UFD, these give the coefficients needed for an affine
principal-divisor calculation.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v w

variable {L : Type v} [CommRing L] [IsDomain L] [IsNoetherianRing L]
    [Ring.KrullDimLE 1 L] [IsLocalRing L]
    {K : Type w} [Field K] [Algebra L K] [IsFractionRing L K]

/-- The quotient by a maximal ideal has module length one. -/
theorem length_quotient_maximalIdeal :
    Module.length L (L ⧸ IsLocalRing.maximalIdeal L) = 1 := by
  rw [Module.length_eq_one_iff]
  rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    (S := L ⧸ IsLocalRing.maximalIdeal L) Ideal.Quotient.mk_surjective]
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal L)
  exact instIsSimpleModule _

/-- A nonzero generator of the maximal ideal has signed local order one. -/
theorem localOrder_generator_of_maximalIdeal (a : L) (ha : a ≠ 0)
    (hmax : Ideal.span {a} = IsLocalRing.maximalIdeal L) :
    localOrder L (Units.mk0 (algebraMap L K a)
      (by simpa only [map_zero] using (IsFractionRing.injective L K).ne ha)) = 1 := by
  rw [localOrder_algebraMap L a ha, hmax, length_quotient_maximalIdeal]
  rfl

/-- A nonzero local unit has signed local order zero. -/
theorem localOrder_of_isUnit (a : L) (ha : a ≠ 0) (hu : IsUnit a) :
    localOrder L (Units.mk0 (algebraMap L K a)
      (by simpa only [map_zero] using (IsFractionRing.injective L K).ne ha)) = 0 := by
  rw [localOrder_algebraMap L a ha,
    Ideal.span_singleton_eq_top.mpr hu]
  simp

variable {R : Type u} [CommRing R] [IsDomain R]
    [Algebra R L] (P : Ideal R) [P.IsPrime]

/-- At a principal prime, the image of its generator is the actual maximal
ideal of the localized ring. -/
theorem span_algebraMap_generator_eq_maximalIdeal
    [IsLocalization.AtPrime L P] (a : R) (hP : P = Ideal.span {a}) :
    Ideal.span {algebraMap R L a} = IsLocalRing.maximalIdeal L := by
  calc
    Ideal.span {algebraMap R L a} = (Ideal.span {a}).map (algebraMap R L) := by
      rw [Ideal.map_span, Set.image_singleton]
    _ = P.map (algebraMap R L) := by rw [hP]
    _ = IsLocalRing.maximalIdeal L := IsLocalization.AtPrime.map_eq_maximalIdeal P L

/-- A principal height-one prime's generator has local order one in its
prime localization. The dimension-one hypothesis is carried by the local
order API and is satisfied at an actual height-one scheme point. -/
theorem localOrder_primeGenerator [IsLocalization.AtPrime L P]
    (a : R) (ha : algebraMap R L a ≠ 0)
    (hP : P = Ideal.span {a}) :
    localOrder L (Units.mk0 (algebraMap L K (algebraMap R L a))
      (by simpa only [map_zero] using (IsFractionRing.injective L K).ne ha)) = 1 :=
  localOrder_generator_of_maximalIdeal (K := K) (algebraMap R L a) ha
    (span_algebraMap_generator_eq_maximalIdeal P a hP)

/-- Distinct height-one prime ideals cannot both contain a generator of
one of them. -/
theorem generator_not_mem_other_heightOnePrime
    [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime]
    (hPheight : P.height = 1) (hQheight : Q.height = 1)
    (hPQ : P ≠ Q) (a : R) (hP : P = Ideal.span {a}) : a ∉ Q := by
  intro haQ
  have hle : P ≤ Q := by
    rw [hP]
    exact Q.span_singleton_le_iff_mem.mpr haQ
  exact hPQ (P.eq_of_le_of_height_le hle (by rw [hPheight, hQheight]))

/-- In a UFD, every height-one prime has an actual single generator. -/
theorem exists_generator_of_height_one [UniqueFactorizationMonoid R]
    (hPheight : P.height = 1) :
    ∃ a : R, P = Ideal.span {a} := by
  letI : P.IsPrincipal :=
    UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hPheight
  exact ⟨Submodule.IsPrincipal.generator P,
    (Submodule.IsPrincipal.span_singleton_generator P).symm⟩

/-- The generator of a distinct height-one prime is a unit at this prime
and therefore has signed local order zero. -/
theorem localOrder_otherPrimeGenerator
    [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime]
    [IsLocalization.AtPrime L Q]
    (hPheight : P.height = 1) (hQheight : Q.height = 1)
    (hPQ : P ≠ Q) (a : R) (hP : P = Ideal.span {a}) :
    localOrder L (Units.mk0 (algebraMap L K (algebraMap R L a))
      (by
        have haQ : a ∉ Q := generator_not_mem_other_heightOnePrime P Q
          hPheight hQheight hPQ a hP
        have hu : IsUnit (algebraMap R L a) :=
          IsLocalization.map_units L (⟨a, haQ⟩ : Q.primeCompl)
        simpa only [map_zero] using (IsFractionRing.injective L K).ne hu.ne_zero)) = 0 := by
  have haQ : a ∉ Q := generator_not_mem_other_heightOnePrime P Q
    hPheight hQheight hPQ a hP
  have hu : IsUnit (algebraMap R L a) :=
    IsLocalization.map_units L (⟨a, haQ⟩ : Q.primeCompl)
  exact localOrder_of_isUnit (K := K) (algebraMap R L a) hu.ne_zero hu

/-- Global fraction-field form of the order-one calculation, suited to an
affine scheme stalk whose function field is shared with the coordinate
domain. -/
theorem localOrder_atPrime_generator_self
    [IsLocalization.AtPrime L P] [Algebra R K] [IsFractionRing R K]
    [IsScalarTower R L K] (a : R) (ha : a ≠ 0)
    (hP : P = Ideal.span {a}) :
    localOrder L (Units.mk0 (algebraMap R K a)
      (by simpa only [map_zero] using (IsFractionRing.injective R K).ne ha)) = 1 := by
  have haL : algebraMap R L a ≠ 0 :=
    (map_ne_zero_iff _
      (IsLocalization.injective L P.primeCompl_le_nonZeroDivisors)).mpr ha
  simpa only [← IsScalarTower.algebraMap_apply] using
    localOrder_primeGenerator (K := K) P a haL hP

/-- Global fraction-field form of the vanishing at a distinct height-one
prime of the same Noetherian domain. -/
theorem localOrder_atPrime_generator_other
    [IsNoetherianRing R] [Algebra R K] [IsFractionRing R K]
    [IsScalarTower R L K] (Q : Ideal R) [Q.IsPrime]
    [IsLocalization.AtPrime L Q]
    (hPheight : P.height = 1) (hQheight : Q.height = 1)
    (hPQ : P ≠ Q) (a : R) (ha : a ≠ 0)
    (hP : P = Ideal.span {a}) :
    localOrder L (Units.mk0 (algebraMap R K a)
      (by simpa only [map_zero] using (IsFractionRing.injective R K).ne ha)) = 0 := by
  have h := localOrder_otherPrimeGenerator (R := R) (L := L) (K := K)
    P Q hPheight hQheight hPQ a hP
  simpa only [← IsScalarTower.algebraMap_apply] using h

end

end HodgeConjecture.SchemeCycles

end
