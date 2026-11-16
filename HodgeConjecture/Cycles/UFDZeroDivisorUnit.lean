module

public import HodgeConjecture.Cycles.UFDHeightOneLocalOrder
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Local unit criteria for UFD height-one orders

This module derives the zero-divisor unit criterion from the length-based
local order. A nonzero element has zero order exactly when it is invertible
in the one-dimensional local ring. Reduced numerators and denominators in
a Noetherian UFD then show that a fraction with zero order at every
height-one prime comes from a unit of the original ring.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v

variable {L : Type u} [CommRing L] [IsDomain L] [IsNoetherianRing L]
    [Ring.KrullDimLE 1 L]
    {K : Type v} [Field K] [Algebra L K] [IsFractionRing L K]

/-- A nonzero element of a one-dimensional Noetherian domain has local
order zero precisely when it is a unit. -/
theorem localOrder_algebraMap_eq_zero_iff_isUnit (a : L) (ha : a ≠ 0) :
    localOrder L (Units.mk0 (algebraMap L K a)
      (by simpa only [map_zero] using (IsFractionRing.injective L K).ne ha)) = 0 ↔
      IsUnit a := by
  rw [localOrder_algebraMap L a ha]
  constructor
  · intro h
    have hlength : Module.length L (L ⧸ Ideal.span {a}) = 0 := by
      have hnat : (Module.length L (L ⧸ Ideal.span {a})).toNat = 0 := by
        exact_mod_cast h
      rcases ENat.toNat_eq_zero.mp hnat with hz | ht
      · exact hz
      · exact (principalQuotient_length_ne_top L a ha ht).elim
    have hsub : Subsingleton (L ⧸ Ideal.span {a}) :=
      Module.length_eq_zero_iff.mp hlength
    exact Ideal.span_singleton_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hsub)
  · intro hu
    rw [Ideal.span_singleton_eq_top.mpr hu]
    simp

variable {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [UniqueFactorizationMonoid R]

/-- The signed local order of a fraction at an actual height-one prime,
using the canonical prime localization and fraction field. -/
def heightOneOrder (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (f : (FractionRing R)ˣ) : ℤ := by
  letI : Ring.KrullDimLE 1 (Localization.AtPrime P) :=
    Ring.krullDimLE_iff.mpr (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP]
      exact le_refl _)
  exact localOrder (Localization.AtPrime P) f

/-- Inverting a fraction negates its order at each height-one prime. -/
theorem heightOneOrder_inv (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (f : (FractionRing R)ˣ) :
    heightOneOrder P hP f⁻¹ = -heightOneOrder P hP f := by
  letI : Ring.KrullDimLE 1 (Localization.AtPrime P) :=
    Ring.krullDimLE_iff.mpr (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP]
      exact le_refl _)
  unfold heightOneOrder
  exact localOrder_inv _ f

theorem heightOneOrder_div (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (f g : (FractionRing R)ˣ) :
    heightOneOrder P hP (f / g) =
      heightOneOrder P hP f - heightOneOrder P hP g := by
  letI : Ring.KrullDimLE 1 (Localization.AtPrime P) :=
    Ring.krullDimLE_iff.mpr (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP]
      exact le_refl _)
  unfold heightOneOrder
  exact localOrder_div _ f g

/-- Zero order of a nonzero element at a height-one prime is exactly
invertibility of that element in the prime localization. -/
theorem heightOneOrder_algebraMap_eq_zero_iff_isUnit_atPrime
    (P : Ideal R) [P.IsPrime] (hP : P.height = 1)
    (a : R) (ha : a ≠ 0) :
    heightOneOrder P hP
      (Units.mk0 (algebraMap R (FractionRing R) a)
        (by simpa only [map_zero] using (IsFractionRing.injective R (FractionRing R)).ne ha)) = 0 ↔
      IsUnit (algebraMap R (Localization.AtPrime P) a) := by
  have haL : algebraMap R (Localization.AtPrime P) a ≠ 0 :=
    (map_ne_zero_iff _
      (IsLocalization.injective (Localization.AtPrime P)
        P.primeCompl_le_nonZeroDivisors)).mpr ha
  letI : Ring.KrullDimLE 1 (Localization.AtPrime P) :=
    Ring.krullDimLE_iff.mpr (by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP]
      exact le_refl _)
  unfold heightOneOrder
  simpa only [← IsScalarTower.algebraMap_apply] using
    (localOrder_algebraMap_eq_zero_iff_isUnit
      (L := Localization.AtPrime P) (K := FractionRing R)
      (algebraMap R (Localization.AtPrime P) a) haL)

/-- Coprime nonzero elements with equal orders at every height-one prime
have an invertible first element. -/
private theorem isUnit_of_coprime_equal_heightOneOrders
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsRelPrime a b)
    (heq : ∀ (P : Ideal R) [P.IsPrime] (hP : P.height = 1),
      heightOneOrder P hP
        (Units.mk0 (algebraMap R (FractionRing R) a)
          (by simpa only [map_zero] using
            (IsFractionRing.injective R (FractionRing R)).ne ha)) =
      heightOneOrder P hP
        (Units.mk0 (algebraMap R (FractionRing R) b)
          (by simpa only [map_zero] using
            (IsFractionRing.injective R (FractionRing R)).ne hb))) :
    IsUnit a := by
  by_contra hna
  obtain ⟨p, hp, hpa⟩ := WfDvdMonoid.exists_irreducible_factor hna ha
  let P : Ideal R := Ideal.span {p}
  letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp.prime
  have hP : P.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
  have hpb : ¬p ∣ b := by
    intro hpb
    exact hp.not_isUnit (hab hpa hpb)
  have haP : a ∈ P := Ideal.mem_span_singleton.mpr hpa
  have hbP : b ∉ P := fun h => hpb (Ideal.mem_span_singleton.mp h)
  have hbunit : IsUnit (algebraMap R (Localization.AtPrime P) b) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P b).mpr hbP
  have hb0 :=
    (heightOneOrder_algebraMap_eq_zero_iff_isUnit_atPrime P hP b hb).mpr hbunit
  have ha0 := (heq P hP).trans hb0
  have haunit :=
    (heightOneOrder_algebraMap_eq_zero_iff_isUnit_atPrime P hP a ha).mp ha0
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff
    (Localization.AtPrime P) P a).mp haunit) haP

/-- A fraction over a Noetherian UFD with zero order at every height-one
prime is the image of a unit of the original ring. -/
theorem exists_unit_of_all_heightOneOrder_zero
    (f : (FractionRing R)ˣ)
    (hzero : ∀ (P : Ideal R) [P.IsPrime] (hP : P.height = 1),
      heightOneOrder P hP f = 0) :
    ∃ u : Rˣ, Units.map (algebraMap R (FractionRing R)).toMonoidHom u = f := by
  let a : R := IsFractionRing.num R (f : FractionRing R)
  let b : R := IsFractionRing.den R (f : FractionRing R)
  have ha : a ≠ 0 := by
    intro h
    exact f.ne_zero (IsFractionRing.eq_zero_of_num_eq_zero (A := R) h)
  have hb : b ≠ 0 := by
    simpa only [b] using
      (mem_nonZeroDivisors_iff_ne_zero.mp
        (IsFractionRing.den R (f : FractionRing R)).property)
  have hab : IsRelPrime a b := IsFractionRing.num_den_reduced R (f : FractionRing R)
  let ua : (FractionRing R)ˣ := Units.mk0 (algebraMap R (FractionRing R) a)
    (by simpa only [map_zero] using
      (IsFractionRing.injective R (FractionRing R)).ne ha)
  let ub : (FractionRing R)ˣ := Units.mk0 (algebraMap R (FractionRing R) b)
    (by simpa only [map_zero] using
      (IsFractionRing.injective R (FractionRing R)).ne hb)
  have hf : f = ua / ub := by
    apply Units.ext
    exact (IsFractionRing.mk'_num_den' R (f : FractionRing R)).symm
  have heq : ∀ (P : Ideal R) [P.IsPrime] (hP : P.height = 1),
      heightOneOrder P hP ua = heightOneOrder P hP ub := by
    intro P _ hP
    have h := hzero P hP
    rw [hf, heightOneOrder_div] at h
    exact sub_eq_zero.mp h
  have hau : IsUnit a :=
    isUnit_of_coprime_equal_heightOneOrders a b ha hb hab heq
  have hbu : IsUnit b :=
    isUnit_of_coprime_equal_heightOneOrders b a hb ha hab.symm
      (fun P _ hP => (heq P hP).symm)
  obtain ⟨u, hu⟩ := hau
  obtain ⟨v, hv⟩ := hbu
  refine ⟨u / v, ?_⟩
  apply Units.ext
  have hval : (f : FractionRing R) =
      algebraMap R (FractionRing R) a /
        algebraMap R (FractionRing R) b := by
    exact (IsFractionRing.mk'_num_den' R (f : FractionRing R)).symm
  rw [← hu, ← hv] at hval
  simpa using hval.symm

end

end HodgeConjecture.SchemeCycles

end
