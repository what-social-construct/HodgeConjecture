module

public import HodgeConjecture.Cycles.LocalOrderNorm
public import HodgeConjecture.Cycles.LocalOrderLocalization
public import HodgeConjecture.CommutativeAlgebra.FiniteSemilocal
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

/-!
# The weighted norm--order formula

For a finite extension of domains over a Noetherian local domain of dimension
at most one, the order of the actual field norm is the residue-degree-weighted
sum of the existing local orders at the maximal ideals upstairs.

This is Stacks Project, Tag 02MJ (also allowing a field as the base):
https://stacks.math.columbia.edu/tag/02MJ

Semilocality, finite residue degrees, the upstairs dimension bound and
Noetherianity are derived from the finite extension. The localization maps
go into the original fraction field. The finite-sum notation `∑ᶠ` avoids
requiring an enumeration of the maximal ideals as an input; finiteness is
proved before using the sum. No normality, freeness or separability is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

open HodgeConjecture.CommutativeAlgebra
open scoped HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField

attribute [local instance] finiteAlgebra_maximal_liesOver atPrime_krullDimLE_one

variable (R K L B : Type*) [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsLocalRing R]
  [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

/-- Stacks 02MJ: the norm order is the weighted sum of local orders, for every nonzero fraction. -/
theorem localOrder_norm_eq_sum (y : Lˣ) :
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite R B
    letI : Ring.KrullDimLE 1 B := integralAlgebra_krullDimLE_one R B
    localOrder R (Units.map (Algebra.norm K) y) =
      ∑ᶠ q : MaximalSpectrum B,
        (Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ q.asIdeal) : ℤ) *
          localOrder (Localization.AtPrime q.asIdeal) y := by
  letI : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  letI : Ring.KrullDimLE 1 B := integralAlgebra_krullDimLE_one R B
  letI : Finite (MaximalSpectrum B) := finiteAlgebra_maximalSpectrum_finite R B
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  letI : ∀ q : MaximalSpectrum B,
      q.asIdeal.LiesOver (IsLocalRing.maximalIdeal R) := finiteAlgebra_maximal_liesOver R B
  letI : ∀ q : MaximalSpectrum B,
      Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (B ⧸ q.asIdeal) :=
    finiteAlgebra_residue_finite R B
  rw [finsum_eq_sum_of_fintype]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) (y : L)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply y.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  let u := Units.mk0 (algebraMap B L a)
    ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr ha0)
  let v := Units.mk0 (algebraMap B L b)
    ((map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hb0)
  have hy : y = u / v := by
    apply Units.ext
    simpa only [u, v, Units.val_div_eq_div_val, Units.val_mk0] using hab.symm
  rw [hy, map_div, localOrder_div]
  simp_rw [localOrder_div, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [localOrder_norm_algebraMap_eq_sum_localized_length R K L B a ha0]
    apply Finset.sum_congr rfl
    intro q _
    rw [localOrder_atPrime_algebraMap_eq_localized_length B L q.asIdeal a ha0]
  · rw [localOrder_norm_algebraMap_eq_sum_localized_length R K L B b hb0]
    apply Finset.sum_congr rfl
    intro q _
    rw [localOrder_atPrime_algebraMap_eq_localized_length B L q.asIdeal b hb0]

end

end HodgeConjecture.SchemeCycles
