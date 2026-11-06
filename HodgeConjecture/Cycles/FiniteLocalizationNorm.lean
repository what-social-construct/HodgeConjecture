module

public import HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
public import HodgeConjecture.Cycles.LocalOrderNormFormula

@[expose] public section

/-!
# Applying the norm formula over a localized base

Localize the whole finite algebra at a base prime, keeping the original
fraction fields. The base localization may be an actual scheme stalk.
This is the algebraic coefficient calculation used in Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open HodgeConjecture.CommutativeAlgebra
open scoped HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField
open scoped HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField

noncomputable section

variable (A B R K L : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
  (p : Ideal A) [p.IsPrime]
  [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [Algebra A R] [IsLocalization.AtPrime R p]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra A L] [IsScalarTower A R L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]

local notation "T" => finiteLocalization A B p

local instance finiteNormBaseAlgebra : Algebra R T := finiteLocalization_baseAlgebra A B p R
local instance finiteNormBaseScalarTower : IsScalarTower A R T := finiteLocalization_baseScalarTower A B p R

omit [Module.Finite A B] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [Ring.KrullDimLE 1 R] in
/-- The two routes from the localized base to the original upstairs fraction field agree. -/
theorem finiteLocalization_fractionScalarTower : IsScalarTower R T L := by
  haveI : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B T,
      ← IsScalarTower.algebraMap_apply B T L]
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext p.primeCompl
  ext a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

attribute [local instance] finiteAlgebra_maximal_liesOver atPrime_krullDimLE_one

/-- The full local norm sum applies to the whole localized finite algebra over an actual base localization. -/
theorem localOrder_norm_eq_sum_finiteLocalization (y : Lˣ) :
    letI : IsDomain T := finiteLocalization_isDomain A B p
    letI : Module.Finite R T := Module.Finite.of_isLocalization A B p.primeCompl
    letI : IsNoetherianRing T := IsNoetherianRing.of_finite R T
    letI : Ring.KrullDimLE 1 T := integralAlgebra_krullDimLE_one R T
    localOrder R (Units.map (Algebra.norm K) y) =
      ∑ᶠ q : MaximalSpectrum T,
        (Module.finrank (R ⧸ IsLocalRing.maximalIdeal R) (T ⧸ q.asIdeal) : ℤ) *
          localOrder (Localization.AtPrime q.asIdeal) y := by
  letI : IsDomain T := finiteLocalization_isDomain A B p
  letI : Module.Finite R T := Module.Finite.of_isLocalization A B p.primeCompl
  letI := finiteLocalization_fractionScalarTower A B R L p
  exact localOrder_norm_eq_sum R K L T y

end

end HodgeConjecture.SchemeCycles
