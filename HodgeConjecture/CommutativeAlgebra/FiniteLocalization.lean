import HodgeConjecture.CommutativeAlgebra.FiniteSemilocal
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The semilocal algebra over a prime of the base

For a finite algebra `A → B` and a prime `p` of `A`, localize `B` at the
image of `A \ p`. This whole algebra is finite over `A_p`; its maximal
ideals correspond to the primes of `B` over `p`. Localizing again at one
of these maximal ideals gives the original `B_q`.

This is the localization step in the finite-morphism proof of Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
The construction does not assert that each individual `B_q` is finite over
`A_p`. No normality or freeness is used.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (p : Ideal A) [p.IsPrime]

/-- The whole finite algebra localized over a base prime. -/
abbrev finiteLocalization := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)

local notation "Aₚ" => Localization.AtPrime p
local notation "Bₚ" => finiteLocalization A B p
local notation "S" => Algebra.algebraMapSubmonoid B p.primeCompl

/-- Finiteness holds for the whole localized algebra. -/
theorem finiteLocalization_finite [Module.Finite A B] : Module.Finite Aₚ Bₚ :=
  Module.Finite.of_isLocalization A B p.primeCompl

attribute [local instance] finiteLocalization_finite

private theorem maximal_comap_liesOver [Module.Finite A B] (q : MaximalSpectrum Bₚ) :
    (q.asIdeal.comap (algebraMap B Bₚ)).LiesOver p := by
  letI := finiteAlgebra_maximal_liesOver Aₚ Bₚ q
  constructor
  change p = (q.asIdeal.comap (algebraMap B Bₚ)).comap (algebraMap A B)
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A B Bₚ,
    IsScalarTower.algebraMap_eq A Aₚ Bₚ, ← Ideal.comap_comap]
  have hq : q.asIdeal.comap (algebraMap Aₚ Bₚ) = IsLocalRing.maximalIdeal Aₚ :=
    (Ideal.over_def q.asIdeal (IsLocalRing.maximalIdeal Aₚ)).symm
  rw [hq]
  exact (IsLocalization.AtPrime.comap_maximalIdeal Aₚ p).symm

private theorem over_disjoint (q : p.primesOver B) : Disjoint (S : Set B) (q.val : Set B) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, ha, rfl⟩ hq
  exact ha ((Ideal.mem_of_liesOver q.val p a).mpr hq)

private theorem over_map_comap (q : p.primesOver B) :
    (q.val.map (algebraMap B Bₚ)).comap (algebraMap B Bₚ) = q.val :=
  IsLocalization.comap_map_of_isPrime_disjoint S Bₚ q.val q.property.1
    (over_disjoint A B p q)

private theorem over_map_isMaximal [Module.Finite A B] (q : p.primesOver B) :
    (q.val.map (algebraMap B Bₚ)).IsMaximal := by
  letI : (q.val.map (algebraMap B Bₚ)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S Bₚ q.val q.property.1
      (over_disjoint A B p q)
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := Aₚ)
  have h : (q.val.map (algebraMap B Bₚ)).comap (algebraMap Aₚ Bₚ) =
      IsLocalRing.maximalIdeal Aₚ := by
    apply (IsLocalization.orderEmbedding p.primeCompl Aₚ).injective
    change ((q.val.map (algebraMap B Bₚ)).comap (algebraMap Aₚ Bₚ)).comap
      (algebraMap A Aₚ) = (IsLocalRing.maximalIdeal Aₚ).comap (algebraMap A Aₚ)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A Aₚ Bₚ,
      IsScalarTower.algebraMap_eq A B Bₚ, ← Ideal.comap_comap,
      over_map_comap, IsLocalization.AtPrime.comap_maximalIdeal Aₚ p]
    exact (Ideal.over_def q.val p).symm
  rw [h]
  infer_instance

/-- Maximal ideals of the whole localization are exactly primes over the base prime. -/
def finiteLocalization_maximalEquiv [Module.Finite A B] :
    MaximalSpectrum Bₚ ≃ p.primesOver B where
  toFun q := ⟨q.asIdeal.comap (algebraMap B Bₚ), inferInstance,
    maximal_comap_liesOver A B p q⟩
  invFun q := ⟨q.val.map (algebraMap B Bₚ), over_map_isMaximal A B p q⟩
  left_inv q := MaximalSpectrum.ext (IsLocalization.map_comap S Bₚ q.asIdeal)
  right_inv q := Subtype.ext (over_map_comap A B p q)

/-- The correspondence contracts the maximal ideal along the original localization map. -/
@[simp]
theorem finiteLocalization_maximalEquiv_val [Module.Finite A B] (q : MaximalSpectrum Bₚ) :
    (finiteLocalization_maximalEquiv A B p q).val =
      q.asIdeal.comap (algebraMap B Bₚ) := rfl

/-- There are finitely many primes over each base prime in a finite algebra. -/
theorem finite_primesOver [Module.Finite A B] : Finite (p.primesOver B) := by
  letI := finiteAlgebra_maximalSpectrum_finite Aₚ Bₚ
  exact Finite.of_equiv _ (finiteLocalization_maximalEquiv A B p)

/-- The local rings in the semilocal sum are the original prime localizations. -/
def finiteLocalization_localRingEquiv [Module.Finite A B] (q : MaximalSpectrum Bₚ) :
    Localization.AtPrime (finiteLocalization_maximalEquiv A B p q).val ≃ₐ[B]
      Localization.AtPrime q.asIdeal :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization S q.asIdeal

end

end HodgeConjecture.CommutativeAlgebra
