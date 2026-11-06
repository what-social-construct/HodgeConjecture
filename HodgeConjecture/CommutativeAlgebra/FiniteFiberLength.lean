module

public import HodgeConjecture.CommutativeAlgebra.SemilocalLength
public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

/-!
# Length and degree of a finite algebra over a field

The existing semilocal length formula, applied to the regular module,
expresses the vector-space dimension as the sum of residue degrees times
the lengths of the actual local rings. Nilpotents are retained in those
lengths. This is the algebraic degree calculation used in Stacks 02RH:
https://stacks.math.columbia.edu/tag/02RH
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

/-- A ring isomorphism preserves the length of the regular module. -/
theorem length_regular_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  rw [Module.length_eq_height, Module.length_eq_height]
  simpa using (Order.height_orderIso e.idealComapOrderIso.symm (⊤ : Ideal R)).symm

/-- Localizing the regular module gives the regular module of the actual
localized ring, with the same length. -/
theorem length_localized_regular (B : Type*) [CommRing B] (S : Submonoid B) :
    Module.length (Localization S) (LocalizedModule S B) =
      Module.length (Localization S) (Localization S) := by
  let e := (IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S B)
    (Algebra.linearMap B (Localization S))).extendScalarsOfIsLocalization S (Localization S)
  exact e.length_eq

/-- The dimension of a finite field algebra is the sum of the actual local
lengths weighted by the residue-field degrees. No reducedness is required. -/
theorem finrank_eq_sum_residueDegree_mul_length
    (k B : Type*) [Field k] [CommRing B] [Algebra k B] [Module.Finite k B] :
    Module.finrank k B =
      ∑ᶠ q : MaximalSpectrum B, Module.finrank k (B ⧸ q.asIdeal) *
        (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat := by
  classical
  letI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI : IsNoetherianRing B := isNoetherianRing_iff.mpr (isNoetherian_of_tower k inferInstance)
  letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hM : IsFiniteLength B B := Module.length_ne_top_iff.mp Module.length_ne_top
  have hfinite (q : MaximalSpectrum B) :
      Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) ≠ ⊤ := by
    rw [← length_localized_regular]
    exact length_localized_atMaximal_ne_top B B hM q
  have h := length_restrictScalars_eq_sum_localized B k B hM
  simp_rw [Module.length_eq_finrank, length_localized_regular] at h
  have hsum : (∑ q : MaximalSpectrum B,
      (Module.finrank k (B ⧸ q.asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)) =
      ((∑ q : MaximalSpectrum B, Module.finrank k (B ⧸ q.asIdeal) *
        (Module.length (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Nat.cast_mul, ENat.coe_toNat (hfinite q)]
  have hn := congrArg ENat.toNat (h.trans hsum)
  simpa only [ENat.toNat_coe, finsum_eq_sum_of_fintype] using hn

end

end HodgeConjecture.CommutativeAlgebra
