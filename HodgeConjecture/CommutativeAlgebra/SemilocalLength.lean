import HodgeConjecture.CommutativeAlgebra.LocalLength
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Ideal.Over

/-!
# The semilocal length formula

For a finite-length module over a ring with finitely many maximal ideals,
restriction of scalars has length equal to the sum of the local lengths,
weighted by the base lengths of the residue fields. For a local base with
finite residue extensions lying over its maximal ideal, these weights are
the canonical residue degrees. This proves Stacks Project, Tag 02M0:
https://stacks.math.columbia.edu/tag/02M0

The localizations are Mathlib's actual `LocalizedModule` constructions.
The proof uses exactness of localization and a composition series, and
does not require Noetherianity, reducedness, normality or freeness.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

variable (B : Type*) [CommRing B]

private theorem simple_of_restrictScalars (S M : Type*) [CommRing S] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module S M] [IsScalarTower B S M]
    [IsSimpleModule B M] : IsSimpleModule S M := by
  haveI := IsSimpleModule.nontrivial B M
  apply (isSimpleModule_iff S M).mpr
  refine ⟨fun N => ?_⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (N.restrictScalars B) with h | h
  · left; exact Submodule.restrictScalars_injective B S M h
  · right; exact Submodule.restrictScalars_injective B S M h

private theorem localized_quotient_self_length (p : Ideal B) [p.IsMaximal] :
    Module.length (Localization p.primeCompl) (LocalizedModule p.primeCompl (B ⧸ p)) = 1 := by
  letI := Ideal.Quotient.field p
  letI : IsLocalizedModule p.primeCompl (LinearMap.id : (B ⧸ p) →ₗ[B] (B ⧸ p)) := {
    map_units := fun s => by
      rw [← (Algebra.lmul B (B ⧸ p)).commutes, Algebra.lmul_isUnit_iff]
      change IsUnit (Ideal.Quotient.mk p (s : B))
      exact isUnit_iff_ne_zero.mpr (Ideal.Quotient.eq_zero_iff_mem.not.mpr s.property)
    surj := fun y => ⟨⟨y, 1⟩, by simp⟩
    exists_of_eq := fun h => ⟨1, by simpa using h⟩ }
  let e := IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (B ⧸ p)) (LinearMap.id : (B ⧸ p) →ₗ[B] (B ⧸ p))
  letI : IsSimpleModule B (B ⧸ p) := isSimpleModule_iff_isCoatom.mpr (inferInstance : p.IsMaximal).1
  letI := IsSimpleModule.congr e
  letI := simple_of_restrictScalars B (Localization p.primeCompl) (LocalizedModule p.primeCompl (B ⧸ p))
  exact Module.length_eq_one _ _

private theorem localized_quotient_other_length (p q : Ideal B) [p.IsMaximal] [q.IsMaximal]
    (hpq : p ≠ q) :
    Module.length (Localization q.primeCompl) (LocalizedModule q.primeCompl (B ⧸ p)) = 0 := by
  have hnot : ¬p ≤ q := fun h => hpq (Ideal.IsMaximal.eq_of_le (inferInstance : p.IsMaximal)
    (inferInstance : q.IsMaximal).ne_top h)
  obtain ⟨b, hbp, hbq⟩ := SetLike.not_le_iff_exists.mp hnot
  letI : Subsingleton (LocalizedModule q.primeCompl (B ⧸ p)) := LocalizedModule.subsingleton_iff.mpr
    (fun m => ⟨b, hbq, by
      change Ideal.Quotient.mk p b * m = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hbp, zero_mul]⟩)
  exact Module.length_eq_zero

private theorem localized_length_exact
    (S : Submonoid B) {N M P : Type*} [AddCommGroup N] [AddCommGroup M] [AddCommGroup P]
    [Module B N] [Module B M] [Module B P]
    (f : N →ₗ[B] M) (g : M →ₗ[B] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Module.length (Localization S) (LocalizedModule S M) =
      Module.length (Localization S) (LocalizedModule S N) +
        Module.length (Localization S) (LocalizedModule S P) := by
  exact Module.length_eq_add_of_exact
    (IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S N)
      (LocalizedModule.mkLinearMap S M) (Localization S) f)
    (IsLocalizedModule.mapExtendScalars S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S P) (Localization S) g)
    (IsLocalizedModule.map_injective S _ _ f hf)
    (IsLocalizedModule.map_surjective S _ _ g hg)
    (LocalizedModule.map_exact S f g hex)

variable (A : Type*) [CommRing A] [Algebra A B] [Fintype (MaximalSpectrum B)]

private theorem simple_semilocal_length
    (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [IsSimpleModule B M] :
    Module.length A M = ∑ q : MaximalSpectrum B, Module.length A (B ⧸ q.asIdeal) *
      Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M) := by
  classical
  obtain ⟨p, hp, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule B M)
  letI := hp
  have he (q : MaximalSpectrum B) :
      Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M) =
        Module.length (Localization q.asIdeal.primeCompl)
          (LocalizedModule q.asIdeal.primeCompl (B ⧸ p)) :=
    (IsLocalizedModule.mapEquiv q.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M)
      (LocalizedModule.mkLinearMap _ (B ⧸ p)) (Localization q.asIdeal.primeCompl) e).length_eq
  simp_rw [he]
  rw [Finset.sum_eq_single (⟨p, hp⟩ : MaximalSpectrum B)]
  · rw [localized_quotient_self_length, mul_one]
    exact (e.restrictScalars A).length_eq
  · intro q _ hq
    have hpq : p ≠ q.asIdeal := fun h => hq (MaximalSpectrum.ext h.symm)
    rw [localized_quotient_other_length B p q.asIdeal hpq, mul_zero]
  · simp

/-- Restriction of scalars decomposes over the actual localizations, with the base lengths of the residue fields as weights. -/
theorem length_restrictScalars_eq_sum_localized
    (M : Type*) [AddCommGroup M] [Module B M] (hM : IsFiniteLength B M) :
    ∀ [Module A M] [IsScalarTower A B M],
    Module.length A M = ∑ q : MaximalSpectrum B, Module.length A (B ⧸ q.asIdeal) *
      Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M) := by
  induction hM with
  | of_subsingleton => intro _ _; simp
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars A)
      (N.mkQ.restrictScalars A) N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), ih, simple_semilocal_length B A (M ⧸ N)]
    simp_rw [localized_length_exact B _ N.subtype N.mkQ N.subtype_injective N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N), mul_add, Finset.sum_add_distrib]

/-- Finite length is the sum of the lengths at the maximal localizations. -/
theorem length_eq_sum_localized
    (M : Type*) [AddCommGroup M] [Module B M] (hM : IsFiniteLength B M) :
    Module.length B M = ∑ q : MaximalSpectrum B,
      Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M) := by
  have h (q : MaximalSpectrum B) : Module.length B (B ⧸ q.asIdeal) = 1 := by
    letI : IsSimpleModule B (B ⧸ q.asIdeal) := isSimpleModule_iff_isCoatom.mpr q.isMaximal.1
    exact Module.length_eq_one _ _
  simpa only [h, one_mul] using length_restrictScalars_eq_sum_localized B B M hM

/-- Each term in the semilocal length sum is finite. -/
theorem length_localized_atMaximal_ne_top
    (M : Type*) [AddCommGroup M] [Module B M] (hM : IsFiniteLength B M)
    (q : MaximalSpectrum B) :
    Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M) ≠ ⊤ := by
  have h := Module.length_ne_top_iff.mpr hM
  rw [length_eq_sum_localized B M hM] at h
  apply ne_top_of_le_ne_top h
  exact Finset.single_le_sum (f := fun q : MaximalSpectrum B =>
    Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M))
    (fun _ _ => zero_le _) (Finset.mem_univ q)

variable [IsLocalRing A]
  [∀ q : MaximalSpectrum B, q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A)]
  [∀ q : MaximalSpectrum B, Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal)]

attribute [local instance] Ideal.Quotient.field

omit [Fintype (MaximalSpectrum B)] in
private theorem quotient_length (q : MaximalSpectrum B) :
    Module.length A (B ⧸ q.asIdeal) =
      Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) := by
  let b := Module.finBasis (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal)
  rw [(b.equivFun.restrictScalars A).length_eq, Module.length_pi]
  have : IsSimpleModule A (A ⧸ IsLocalRing.maximalIdeal A) := by
    exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal A).1
  simp

/-- The semilocal length formula of Stacks 02M0, with canonical quotient-field degrees. The base residue field is written as its actual quotient. -/
theorem length_restrictScalars_eq_sum_residueDegree
    (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hM : IsFiniteLength B M) :
    Module.length A M = ∑ q : MaximalSpectrum B,
      (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) : ℕ∞) *
        Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M) := by
  simpa only [quotient_length B A] using length_restrictScalars_eq_sum_localized B A M hM

/-- The integer form of the residue-degree sum; each localized length is finite. -/
theorem length_restrictScalars_toNat_eq_sum_residueDegree
    (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hM : IsFiniteLength B M) :
    ((Module.length A M).toNat : ℤ) = ∑ q : MaximalSpectrum B,
      (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) : ℤ) *
        ((Module.length (Localization q.asIdeal.primeCompl)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℤ) := by
  rw [length_restrictScalars_eq_sum_residueDegree B A M hM]
  have h : (∑ q : MaximalSpectrum B,
      (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) : ℕ∞) *
        Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M)) =
      ((∑ q : MaximalSpectrum B,
        Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) *
          (Module.length (Localization q.asIdeal.primeCompl)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Nat.cast_mul, ENat.coe_toNat (length_localized_atMaximal_ne_top B M hM q)]
  rw [h, ENat.toNat_coe, Nat.cast_sum]
  simp only [Nat.cast_mul]

/-- Finite residue degrees imply finite length over the local base. -/
theorem isFiniteLength_restrictScalars_of_semilocal
    (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hM : IsFiniteLength B M) : IsFiniteLength A M := by
  apply Module.length_ne_top_iff.mp
  rw [length_restrictScalars_eq_sum_residueDegree B A M hM]
  have h : (∑ q : MaximalSpectrum B,
      (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) : ℕ∞) *
        Module.length (Localization q.asIdeal.primeCompl) (LocalizedModule q.asIdeal.primeCompl M)) =
      ((∑ q : MaximalSpectrum B,
        Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ q.asIdeal) *
          (Module.length (Localization q.asIdeal.primeCompl)
            (LocalizedModule q.asIdeal.primeCompl M)).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Nat.cast_mul, ENat.coe_toNat (length_localized_atMaximal_ne_top B M hM q)]
  rw [h]
  exact ENat.coe_ne_top _

end

end HodgeConjecture.CommutativeAlgebra
