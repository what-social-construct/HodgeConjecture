import HodgeConjecture.Boundary.Normalization.SectionLocalization
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Ideal

/-!
# Sections with a pole along a removed divisor

At a height-one prime containing a nonzero ideal `J`, a power of `J`
locally clears the denominator of a nonzero `f ∈ J`. Finite generation
then clears this localized containment by one element outside the prime.
The resulting fraction is an actual section off `V(J)` and is not in the
base ring. This construction uses no boundary-separation or trace-landing
hypothesis.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Finite generation clears a localized ideal containment by one denominator. -/
private theorem exists_denominator_mul_mem_of_map_le
    {T S : Type*} [CommRing T] [CommRing S] [Algebra T S]
    (M : Submonoid T) [IsLocalization M S]
    (I J : Ideal T) (hI : I.FG)
    (hIJ : I.map (algebraMap T S) ≤ J.map (algebraMap T S)) :
    ∃ t ∈ M, ∀ x ∈ I, t * x ∈ J := by
  revert hIJ
  refine Submodule.fg_induction T T
    (fun K : Ideal T =>
      K.map (algebraMap T S) ≤ J.map (algebraMap T S) →
        ∃ t ∈ M, ∀ x ∈ K, t * x ∈ J) ?_ ?_ I hI
  · intro x hMap
    have hx : algebraMap T S x ∈ J.map (algebraMap T S) :=
      hMap (Ideal.mem_map_of_mem _ (Submodule.mem_span_singleton_self x))
    obtain ⟨t, ht, htx⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J x).mp hx
    refine ⟨t, ht, ?_⟩
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simpa only [smul_eq_mul, mul_left_comm t a x] using J.mul_mem_left a htx
  · intro K L hK hL hMap
    obtain ⟨t, ht, htx⟩ := hK ((Ideal.map_mono le_sup_left).trans hMap)
    obtain ⟨u, hu, hux⟩ := hL ((Ideal.map_mono le_sup_right).trans hMap)
    refine ⟨t * u, M.mul_mem ht hu, ?_⟩
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hsum := J.add_mem (J.mul_mem_left u (htx y hy))
      (J.mul_mem_left t (hux z hz))
    convert hsum using 1
    ring

section Algebra

variable {T : Type*} [CommRing T] [IsDomain T] [IsNoetherianRing T]

/-- A prescribed nonzero element is a local ideal-power denominator
at a height-one prime containing `J`; its clearing multiplier avoids that prime. -/
theorem exists_heightOne_boundary_denominator_of_ne_zero
    (J : Ideal T) (p : PrimeSpectrum T)
    (hp : p.asIdeal.primeHeight = 1) (hJp : J ≤ p.asIdeal)
    (f : T) (hf0 : f ≠ 0) :
    ∃ (t : T) (n : ℕ), t ∉ p.asIdeal ∧
      ∀ x ∈ J ^ n, t * x ∈ Ideal.span {f} := by
  let A := Localization.AtPrime p.asIdeal
  have hdim : ringKrullDim A ≤ (1 : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal A,
      Ideal.height_eq_primeHeight, hp]
    exact_mod_cast le_rfl
  letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hdim
  have hfA : algebraMap T A f ≠ 0 := by
    simpa using (FaithfulSMul.algebraMap_injective T A).ne hf0
  have hrad : IsLocalRing.maximalIdeal A ≤
      (Ideal.span {algebraMap T A f}).radical := by
    rw [Ideal.radical_eq_sInf]
    apply le_sInf
    rintro Q ⟨hfQ, hPrime⟩
    have hQ : Q ≠ ⊥ := by
      intro hzero
      have hfmem := hfQ (Ideal.subset_span (Set.mem_singleton _))
      rw [hzero, Ideal.mem_bot] at hfmem
      exact hfA hfmem
    have hMax := (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
      (inferInstance : Ring.KrullDimLE 1 A)) Q hQ hPrime
    exact (IsLocalRing.eq_maximalIdeal hMax).ge
  have hlocal : J.map (algebraMap T A) ≤
      (Ideal.span {algebraMap T A f}).radical := by
    apply le_trans (Ideal.map_mono hJp)
    rwa [Localization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hlocal
    (IsNoetherian.noetherian _)
  have hmap : (J ^ n).map (algebraMap T A) ≤
      (Ideal.span {f}).map (algebraMap T A) := by
    rw [Ideal.map_pow (algebraMap T A) J n, Ideal.map_span, Set.image_singleton]
    exact hn
  obtain ⟨t, ht, hclear⟩ := exists_denominator_mul_mem_of_map_le
    (S := A) p.asIdeal.primeCompl (J ^ n) (Ideal.span {f})
    (IsNoetherian.noetherian _) hmap
  exact ⟨t, n, ht, hclear⟩

/-- A height-one prime containing `J` gives an ideal-power denominator
whose numerator is outside that prime. -/
theorem exists_heightOne_boundary_denominator
    (J : Ideal T) (hJ : J ≠ ⊥) (p : PrimeSpectrum T)
    (hp : p.asIdeal.primeHeight = 1) (hJp : J ≤ p.asIdeal) :
    ∃ (f t : T) (n : ℕ), f ∈ J ∧ f ≠ 0 ∧ t ∉ p.asIdeal ∧
      ∀ x ∈ J ^ n, t * x ∈ Ideal.span {f} := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨t, n, ht, hclear⟩ :=
    exists_heightOne_boundary_denominator_of_ne_zero J p hp hJp f hf0
  exact ⟨f, t, n, hf, hf0, ht, hclear⟩

end Algebra

open AlgebraicGeometry CategoryTheory

universe u v

variable {T : CommRingCat.{u}} [IsDomain T] [IsNoetherianRing T]
variable {N : Type v} [Field N] [Algebra T N] [IsFractionRing T N]

/-- A removed height-one prime gives an actual rational section outside
the embedded base ring. The open may be any nonempty subset of `D(J)`.
Here `⊥` is the base subalgebra, not the zero ring. -/
theorem affineSectionSubalgebra_ne_bot_of_heightOne
    (U : (Spec T).Opens) [Nonempty U]
    (J : Ideal T) (hJ : J ≠ ⊥)
    (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1)
    (hJp : J ≤ p.asIdeal) :
    affineSectionSubalgebra (N := N) U ≠ ⊥ := by
  obtain ⟨f, t, n, hf, hf0, htp, hclear⟩ :=
    exists_heightOne_boundary_denominator J hJ p hp hJp
  let z : N := algebraMap T N t / algebraMap T N f
  have hfN : algebraMap T N f ≠ 0 := by
    simpa using (IsFractionRing.injective T N).ne hf0
  have hz : z ∈ affineSectionSubalgebra U := by
    apply mem_affineSectionSubalgebra_of_ideal_pow_mul U J n z hU
    intro x hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp (hclear x hx)
    refine ⟨a, ?_⟩
    change algebraMap T N x * (algebraMap T N t / algebraMap T N f) = _
    field_simp [hfN]
    simpa only [map_mul, mul_comm] using congrArg (algebraMap T N) ha
  intro hbot
  rw [hbot, Algebra.mem_bot] at hz
  obtain ⟨a, ha⟩ := hz
  have htf : t = a * f := by
    apply IsFractionRing.injective T N
    rw [map_mul]
    exact (div_eq_iff hfN).mp ha.symm
  apply htp
  rw [htf]
  exact p.asIdeal.mul_mem_left a (hJp hf)

end

end HodgeConjecture.NormalizationInertia
