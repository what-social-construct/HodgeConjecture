import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingDown
import HodgeConjecture.CommutativeAlgebra.MonicPrimeCoefficients
import HodgeConjecture.CommutativeAlgebra.IntegralIdealPolynomial

/-!
# Going down over an integrally closed domain

This module proves going down for an injective integral extension of domains
with integrally closed base. The proof uses actual minimal polynomials and
prime ideals; no going-down hypothesis is supplied as an input.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

open Polynomial

universe u v

private theorem mem_prime_of_scaled_annihilator
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [IsIntegrallyClosed R]
    (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hpQ : p ≤ Q.under R) {a : R} (ha : a ∉ p) {b : S}
    (hb : IsIntegral R b) (F : R[X]) (hF : F.Monic)
    (hroot : aeval (algebraMap R S a * b) F = 0)
    (hcoeff : ∀ i < F.natDegree, F.coeff i ∈ p) : b ∈ Q := by
  letI : NoZeroSMulDivisors R S :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr hinj
  have hdiv : minpoly R b ∣ F.comp (C a * X) := by
    apply minpoly.isIntegrallyClosed_dvd hb
    simpa only [aeval_comp, aeval_mul, aeval_C, aeval_X] using hroot
  have hgcoeff := coeff_mem_prime_of_monic_dvd_scaled p ha hF (minpoly.monic hb)
    hcoeff hdiv
  let q : R →+* S ⧸ Q := (Ideal.Quotient.mk Q).comp (algebraMap R S)
  have hgmap : (minpoly R b).map q = X ^ (minpoly R b).natDegree := by
    apply monic_map_eq_X_pow_of_lower_coeff_zero q (minpoly.monic hb)
    intro i hi
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hpQ (hgcoeff i hi))
  have hroot' : aeval (Ideal.Quotient.mk Q b) ((minpoly R b).map q) = 0 := by
    rw [← map_aeval_eq_aeval_map (ψ := Ideal.Quotient.mk Q)
      (by ext r; rfl) (minpoly R b) b, minpoly.aeval, map_zero]
  rw [hgmap, map_pow, aeval_X] at hroot'
  apply (inferInstance : Q.IsPrime).mem_of_pow_mem (minpoly R b).natDegree
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_pow] using hroot')

private theorem exists_prime_below_of_mul_cancellation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hcancel : ∀ (a : R) (b : S), a ∉ p →
      algebraMap R S a * b ∈ p.map (algebraMap R S) → b ∈ Q) :
    ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p := by
  let T : Submonoid S := p.primeCompl.map (algebraMap R S) ⊔ Q.primeCompl
  have hdisjoint : Disjoint (p.map (algebraMap R S) : Set S) T := by
    apply Set.disjoint_left.mpr
    intro x hx hxT
    obtain ⟨a', ha', b, hb, hab⟩ := Submonoid.mem_sup.mp hxT
    obtain ⟨a, ha, rfl⟩ := ha'
    exact hb (hcancel a b ha (hab ▸ hx))
  obtain ⟨P, hP, hmapP, hPT⟩ :=
    (p.map (algebraMap R S)).exists_le_prime_disjoint T hdisjoint
  refine ⟨P, ?_, hP, ?_⟩
  · intro b hb
    by_contra hbQ
    exact Set.disjoint_left.mp hPT hb (Submonoid.mem_sup_right hbQ)
  · constructor
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mp hmapP
    · exact (Ideal.disjoint_map_primeCompl_iff_comap_le).mp
        (hPT.mono_right (show (p.primeCompl.map (algebraMap R S) : Set S) ⊆ T from
          fun _ hx ↦ Submonoid.mem_sup_left hx))

/-- Normality cancels a scalar outside the smaller prime in an extended
ideal, relative to any prime above the larger contraction. -/
theorem mem_prime_of_mul_mem_map_of_isIntegrallyClosed
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [IsIntegrallyClosed R]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hpQ : p ≤ Q.under R) (a : R) (b : S) (ha : a ∉ p)
    (hab : algebraMap R S a * b ∈ p.map (algebraMap R S)) : b ∈ Q := by
  obtain ⟨F, hF, hroot, hcoeff⟩ :=
    exists_monic_annihilator_of_mem_map R S p (algebraMap R S a * b) hab
  exact mem_prime_of_scaled_annihilator hinj p Q hpQ ha
    (Algebra.IsIntegral.isIntegral b) F hF hroot hcoeff

/-- An injective integral extension of domains has going down when its
base is integrally closed. Neither finite generation, Noetherianity,
separability nor normality of the target is required. -/
theorem hasGoingDown_of_isIntegrallyClosed
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [IsIntegrallyClosed R]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    Algebra.HasGoingDown R S := by
  constructor
  intro p hp Q hQ hpQ
  exact exists_prime_below_of_mul_cancellation p Q
    (mem_prime_of_mul_mem_map_of_isIntegrallyClosed R S hinj p Q hpQ.le)

end

end HodgeConjecture.CommutativeAlgebra
