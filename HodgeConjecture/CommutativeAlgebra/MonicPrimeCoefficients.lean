import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Prime-ideal coefficients of monic polynomial divisors

After reduction modulo a prime, a monic polynomial whose lower coefficients
lie in that prime becomes a power of `X`. A monic divisor has the same
property. The scaled variant allows an argument `a * X` with `a` outside
the prime and is used in the normal-base going-down proof.

This is the prime-ideal specialization of Stacks Tag 00H6's coefficient
comparison, proved with actual quotient and fraction-field maps.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

open Polynomial

universe u

/-- A monic polynomial becomes a power of `X` under a ring map which
kills all of its lower coefficients. -/
theorem monic_map_eq_X_pow_of_lower_coeff_zero
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A)
    {F : R[X]} (hF : F.Monic)
    (hcoeff : ∀ i < F.natDegree, f (F.coeff i) = 0) :
    F.map f = X ^ F.natDegree := by
  ext i
  rcases lt_trichotomy i F.natDegree with hi | hi | hi
  · simp [hcoeff i hi, coeff_X_pow, hi.ne]
  · subst i
    simp [hF.coeff_natDegree]
  · simp [coeff_eq_zero_of_natDegree_lt hi, coeff_X_pow, hi.ne']

/-- A monic divisor of a polynomial which becomes a power of `a * X`
modulo a prime, with `a` outside that prime, also becomes a power of `X`.
The conclusion is stated using the original coefficients. -/
theorem coeff_mem_prime_of_monic_dvd_scaled
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {a : R} (ha : a ∉ p) {F g : R[X]} (hF : F.Monic) (hg : g.Monic)
    (hcoeff : ∀ i < F.natDegree, F.coeff i ∈ p)
    (hdiv : g ∣ F.comp (C a * X)) :
    ∀ i < g.natDegree, g.coeff i ∈ p := by
  let K := FractionRing (R ⧸ p)
  let f : R →+* K := (algebraMap (R ⧸ p) K).comp (Ideal.Quotient.mk p)
  have hfzero (r : R) : f r = 0 ↔ r ∈ p := by
    change algebraMap (R ⧸ p) K (Ideal.Quotient.mk p r) = 0 ↔ r ∈ p
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ p) K),
      Ideal.Quotient.eq_zero_iff_mem]
  have hFmap : F.map f = X ^ F.natDegree :=
    monic_map_eq_X_pow_of_lower_coeff_zero f hF
      (fun i hi ↦ (hfzero _).mpr (hcoeff i hi))
  have hdiv' : g.map f ∣ C (f a ^ F.natDegree) * X ^ F.natDegree := by
    have := map_dvd f hdiv
    simpa only [map_comp, Polynomial.map_mul, map_C, map_X, hFmap, pow_comp,
      X_comp, mul_pow, ← C_pow] using this
  have hpower : g.map f ∣ X ^ F.natDegree :=
    (dvd_C_mul (pow_ne_zero _ (mt (hfzero a).mp ha))).mp hdiv'
  obtain ⟨j, _, hj⟩ := (dvd_prime_pow (prime_X (R := K)) F.natDegree).mp hpower
  have heq : g.map f = X ^ j :=
    eq_of_monic_of_associated (hg.map f) (monic_X.pow j) hj
  have hjdeg : j = g.natDegree := by
    simpa only [hg.natDegree_map, natDegree_X_pow] using congrArg natDegree heq.symm
  intro i hi
  apply (hfzero _).mp
  have := congrArg (fun P : K[X] ↦ P.coeff i) heq
  simpa only [coeff_map, coeff_X_pow, hjdeg, if_neg hi.ne] using this

/-- Every lower coefficient of a monic divisor belongs to a prime
containing the lower coefficients of the original monic polynomial. -/
theorem coeff_mem_prime_of_monic_dvd
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {F g : R[X]} (hF : F.Monic) (hg : g.Monic) (hdiv : g ∣ F)
    (hcoeff : ∀ i < F.natDegree, F.coeff i ∈ p) :
    ∀ i < g.natDegree, g.coeff i ∈ p := by
  apply coeff_mem_prime_of_monic_dvd_scaled p (a := 1) p.one_notMem hF hg hcoeff
  simpa using hdiv

end

end HodgeConjecture.CommutativeAlgebra
