/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Source: StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/IntersectionInvertibleSheaf.lean
Only the one-dimensional colength formula is retained.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.CommutativeAlgebra.Multiplicity.RestrictedDivisors
public import Mathlib.Data.ENat.BigOperators

@[expose] public section

namespace AlgebraicGeometry

/-- Localizing `R ⧸ (0)` at a prime gives the localization of `R` at that prime, so the two have
the same length over it. -/
theorem length_localizedModule_quotientBot {R : Type*} [CommRing R] (p : PrimeSpectrum R) :
    Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (R ⧸ (⊥ : Ideal R))) =
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
  (IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (R ⧸ (⊥ : Ideal R)))
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal))
    (Localization.AtPrime p.asIdeal) (AlgEquiv.quotientBot R R).toLinearEquiv).length_eq

/-- **Stacks 02QG**, in the form used for cycles. For a nonzerodivisor `a` of a one-dimensional
Noetherian local ring `R` of finite colength, the colength of `(a)` is the sum over the minimal
primes `p` of `R` of the length of `R_p` times the colength of `(a, p)`. -/
theorem natCast_length_quotient_span_eq_sum_minimalPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (a : R) (ha : IsSMulRegular R a)
    (hdim : ringKrullDim R = 1)
    (hfinite : Module.length R (R ⧸ Ideal.span {a}) ≠ ⊤) :
    ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) =
      ∑ᶠ p : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal))).toNat : ℤ) := by
  classical
  have hfin : {p : PrimeSpectrum R | p.asIdeal ∈ minimalPrimes R}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)
  let : Fintype {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R} := hfin.fintype
  have h := length_quotient_span_sup_eq_sum_minimalPrimes a ⊥
    (((AlgEquiv.quotientBot R R).toLinearEquiv.isSMulRegular_congr a).mpr ha)
    ((RingEquiv.quotientBot R).ringKrullDim.trans hdim)
  rw [sup_bot_eq, ← finsum_set_coe_eq_finsum_mem] at h
  simp_rw [length_localizedModule_quotientBot] at h
  change Module.length R (R ⧸ Ideal.span {a}) =
    ∑ᶠ p : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R},
      Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal)) *
        Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal) at h
  rw [finsum_eq_sum_of_fintype] at h ⊢
  have hterms (p : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}) :
      Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal)) *
        Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfinite
    rw [h]
    exact Finset.single_le_sum
      (f := fun q : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R} =>
        Module.length R (R ⧸ (Ideal.span {a} ⊔ q.1.asIdeal)) *
          Module.length (Localization.AtPrime q.1.asIdeal)
            (Localization.AtPrime q.1.asIdeal))
      (fun _ _ => zero_le) (Finset.mem_univ p)
  rw [h, ENat.toNat_sum (fun p _ => hterms p), Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENat.toNat_mul, Nat.cast_mul, mul_comm]


end AlgebraicGeometry
