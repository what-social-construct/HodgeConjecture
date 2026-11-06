/-
Adapted from AxiomMath/Stacks at f8e70c5dd04bfabcb423d5e325461f527c85a5d6.
Source: StacksFrontier/AlgebraicGeometry/Chow/CalculationMultiplicities/RestrictedDivisors.lean
Only the regular-element and quotient-ring cases are retained.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.CommutativeAlgebra.Multiplicity.Multiplication
public import Mathlib.RingTheory.KrullDimension.Regular

@[expose] public section

namespace AlgebraicGeometry

/-- At a point of the support, the colength of `x` together with that point is finite as soon
as the quotient by `x` has zero-dimensional support. -/
private lemma quotient_length_ne_top {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hxM : Module.supportDim R (QuotSMulTop x M) ≤ 0)
    (q : PrimeSpectrum R) (hq : q ∈ Module.support R M) :
    Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) ≠ ⊤ := by
  apply Module.length_ne_top_iff.mpr
  apply finite_length_of_supportDim_le_zero
  have hs : Module.support R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) ⊆
      Module.support R (QuotSMulTop x M) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    intro p hp
    change Ideal.span {x} ⊔ q.asIdeal ≤ p.asIdeal at hp
    rw [Module.support_quotSMulTop]
    exact ⟨Module.mem_support_mono (show q.asIdeal ≤ p.asIdeal from le_sup_right.trans hp) hq,
      fun y hy => hp (Ideal.mem_sup_left (Ideal.subset_span hy))⟩
  exact (Order.krullDim_le_of_strictMono
    (fun p : Module.support R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) =>
      (⟨p.val, hs p.property⟩ : Module.support R (QuotSMulTop x M)))
    (fun _ _ h => h)).trans hxM

/-- A regular element drops the support dimension: from at most one to at most zero. -/
private lemma supportDim_quotSMulTop_le_zero_of_regular {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : IsSMulRegular M x) (hM : Module.supportDim R M ≤ 1) :
    Module.supportDim R (QuotSMulTop x M) ≤ 0 := by
  have h := (Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
    (fun _ hp => hx.notMem_of_mem_minimalPrimes hp)).trans hM
  cases hd : Module.supportDim R (QuotSMulTop x M) with
  | bot => exact bot_le
  | coe d =>
    rw [hd] at h
    have h : d + 1 ≤ 1 := by exact_mod_cast h
    have hd0 : d ≤ 0 := (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp
      (by simpa using h)
    exact WithBot.coe_le_coe.mpr hd0

/-- The additivity formula for a regular element on a module whose support has dimension one. -/
private lemma length_quotSMulTop_eq_sum_of_regular {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : IsSMulRegular M x) (hM : Module.supportDim R M = 1) :
    Module.length R (QuotSMulTop x M) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
  classical
  have hxM := supportDim_quotSMulTop_le_zero_of_regular x hx hM.le
  have hi := periodicLength_mul_eq_finsum_support x hM.le hxM
  rw [periodicLength_mul_eq_length_quotSMulTop x hx, ← minimal_support_eq_nonclosed hM] at hi
  simp_rw [ord_quotient_eq_length] at hi
  have hs := finite_minimal_support (R := R) (M := M)
  rw [finsum_mem_eq_finite_toFinset_sum _ hs] at hi ⊢
  have hn : (Module.length R (QuotSMulTop x M)).toNat =
      ∑ q ∈ hs.toFinset, (Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal))).toNat *
        (Module.length (Localization.AtPrime q.asIdeal)
          (LocalizedModule q.asIdeal.primeCompl M)).toNat := by
    exact_mod_cast hi
  rw [← ENat.natCast_toNat (Module.length_ne_top_iff.mpr
    (finite_length_of_supportDim_le_zero hxM)), hn]
  push_cast
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' := hs.mem_toFinset.mp hq
  rw [ENat.natCast_toNat (quotient_length_ne_top x hxM q hq'.1),
    ENat.natCast_toNat (localized_length_ne_top q hq')]

/-- **Stacks Project, Tag 02QG, second assertion.** If `x` is a
nonzerodivisor on the one-dimensional quotient `R / I`, then the colength of
`(x, I)` is the sum of the colength of `(x, q)` times the length of
`(R / I)` localized at `q`, over the minimal primes `q` above `I`. -/
public theorem length_quotient_span_sup_eq_sum_minimalPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (I : Ideal R) (hx : IsSMulRegular (R ⧸ I) x)
    (hI : ringKrullDim (R ⧸ I) = 1) :
    Module.length R (R ⧸ (Ideal.span {x} ⊔ I)) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | q.asIdeal ∈ I.minimalPrimes},
        Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl (R ⧸ I)) := by
  have hM : Module.supportDim R (R ⧸ I) = 1 := by
    rw [Module.supportDim_quotient_eq_ringKrullDim, hI]
  have h := length_quotSMulTop_eq_sum_of_regular x hx hM
  rw [(quotSMulTopQuotientEquiv x I).length_eq] at h
  simpa only [minimal_support_iff, Ideal.annihilator_quotient] using h


end AlgebraicGeometry
