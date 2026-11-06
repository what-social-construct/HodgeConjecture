module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-!
# Consecutive primes in the actual quotient

A cover in the prime spectrum of a commutative ring becomes a cover above
zero after quotienting by its lower prime. Consequently the actual image
of the upper prime has height one. Covers here concern prime ideals, not
all ideals; no domain, Noetherianity or catenarity assumption on the
ambient ring is needed.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u

private theorem height_eq_one_of_bot_covBy
    {α : Type*} [PartialOrder α] [OrderBot α] {x : α} (h : (⊥ : α) ⋖ x) :
    Order.height x = 1 := by
  apply le_antisymm
  · apply (Order.height_le_coe_iff (n := 1)).mpr
    intro y hy
    rcases h.eq_or_eq bot_le hy.le with hbot | heq
    · simp [hbot]
    · exact (hy.ne heq).elim
  · simpa only [Order.height_bot, zero_add] using Order.height_add_one_le h.lt

/-- The image of a prime containing the quotient ideal is prime. This
uses the actual quotient map and its actual kernel. -/
theorem primeQuotient_map_isPrime
    (B : Type u) [CommRing B] (p q : PrimeSpectrum B) (hpq : p ≤ q) :
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime := by
  letI : q.asIdeal.IsPrime := q.isPrime
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hpq)

/-- The prime-spectrum quotient correspondence sends a consecutive
prime pair to zero covered by the actual upper image prime. -/
theorem primeQuotient_bot_covBy_map
    (B : Type u) [CommRing B] (p q : PrimeSpectrum B) (h : p ⋖ q) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI := primeQuotient_map_isPrime B p q h.le
    (⊥ : PrimeSpectrum (B ⧸ p.asIdeal)) ⋖
      (⟨q.asIdeal.map (Ideal.Quotient.mk p.asIdeal), inferInstance⟩ :
        PrimeSpectrum (B ⧸ p.asIdeal)) := by
  letI : p.asIdeal.IsPrime := p.isPrime
  letI := primeQuotient_map_isPrime B p q h.le
  let e := p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  let p₀ : PrimeSpectrum.zeroLocus p.asIdeal := ⟨p, by
    change p.asIdeal ≤ p.asIdeal
    exact le_rfl⟩
  let q₀ : PrimeSpectrum.zeroLocus p.asIdeal := ⟨q, by
    change p.asIdeal ≤ q.asIdeal
    exact h.le⟩
  have hsub : p₀ ⋖ q₀ := by
    refine ⟨h.lt, ?_⟩
    intro r hpr hrq
    exact h.2 hpr hrq
  have hbot : e.symm p₀ = ⊥ := by
    apply PrimeSpectrum.ext
    exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk p.asIdeal)).mpr
      (by rw [Ideal.mk_ker])
  have h' := (apply_covBy_apply_iff e.symm).mpr hsub
  rw [hbot] at h'
  exact h'

/-- The actual upper prime modulo a consecutive lower prime has height
one. The ambient ring need not be a domain. -/
theorem primeQuotient_primeHeight_eq_one_of_covBy
    (B : Type u) [CommRing B] (p q : PrimeSpectrum B) (h : p ⋖ q) :
    letI := primeQuotient_map_isPrime B p q h.le
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height = 1 := by
  letI : p.asIdeal.IsPrime := p.isPrime
  letI := primeQuotient_map_isPrime B p q h.le
  change (⟨q.asIdeal.map (Ideal.Quotient.mk p.asIdeal), inferInstance⟩ :
    PrimeSpectrum (B ⧸ p.asIdeal)).asIdeal.height = 1
  rw [PrimeSpectrum.height_eq_orderHeight]
  exact height_eq_one_of_bot_covBy (primeQuotient_bot_covBy_map B p q h)

end

end HodgeConjecture.CommutativeAlgebra
