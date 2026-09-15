import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Krull dimension under integral extensions

Incomparability makes contraction strictly monotone on prime chains. Lying
over and going up lift every finite prime chain along an injective integral
map. These two actual chain comparisons prove equality of Krull dimensions;
no Noetherianity, domain, or finite-dimensionality assumption is needed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open Order

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S] [Algebra.IsIntegral R S]

/-- Incomparability gives strict contraction along an integral extension. -/
theorem integral_specComap_strictMono :
    StrictMono (algebraMap R S).specComap := by
  intro P Q hPQ
  change P.asIdeal < Q.asIdeal at hPQ
  obtain ⟨hle, x, hxQ, hxP⟩ := SetLike.lt_iff_le_and_exists.mp hPQ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩
    (Algebra.IsIntegral.isIntegral x)

/-- Integral contraction does not increase the lengths of prime chains. -/
theorem ringKrullDim_le_of_integral : ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono _ (integral_specComap_strictMono R S)

/-- Lying over and going up lift a finite chain, preserving its length and last point. -/
theorem exists_primeSeries_lift_of_injective_integral
    (hinj : Function.Injective (algebraMap R S)) (s : LTSeries (PrimeSpectrum R)) :
    ∃ t : LTSeries (PrimeSpectrum S), t.length = s.length ∧
      (algebraMap R S).specComap t.last = s.last := by
  induction s using RelSeries.inductionOn' with
  | singleton P =>
      have hbot : (⊥ : Ideal S).comap (algebraMap R S) ≤ P.asIdeal := by
        rw [← RingHom.ker_eq_comap_bot,
          (RingHom.injective_iff_ker_eq_bot (algebraMap R S)).mp hinj]
        exact bot_le
      obtain ⟨Q, _, hQ, hQP⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal S) hbot
      refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, ?_⟩
      exact PrimeSpectrum.ext_iff.mpr hQP
  | snoc s P hP ih =>
      obtain ⟨t, hlen, hlast⟩ := ih
      have hle : t.last.asIdeal.comap (algebraMap R S) ≤ P.asIdeal := by
        change (algebraMap R S).specComap t.last ≤ P
        rw [hlast]
        exact hP.le
      obtain ⟨Q, htQ, hQ, hQP⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P.asIdeal t.last.asIdeal hle
      let Q' : PrimeSpectrum S := ⟨Q, hQ⟩
      have hQP' : (algebraMap R S).specComap Q' = P := PrimeSpectrum.ext_iff.mpr hQP
      have hlt : t.last < Q' := by
        refine lt_of_le_of_ne htQ ?_
        intro heq
        have := congrArg (algebraMap R S).specComap heq
        rw [hlast, hQP'] at this
        exact hP.ne this
      refine ⟨t.snoc Q' hlt, ?_, ?_⟩
      · simpa using hlen
      · simpa using hQP'

/-- An injective integral extension has at least as many prime-chain lengths as its base. -/
theorem ringKrullDim_le_of_injective_integral
    (hinj : Function.Injective (algebraMap R S)) : ringKrullDim R ≤ ringKrullDim S := by
  change (⨆ s : LTSeries (PrimeSpectrum R), (s.length : WithBot ℕ∞)) ≤ _
  apply iSup_le
  intro s
  obtain ⟨t, hlen, _⟩ := exists_primeSeries_lift_of_injective_integral R S hinj s
  rw [← hlen]
  exact LTSeries.length_le_krullDim t

/-- Krull dimension is invariant under an injective integral algebra map. -/
theorem ringKrullDim_eq_of_injective_integral
    (hinj : Function.Injective (algebraMap R S)) : ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_injective_integral R S hinj)
    (ringKrullDim_le_of_integral R S)

end HodgeConjecture.SchemeCycles
