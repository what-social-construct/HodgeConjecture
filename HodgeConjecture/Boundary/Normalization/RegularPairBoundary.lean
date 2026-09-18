import HodgeConjecture.Boundary.Normalization.BoundaryPole
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regular pairs in the fixed--moving boundary ideal

A nonzero first element and a second element acting injectively modulo the
first exclude height-one primes containing their ideal. The proof uses the
prescribed-element height-one denominator and cancellation on the existing
quotient module.

For a normalized cover, witnesses from the fixed-locus and moving-boundary
summands therefore establish conjugate-boundary separation. Their existence
is explicit geometric input; the construction uses no new ideal or carrier.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.NormalizationInertia

noncomputable section

section Algebra

variable {T : Type*} [CommRing T] [IsDomain T] [IsNoetherianRing T]

/-- An ideal containing a nonzero element and an element regular modulo it
is contained in no height-one prime. -/
theorem not_le_heightOne_of_regularPair
    (J : Ideal T) (f g : T) (hf : f ∈ J) (hg : g ∈ J) (hf0 : f ≠ 0)
    (hRegular : IsSMulRegular (T ⧸ Ideal.span {f}) g)
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1) :
    ¬ J ≤ p.asIdeal := by
  intro hJp
  obtain ⟨t, n, htp, hclear⟩ :=
    exists_heightOne_boundary_denominator_of_ne_zero J p hp hJp f hf0
  have hpow : g ^ n ∈ J ^ n := Ideal.pow_mem_pow hg n
  have ht : t ∈ Ideal.span {f} :=
    mem_of_isSMulRegular_quotient_of_smul_mem (hRegular.pow n)
      (by simpa only [smul_eq_mul, mul_comm] using hclear (g ^ n) hpow)
  exact htp ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hJp hf))) ht)

end Algebra

open AlgebraicGeometry CategoryTheory

universe u

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)
variable [IsNoetherianRing B]

local notation "T₀" => NormalClosureNormalizationRing (B := B) (N := N)

omit [IsFractionRing B K] in
/-- Independent regular-pair witnesses in the fixed and moving summands
suffice for the existing boundary-separation endpoint. -/
theorem conjugateBoundarySeparation_of_fixedMoving_regularPairs
    (hPairs : ∀ (I : Subgroup C.GaloisGroup), I ≠ ⊥ →
      ∃ f g : T₀, f ∈ fixedLocusIdeal I ∧ f ≠ 0 ∧
        g ∈ movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I ∧
        IsSMulRegular (T₀ ⧸ Ideal.span {f}) g) :
    ConjugateBoundarySeparation C := by
  letI : IsNoetherianRing T₀ := normalization_isNoetherianRing C
  intro I hI p hp
  obtain ⟨f, g, hf, hf0, hg, hRegular⟩ := hPairs I hI
  apply not_le_heightOne_of_regularPair (fixedMovingBoundaryIdeal C I)
    f g (show f ∈ fixedLocusIdeal I +
      movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I from
      Ideal.mem_sup_left hf)
    (show g ∈ fixedLocusIdeal I +
      movingBoundaryIdeal (pulledBackConjugateBoundaryIdeal C) I from
      Ideal.mem_sup_right hg) hf0 hRegular p hp

end

end HodgeConjecture.NormalizationInertia
