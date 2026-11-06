/-
The minimal-prime calculation is adapted from AxiomMath/Stacks at
f8e70c5dd04bfabcb423d5e325461f527c85a5d6, FlatPullbackPrincipalDivisor.lean.
Apache-2.0; see third_party/axiom-stacks/LICENSE and README.md.
-/
module

public import HodgeConjecture.CommutativeAlgebra.FlatLocalLength
public import HodgeConjecture.CommutativeAlgebra.Multiplicity.MinimalPrimeColength
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

/-!
# Flat local multiplicities, with the actual minimal-prime lengths

These formulas compare principal quotients across a flat local map and
then decompose them over the minimal primes of the original source ring.
The signed formula is the numerator-minus-denominator calculation needed
for principal-divisor pullback. No reducedness of the source is required.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

open AlgebraicGeometry

noncomputable section

/-- A quotient by a principal ideal together with a surjection's kernel is the actual
principal quotient in the target, with its target-ring length. -/
theorem length_quotient_span_sup_ker {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (a : R) :
    Module.length R (R ⧸ (Ideal.span {a} ⊔ RingHom.ker φ)) =
      Module.length S (S ⧸ Ideal.span {φ a}) := by
  let J : Ideal S := Ideal.span {φ a}
  let ψ : R →+* S ⧸ J := (Ideal.Quotient.mk J).comp φ
  have hψ : Function.Surjective ψ := Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ψ = Ideal.span {a} ⊔ RingHom.ker φ := by
    rw [← RingHom.comap_ker, Ideal.mk_ker,
      show J = Ideal.map φ (Ideal.span {a}) by rw [Ideal.map_span, Set.image_singleton],
      Ideal.comap_map_of_surjective φ hφ, ← RingHom.ker_eq_comap_bot]
  letI : Algebra R S := φ.toAlgebra
  letI : Algebra R (S ⧸ J) := ψ.toAlgebra
  letI : IsScalarTower R S (S ⧸ J) := IsScalarTower.of_algebraMap_eq' rfl
  have hlen : Module.length R (R ⧸ RingHom.ker ψ) = Module.length R (S ⧸ J) :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R (S ⧸ J))
      hψ).toLinearEquiv.length_eq
  rw [← hker, hlen]
  exact Module.length_eq_of_surjective (M := S ⧸ J) hφ

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsNoetherianRing B]

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] in
/-- Flatness retains the regularity of every nonzero element of a domain. -/
theorem isSMulRegular_algebraMap_of_ne_zero [IsDomain A] {a : A} (ha : a ≠ 0) :
    IsSMulRegular B (algebraMap A B a) := by
  have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
    (mem_nonZeroDivisors_of_ne_zero ha)
  intro b c hbc
  apply h
  simpa [Algebra.smul_def] using hbc

/-- The flat multiplicity times a principal colength equals the weighted
sum of the actual minimal-prime colengths. -/
theorem flatLocal_colength_eq_sum_minimalPrimes (hdim : ringKrullDim B = 1)
    (a : A) (hreg : IsSMulRegular B (algebraMap A B a)) :
    ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) *
        ((Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map
          (algebraMap A B))).toNat : ℤ) =
      ∑ᶠ p : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
        ((Module.length B (B ⧸ (Ideal.span {algebraMap A B a} ⊔ p.1.asIdeal))).toNat : ℤ) := by
  letI : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by rw [hdim]; norm_num)
  have hnonzero : algebraMap A B a ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro other hzero
    exact hreg (by simpa [smul_eq_mul, mul_comm] using hzero)
  have hfinite : Module.length B (B ⧸ Ideal.span {algebraMap A B a}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton B hnonzero)
  rw [← natCast_length_quotient_span_eq_sum_minimalPrimes (algebraMap A B a)
    hreg hdim hfinite, length_quotient_span_algebraMap_of_flat A B a,
    ENat.toNat_mul, Nat.cast_mul]

/-- Subtracting the two principal-quotient formulas gives the signed
coefficient calculation, retaining each component's nilpotent multiplicity. -/
theorem flatLocal_length_difference_eq_sum_minimalPrimes [IsDomain A]
    (hdim : ringKrullDim B = 1) (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    (((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) -
      ((Module.length A (A ⧸ Ideal.span {b})).toNat : ℤ)) *
        ((Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map
          (algebraMap A B))).toNat : ℤ) =
      ∑ᶠ p : {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
        (((Module.length B (B ⧸ (Ideal.span {algebraMap A B a} ⊔ p.1.asIdeal))).toNat : ℤ) -
         ((Module.length B (B ⧸ (Ideal.span {algebraMap A B b} ⊔ p.1.asIdeal))).toNat : ℤ)) := by
  classical
  have hfin : {p : PrimeSpectrum B | p.asIdeal ∈ minimalPrimes B}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing B ⊥).preimage
      (fun p _ q _ h ↦ PrimeSpectrum.ext h)
  letI : Fintype {p : PrimeSpectrum B // p.asIdeal ∈ minimalPrimes B} := hfin.fintype
  rw [sub_mul,
    flatLocal_colength_eq_sum_minimalPrimes hdim a (isSMulRegular_algebraMap_of_ne_zero ha),
    flatLocal_colength_eq_sum_minimalPrimes hdim b (isSMulRegular_algebraMap_of_ne_zero hb)]
  simp only [finsum_eq_sum_of_fintype, mul_sub, Finset.sum_sub_distrib]

end

end HodgeConjecture.CommutativeAlgebra
