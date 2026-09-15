import HodgeConjecture.Cycles.ResidueNormalizationLocalization
import HodgeConjecture.Cycles.LocalizationTranscendenceDegree
import HodgeConjecture.Cycles.AffineSupportDimension

/-!
# The prime dimension formula for finite-type domains

The actual residue-normalization localization preserves transcendence
degree over the original field. Its canonical fraction-field scalar tower
splits this degree into the normalization variable count and the generic
fiber's degree. Combining this with the proved maximal-height comparison
gives the prime dimension formula, including the actual residue field and
prime-localization interfaces. The coefficient fraction field is not
assumed finite type over the original field.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open CommutativeAlgebra

noncomputable section

universe u v

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

/-- The actual polynomial generic fiber splits the finite transcendence
degree over the original field. Only an injective polynomial map is needed;
neither it nor its quotient composite is assumed integral. -/
theorem polynomial_genericFiber_trdeg_toNat_add (n : ℕ)
    (f : MvPolynomial (Fin n) k →ₐ[k] B) (hinj : Function.Injective f) :
    letI := f.toRingHom.toAlgebra
    let B' := Localization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
    letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
    n + (Algebra.trdeg (FractionRing (MvPolynomial (Fin n) k)) B').toNat =
      (Algebra.trdeg k B).toNat := by
  algebraize [f.toRingHom]
  let P := MvPolynomial (Fin n) k
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors P)
  let B' := Localization M
  let K := FractionRing P
  letI := genericFiberAlgebra P B B'
  letI : IsScalarTower P K B' := genericFiberAlgebra_isScalarTower P B B'
  letI : IsScalarTower k K B' := genericFiber_isScalarTower_base P B' k K
  letI : Algebra.FiniteType P B := Algebra.FiniteType.of_restrictScalars_finiteType k P B
  letI : Algebra.FiniteType K B' := genericFiber_finiteType P B B'
  letI : IsDomain B' := genericFiber_isDomain P B B' hinj
  have hlocal : Algebra.trdeg k B = Algebra.trdeg k B' :=
    trdeg_eq_of_isLocalization k B B' M
      (genericFiber_denominators_le_nonZeroDivisors P B hinj)
  have hK : Algebra.trdeg k K = n := by
    rw [← trdeg_eq_fractionRing k P]
    simp only [P, MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Fintype.card_fin,
      Cardinal.lift_natCast]
  have hfiniteK : Algebra.trdeg k K < Cardinal.aleph0 := by
    rw [hK]
    exact Cardinal.nat_lt_aleph0 n
  have hfiniteB' : Algebra.trdeg K B' < Cardinal.aleph0 :=
    trdeg_lt_aleph0 (R := K) (S := B')
  have h := congrArg Cardinal.toNat (lift_trdeg_add_eq k K B')
  rw [Cardinal.toNat_lift_add_lift hfiniteK hfiniteB', Cardinal.toNat_lift,
    ← hlocal, hK] at h
  simpa using h

/-- Every prime of a finite-type domain satisfies the dimension formula
over the original field. Its height is not assumed finite: finiteness is
a consequence of this equality with the finite transcendence degree. -/
theorem primeHeight_add_quotient_trdeg_eq (q : Ideal B) [q.IsPrime] :
    q.primeHeight + ((Algebra.trdeg k (B ⧸ q)).toNat : ℕ∞) =
      ((Algebra.trdeg k B).toNat : ℕ∞) := by
  obtain ⟨n, f, hf, hinj, hint⟩ := exists_lifted_residue_normalization k B q
  have hheight := primeHeight_eq_residueNormalization_trdeg k B q n f hinj hint
  have hsum := polynomial_genericFiber_trdeg_toNat_add k B n f hf
  rw [trdeg_eq_normalization_size k (B ⧸ q) n ((Ideal.Quotient.mkₐ k q).comp f)
    hinj hint, Cardinal.toNat_natCast, hheight]
  exact_mod_cast (by simpa only [add_comm] using hsum)

/-- Ordinary ideal-height form of the prime dimension formula. -/
theorem height_add_quotient_trdeg_eq (q : Ideal B) [q.IsPrime] :
    q.height + ((Algebra.trdeg k (B ⧸ q)).toNat : ℕ∞) =
      ((Algebra.trdeg k B).toNat : ℕ∞) := by
  rw [Ideal.height_eq_primeHeight]
  exact primeHeight_add_quotient_trdeg_eq k B q

/-- The residue field is the existing actual residue field of the prime
localization, not an independently chosen field model. -/
theorem primeHeight_add_residueField_trdeg_eq (q : Ideal B) [q.IsPrime] :
    q.primeHeight + ((Algebra.trdeg k q.ResidueField).toNat : ℕ∞) =
      ((Algebra.trdeg k B).toNat : ℕ∞) := by
  rw [← primeQuotient_trdeg_eq_residueField k B (⟨q, inferInstance⟩ : PrimeSpectrum B)]
  exact primeHeight_add_quotient_trdeg_eq k B q

include k in
/-- Prime height plus the actual quotient's Krull dimension gives the
global dimension of a finite-type domain. -/
theorem height_add_quotient_dimension_eq (q : Ideal B) [q.IsPrime] :
    (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = ringKrullDim B := by
  rw [ringKrullDim_eq_trdeg_toNat_of_finiteType k (B ⧸ q),
    ringKrullDim_eq_trdeg_toNat_of_finiteType k B]
  exact_mod_cast height_add_quotient_trdeg_eq k B q

include k in
/-- The formula for the actual local ring at an arbitrary prime. -/
theorem localization_dimension_add_quotient_dimension_eq (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) + ringKrullDim (B ⧸ q) = ringKrullDim B := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
  exact height_add_quotient_dimension_eq k B q

end

end HodgeConjecture.SchemeCycles
