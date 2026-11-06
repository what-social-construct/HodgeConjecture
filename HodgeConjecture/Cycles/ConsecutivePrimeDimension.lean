module

public import HodgeConjecture.CommutativeAlgebra.PrimeQuotientCover
public import HodgeConjecture.Cycles.AffinePrimeDimension
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# The unit dimension drop between consecutive primes

For consecutive points in the prime spectrum, the upper prime has height
one in the actual quotient by the lower prime. Apply the finite-type
domain prime formula to that quotient and identify the actual double
quotient. The ambient algebra need not be a domain or reduced.

The cover relation is in the prime spectrum, not the full ideal lattice.
The residue-field adapter reuses the actual prime-localization residue
fields. Transport of this law to general scheme charts is separate.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open CommutativeAlgebra

noncomputable section

universe u v

variable (k : Type u) [Field k] (B : Type v) [CommRing B]
  [Algebra k B] [Algebra.FiniteType k B]

/-- Consecutive prime quotients differ in finite transcendence degree by
exactly one. Only the actual lower-prime quotient needs to be a domain. -/
theorem primeQuotient_trdeg_toNat_add_one_of_covBy
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    (Algebra.trdeg k (B ⧸ q.asIdeal)).toNat + 1 =
      (Algebra.trdeg k (B ⧸ p.asIdeal)).toNat := by
  let q' := q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)
  letI : q'.IsPrime := primeQuotient_map_isPrime B p q hpq.le
  have hdim := primeHeight_add_quotient_trdeg_eq k (B ⧸ p.asIdeal) q'
  rw [primeQuotient_primeHeight_eq_one_of_covBy B p q hpq] at hdim
  have hquot : Algebra.trdeg k ((B ⧸ p.asIdeal) ⧸ q') =
      Algebra.trdeg k (B ⧸ q.asIdeal) :=
    (DoubleQuot.quotQuotEquivQuotOfLEₐ k
      (show p.asIdeal ≤ q.asIdeal from hpq.le)).trdeg_eq
  rw [hquot] at hdim
  have hnat : 1 + (Algebra.trdeg k (B ⧸ q.asIdeal)).toNat =
      (Algebra.trdeg k (B ⧸ p.asIdeal)).toNat := by
    exact_mod_cast hdim
  simpa only [add_comm] using hnat

/-- The unit drop in the actual prime-localization residue fields. -/
theorem prime_residueField_trdeg_toNat_add_one_of_covBy
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    (Algebra.trdeg k q.asIdeal.ResidueField).toNat + 1 =
      (Algebra.trdeg k p.asIdeal.ResidueField).toNat := by
  rw [← primeQuotient_trdeg_eq_residueField k B p,
    ← primeQuotient_trdeg_eq_residueField k B q]
  exact primeQuotient_trdeg_toNat_add_one_of_covBy k B p q hpq

include k in
/-- The actual quotient-ring dimensions have the same unit drop, even
when the ambient finite-type algebra is reducible or nonreduced. -/
theorem primeQuotient_dimension_add_one_of_covBy
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    ringKrullDim (B ⧸ q.asIdeal) + 1 = ringKrullDim (B ⧸ p.asIdeal) := by
  rw [ringKrullDim_eq_trdeg_toNat_of_finiteType k (B ⧸ q.asIdeal),
    ringKrullDim_eq_trdeg_toNat_of_finiteType k (B ⧸ p.asIdeal)]
  exact_mod_cast primeQuotient_trdeg_toNat_add_one_of_covBy k B p q hpq

end

end HodgeConjecture.SchemeCycles
