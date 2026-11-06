module

public import HodgeConjecture.Cycles.AffineDimension
public import HodgeConjecture.Cycles.SupportDimension
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

/-!
# Actual affine point-closure dimensions

The order of scheme points is the reverse of prime-ideal inclusion.
The actual reduced closure of an affine point has the dimension of its
prime quotient. This identifies the geometric quantity used by the cycle
grading without assuming a dimension-function unit-step law.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

/-- The actual affine scheme-point order is the dual of prime-ideal inclusion.
The underlying point map is the identity. -/
def specPointOrderIso (A : Type v) [CommRing A] :
    (Spec (CommRingCat.of A) : Scheme) ≃o (PrimeSpectrum A)ᵒᵈ where
  toEquiv := Equiv.refl _
  map_rel_iff' := by
    intro x y
    change y.asIdeal ≤ x.asIdeal ↔ _
    rw [Scheme.le_iff_specializes]
    exact (PrimeSpectrum.le_iff_specializes (x := y) (y := x))

/-- Prime coheight is the actual dimension of the corresponding quotient. -/
theorem prime_coheight_eq_quotientDim (A : Type v) [CommRing A]
    (p : PrimeSpectrum A) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by
  rw [Order.coheight_eq_krullDim_Ici, ringKrullDim_quotient]
  rfl

/-- In the scheme's closure order, affine point height is prime coheight. -/
theorem spec_point_height_eq_prime_coheight (A : Type v) [CommRing A]
    (p : PrimeSpectrum A) :
    Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p = Order.coheight p :=
  (Order.height_orderIso (specPointOrderIso A) p).symm

/-- The existing actual reduced carrier, not a new proxy for it, has the
dimension of the prime quotient. -/
theorem spec_pointSupport_dimension_eq_quotientDim (A : Type v) [CommRing A]
    (p : PrimeSpectrum A) :
    topologicalKrullDim (pointSupport (Spec (CommRingCat.of A)) p).val.subscheme =
      ringKrullDim (A ⧸ p.asIdeal) := by
  rw [← point_height_eq_supportDim, spec_point_height_eq_prime_coheight,
    prime_coheight_eq_quotientDim]

/-- The actual residue field is a fraction field of the prime quotient,
so its transcendence degree agrees with that quotient's. -/
theorem primeQuotient_trdeg_eq_residueField (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] (p : PrimeSpectrum A) :
    Algebra.trdeg k (A ⧸ p.asIdeal) = Algebra.trdeg k p.asIdeal.ResidueField := by
  letI : IsScalarTower k (A ⧸ p.asIdeal) p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply k A (A ⧸ p.asIdeal),
        IsScalarTower.algebraMap_apply k A p.asIdeal.ResidueField]
      rfl
  exact trdeg_eq_of_isFractionRing k (A ⧸ p.asIdeal) p.asIdeal.ResidueField

/-- For a finite-type algebra, the actual reduced closure of each point
has dimension equal to the finite transcendence degree of its residue field.
The ambient algebra need not be a domain. -/
theorem spec_pointSupport_dimension_eq_residueField_trdeg
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    topologicalKrullDim (pointSupport (Spec (CommRingCat.of A)) p).val.subscheme =
      ((Algebra.trdeg k p.asIdeal.ResidueField).toNat : WithBot ℕ∞) := by
  rw [spec_pointSupport_dimension_eq_quotientDim,
    ringKrullDim_eq_trdeg_toNat_of_finiteType k (A ⧸ p.asIdeal),
    primeQuotient_trdeg_eq_residueField]

/-- Integer grading can use the actual residue-field value on an affine
chart; this is an equality of values, not yet a unit-step theorem. -/
theorem spec_point_height_toNat_eq_residueField_trdeg
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    (Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p).toNat =
      (Algebra.trdeg k p.asIdeal.ResidueField).toNat := by
  have h : (Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p : WithBot ℕ∞) =
      ((Algebra.trdeg k p.asIdeal.ResidueField).toNat : WithBot ℕ∞) := by
    exact (point_height_eq_supportDim (Spec (CommRingCat.of A)) p).trans
      (spec_pointSupport_dimension_eq_residueField_trdeg k A p)
  have h' : Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p =
      ((Algebra.trdeg k p.asIdeal.ResidueField).toNat : ℕ∞) := WithBot.coe_injective h
  rw [h']
  simp

/-- Proper specialization strictly lowers the actual affine residue-field
transcendence degree, also on reducible ambient algebras. -/
theorem prime_residueField_trdeg_toNat_strictAnti
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] :
    StrictAnti (fun p : PrimeSpectrum A ↦ (Algebra.trdeg k p.asIdeal.ResidueField).toNat) := by
  intro p q hpq
  have h := primeQuotient_trdeg_toNat_strictAnti k A hpq
  change (Algebra.trdeg k (A ⧸ q.asIdeal)).toNat <
    (Algebra.trdeg k (A ⧸ p.asIdeal)).toNat at h
  rw [primeQuotient_trdeg_eq_residueField k A p,
    primeQuotient_trdeg_eq_residueField k A q] at h
  exact h

end

end HodgeConjecture.SchemeCycles
