import HodgeConjecture.Cycles.ConsecutivePrimeDimension
import HodgeConjecture.Cycles.CycleDegree
import HodgeConjecture.Cycles.FiniteTypeDimension

/-!
# The actual dimension function on a finite-type affine spectrum

The residue-field transcendence degree defines an integer-valued dimension
function on the actual scheme `Spec A`. The existing point-order isomorphism
reverses prime inclusion; strict degree drop and the consecutive-prime unit
law prove both dimension-function conditions.

The values equal actual point-closure dimensions. Thus degrees of existing
integral closed supports and their fundamental cycles are their geometric
dimensions. No domain, reducedness or dimension-at-most-one assumption on
the ambient algebra is needed. The residue fields here are the existing
prime-localization residue fields, not a new scheme residue-field model.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u v

variable (k : Type u) [Field k] (A : Type v) [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A]

/-- Finite-type affine spectra carry the actual residue-degree dimension
function, with both strictness and the unit step proved. -/
def DimensionFunction.ofSpecFiniteType : DimensionFunction (Spec (CommRingCat.of A)) where
  toFun x := (Algebra.trdeg k x.asIdeal.ResidueField).toNat
  strictMono := by
    intro x y hxy
    have h := prime_residueField_trdeg_toNat_strictAnti k A
      ((specPointOrderIso A).strictMono hxy)
    change (Algebra.trdeg k x.asIdeal.ResidueField).toNat <
      (Algebra.trdeg k y.asIdeal.ResidueField).toNat at h
    change ((Algebra.trdeg k x.asIdeal.ResidueField).toNat : ℤ) <
      ((Algebra.trdeg k y.asIdeal.ResidueField).toNat : ℤ)
    exact_mod_cast h
  map_covBy := by
    intro x y hxy
    have hp := ((specPointOrderIso A).map_covBy.mpr hxy).ofDual
    exact_mod_cast (prime_residueField_trdeg_toNat_add_one_of_covBy k A y x hp).symm

/-- Evaluation uses the literal prime-localization residue field. -/
@[simp]
theorem DimensionFunction.ofSpecFiniteType_apply (x : Spec (CommRingCat.of A)) :
    ofSpecFiniteType k A x = ((Algebra.trdeg k x.asIdeal.ResidueField).toNat : ℤ) := rfl

/-- The constructed function equals the intrinsic finite point-height value. -/
theorem DimensionFunction.ofSpecFiniteType_eq_pointHeight (x : Spec (CommRingCat.of A)) :
    ofSpecFiniteType k A x = ((Order.height x).toNat : ℤ) := by
  rw [ofSpecFiniteType_apply, spec_point_height_toNat_eq_residueField_trdeg k A x]

/-- Every point has nonnegative degree. -/
theorem DimensionFunction.ofSpecFiniteType_nonneg (x : Spec (CommRingCat.of A)) :
    0 ≤ ofSpecFiniteType k A x := Int.natCast_nonneg _

/-- The degree of an actual integral closed support is its geometric dimension;
finite type ensures that the integer conversion loses no information. -/
theorem supportDegree_ofSpecFiniteType_eq_iff
    (W : IntegralClosedSubscheme (Spec (CommRingCat.of A))) (n : ℕ) :
    supportDegree (DimensionFunction.ofSpecFiniteType k A) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  have h := point_height_toNat_eq (Spec (CommRingCat.of A))
    (spec_topologicalKrullDim_lt_top_of_finiteType k A) (ambientGenericPoint W)
  rw [pointSupport_ambientGenericPoint] at h
  rw [supportDegree, DimensionFunction.ofSpecFiniteType_eq_pointHeight, ← h]
  norm_cast

/-- Existing homogeneous-cycle membership is exactly the carrier-dimension test. -/
theorem fundamentalCycle_mem_ofSpecFiniteType_iff
    (R : Type*) [Semiring R] [Nontrivial R]
    (W : IntegralClosedSubscheme (Spec (CommRingCat.of A))) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofSpecFiniteType k A) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  rw [fundamentalCycle_mem_cyclesOfDegree_iff, supportDegree_ofSpecFiniteType_eq_iff]

end

end HodgeConjecture.SchemeCycles
