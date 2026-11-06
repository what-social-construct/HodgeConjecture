module

public import HodgeConjecture.Cycles.AffineSchemeResidueDegree

@[expose] public section

/-!
# Pointwise residue degrees and affine-chart values

Every point of a scheme locally of finite type over a field has finite
structural residue-field transcendence degree. One actual affine chart
through the point is enough; no finite subcover or global dimension bound
is needed.

The existing dimension function on any affine open chart equals the
structural residue degree at its ambient image. Consequently two charts
give equal values at points with the same ambient image. All comparisons
use the existing actual residue fields and their structural scalar actions.
These are pointwise value theorems, not a global dimension-function
constructor or a proof of its specialization and cover laws.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Locally finite type over a field suffices for finite actual structural
residue degree at every point, without affineness or quasi-compactness. -/
theorem schemeResidueField_trdeg_lt_aleph0
    (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  letI := residueFieldBaseAlgebra k p ((X.affineCover.f i).base y)
  rw [residueFieldBase_trdeg_eq_of_isOpenImmersion k p (X.affineCover.f i) y]
  exact affine_schemeResidueField_trdeg_lt_aleph0 k (X.affineCover.X i)
    (X.affineCover.f i ≫ p) y

/-- The existing affine-chart dimension value is the actual structural
residue degree at its ambient image; the ambient scheme need not be affine. -/
theorem affineChart_dimension_eq_schemeResidueField_trdeg
    (k : Type u) [Field k] {X U : Scheme.{u}} [IsAffine U]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (i : U ⟶ X) [IsOpenImmersion i] (x : U) :
    letI := residueFieldBaseAlgebra k p (i.base x)
    DimensionFunction.ofAffineLocallyOfFiniteType k U (i ≫ p) x =
      ((Algebra.trdeg k (X.residueField (i.base x))).toNat : ℤ) := by
  rw [DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg,
    residueFieldBase_trdeg_eq_of_isOpenImmersion k p i x]

/-- Two actual affine charts assign the same existing dimension value
to points whose actual images in the ambient scheme agree. -/
theorem affineChart_dimension_eq_of_eq_image
    (k : Type u) [Field k] {X U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (i : U ⟶ X) [IsOpenImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    (x : U) (y : V) (h : i.base x = j.base y) :
    DimensionFunction.ofAffineLocallyOfFiniteType k U (i ≫ p) x =
      DimensionFunction.ofAffineLocallyOfFiniteType k V (j ≫ p) y := by
  let d : X → ℤ := fun z ↦
    letI := residueFieldBaseAlgebra k p z
    ((Algebra.trdeg k (X.residueField z)).toNat : ℤ)
  calc
    _ = d (i.base x) := affineChart_dimension_eq_schemeResidueField_trdeg k p i x
    _ = d (j.base y) := congrArg d h
    _ = _ := (affineChart_dimension_eq_schemeResidueField_trdeg k p j y).symm

end

end HodgeConjecture.SchemeCycles
