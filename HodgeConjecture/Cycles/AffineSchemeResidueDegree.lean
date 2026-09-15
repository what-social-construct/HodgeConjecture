import HodgeConjecture.Cycles.AffineSchemeDimensionFunction
import HodgeConjecture.Cycles.AffineResidueFieldDimension

/-!
# Structural residue degrees on actual affine schemes

The existing height-defined dimension function on an affine scheme locally
of finite type over a field equals its actual structural residue-field
degree. The structural morphism supplies the sections algebra, and the
canonical affine isomorphism transports residue degrees through the
base-compatible geometric residue map. Finiteness is proved before any
natural-number conversion.

Affine open immersions preserve these dimension-function values. This is
a comparison of the existing affine functions, not a new global dimension
function or a claim of unrestricted height invariance under open immersion.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem affine_residueDegree_and_pointHeight
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 ∧
      ((Order.height x).toNat : ℤ) =
        ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) := by
  letI := residueFieldBaseAlgebra k p x
  let q : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of k) := X.isoSpec.inv ≫ p
  haveI : LocallyOfFiniteType q := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective q
  change Spec.map φ = q at hφ
  have h : RingHom.FiniteType φ.hom := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
    rw [hφ]
    infer_instance
  algebraize [φ.hom]
  have hcomp : X.isoSpec.hom ≫ Spec.map φ = p := by
    rw [hφ]
    simp only [q, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hdeg := residueFieldBase_trdeg_eq_of_isOpenImmersion k
    (Spec.map φ) X.isoSpec.hom x
  simp only [hcomp] at hdeg
  constructor
  · rw [← hdeg]
    exact spec_schemeResidueField_trdeg_lt_aleph0 k Γ(X, ⊤) (X.isoSpec.hom.base x)
  · rw [← hdeg, ← DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg,
      DimensionFunction.ofSpecFiniteType_eq_pointHeight, point_height_iso]

/-- The actual structural residue degree on an affine scheme locally of
finite type over a field is finite. No sections algebra is an input. -/
theorem affine_schemeResidueField_trdeg_lt_aleph0
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 :=
  (affine_residueDegree_and_pointHeight k X p x).1

/-- The existing dimension function on an actual affine structural scheme
equals the finite degree of its actual scheme residue field. -/
theorem DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    ofAffineLocallyOfFiniteType k X p x =
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) :=
  (affine_residueDegree_and_pointHeight k X p x).2

/-- Affine open immersions over the structural field preserve the values
of the existing dimension functions, by actual residue-field compatibility. -/
theorem DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    ofAffineLocallyOfFiniteType k X (f ≫ p) x =
      ofAffineLocallyOfFiniteType k Y p (f.base x) := by
  rw [ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg,
    ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg,
    residueFieldBase_trdeg_eq_of_isOpenImmersion k p f x]

end

end HodgeConjecture.SchemeCycles
