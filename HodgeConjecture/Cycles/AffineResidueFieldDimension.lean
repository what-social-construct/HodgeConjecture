module

public import HodgeConjecture.Cycles.AffineResidueField
public import HodgeConjecture.Cycles.AffineDimensionFunction

@[expose] public section

/-!
# Dimension values in the actual scheme residue fields

The structural-field affine algebra equivalence identifies the full
transcendence-degree cardinal of the actual scheme residue field with
that of the prime-localization residue field. Finite type then makes
that value finite and identifies it with the already constructed affine
dimension function. The existing function is reused, not redefined.

Actual open-immersion residue maps preserve the full transcendence degree
over the structural field. This is a value comparison; agreement of affine
chart presentations and global dimension-function assembly are separate.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory Algebra

noncomputable section

universe u

variable (k : Type u) [Field k] (A : Type u) [CommRing A] [Algebra k A]

/-- The actual affine scheme and prime-localization residue fields have
equal transcendence-degree cardinals, without a finite-type premise. -/
theorem spec_schemeResidueField_trdeg_eq (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x) =
      Algebra.trdeg k x.asIdeal.ResidueField := by
  letI := residueFieldBaseAlgebra k (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
  exact (specResidueFieldAlgEquiv k A x).trdeg_eq

/-- Finite type proves finiteness of the actual scheme residue degree
before any passage to a natural-number value. -/
theorem spec_schemeResidueField_trdeg_lt_aleph0 [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x) < Cardinal.aleph0 := by
  letI := residueFieldBaseAlgebra k (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
  rw [spec_schemeResidueField_trdeg_eq, ← primeQuotient_trdeg_eq_residueField k A x]
  exact trdeg_lt_aleph0_of_finiteType (R := k) (S := A ⧸ x.asIdeal)

/-- The existing affine dimension function is the degree of the actual
scheme residue field with its independently defined structural action. -/
theorem DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg
    [Algebra.FiniteType k A] (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    ofSpecFiniteType k A x =
      ((Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x)).toNat : ℤ) := by
  letI := residueFieldBaseAlgebra k (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
  rw [spec_schemeResidueField_trdeg_eq]
  rfl

/-- Open-immersion residue-field equivalence preserves the full structural
transcendence-degree cardinal. Neither source needs to be affine or finite type. -/
theorem residueFieldBase_trdeg_eq_of_isOpenImmersion {X Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    Algebra.trdeg k (Y.residueField (f.base x)) = Algebra.trdeg k (X.residueField x) := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  exact (residueFieldBaseAlgEquivOfIsOpenImmersion k p f x).trdeg_eq

end

end HodgeConjecture.SchemeCycles
