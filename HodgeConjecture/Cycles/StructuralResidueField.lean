import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Algebra.Equiv

/-!
# Structural base actions on actual scheme residue fields

A structural morphism to `Spec k` gives a ring map from `k` to each
actual scheme residue field by pulling back global constants and evaluating.
This defines the base algebra independently of any affine residue-field
comparison. The algebra is an ordinary definition, installed only locally.

Naturality of actual evaluation proves compatibility of the existing
residue-field maps with this base action. In particular, an open immersion
gives an actual base-algebra equivalence. No field, finite-type, reducedness
or affine-source assumption is needed for these comparisons.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

variable (k : Type u) [CommRing k] {X Y Z : Scheme.{u}}

/-- Pull back actual global constants along the structural morphism and
evaluate at the point in its actual stalk residue field. -/
def residueFieldBaseMap (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    k →+* X.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom

/-- The structural algebra is an ordinary definition, not a global instance. -/
def residueFieldBaseAlgebra (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Algebra k (X.residueField x) :=
  (residueFieldBaseMap k p x).toAlgebra

/-- The local algebra retains the independently defined structural ring map. -/
theorem residueFieldBaseAlgebra_algebraMap
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    letI := residueFieldBaseAlgebra k p x
    algebraMap k (X.residueField x) = residueFieldBaseMap k p x := rfl

/-- Actual residue-field maps commute with structural constants. -/
theorem residueFieldBaseMap_comp
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X) :
    (f.residueFieldMap x).hom.comp (residueFieldBaseMap k p (f.base x)) =
      residueFieldBaseMap k (f ≫ p) x := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫
    Y.Γevaluation (f.base x) ≫ f.residueFieldMap x).hom = _
  rw [Scheme.Γevaluation_naturality]
  simp only [residueFieldBaseMap, Scheme.comp_appTop, Category.assoc]

/-- The existing residue-field homomorphism, with its structural base
compatibility proved rather than supplied. -/
def residueFieldBaseAlgHom
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    Y.residueField (f.base x) →ₐ[k] X.residueField x := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  exact
    { (f.residueFieldMap x).hom with
      commutes' := fun a ↦ congrArg (fun h : k →+* X.residueField x ↦ h a)
        (residueFieldBaseMap_comp k p f x) }

/-- Bundling does not change the underlying geometric residue-field map. -/
@[simp]
theorem residueFieldBaseAlgHom_apply
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X)
    (a : Y.residueField (f.base x)) :
    residueFieldBaseAlgHom k p f x a = f.residueFieldMap x a := rfl

/-- An actual open immersion induces an equivalence of structural base algebras. -/
def residueFieldBaseAlgEquivOfIsOpenImmersion
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    Y.residueField (f.base x) ≃ₐ[k] X.residueField x := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  exact AlgEquiv.ofRingEquiv
    (f := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv)
    (residueFieldBaseAlgHom k p f x).commutes

/-- The equivalence keeps the original open-immersion residue-field map. -/
@[simp]
theorem residueFieldBaseAlgEquivOfIsOpenImmersion_apply
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (a : Y.residueField (f.base x)) :
    residueFieldBaseAlgEquivOfIsOpenImmersion k p f x a = f.residueFieldMap x a := rfl

end

end HodgeConjecture.SchemeCycles
