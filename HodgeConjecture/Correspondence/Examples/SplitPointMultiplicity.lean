import HodgeConjecture.Correspondence.Examples.SplitPointMaps
import HodgeConjecture.Cycles.ResidueDegree
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Length

/-!
# Multiplicity one at actual split rational points

The stalk of a finite split scheme at a labelled rational point is
isomorphic to the base field. Its length as a module over itself is therefore
one, the multiplicity used in its fundamental zero-cycle.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SplitPointGeometry

variable (K : Type u) [Field K]

/-- The actual stalk of the base scheme is its field, at any of its points. -/
def baseStalkIso (x : Spec (.of K)) :
    (Spec (.of K)).presheaf.stalk x ≅ CommRingCat.of K :=
  eqToIso (congrArg (fun y ↦ (Spec (.of K)).presheaf.stalk y)
    (Subsingleton.elim x (IsLocalRing.closedPoint (CommRingCat.of K)))) ≪≫
      stalkClosedPointIso (CommRingCat.of K)

variable (I : Type u) [Finite I]

/-- The component open immersion identifies the actual point stalk with
the base field. -/
def pointStalkIso (i : I) :
    (scheme K I).presheaf.stalk (labelEquivScheme K I i) ≅ CommRingCat.of K := by
  rw [labelEquivScheme_apply]
  exact asIso ((pointInclusion K I i).stalkMap default) ≪≫ baseStalkIso K default

/-- Every local ring of the split finite scheme is a field. -/
theorem pointStalk_isField (i : I) :
    IsField ((scheme K I).presheaf.stalk (labelEquivScheme K I i)) :=
  (pointStalkIso K I i).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)

/-- The fundamental-cycle multiplicity at an actual rational point is one. -/
theorem pointStalk_length (i : I) :
    Module.length ((scheme K I).presheaf.stalk (labelEquivScheme K I i))
      ((scheme K I).presheaf.stalk (labelEquivScheme K I i)) = 1 := by
  letI := (pointStalk_isField K I i).toField
  exact Module.length_eq_one _ _

/-- Every actual point, without a chosen label, has a field as its local ring. -/
theorem stalk_isField (x : scheme K I) : IsField ((scheme K I).presheaf.stalk x) := by
  obtain ⟨i, rfl⟩ := (labelEquivScheme K I).surjective x
  exact pointStalk_isField K I i

/-- Multiplicity one is preserved under an actual scheme isomorphism to a
finite split scheme, in particular for the geometric fibers of split maps. -/
theorem stalk_length_of_iso_to_split {X : Scheme.{u}}
    (e : X ≅ scheme K I) (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) = 1 := by
  have hField : IsField (X.presheaf.stalk x) :=
    (asIso (e.hom.stalkMap x)).symm.commRingCatIsoToRingEquiv.toMulEquiv.isField
      (stalk_isField K I (e.hom.base x))
  letI := hField.toField
  exact Module.length_eq_one _ _

/-- The local multiplicity of an open component in the split ambient scheme
is one. Scalars act through its actual scheme stalk map, as required in the
definition of the fundamental cycle of a closed subscheme. -/
theorem stalkMap_length_of_isOpenImmersion {X : Scheme.{u}}
    (f : X ⟶ scheme K I) [IsOpenImmersion f] (x : X) :
    letI : Algebra ((scheme K I).presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Module.length ((scheme K I).presheaf.stalk (f.base x)) (X.presheaf.stalk x) = 1 := by
  letI := (stalk_isField K I (f.base x)).toField
  letI : Algebra ((scheme K I).presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let e : ((scheme K I).presheaf.stalk (f.base x)) ≃ₗ[
      (scheme K I).presheaf.stalk (f.base x)] (X.presheaf.stalk x) :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _)
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.bijective
  rw [← e.length_eq]
  exact Module.length_eq_one _ _

/-- An isomorphism of actual schemes induces a degree-one extension on
residue fields, with the scalar structure given by its actual residue map. -/
theorem residueFieldMap_finrank_of_isIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Module.finrank (Y.residueField (f.base x)) (X.residueField x) = 1 :=
  SchemeCycles.residueFieldMap_finrank_of_isIso f x

end SplitPointGeometry

end

end HodgeConjecture
