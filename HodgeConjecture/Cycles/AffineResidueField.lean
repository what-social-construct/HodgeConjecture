module

public import HodgeConjecture.Cycles.StructuralResidueField
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section

/-!
# Actual residue fields on an affine spectrum

The canonical stalk-to-localization isomorphism induces an isomorphism
between the scheme's actual residue field and the existing residue field
of the corresponding prime ideal. Evaluation of an actual constant
section is carried to the usual algebra map into the prime residue
field. No domain, reducedness or finite-type hypothesis is needed.

For any commutative base ring, this comparison is an algebra equivalence
for the independently defined structural action on the scheme residue
field. Compatibility follows from actual global-section naturality,
not from defining the structural action by transport through the equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The actual affine stalk residue field, identified through the
canonical stalk-to-localization isomorphism. -/
def specResidueFieldEquiv (A : Type u) [CommRing A]
    (x : Spec (CommRingCat.of A)) :
    (Spec (CommRingCat.of A)).residueField x ≃+* x.asIdeal.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv
    (StructureSheaf.stalkIso A x).symm.toRingEquiv

/-- Under the actual residue-field comparison, evaluating a constant
section is the existing algebra map into the prime residue field. -/
theorem specResidueFieldEquiv_evaluation (A : Type u) [CommRing A]
    (x : Spec (CommRingCat.of A)) (a : A) :
    specResidueFieldEquiv A x
        ((Spec (CommRingCat.of A)).Γevaluation x ((Scheme.ΓSpecIso (.of A)).inv a)) =
      algebraMap A x.asIdeal.ResidueField a := by
  change IsLocalRing.residue (Localization.AtPrime x.asIdeal)
    ((StructureSheaf.stalkIso A x).symm (StructureSheaf.toStalk A x a)) = _
  exact congrArg (IsLocalRing.residue (Localization.AtPrime x.asIdeal))
    ((StructureSheaf.stalkIso A x).symm.commutes a)

/-- The affine residue-field comparison is linear over the actual
structural base action, for any commutative base ring. -/
def specResidueFieldAlgEquiv (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    (Spec (CommRingCat.of A)).residueField x ≃ₐ[k] x.asIdeal.ResidueField := by
  letI := residueFieldBaseAlgebra k
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
  refine { specResidueFieldEquiv A x with commutes' := ?_ }
  intro a
  change specResidueFieldEquiv A x
    (((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k A))).appTop ≫
      (Spec (CommRingCat.of A)).Γevaluation x) a) =
    algebraMap k x.asIdeal.ResidueField a
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  change specResidueFieldEquiv A x
    ((Spec (CommRingCat.of A)).Γevaluation x
      ((Scheme.ΓSpecIso (.of A)).inv (algebraMap k A a))) = _
  rw [specResidueFieldEquiv_evaluation]
  exact (IsScalarTower.algebraMap_apply k A x.asIdeal.ResidueField a).symm

/-- Bundling the base compatibility does not change the underlying
canonical residue-field equivalence. -/
@[simp]
theorem specResidueFieldAlgEquiv_apply (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] (x : Spec (CommRingCat.of A))
    (a : (Spec (CommRingCat.of A)).residueField x) :
    specResidueFieldAlgEquiv k A x a = specResidueFieldEquiv A x a := rfl

end

end HodgeConjecture.SchemeCycles
