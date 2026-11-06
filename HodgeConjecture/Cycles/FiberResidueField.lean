module

public import HodgeConjecture.Cycles.FunctionFieldResidue
public import HodgeConjecture.Cycles.StructuralResidueField
public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section

/-!
# Actual residue fields of a scheme-theoretic fiber

The preimmersion from a fiber to the source identifies the residue fields.
The identification respects the independently defined structural action of
the target residue field, through the original pullback square.

The geometric compatibility proof is adapted from AxiomMath/Stacks,
`StacksFrontier/AlgebraicGeometry/F6Rank128/FiberResidueField.lean` at
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6` (Apache-2.0).
See `third_party/axiom-stacks/` for its license and attribution.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/-- The structural residue-field algebra is characterized by the actual
map from the spectrum of that residue field. -/
theorem specMap_residueFieldBaseMap (A : Type u) [CommRing A]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (CommRingCat.of A)) (z : Z) :
    Spec.map (CommRingCat.ofHom (residueFieldBaseMap A p z)) =
      Z.fromSpecResidueField z ≫ p := by
  rw [← cancel_mono (Spec (.of A)).isoSpec.hom]
  show _ ≫ (Spec _).toSpecΓ = _ ≫ (Spec _).toSpecΓ
  conv_rhs => rw [Category.assoc, Scheme.toSpecΓ_naturality]
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ_assoc, ← AlgebraicGeometry.Spec.map_comp]
  rw [← SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_comp, Spec.map_inj]
  change (((Scheme.ΓSpecIso (.of A)).hom ≫ (Scheme.ΓSpecIso (.of A)).inv) ≫
    p.appTop) ≫ Z.Γevaluation z = _
  rw [Iso.hom_inv_id, Category.id_comp]
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- The original fiber inclusion induces this actual residue-field map. -/
def fiberResidueFieldMap :
    X.residueField x ⟶ (f.fiber (f.base x)).residueField (f.asFiber x) :=
  (X.residueFieldCongr (f.fiberι_asFiber x).symm).hom ≫
    (f.fiberι (f.base x)).residueFieldMap (f.asFiber x)

/-- The comparison is an isomorphism, because the fiber inclusion is
surjective on stalks. -/
def fiberResidueFieldEquiv :
    X.residueField x ≃+* (f.fiber (f.base x)).residueField (f.asFiber x) :=
  (X.residueFieldCongr (f.fiberι_asFiber x).symm).commRingCatIsoToRingEquiv.trans
    (residueFieldEquivOfSurjectiveOnStalks (f.fiberι (f.base x)) (f.asFiber x))

/-- The field equivalence retains the original geometric map. -/
@[simp]
theorem fiberResidueFieldEquiv_apply (a : X.residueField x) :
    fiberResidueFieldEquiv f x a = fiberResidueFieldMap f x a := rfl

private theorem specMap_fiberResidueFieldMap :
    Spec.map (fiberResidueFieldMap f x) ≫ X.fromSpecResidueField x =
      (f.fiber (f.base x)).fromSpecResidueField (f.asFiber x) ≫ f.fiberι (f.base x) := by
  rw [fiberResidueFieldMap, Spec.map_comp, Category.assoc,
    Scheme.residueFieldCongr_fromSpecResidueField]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ _

/-- The fiber field map respects the original target-residue-field action,
as an equality of the actual ring maps. -/
theorem fiberResidueFieldMap_comp :
    (fiberResidueFieldMap f x).hom.comp (f.residueFieldMap x).hom =
      residueFieldBaseMap (Y.residueField (f.base x))
        (f.fiberToSpecResidueField (f.base x)) (f.asFiber x) := by
  change (f.residueFieldMap x ≫ fiberResidueFieldMap f x).hom = _
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  have hSpec := specMap_residueFieldBaseMap (Y.residueField (f.base x))
    (f.fiberToSpecResidueField (f.base x)) (f.asFiber x)
  change Spec.map ((Scheme.ΓSpecIso (.of (Y.residueField (f.base x)))).inv ≫
    (f.fiberToSpecResidueField (f.base x)).appTop ≫
      (f.fiber (f.base x)).Γevaluation (f.asFiber x)) = _ at hSpec
  rw [Spec.map_comp, ← cancel_mono (Y.fromSpecResidueField (f.base x)), hSpec]
  rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Category.assoc, specMap_fiberResidueFieldMap, Category.assoc]
  simpa only [Scheme.Hom.fiberι, Scheme.Hom.fiberToSpecResidueField, Category.assoc] using
    congrArg
      (fun g ↦ (f.fiber (f.base x)).fromSpecResidueField (f.asFiber x) ≫ g)
      (pullback.condition (f := f) (g := Y.fromSpecResidueField (f.base x)))

/-- The actual residue fields are equivalent as algebras for the two
independently specified geometric base actions. -/
def fiberResidueFieldAlgEquiv :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    letI := residueFieldBaseAlgebra (Y.residueField (f.base x))
      (f.fiberToSpecResidueField (f.base x)) (f.asFiber x)
    X.residueField x ≃ₐ[Y.residueField (f.base x)]
      (f.fiber (f.base x)).residueField (f.asFiber x) := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI := residueFieldBaseAlgebra (Y.residueField (f.base x))
    (f.fiberToSpecResidueField (f.base x)) (f.asFiber x)
  exact { fiberResidueFieldEquiv f x with
    commutes' := fun a ↦ DFunLike.congr_fun (fiberResidueFieldMap_comp f x) a }

end

end HodgeConjecture.SchemeCycles
