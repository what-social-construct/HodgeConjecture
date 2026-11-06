module

public import HodgeConjecture.Cycles.AffineResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances

@[expose] public section

/-!
# Algebraicity of the actual residue maps of finite morphisms

The affine proof compares actual scheme residue fields with the canonical
prime residue fields. Open affine charts then transport algebraicity along
the actual residue-field isomorphisms, retaining the original residue map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

private theorem spec_residueFieldMap_isAlgebraic
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (x : Spec (.of B)) :
    let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
    letI : Algebra ((Spec (.of A)).residueField (f.base x))
        ((Spec (.of B)).residueField x) := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic ((Spec (.of A)).residueField (f.base x))
      ((Spec (.of B)).residueField x) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let y : Spec (.of A) := f.base x
  letI : x.asIdeal.LiesOver y.asIdeal := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver y.asIdeal x.asIdeal
  letI : Algebra ((Spec (.of A)).residueField (f.base x))
      ((Spec (.of B)).residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let eA := specResidueFieldEquiv A y
  let eB := specResidueFieldEquiv B x
  have hmap : algebraMap y.asIdeal.ResidueField x.asIdeal.ResidueField =
      (eB.toRingHom.comp (f.residueFieldMap x).hom).comp eA.symm.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := A ⧸ y.asIdeal)
    intro c
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    change algebraMap y.asIdeal.ResidueField x.asIdeal.ResidueField
        (algebraMap A y.asIdeal.ResidueField a) =
      eB (f.residueFieldMap x (eA.symm (algebraMap A y.asIdeal.ResidueField a)))
    have he : eA.symm (algebraMap A y.asIdeal.ResidueField a) =
        (Spec (.of A)).Γevaluation y ((Scheme.ΓSpecIso (.of A)).inv a) := by
      apply eA.injective
      rw [RingEquiv.apply_symm_apply]
      exact (specResidueFieldEquiv_evaluation A y a).symm
    rw [he, Scheme.Γevaluation_naturality_apply]
    have hn := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))) a
    change (Scheme.ΓSpecIso (.of B)).inv (algebraMap A B a) =
      f.appTop ((Scheme.ΓSpecIso (.of A)).inv a) at hn
    change _ = eB ((Spec (.of B)).Γevaluation x
      (f.appTop ((Scheme.ΓSpecIso (.of A)).inv a)))
    rw [← hn]
    change _ = specResidueFieldEquiv B x
      ((Spec (.of B)).Γevaluation x ((Scheme.ΓSpecIso (.of B)).inv (algebraMap A B a)))
    rw [specResidueFieldEquiv_evaluation]
    rw [← IsScalarTower.algebraMap_apply A y.asIdeal.ResidueField x.asIdeal.ResidueField,
      ← IsScalarTower.algebraMap_apply A B x.asIdeal.ResidueField]
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq eA eB eA.surjective eB.injective
  apply RingHom.ext
  intro c
  have hc := DFunLike.congr_fun hmap (eA c)
  change algebraMap y.asIdeal.ResidueField x.asIdeal.ResidueField (eA c) =
    eB (f.residueFieldMap x (eA.symm (eA c))) at hc
  change algebraMap y.asIdeal.ResidueField x.asIdeal.ResidueField (eA c) =
    eB (f.residueFieldMap x c)
  simpa only [RingEquiv.symm_apply_apply] using hc

private theorem residue_algebraic_comp_open
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g] (x : X)
    (h : letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
        (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x)) :
    letI : Algebra (Z.residueField ((f ≫ g).base x)) (X.residueField x) :=
      ((f ≫ g).residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Z.residueField ((f ≫ g).base x)) (X.residueField x) := by
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI : Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) := h
  letI : Algebra (Z.residueField (g.base (f.base x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let e := (asIso (g.residueFieldMap (f.base x))).commRingCatIsoToRingEquiv
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq e (RingEquiv.refl (X.residueField x))
    e.surjective (RingEquiv.refl (X.residueField x)).injective
  change (g.residueFieldMap (f.base x) ≫ f.residueFieldMap x).hom =
    ((f ≫ g).residueFieldMap x).hom
  rw [Scheme.residueFieldMap_comp]

private theorem residue_algebraic_of_precomp_open
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (f : Y ⟶ Z) (x : X)
    (h : letI : Algebra (Z.residueField ((i ≫ f).base x)) (X.residueField x) :=
        ((i ≫ f).residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic (Z.residueField ((i ≫ f).base x)) (X.residueField x)) :
    letI : Algebra (Z.residueField (f.base (i.base x))) (Y.residueField (i.base x)) :=
      (f.residueFieldMap (i.base x)).hom.toAlgebra
    Algebra.IsAlgebraic (Z.residueField (f.base (i.base x)))
      (Y.residueField (i.base x)) := by
  letI : Algebra (Z.residueField ((i ≫ f).base x)) (X.residueField x) :=
    ((i ≫ f).residueFieldMap x).hom.toAlgebra
  letI : Algebra.IsAlgebraic (Z.residueField ((i ≫ f).base x)) (X.residueField x) := h
  letI : Algebra (Z.residueField ((i ≫ f).base x)) (Y.residueField (i.base x)) :=
    (f.residueFieldMap (i.base x)).hom.toAlgebra
  let e := (asIso (i.residueFieldMap x)).commRingCatIsoToRingEquiv
  apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq
    (RingEquiv.refl (Z.residueField ((i ≫ f).base x))) e
    (RingEquiv.refl (Z.residueField ((i ≫ f).base x))).surjective e.injective
  change ((i ≫ f).residueFieldMap x).hom =
    (f.residueFieldMap (i.base x) ≫ i.residueFieldMap x).hom
  rw [Scheme.residueFieldMap_comp]

/-- Every finite scheme morphism induces an algebraic extension through its
literal residue-field map, without conditions on either ambient scheme. -/
theorem residueFieldMap_isAlgebraic_of_isFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (x : X) :
    letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f.base x)) (X.residueField x) := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := f.base x) (by trivial)
  let hV := hU.preimage f
  let x' := hV.primeIdealOf ⟨x, hx⟩
  have hx' : hV.fromSpec.base x' = x := hV.fromSpec_primeIdealOf ⟨x, hx⟩
  letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  letI : Algebra.IsIntegral Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    algebraMap_isIntegral_iff.mp (IsIntegralHom.isIntegral_app (f := f) U hU)
  have hsq : Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl)
  have h := residue_algebraic_comp_open (Spec.map (f.app U)) hU.fromSpec x'
    (spec_residueFieldMap_isAlgebraic Γ(Y, U) Γ(X, f ⁻¹ᵁ U) x')
  rw [hsq] at h
  let P (z : X) : Prop :=
    letI : Algebra (Y.residueField (f.base z)) (X.residueField z) :=
      (f.residueFieldMap z).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f.base z)) (X.residueField z)
  have h' : P (hV.fromSpec.base x') :=
    residue_algebraic_of_precomp_open hV.fromSpec f x' h
  exact (congrArg P hx').mp h'

end

end HodgeConjecture.SchemeCycles
