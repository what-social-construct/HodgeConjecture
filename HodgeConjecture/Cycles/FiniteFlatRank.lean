module

public import HodgeConjecture.Cycles.FiniteFiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

@[expose] public section

/-!
# The finite-fiber degree is the geometric rank

The degree computed from the actual fiber's global sections agrees with
Mathlib's rank of the same finite flat morphism. Constant geometric rank
therefore supplies the cycle degree law without a separate fiber-degree
premise. This comparison makes no claim about rational-equivalence descent.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

/-- Over a field, geometric rank is the dimension of the actual global
sections with their structural scalar action. Empty finite schemes are allowed. -/
theorem finrank_toSpec_eq_globalSection_finrank (k : Type u) [Field k]
    {S : Scheme.{u}} (p : S ⟶ Spec (CommRingCat.of k)) [IsFinite p]
    (z : Spec (CommRingCat.of k)) :
    p.finrank z =
      letI := globalSectionBaseAlgebra k p
      Module.finrank k Γ(S, ⊤) := by
  letI := globalSectionBaseAlgebra k p
  letI : IsAffine S := isAffine_of_isAffineHom p
  letI := globalSectionBaseAlgebra_moduleFinite k p
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap k Γ(S, ⊤))) =
      S.isoSpec.inv ≫ p := by
    change Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop) = _
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have hr := Scheme.Hom.finrank_SpecMap_algebraMap k Γ(S, ⊤) z
  rw [hmap, Scheme.Hom.finrank_comp_left_of_isIso,
    Module.rankAtStalk_eq_finrank_of_free] at hr
  exact hr

/-- The actual finite-fiber degree equals Mathlib's rank of the same map. -/
theorem finiteFiberDegree_eq_finrank {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Flat f] (y : Y) :
    finiteFiberDegree f y = f.finrank y := by
  let z : Spec (CommRingCat.of (Y.residueField y)) := IsLocalRing.closedPoint _
  letI : IsFinite (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have h := finrank_toSpec_eq_globalSection_finrank (Y.residueField y)
    (f.fiberToSpecResidueField y) z
  change (pullback.snd f (Y.fromSpecResidueField y)).finrank z = finiteFiberDegree f y at h
  rw [Scheme.Hom.finrank_pullback_snd, Scheme.fromSpecResidueField_apply] at h
  exact h.symm

/-- In affine coordinates the same degree is the rank of the original algebra. -/
theorem finiteFiberDegree_SpecMap_algebraMap (A B : Type u)
    [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Flat A B]
    (y : PrimeSpectrum A) :
    finiteFiberDegree (Spec.map (CommRingCat.ofHom (algebraMap A B))) y =
      Module.rankAtStalk B y := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap).mpr inferInstance
  letI : Flat (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff).mpr inferInstance
  rw [finiteFiberDegree_eq_finrank, Scheme.Hom.finrank_SpecMap_algebraMap]

/-- A finite algebra over a field has its actual vector-space dimension as fiber degree. -/
theorem finiteFiberDegree_SpecMap_field (k B : Type u) [Field k]
    [CommRing B] [Algebra k B] [Module.Finite k B] (y : PrimeSpectrum k) :
    finiteFiberDegree (Spec.map (CommRingCat.ofHom (algebraMap k B))) y =
      Module.finrank k B := by
  rw [finiteFiberDegree_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- The computed degree inherits local constancy for a finite flat map of finite presentation. -/
theorem finiteFiberDegree_isLocallyConstant {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] :
    IsLocallyConstant (finiteFiberDegree f) := by
  have h : finiteFiberDegree f = f.finrank := funext (finiteFiberDegree_eq_finrank f)
  rw [h]
  exact f.isLocallyConstant_finrank

/-- Constant geometric rank gives the degree formula on the existing cycle maps. -/
theorem finitePushforward_finiteFiberPullback_of_finrank_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]
    (R : Type v) [CommSemiring R] (d : ℕ)
    (hd : ∀ y : Y, f.finrank y = d) (c : Cycles Y R) :
    finitePushforward R f (finiteFiberPullback f R c) = d • c :=
  finitePushforward_finiteFiberPullback_of_degree_eq f R d
    (fun y ↦ (finiteFiberDegree_eq_finrank f y).trans (hd y)) c

end

end HodgeConjecture.SchemeCycles
