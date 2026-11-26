module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

/-!
# The actual split double cover of a scheme

The fold from two copies of a scheme is finite étale and surjective. Its
geometric rank is two at every point. The rank calculation uses the affine
product-ring presentation and actual open base change of the fold. Both
component inclusions are open and closed, and each original fold stalk map
is an isomorphism.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitDoubleCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/-- The actual scheme morphism identifying two identical components. -/
def fold (X : Scheme.{u}) : X ⨿ X ⟶ X :=
  coprod.desc (𝟙 X) (𝟙 X)

/-- The first original scheme component. -/
abbrev inl (X : Scheme.{u}) : X ⟶ X ⨿ X := coprod.inl

/-- The second original scheme component. -/
abbrev inr (X : Scheme.{u}) : X ⟶ X ⨿ X := coprod.inr

@[simp, reassoc]
theorem inl_fold (X : Scheme.{u}) : inl X ≫ fold X = 𝟙 X :=
  coprod.inl_desc _ _

@[simp, reassoc]
theorem inr_fold (X : Scheme.{u}) : inr X ≫ fold X = 𝟙 X :=
  coprod.inr_desc _ _

@[simp]
theorem fold_inl_apply (X : Scheme.{u}) (x : X) : fold X (inl X x) = x :=
  congrArg (fun f : X ⟶ X => f x) (inl_fold X)

@[simp]
theorem fold_inr_apply (X : Scheme.{u}) (x : X) : fold X (inr X x) = x :=
  congrArg (fun f : X ⟶ X => f x) (inr_fold X)

/-- The upstairs structure map is the exact composite through the fold. -/
abbrev sourceStructure {X S : Scheme.{u}} (p : X ⟶ S) : X ⨿ X ⟶ S :=
  fold X ≫ p

@[simp, reassoc]
theorem inl_sourceStructure {X S : Scheme.{u}} (p : X ⟶ S) :
    inl X ≫ sourceStructure p = p := by
  simp [sourceStructure, fold]

@[simp, reassoc]
theorem inr_sourceStructure {X S : Scheme.{u}} (p : X ⟶ S) :
    inr X ≫ sourceStructure p = p := by
  simp [sourceStructure, fold]

instance fold_isFinite (X : Scheme.{u}) : IsFinite (fold X) := by
  unfold fold
  infer_instance

instance fold_isEtale (X : Scheme.{u}) : Etale (fold X) := by
  apply IsZariskiLocalAtSource.of_openCover (coprodOpenCover.{u, 0} X X)
  rintro (i | i) <;>
    simpa [coprodOpenCover, fold] using (inferInstanceAs (Etale (𝟙 X)))

instance fold_isFlat (X : Scheme.{u}) : Flat (fold X) := inferInstance

instance fold_isSurjective (X : Scheme.{u}) : Surjective (fold X) where
  surj x := ⟨inl X x, fold_inl_apply X x⟩

instance inl_isFinite (X : Scheme.{u}) : IsFinite (inl X) := by
  have : IsFinite (inl X ≫ fold X) := by rw [inl_fold]; infer_instance
  exact IsFinite.of_comp (inl X) (fold X)

instance inr_isFinite (X : Scheme.{u}) : IsFinite (inr X) := by
  have : IsFinite (inr X ≫ fold X) := by rw [inr_fold]; infer_instance
  exact IsFinite.of_comp (inr X) (fold X)

instance inl_isClosedImmersion (X : Scheme.{u}) : IsClosedImmersion (inl X) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

instance inr_isClosedImmersion (X : Scheme.{u}) : IsClosedImmersion (inr X) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- The coproduct source retains Noetherianity from the original scheme. -/
instance source_isNoetherian (X : Scheme.{u}) [IsNoetherian X] :
    IsNoetherian (X ⨿ X) where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (fold X)
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (fold X)

/-- On either component the original fold map identifies the actual local rings. -/
instance fold_stalkMap_isIso (X : Scheme.{u}) (x : (X ⨿ X : Scheme.{u})) :
    IsIso ((fold X).stalkMap x) := by
  obtain ⟨x | x, rfl⟩ := (coprodMk X X).surjective x
  · have h := Scheme.Hom.stalkMap_comp (inl X) (fold X) x
    rw [← IsIso.comp_inv_eq,
      Scheme.Hom.stalkMap_congr_hom _ (𝟙 X) (inl_fold X)] at h
    rw [coprodMk_inl, ← h]
    infer_instance
  · have h := Scheme.Hom.stalkMap_comp (inr X) (fold X) x
    rw [← IsIso.comp_inv_eq,
      Scheme.Hom.stalkMap_congr_hom _ (𝟙 X) (inr_fold X)] at h
    rw [coprodMk_inr, ← h]
    infer_instance

/-- Doubling any actual scheme morphism commutes with the original folds. -/
@[reassoc]
theorem map_fold {U X : Scheme.{u}} (j : U ⟶ X) :
    coprod.map j j ≫ fold X = fold U ≫ j := by
  apply coprod.hom_ext <;> simp [fold]

instance doubleMap_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsOpenImmersion (coprod.map j j) :=
  IsZariskiLocalAtTarget.coprodMap j j inferInstance inferInstance

private theorem map_range_preimage {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    fold X ⁻¹ᵁ j.opensRange = (coprod.map j j).opensRange := by
  ext z
  change fold X z ∈ Set.range j ↔ z ∈ Set.range (coprod.map j j)
  constructor
  · intro hz
    obtain ⟨z | z, rfl⟩ := (coprodMk X X).surjective z
    · obtain ⟨u, hu⟩ := hz
      simp only [coprodMk_inl, fold_inl_apply] at hu ⊢
      refine ⟨inl U u, ?_⟩
      calc
        (coprod.map j j) (inl U u) = inl X (j u) :=
          congrArg (fun f : U ⟶ X ⨿ X => f u) (coprod.inl_map j j)
        _ = inl X z := congrArg (inl X) hu
    · obtain ⟨u, hu⟩ := hz
      simp only [coprodMk_inr, fold_inr_apply] at hu ⊢
      refine ⟨inr U u, ?_⟩
      calc
        (coprod.map j j) (inr U u) = inr X (j u) :=
          congrArg (fun f : U ⟶ X ⨿ X => f u) (coprod.inr_map j j)
        _ = inr X z := congrArg (inr X) hu
  · rintro ⟨u, rfl⟩
    refine ⟨fold U u, ?_⟩
    exact (congrArg (fun f : U ⨿ U ⟶ X => f u) (map_fold j)).symm

/-- Restricting the actual fold along an open immersion gives the actual
fold of the open scheme, with the original doubled chart inclusion. -/
theorem fold_baseChange_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    IsPullback (coprod.map j j) (fold U) (fold X) j :=
  (IsOpenImmersion.isPullback (fold U) (coprod.map j j) j (fold X)
    (map_fold j) (map_range_preimage j)).flip

/-- The affine fold is induced by the original diagonal algebra map. -/
theorem coprodSpec_comp_diagonal (R : CommRingCat.{u}) :
    coprodSpec R R ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R × R))) =
      fold (Spec R) := by
  unfold fold
  apply coprod.hom_ext
  · rw [coprodSpec_inl_assoc, coprod.inl_desc, ← Spec.map_comp]
    convert Spec.map_id R using 1
    congr 1
  · rw [coprodSpec_inr_assoc, coprod.inr_desc, ← Spec.map_comp]
    convert Spec.map_id R using 1
    congr 1

/-- The affine product ring has rank two over its diagonal base ring. -/
theorem fold_spec_finrank (R : CommRingCat.{u}) (x : Spec R) :
    (fold (Spec R)).finrank x = 2 := by
  let : Nontrivial R := (x : PrimeSpectrum R).nontrivial
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) := by
    rw [Flat.SpecMap_iff]
    exact (RingHom.flat_algebraMap_iff).mpr inferInstance
  rw [← coprodSpec_comp_diagonal R, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_prod,
    Module.rankAtStalk_self]
  simp

/-- The actual finite flat fold has constant geometric rank two. -/
theorem fold_finrank (X : Scheme.{u}) (x : X) : (fold X).finrank x = 2 := by
  obtain ⟨R, j, hj, y, rfl⟩ := X.exists_Spec_apply_eq x
  let := hj
  have h := Scheme.Hom.finrank_of_isPullback (coprod.map j j) (fold (Spec R))
    (fold X) j (fold_baseChange_of_isOpenImmersion j) y
  rw [fold_spec_finrank] at h
  exact h.symm

end

end HodgeConjecture.SplitDoubleCover
