module

public import HodgeConjecture.Realization.Betti.SingularMayerVietoris

@[expose] public section

/-!
# The original continuous maps in singular Mayer–Vietoris

The constructed cover maps agree with pullback along the actual inclusions
of the two subtype pieces and their intersection. These formulas retain
the first-minus-second difference sign used by the actual cochain sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularMayerVietoris

open CategoryTheory HomologicalComplex SingularSubcomplexes

/-- The actual continuous inclusion of the intersection in the first subtype piece. -/
def intersectionToLeft (X : TopCat.{0}) (U V : Set X) :
    TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, x.property.1⟩,
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.1)⟩

/-- The actual continuous inclusion of the intersection in the second subtype piece. -/
def intersectionToRight (X : TopCat.{0}) (U V : Set X) :
    TopCat.of ↥(U ∩ V) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, x.property.2⟩,
    continuous_subtype_val.subtype_mk (fun x ↦ x.property.2)⟩

@[simp]
theorem intersectionToLeft_apply (X : TopCat.{0}) (U V : Set X) (x : ↥(U ∩ V)) :
    intersectionToLeft X U V x = ⟨x.val, x.property.1⟩ := rfl

@[simp]
theorem intersectionToRight_apply (X : TopCat.{0}) (U V : Set X) (x : ↥(U ∩ V)) :
    intersectionToRight X U V x = ⟨x.val, x.property.2⟩ := rfl

@[reassoc (attr := simp)]
theorem intersectionToLeft_subsetInclusion (X : TopCat.{0}) (U V : Set X) :
    intersectionToLeft X U V ≫ subsetInclusion X U = subsetInclusion X (U ∩ V) := by
  ext x
  rfl

@[reassoc (attr := simp)]
theorem intersectionToRight_subsetInclusion (X : TopCat.{0}) (U V : Set X) :
    intersectionToRight X U V ≫ subsetInclusion X V = subsetInclusion X (U ∩ V) := by
  ext x
  rfl

@[simp]
theorem chartCohomologyIso_hom (X : TopCat.{0}) (U : Set X) (n : ℕ) :
    (chartCohomologyIso X U n).hom =
      homologyMap (SubcomplexCochains.pullback (subtypeToSubset X U)) n := rfl

@[simp]
theorem chartCohomologyIso_inv (X : TopCat.{0}) (U : Set X) (n : ℕ) :
    (chartCohomologyIso X U n).inv =
      homologyMap (SubcomplexCochains.pullback (subsetToSubtype X U)) n := rfl

theorem restriction_cochain_fst (X : TopCat.{0}) (U V : Set X) :
    CochainDualComparison.smallRestriction X U V ≫
      SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V) ≫
        CochainPair.fst (subsetSingular X U) (subsetSingular X V) ≫
          SubcomplexCochains.pullback (subtypeToSubset X U) =
      SingularCochains.pullback (subsetInclusion X U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

theorem restriction_cochain_snd (X : TopCat.{0}) (U V : Set X) :
    CochainDualComparison.smallRestriction X U V ≫
      SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V) ≫
        CochainPair.snd (subsetSingular X U) (subsetSingular X V) ≫
          SubcomplexCochains.pullback (subtypeToSubset X V) =
      SingularCochains.pullback (subsetInclusion X V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

theorem restriction_homology_fst (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    homologyMap (CochainDualComparison.smallRestriction X U V) n ≫
      homologyMap (SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V)) n ≫
        homologyMap (CochainPair.fst (subsetSingular X U) (subsetSingular X V)) n ≫
          (chartCohomologyIso X U n).hom =
      SingularCochains.cohomologyPullback (subsetInclusion X U) n := by
  rw [chartCohomologyIso_hom, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_comp,
    restriction_cochain_fst]
  rfl

theorem restriction_homology_snd (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    homologyMap (CochainDualComparison.smallRestriction X U V) n ≫
      homologyMap (SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V)) n ≫
        homologyMap (CochainPair.snd (subsetSingular X U) (subsetSingular X V)) n ≫
          (chartCohomologyIso X V n).hom =
      SingularCochains.cohomologyPullback (subsetInclusion X V) n := by
  rw [chartCohomologyIso_hom, ← homologyMap_comp, ← homologyMap_comp, ← homologyMap_comp,
    restriction_cochain_snd]
  rfl

/-- The original cover restriction is the pair of original continuous pullbacks. -/
theorem restriction_apply (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (z : SingularCochains.Cohomology X n) :
    restriction X U V n z =
      (SingularCochains.cohomologyPullback (subsetInclusion X U) n z,
        SingularCochains.cohomologyPullback (subsetInclusion X V) n z) := by
  apply Prod.ext
  · exact congrArg (fun f ↦ f z) (restriction_homology_fst X U V n)
  · exact congrArg (fun f ↦ f z) (restriction_homology_snd X U V n)

theorem difference_cochain_inl {S : SSet.{0}} (A B : S.Subcomplex) :
    CochainPair.inl A B ≫ SubcomplexCochains.coverDifference A B =
      SubcomplexCochains.restriction (show A ⊓ B ≤ A from inf_le_left) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change φ ⟨σ.val, σ.property.1⟩ - 0 = φ ⟨σ.val, σ.property.1⟩
  exact sub_zero _

theorem difference_cochain_inr {S : SSet.{0}} (A B : S.Subcomplex) :
    CochainPair.inr A B ≫ SubcomplexCochains.coverDifference A B =
      -SubcomplexCochains.restriction (show A ⊓ B ≤ B from inf_le_right) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change 0 - φ ⟨σ.val, σ.property.2⟩ = -φ ⟨σ.val, σ.property.2⟩
  exact zero_sub _

/-- Original simplicial restriction to the intersection is pullback along its actual first inclusion. -/
theorem intersection_cochain_left (X : TopCat.{0}) (U V : Set X) :
    SubcomplexCochains.pullback (subsetToSubtype X U) ≫
      SubcomplexCochains.restriction
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X U from inf_le_left) ≫
      (pullbackIso (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V))).hom ≫
      SubcomplexCochains.pullback (subtypeToSubset X (U ∩ V)) =
      SingularCochains.pullback (intersectionToLeft X U V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

/-- Original simplicial restriction to the intersection is pullback along its actual second inclusion. -/
theorem intersection_cochain_right (X : TopCat.{0}) (U V : Set X) :
    SubcomplexCochains.pullback (subsetToSubtype X V) ≫
      SubcomplexCochains.restriction
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X V from inf_le_right) ≫
      (pullbackIso (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V))).hom ≫
      SubcomplexCochains.pullback (subtypeToSubset X (U ∩ V)) =
      SingularCochains.pullback (intersectionToRight X U V) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

theorem intersection_homology_left (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (chartCohomologyIso X U n).inv ≫
      homologyMap (SubcomplexCochains.restriction
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X U from inf_le_left)) n ≫
      (intersectionCohomologyIso X U V n).hom =
      SingularCochains.cohomologyPullback (intersectionToLeft X U V) n := by
  change homologyMap (SubcomplexCochains.pullback (subsetToSubtype X U)) n ≫
      homologyMap (SubcomplexCochains.restriction
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X U from inf_le_left)) n ≫
      homologyMap ((pullbackIso (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V))).hom) n ≫
      homologyMap (SubcomplexCochains.pullback (subtypeToSubset X (U ∩ V))) n = _
  rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_comp, intersection_cochain_left]
  rfl

theorem intersection_homology_right (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (chartCohomologyIso X V n).inv ≫
      homologyMap (SubcomplexCochains.restriction
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X V from inf_le_right)) n ≫
      (intersectionCohomologyIso X U V n).hom =
      SingularCochains.cohomologyPullback (intersectionToRight X U V) n := by
  change homologyMap (SubcomplexCochains.pullback (subsetToSubtype X V)) n ≫
      homologyMap (SubcomplexCochains.restriction
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X V from inf_le_right)) n ≫
      homologyMap ((pullbackIso (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V))).hom) n ≫
      homologyMap (SubcomplexCochains.pullback (subtypeToSubset X (U ∩ V))) n = _
  rw [← homologyMap_comp, ← homologyMap_comp, ← homologyMap_comp, intersection_cochain_right]
  rfl

/-- The actual intersection difference is first continuous pullback minus second continuous pullback. -/
theorem difference_apply (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (a : SingularCochains.Cohomology (TopCat.of U) n)
    (b : SingularCochains.Cohomology (TopCat.of V) n) :
    difference X U V n (a, b) =
      SingularCochains.cohomologyPullback (intersectionToLeft X U V) n a -
        SingularCochains.cohomologyPullback (intersectionToRight X U V) n b := by
  change (intersectionCohomologyIso X U V n).hom
      (homologyMap (SubcomplexCochains.coverDifference (subsetSingular X U) (subsetSingular X V)) n
        (homologyMap (CochainPair.inl (subsetSingular X U) (subsetSingular X V)) n
            ((chartCohomologyIso X U n).inv a) +
          homologyMap (CochainPair.inr (subsetSingular X U) (subsetSingular X V)) n
            ((chartCohomologyIso X V n).inv b))) = _
  rw [map_add, map_add]
  have hleft := congrArg (fun f ↦ f ((chartCohomologyIso X U n).inv a))
    (homologyMap_comp (CochainPair.inl (subsetSingular X U) (subsetSingular X V))
      (SubcomplexCochains.coverDifference (subsetSingular X U) (subsetSingular X V)) n)
  have hright := congrArg (fun f ↦ f ((chartCohomologyIso X V n).inv b))
    (homologyMap_comp (CochainPair.inr (subsetSingular X U) (subsetSingular X V))
      (SubcomplexCochains.coverDifference (subsetSingular X U) (subsetSingular X V)) n)
  rw [difference_cochain_inl] at hleft
  rw [difference_cochain_inr, homologyMap_neg] at hright
  simp only [ModuleCat.comp_apply] at hleft hright
  rw [← hleft, ← hright]
  simp only [ModuleCat.hom_neg, LinearMap.neg_apply, map_neg]
  have hU := congrArg (fun f ↦ f a) (intersection_homology_left X U V n)
  have hV := congrArg (fun f ↦ f b) (intersection_homology_right X U V n)
  simp only [ModuleCat.comp_apply] at hU hV
  simpa only [sub_eq_add_neg] using congrArg₂ (· - ·) hU hV

end HodgeConjecture.SingularMayerVietoris
