module

public import HodgeConjecture.Realization.Betti.SingularMayerVietoris
public import HodgeConjecture.Realization.Betti.RelativeCochains

@[expose] public section

/-!
# Naturality of the original singular Mayer–Vietoris boundary

A genuine continuous map carrying the two source opens into the two target
opens induces a morphism of the original restriction/difference short exact
sequences. Native connecting naturality then commutes with the existing
full-singular Mayer–Vietoris boundary. All comparisons use the original
small restriction and actual intersection subtype maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularMayerVietorisNaturality

open CategoryTheory HomologicalComplex Opposite Simplicial
open SingularSubcomplexes

section Simplicial

variable {S T : SSet.{0}}
  {A B : S.Subcomplex} {C D : T.Subcomplex}
  (f : S ⟶ T) (hA : A ≤ C.preimage f) (hB : B ≤ D.preimage f)

include hA hB in
theorem unionCondition : A ⊔ B ≤ (C ⊔ D).preimage f := by
  intro n σ hσ
  rcases hσ with h | h
  · exact Or.inl (hA n h)
  · exact Or.inr (hB n h)

include hA hB in
theorem intersectionCondition : A ⊓ B ≤ (C ⊓ D).preimage f := by
  intro n σ hσ
  exact ⟨hA n hσ.1, hB n hσ.2⟩

def unionMap : (A ⊔ B).toSSet ⟶ (C ⊔ D).toSSet :=
  RelativeCochains.subcomplexMap f (unionCondition f hA hB)

def intersectionSimplexMap : (A ⊓ B).toSSet ⟶ (C ⊓ D).toSSet :=
  RelativeCochains.subcomplexMap f (intersectionCondition f hA hB)

/-- The two actual component cochain pullbacks in one complex morphism. -/
def pairPullback : SubcomplexCochains.pairComplex C D ⟶
    SubcomplexCochains.pairComplex A B where
  f n := ModuleCat.ofHom
    (((SubcomplexCochains.pullback (RelativeCochains.subcomplexMap f hA)).f n).hom.prodMap
      ((SubcomplexCochains.pullback (RelativeCochains.subcomplexMap f hB)).f n).hom)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [SubcomplexCochains.pairComplex_d, SubcomplexCochains.pairComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    have ha := congrArg (fun g ↦ g.hom φ.1)
      ((SubcomplexCochains.pullback (RelativeCochains.subcomplexMap f hA)).comm i (i + 1))
    have hb := congrArg (fun g ↦ g.hom φ.2)
      ((SubcomplexCochains.pullback (RelativeCochains.subcomplexMap f hB)).comm i (i + 1))
    rw [SubcomplexCochains.complex_d, SubcomplexCochains.complex_d] at ha hb
    exact Prod.ext ha hb

/-- A morphism of the original restriction/difference short exact sequences. -/
def coverShortComplexMap :
    SubcomplexCochains.coverShortComplex C D ⟶
      SubcomplexCochains.coverShortComplex A B where
  τ₁ := SubcomplexCochains.pullback (unionMap f hA hB)
  τ₂ := pairPullback f hA hB
  τ₃ := SubcomplexCochains.pullback (intersectionSimplexMap f hA hB)
  comm₁₂ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply Prod.ext <;> funext σ <;> rfl
  comm₂₃ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    funext σ
    rfl

theorem subcomplex_connecting_naturality (n : ℕ) :
    SubcomplexCochains.connecting C D n ≫
        homologyMap (SubcomplexCochains.pullback (unionMap f hA hB)) (n + 1) =
      homologyMap (SubcomplexCochains.pullback (intersectionSimplexMap f hA hB)) n ≫
        SubcomplexCochains.connecting A B n :=
  HomologySequence.δ_naturality (coverShortComplexMap f hA hB)
    (SubcomplexCochains.coverShortComplex_shortExact C D)
    (SubcomplexCochains.coverShortComplex_shortExact A B) n (n + 1) (by simp)

end Simplicial

section Topological

variable {X Y : TopCat.{0}} (f : X ⟶ Y)
  (U V : Set X) (W Z : Set Y)
  (hUW : Set.MapsTo f U W) (hVZ : Set.MapsTo f V Z)

theorem subsetCondition (h : Set.MapsTo f U W) :
    subsetSingular X U ≤ (subsetSingular Y W).preimage (TopCat.toSSet.map f) := by
  intro n σ hσ t
  exact h (hσ t)

def smallMap : (smallSingular X U V).toSSet ⟶ (smallSingular Y W Z).toSSet :=
  unionMap (TopCat.toSSet.map f) (subsetCondition f U W hUW)
    (subsetCondition f V Z hVZ)

def intersectionMap : TopCat.of ↥(U ∩ V) ⟶ TopCat.of ↥(W ∩ Z) :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.val, ⟨hUW x.property.1, hVZ x.property.2⟩⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

def containedIntersectionMap :
    (subsetSingular X U ⊓ subsetSingular X V).toSSet ⟶
      (subsetSingular Y W ⊓ subsetSingular Y Z).toSSet :=
  intersectionSimplexMap (TopCat.toSSet.map f)
    (subsetCondition f U W hUW) (subsetCondition f V Z hVZ)

/-- The literal native subtype-to-contained-simplex map of an intersection. -/
def intersectionToContained (X : TopCat.{0}) (U V : Set X) :
    TopCat.toSSet.obj (TopCat.of ↥(U ∩ V)) ⟶
      (subsetSingular X U ⊓ subsetSingular X V).toSSet :=
  subtypeToSubset X (U ∩ V) ≫ (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V)).hom

theorem intersectionToContained_naturality :
    intersectionToContained X U V ≫ containedIntersectionMap f U V W Z hUW hVZ =
      TopCat.toSSet.map (intersectionMap f U V W Z hUW hVZ) ≫
        intersectionToContained Y W Z := by
  ext n σ
  rfl

theorem intersectionCohomologyIso_hom (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (SingularMayerVietoris.intersectionCohomologyIso X U V n).hom =
      homologyMap (SubcomplexCochains.pullback (intersectionToContained X U V)) n := by
  change homologyMap (SubcomplexCochains.pullback
      (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V)).hom) n ≫
    homologyMap (SubcomplexCochains.pullback (subtypeToSubset X (U ∩ V))) n = _
  rw [← homologyMap_comp, ← SubcomplexCochains.pullback_comp]
  rfl

theorem intersectionCohomologyIso_naturality (n : ℕ) :
    homologyMap (SubcomplexCochains.pullback
        (containedIntersectionMap f U V W Z hUW hVZ)) n ≫
      (SingularMayerVietoris.intersectionCohomologyIso X U V n).hom =
    (SingularMayerVietoris.intersectionCohomologyIso Y W Z n).hom ≫
      SingularCochains.cohomologyPullback (intersectionMap f U V W Z hUW hVZ) n := by
  rw [intersectionCohomologyIso_hom, intersectionCohomologyIso_hom]
  change homologyMap (SubcomplexCochains.pullback
      (containedIntersectionMap f U V W Z hUW hVZ)) n ≫
      homologyMap (SubcomplexCochains.pullback (intersectionToContained X U V)) n =
    homologyMap (SubcomplexCochains.pullback (intersectionToContained Y W Z)) n ≫
      homologyMap (SubcomplexCochains.pullback
        (TopCat.toSSet.map (intersectionMap f U V W Z hUW hVZ))) n
  rw [← homologyMap_comp, ← homologyMap_comp,
    ← SubcomplexCochains.pullback_comp, ← SubcomplexCochains.pullback_comp,
    intersectionToContained_naturality]

theorem smallRestriction_naturality :
    SingularCochains.pullback f ≫ CochainDualComparison.smallRestriction X U V =
      CochainDualComparison.smallRestriction Y W Z ≫
        SubcomplexCochains.pullback (smallMap f U V W Z hUW hVZ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

variable (hU : IsOpen U) (hV : IsOpen V) (hcoverX : U ∪ V = Set.univ)
  (hW : IsOpen W) (hZ : IsOpen Z) (hcoverY : W ∪ Z = Set.univ)

theorem smallCohomologyIso_naturality (n : ℕ) :
    SingularCochains.cohomologyPullback f n ≫
        (CochainDualComparison.smallCohomologyIso X U V hU hV hcoverX n).hom =
      (CochainDualComparison.smallCohomologyIso Y W Z hW hZ hcoverY n).hom ≫
        homologyMap (SubcomplexCochains.pullback (smallMap f U V W Z hUW hVZ)) n := by
  rw [CochainDualComparison.smallCohomologyIso_hom,
    CochainDualComparison.smallCohomologyIso_hom]
  change homologyMap (SingularCochains.pullback f) n ≫ _ = _
  rw [← homologyMap_comp, ← homologyMap_comp, smallRestriction_naturality]

/-- The existing full-singular boundary commutes with the original continuous pullback. -/
theorem connecting_naturality (n : ℕ) :
    SingularMayerVietoris.connecting Y W Z hW hZ hcoverY n ≫
        SingularCochains.cohomologyPullback f (n + 1) =
      SingularCochains.cohomologyPullback (intersectionMap f U V W Z hUW hVZ) n ≫
        SingularMayerVietoris.connecting X U V hU hV hcoverX n := by
  apply (cancel_mono
    (CochainDualComparison.smallCohomologyIso X U V hU hV hcoverX (n + 1)).hom).mp
  have hi := intersectionCohomologyIso_naturality f U V W Z hUW hVZ n
  have hinv :
      (SingularMayerVietoris.intersectionCohomologyIso Y W Z n).inv ≫
        homologyMap (SubcomplexCochains.pullback
          (containedIntersectionMap f U V W Z hUW hVZ)) n =
      SingularCochains.cohomologyPullback (intersectionMap f U V W Z hUW hVZ) n ≫
        (SingularMayerVietoris.intersectionCohomologyIso X U V n).inv := by
    apply (cancel_mono (SingularMayerVietoris.intersectionCohomologyIso X U V n).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hi]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  calc
    (SingularMayerVietoris.connecting Y W Z hW hZ hcoverY n ≫
        SingularCochains.cohomologyPullback f (n + 1)) ≫
        (CochainDualComparison.smallCohomologyIso X U V hU hV hcoverX (n + 1)).hom =
      (SingularMayerVietoris.intersectionCohomologyIso Y W Z n).inv ≫
        SubcomplexCochains.connecting (subsetSingular Y W) (subsetSingular Y Z) n ≫
          homologyMap (SubcomplexCochains.pullback (smallMap f U V W Z hUW hVZ)) (n + 1) := by
      simp only [SingularMayerVietoris.connecting, Category.assoc]
      rw [smallCohomologyIso_naturality f U V W Z hUW hVZ hU hV hcoverX hW hZ hcoverY]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    _ = (SingularMayerVietoris.intersectionCohomologyIso Y W Z n).inv ≫
        homologyMap (SubcomplexCochains.pullback
          (containedIntersectionMap f U V W Z hUW hVZ)) n ≫
        SubcomplexCochains.connecting (subsetSingular X U) (subsetSingular X V) n := by
      exact congrArg
        (fun g ↦ (SingularMayerVietoris.intersectionCohomologyIso Y W Z n).inv ≫ g)
        (subcomplex_connecting_naturality (TopCat.toSSet.map f)
          (subsetCondition f U W hUW) (subsetCondition f V Z hVZ) n)
    _ = (SingularCochains.cohomologyPullback (intersectionMap f U V W Z hUW hVZ) n ≫
        SingularMayerVietoris.connecting X U V hU hV hcoverX n) ≫
        (CochainDualComparison.smallCohomologyIso X U V hU hV hcoverX (n + 1)).hom := by
      rw [← Category.assoc, hinv]
      simp only [SingularMayerVietoris.connecting, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]

end Topological

end HodgeConjecture.SingularMayerVietorisNaturality

end
