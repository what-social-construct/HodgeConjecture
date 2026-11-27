module

public import HodgeConjecture.Realization.Betti.SingularMayerVietorisNaturality

@[expose] public section

/-!
# Swapping the two original Mayer–Vietoris cover members

The original cochain sequence uses first restriction minus second restriction.
Its actual tuple swap therefore forms a morphism of short exact sequences
with minus the intersection reindexing. Naturality of the original connecting
morphism gives the sign, before transport to full singular cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularMayerVietorisSwap

open CategoryTheory HomologicalComplex SingularSubcomplexes

section Simplicial

variable {S : SSet.{0}} (A B : S.Subcomplex)

/-- Reorder membership proofs without changing any actual union simplex. -/
def unionSwap : (B ⊔ A).toSSet ⟶ (A ⊔ B).toSSet :=
  (SSet.Subcomplex.eqToIso (sup_comm B A)).hom

/-- Reorder membership proofs without changing any actual intersection simplex. -/
def intersectionSimplexSwap : (B ⊓ A).toSSet ⟶ (A ⊓ B).toSSet :=
  (SSet.Subcomplex.eqToIso (inf_comm B A)).hom

def unionPullback :
    SubcomplexCochains.complex (A ⊔ B).toSSet ⟶
      SubcomplexCochains.complex (B ⊔ A).toSSet :=
  SubcomplexCochains.pullback (unionSwap A B)

def intersectionPullback :
    SubcomplexCochains.complex (A ⊓ B).toSSet ⟶
      SubcomplexCochains.complex (B ⊓ A).toSSet :=
  SubcomplexCochains.pullback (intersectionSimplexSwap A B)

/-- Swap the two actual component cochains. -/
def pairSwap : SubcomplexCochains.pairComplex A B ⟶
    SubcomplexCochains.pairComplex B A where
  f n := ModuleCat.ofHom (LinearEquiv.prodComm ℚ _ _).toLinearMap
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [SubcomplexCochains.pairComplex_d, SubcomplexCochains.pairComplex_d]
    rfl

@[simp]
theorem pairSwap_apply (n : ℕ) (φ : SubcomplexCochains.PairCochain A B n) :
    (pairSwap A B).f n φ = (φ.2, φ.1) := rfl

theorem coverRestriction_swap :
    SubcomplexCochains.coverRestriction A B ≫ pairSwap A B =
      unionPullback A B ≫ SubcomplexCochains.coverRestriction B A := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Prod.ext <;> funext σ <;> rfl

/-- The minus sign is forced by the existing first-minus-second difference. -/
theorem coverDifference_swap :
    SubcomplexCochains.coverDifference A B ≫ (-intersectionPullback A B) =
      pairSwap A B ≫ SubcomplexCochains.coverDifference B A := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  change -(φ.1 ⟨σ.val, σ.property.2⟩ - φ.2 ⟨σ.val, σ.property.1⟩) =
    φ.2 ⟨σ.val, σ.property.1⟩ - φ.1 ⟨σ.val, σ.property.2⟩
  exact neg_sub _ _

/-- A morphism of the original short exact cochain sequences, retaining its sign. -/
def coverShortComplexSwap :
    SubcomplexCochains.coverShortComplex A B ⟶
      SubcomplexCochains.coverShortComplex B A where
  τ₁ := unionPullback A B
  τ₂ := pairSwap A B
  τ₃ := -intersectionPullback A B
  comm₁₂ := coverRestriction_swap A B
  comm₂₃ := (coverDifference_swap A B).symm

/-- The original connecting morphism changes sign when its cover members swap. -/
theorem subcomplex_connecting_swap (n : ℕ) :
    SubcomplexCochains.connecting A B n ≫ homologyMap (unionPullback A B) (n + 1) =
      -(homologyMap (intersectionPullback A B) n ≫
        SubcomplexCochains.connecting B A n) := by
  have h := HomologySequence.δ_naturality (coverShortComplexSwap A B)
    (SubcomplexCochains.coverShortComplex_shortExact A B)
    (SubcomplexCochains.coverShortComplex_shortExact B A) n (n + 1) (by simp)
  change SubcomplexCochains.connecting A B n ≫ homologyMap (unionPullback A B) (n + 1) =
    homologyMap (-intersectionPullback A B) n ≫ SubcomplexCochains.connecting B A n at h
  simpa only [homologyMap_neg, Preadditive.neg_comp] using h

end Simplicial

section Topological

/-- The actual identity-on-points map between the two intersection subtypes. -/
def intersectionSwap (X : TopCat.{0}) (U V : Set X) :
    TopCat.of ↥(U ∩ V) ⟶ TopCat.of ↥(V ∩ U) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, ⟨x.property.2, x.property.1⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem intersectionSwap_apply (X : TopCat.{0}) (U V : Set X) (x : ↥(U ∩ V)) :
    intersectionSwap X U V x = ⟨x.val, ⟨x.property.2, x.property.1⟩⟩ := rfl

@[reassoc (attr := simp)]
theorem intersectionSwap_subsetInclusion (X : TopCat.{0}) (U V : Set X) :
    intersectionSwap X U V ≫ subsetInclusion X (V ∩ U) = subsetInclusion X (U ∩ V) := by
  ext x
  rfl

@[simp]
theorem intersectionSwap_comp (X : TopCat.{0}) (U V : Set X) :
    intersectionSwap X U V ≫ intersectionSwap X V U = 𝟙 _ := by
  ext x
  rfl

theorem intersectionToContained_swap (X : TopCat.{0}) (U V : Set X) :
    SingularMayerVietorisNaturality.intersectionToContained X V U ≫
        intersectionSimplexSwap (subsetSingular X U) (subsetSingular X V) =
      TopCat.toSSet.map (intersectionSwap X V U) ≫
        SingularMayerVietorisNaturality.intersectionToContained X U V := by
  ext n σ
  rfl

theorem intersectionCohomologyIso_swap (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    homologyMap (intersectionPullback (subsetSingular X U) (subsetSingular X V)) n ≫
        (SingularMayerVietoris.intersectionCohomologyIso X V U n).hom =
      (SingularMayerVietoris.intersectionCohomologyIso X U V n).hom ≫
        SingularCochains.cohomologyPullback (intersectionSwap X V U) n := by
  rw [SingularMayerVietorisNaturality.intersectionCohomologyIso_hom,
    SingularMayerVietorisNaturality.intersectionCohomologyIso_hom]
  change homologyMap (SubcomplexCochains.pullback
      (intersectionSimplexSwap (subsetSingular X U) (subsetSingular X V))) n ≫
      homologyMap (SubcomplexCochains.pullback
        (SingularMayerVietorisNaturality.intersectionToContained X V U)) n =
    homologyMap (SubcomplexCochains.pullback
      (SingularMayerVietorisNaturality.intersectionToContained X U V)) n ≫
      homologyMap (SubcomplexCochains.pullback
        (TopCat.toSSet.map (intersectionSwap X V U))) n
  rw [← homologyMap_comp, ← homologyMap_comp,
    ← SubcomplexCochains.pullback_comp, ← SubcomplexCochains.pullback_comp,
    intersectionToContained_swap]

theorem intersectionCohomologyIso_inv_swap (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (SingularMayerVietoris.intersectionCohomologyIso X U V n).inv ≫
        homologyMap (intersectionPullback (subsetSingular X U) (subsetSingular X V)) n =
      SingularCochains.cohomologyPullback (intersectionSwap X V U) n ≫
        (SingularMayerVietoris.intersectionCohomologyIso X V U n).inv := by
  apply (cancel_mono (SingularMayerVietoris.intersectionCohomologyIso X V U n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [intersectionCohomologyIso_swap]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem smallRestriction_swap (X : TopCat.{0}) (U V : Set X) :
    CochainDualComparison.smallRestriction X U V ≫
        unionPullback (subsetSingular X U) (subsetSingular X V) =
      CochainDualComparison.smallRestriction X V U := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  funext σ
  rfl

variable (X : TopCat.{0}) (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

theorem smallCohomologyIso_swap (n : ℕ) :
    (CochainDualComparison.smallCohomologyIso X U V hU hV hcover n).hom ≫
        homologyMap (unionPullback (subsetSingular X U) (subsetSingular X V)) n =
      (CochainDualComparison.smallCohomologyIso X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n).hom := by
  rw [CochainDualComparison.smallCohomologyIso_hom,
    CochainDualComparison.smallCohomologyIso_hom,
    ← homologyMap_comp, smallRestriction_swap]

theorem smallCohomologyIso_inv_swap (n : ℕ) :
    homologyMap (unionPullback (subsetSingular X U) (subsetSingular X V)) n ≫
        (CochainDualComparison.smallCohomologyIso X V U hV hU
          (by simpa only [Set.union_comm] using hcover) n).inv =
      (CochainDualComparison.smallCohomologyIso X U V hU hV hcover n).inv := by
  apply (cancel_epi (CochainDualComparison.smallCohomologyIso X U V hU hV hcover n).hom).mp
  rw [← Category.assoc, smallCohomologyIso_swap X U V hU hV hcover]
  simp only [Iso.hom_inv_id]

/-- The sign law transported through the original full-singular comparisons. -/
theorem connecting_eq_neg_swap (n : ℕ) :
    SingularMayerVietoris.connecting X U V hU hV hcover n =
      -(SingularCochains.cohomologyPullback (intersectionSwap X V U) n ≫
        SingularMayerVietoris.connecting X V U hV hU
          (by simpa only [Set.union_comm] using hcover) n) := by
  calc
    SingularMayerVietoris.connecting X U V hU hV hcover n =
        (SingularMayerVietoris.intersectionCohomologyIso X U V n).inv ≫
          SubcomplexCochains.connecting (subsetSingular X U) (subsetSingular X V) n ≫
          homologyMap (unionPullback (subsetSingular X U) (subsetSingular X V)) (n + 1) ≫
          (CochainDualComparison.smallCohomologyIso X V U hV hU
            (by simpa only [Set.union_comm] using hcover) (n + 1)).inv := by
      simp only [SingularMayerVietoris.connecting,
        smallCohomologyIso_inv_swap X U V hU hV hcover]
    _ = -((SingularMayerVietoris.intersectionCohomologyIso X U V n).inv ≫
          homologyMap (intersectionPullback (subsetSingular X U) (subsetSingular X V)) n ≫
          SubcomplexCochains.connecting (subsetSingular X V) (subsetSingular X U) n ≫
          (CochainDualComparison.smallCohomologyIso X V U hV hU
            (by simpa only [Set.union_comm] using hcover) (n + 1)).inv) := by
      simpa only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg (fun f ↦ (SingularMayerVietoris.intersectionCohomologyIso X U V n).inv ≫ f ≫
          (CochainDualComparison.smallCohomologyIso X V U hV hU
            (by simpa only [Set.union_comm] using hcover) (n + 1)).inv)
          (subcomplex_connecting_swap (subsetSingular X U) (subsetSingular X V) n)
    _ = -(SingularCochains.cohomologyPullback (intersectionSwap X V U) n ≫
        SingularMayerVietoris.connecting X V U hV hU
          (by simpa only [Set.union_comm] using hcover) n) := by
      rw [← Category.assoc, ← Category.assoc, intersectionCohomologyIso_inv_swap]
      simp only [SingularMayerVietoris.connecting, Category.assoc]

/-- Pullback by the actual intersection swap reverses the original boundary sign. -/
theorem connecting_swap (n : ℕ) :
    SingularCochains.cohomologyPullback (intersectionSwap X U V) n ≫
        SingularMayerVietoris.connecting X U V hU hV hcover n =
      -SingularMayerVietoris.connecting X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n := by
  have h := connecting_eq_neg_swap X V U hV hU
    (by simpa only [Set.union_comm] using hcover) n
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

theorem connecting_swap_apply (n : ℕ)
    (z : SingularCochains.Cohomology (TopCat.of ↥(V ∩ U)) n) :
    SingularMayerVietoris.connecting X U V hU hV hcover n
        (SingularCochains.cohomologyPullback (intersectionSwap X U V) n z) =
      -SingularMayerVietoris.connecting X V U hV hU
        (by simpa only [Set.union_comm] using hcover) n z := by
  exact congrArg (fun f ↦ f z) (connecting_swap X U V hU hV hcover n)

end Topological

end HodgeConjecture.SingularMayerVietorisSwap

end
