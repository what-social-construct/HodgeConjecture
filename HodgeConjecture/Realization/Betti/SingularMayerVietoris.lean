module

public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import HodgeConjecture.Realization.Betti.CochainPair

@[expose] public section

/-!
# Mayer–Vietoris for actual rational singular cohomology

For a genuine two-open cover, the proved small-cochain comparison carries
the original subcomplex gluing sequence to the full singular cohomology
of the space. The two pieces and their intersection have their actual
subtype topologies. The middle term is the product of their cohomology.
The difference convention is first restriction minus second restriction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.SingularMayerVietoris

open CategoryTheory CategoryTheory.Limits HomologicalComplex SingularSubcomplexes

/-- Contravariant cochain comparison along an actual simplicial isomorphism. -/
def pullbackIso {S T : SSet.{0}} (e : S ≅ T) :
    SubcomplexCochains.complex T ≅ SubcomplexCochains.complex S where
  hom := SubcomplexCochains.pullback e.hom
  inv := SubcomplexCochains.pullback e.inv
  hom_inv_id := by
    rw [← SubcomplexCochains.pullback_comp, e.inv_hom_id]
    ext n φ
    rfl
  inv_hom_id := by
    rw [← SubcomplexCochains.pullback_comp, e.hom_inv_id]
    ext n φ
    rfl

/-- Cohomology of contained simplices is the singular cohomology of the actual subtype space. -/
def chartCohomologyIso (X : TopCat.{0}) (U : Set X) (n : ℕ) :
    (SubcomplexCochains.complex (subsetSingular X U).toSSet).homology n ≅
      SingularCochains.Cohomology (TopCat.of U) n :=
  (homologyMapIso (pullbackIso (subsetSingularIso X U)) n).symm

/-- The actual pair complex compares with the product of the two actual subtype cohomologies. -/
def pairCohomologyIso (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (SubcomplexCochains.pairComplex (subsetSingular X U) (subsetSingular X V)).homology n ≅
      ModuleCat.of ℚ (SingularCochains.Cohomology (TopCat.of U) n ×
        SingularCochains.Cohomology (TopCat.of V) n) :=
  CochainPair.cohomologyIso (subsetSingular X U) (subsetSingular X V) n ≪≫
    ((chartCohomologyIso X U n).toLinearEquiv.prodCongr
      (chartCohomologyIso X V n).toLinearEquiv).toModuleIso

/-- The simplicial intersection is the singular set of the original intersection subtype. -/
def intersectionCohomologyIso (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    (SubcomplexCochains.complex
      ((subsetSingular X U ⊓ subsetSingular X V : (TopCat.toSSet.obj X).Subcomplex) : SSet)).homology n ≅
      SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) n :=
  homologyMapIso (pullbackIso (SSet.Subcomplex.eqToIso (subsetSingular_inter X U V))) n ≪≫
    chartCohomologyIso X (U ∩ V) n

/-- Move an actual short complex along proved isomorphisms of its three objects. -/
def transport {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y₁ Y₂ Y₃ : C} (e₁ : S.X₁ ≅ Y₁) (e₂ : S.X₂ ≅ Y₂)
    (e₃ : S.X₃ ≅ Y₃) : ShortComplex C :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by simp)

/-- The transported sequence retains the original actual short complex. -/
def transportIso {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y₁ Y₂ Y₃ : C} (e₁ : S.X₁ ≅ Y₁) (e₂ : S.X₂ ≅ Y₂)
    (e₃ : S.X₃ ≅ Y₃) : S ≅ transport S e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃ (by simp [transport]) (by simp [transport])

/-- Exactness is transported only through the constructed object comparisons. -/
theorem transport_exact {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {Y₁ Y₂ Y₃ : C} (e₁ : S.X₁ ≅ Y₁) (e₂ : S.X₂ ≅ Y₂)
    (e₃ : S.X₃ ≅ Y₃) [S.HasHomology] [(transport S e₁ e₂ e₃).HasHomology]
    (h : S.Exact) : (transport S e₁ e₂ e₃).Exact :=
  ShortComplex.exact_of_iso (transportIso S e₁ e₂ e₃) h

/-- The actual restriction map from the full space to both subtype pieces. -/
def restriction (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    SingularCochains.Cohomology X n ⟶
      ModuleCat.of ℚ (SingularCochains.Cohomology (TopCat.of U) n ×
        SingularCochains.Cohomology (TopCat.of V) n) :=
  homologyMap (CochainDualComparison.smallRestriction X U V) n ≫
    homologyMap (SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V)) n ≫
      (pairCohomologyIso X U V n).hom

/-- First restriction minus second restriction on the original intersection. -/
def difference (X : TopCat.{0}) (U V : Set X) (n : ℕ) :
    ModuleCat.of ℚ (SingularCochains.Cohomology (TopCat.of U) n ×
      SingularCochains.Cohomology (TopCat.of V) n) ⟶
        SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) n :=
  (pairCohomologyIso X U V n).inv ≫
    homologyMap (SubcomplexCochains.coverDifference (subsetSingular X U) (subsetSingular X V)) n ≫
      (intersectionCohomologyIso X U V n).hom

/-- The actual connecting morphism, using the proved full-space/small-cochain comparison. -/
def connecting (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of ↥(U ∩ V)) n ⟶ SingularCochains.Cohomology X (n + 1) :=
  (intersectionCohomologyIso X U V n).inv ≫
    SubcomplexCochains.connecting (subsetSingular X U) (subsetSingular X V) n ≫
      (CochainDualComparison.smallCohomologyIso X U V hU hV hcover (n + 1)).inv

/-- The full-space → pair → intersection portion of the actual singular sequence. -/
def pairSequence (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) : ShortComplex (ModuleCat.{0} ℚ) :=
  transport ((SubcomplexCochains.coverShortComplex (subsetSingular X U) (subsetSingular X V)).map
      (homologyFunctor _ _ n))
    (CochainDualComparison.smallCohomologyIso X U V hU hV hcover n).symm
    (pairCohomologyIso X U V n) (intersectionCohomologyIso X U V n)

@[simp]
theorem pairSequence_f (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (pairSequence X U V hU hV hcover n).f = restriction X U V n := by
  simp [pairSequence, transport, restriction, SubcomplexCochains.coverShortComplex]

@[simp]
theorem pairSequence_g (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (pairSequence X U V hU hV hcover n).g = difference X U V n := rfl

theorem pairSequence_exact (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (pairSequence X U V hU hV hcover n).Exact :=
  transport_exact _ _ _ _ (SubcomplexCochains.homology_exact_pair _ _ n)

/-- The pair → intersection → next full-space portion of the actual singular sequence. -/
def intersectionSequence (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) : ShortComplex (ModuleCat.{0} ℚ) :=
  transport (ShortComplex.mk
    (homologyMap (SubcomplexCochains.coverDifference (subsetSingular X U) (subsetSingular X V)) n)
    (SubcomplexCochains.connecting (subsetSingular X U) (subsetSingular X V) n)
    ((SubcomplexCochains.coverShortComplex_shortExact (subsetSingular X U) (subsetSingular X V)).comp_δ
      n (n + 1) (by simp)))
    (pairCohomologyIso X U V n) (intersectionCohomologyIso X U V n)
    (CochainDualComparison.smallCohomologyIso X U V hU hV hcover (n + 1)).symm

@[simp]
theorem intersectionSequence_f (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (intersectionSequence X U V hU hV hcover n).f = difference X U V n := rfl

@[simp]
theorem intersectionSequence_g (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (intersectionSequence X U V hU hV hcover n).g = connecting X U V hU hV hcover n := rfl

theorem intersectionSequence_exact (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (intersectionSequence X U V hU hV hcover n).Exact :=
  transport_exact _ _ _ _ (SubcomplexCochains.homology_exact_intersection _ _ n)

/-- The intersection → next full-space → next pair portion of the actual singular sequence. -/
def unionSequence (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) : ShortComplex (ModuleCat.{0} ℚ) :=
  transport (ShortComplex.mk
    (SubcomplexCochains.connecting (subsetSingular X U) (subsetSingular X V) n)
    (homologyMap (SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V)) (n + 1))
    ((SubcomplexCochains.coverShortComplex_shortExact (subsetSingular X U) (subsetSingular X V)).δ_comp
      n (n + 1) (by simp)))
    (intersectionCohomologyIso X U V n)
    (CochainDualComparison.smallCohomologyIso X U V hU hV hcover (n + 1)).symm
    (pairCohomologyIso X U V (n + 1))

@[simp]
theorem unionSequence_f (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (unionSequence X U V hU hV hcover n).f = connecting X U V hU hV hcover n := rfl

@[simp]
theorem unionSequence_g (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (unionSequence X U V hU hV hcover n).g = restriction X U V (n + 1) := by
  simp [unionSequence, transport, restriction]

theorem unionSequence_exact (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (unionSequence X U V hU hV hcover n).Exact :=
  transport_exact _ _ _ _ (SubcomplexCochains.homology_exact_union _ _ n)

theorem restriction_comp_difference (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    restriction X U V n ≫ difference X U V n = 0 := by
  simpa only [pairSequence_f, pairSequence_g] using (pairSequence X U V hU hV hcover n).zero

theorem difference_comp_connecting (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    difference X U V n ≫ connecting X U V hU hV hcover n = 0 := by
  simpa only [intersectionSequence_f, intersectionSequence_g] using
    (intersectionSequence X U V hU hV hcover n).zero

theorem connecting_comp_restriction (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    connecting X U V hU hV hcover n ≫ restriction X U V (n + 1) = 0 := by
  simpa only [unionSequence_f, unionSequence_g] using (unionSequence X U V hU hV hcover n).zero

/-- The sequence starts with an actual injection on degree-zero singular cohomology. -/
theorem mono_restriction_zero (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : Mono (restriction X U V 0) := by
  have := CochainDualComparison.smallRestriction_quasiIso X U V hU hV hcover
  have : Mono ((SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V)).f 0) :=
    (SubcomplexCochains.coverShortComplex_degreewise_shortExact (subsetSingular X U)
      (subsetSingular X V) 0).mono_f
  have : Mono (homologyMap
      (SubcomplexCochains.coverRestriction (subsetSingular X U) (subsetSingular X V)) 0) :=
    mono_homologyMap_of_mono_of_not_rel _ 0 (by intro i; simp)
  dsimp only [restriction]
  infer_instance

end HodgeConjecture.SingularMayerVietoris
