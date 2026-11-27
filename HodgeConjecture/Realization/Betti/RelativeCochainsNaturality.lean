module

public import HodgeConjecture.Realization.Betti.RelativeCochains
public import HodgeConjecture.Realization.Betti.SingularMayerVietoris

@[expose] public section

/-!
# Functoriality of the original relative cochain pullback

Maps of simplicial pairs act by the existing precomposition on the
literal kernels of restriction. Identity, composition and forgetting
support are checked on those original cochains and their native homology
maps. For topological pairs, the actual contained-simplex comparison is
natural with respect to a supplied subtype map and its inclusion square.
The resulting connecting square retains the original relative boundary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.RelativeCochains

open CategoryTheory HomologicalComplex Opposite Simplicial

universe u

section Simplicial

variable {S T U : SSet.{u}} {A : S.Subcomplex} {B : T.Subcomplex} {C : U.Subcomplex}

/-- Actual pair conditions compose by applying the two original simplex maps. -/
theorem pairCondition_comp {f : S ⟶ T} {g : T ⟶ U}
    (hf : A ≤ B.preimage f) (hg : B ≤ C.preimage g) :
    A ≤ C.preimage (f ≫ g) := by
  intro n σ hσ
  exact hg _ (hf _ hσ)

@[simp]
theorem pullbackLinear_apply (f : S ⟶ T) (h : A ≤ B.preimage f) (n : ℕ)
    (φ : Cochain B n) (σ : S.obj (op ⦋n⦌)) :
    (pullbackLinear f h n φ).val σ = φ.val (f.app (op ⦋n⦌) σ) := rfl

/-- The identity acts identically on the original vanishing-cochain complex. -/
@[simp]
theorem pullback_id (A : S.Subcomplex) (h : A ≤ A.preimage (𝟙 S)) :
    pullback (𝟙 S) h = 𝟙 (complex A) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

/-- Original relative precomposition is contravariantly functorial. -/
theorem pullback_comp (f : S ⟶ T) (g : T ⟶ U)
    (hf : A ≤ B.preimage f) (hg : B ≤ C.preimage g) :
    pullback (f ≫ g) (pairCondition_comp hf hg) = pullback g hg ≫ pullback f hf := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  rfl

/-- Equal actual simplex maps have equal pullbacks, independently of their pair proofs. -/
theorem pullback_congr {f g : S ⟶ T} (hfg : f = g)
    (hf : A ≤ B.preimage f) (hg : A ≤ B.preimage g) : pullback f hf = pullback g hg := by
  cases hfg
  rfl

/-- Native relative cohomology pullback induced by the original cochain map. -/
def cohomologyPullback (f : S ⟶ T) (h : A ≤ B.preimage f) (n : ℕ) :
    Cohomology B n ⟶ Cohomology A n := homologyMap (pullback f h) n

@[simp]
theorem cohomologyPullback_id (A : S.Subcomplex) (h : A ≤ A.preimage (𝟙 S)) (n : ℕ) :
    cohomologyPullback (𝟙 S) h n = 𝟙 (Cohomology A n) := by
  simp only [cohomologyPullback, pullback_id, homologyMap_id]

theorem cohomologyPullback_comp (f : S ⟶ T) (g : T ⟶ U)
    (hf : A ≤ B.preimage f) (hg : B ≤ C.preimage g) (n : ℕ) :
    cohomologyPullback (f ≫ g) (pairCondition_comp hf hg) n =
      cohomologyPullback g hg n ≫ cohomologyPullback f hf n := by
  simp only [cohomologyPullback, pullback_comp f g hf hg, homologyMap_comp]

theorem cohomologyPullback_congr {f g : S ⟶ T} (hfg : f = g)
    (hf : A ≤ B.preimage f) (hg : A ≤ B.preimage g) (n : ℕ) :
    cohomologyPullback f hf n = cohomologyPullback g hg n := by
  cases hfg
  rfl

/-- Forgetting support commutes with the native cohomology map of the same original pair map. -/
@[reassoc]
theorem cohomologyPullback_forget (f : S ⟶ T) (h : A ≤ B.preimage f) (n : ℕ) :
    cohomologyPullback f h n ≫ forget A n =
      forget B n ≫ homologyMap (SubcomplexCochains.pullback f) n := by
  simp only [cohomologyPullback, forget]
  rw [← homologyMap_comp, ← homologyMap_comp, pullback_inclusion]

end Simplicial

section Topological

open SingularSubcomplexes

/-- A genuine continuous map of subsets gives the actual simplicial pair condition. -/
theorem subsetCondition {X Y : TopCat.{0}} (f : X ⟶ Y) (U : Set X) (V : Set Y)
    (h : Set.MapsTo f U V) :
    subsetSingular X U ≤ (subsetSingular Y V).preimage (TopCat.toSSet.map f) := by
  intro n σ hσ t
  exact h (hσ t)

theorem subcomplexMap_subsetCondition {X Y : TopCat.{0}}
    (f : X ⟶ Y) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V) :
    subcomplexMap (TopCat.toSSet.map f) (subsetCondition f U V h) = subsetMap f U V h := by
  ext n σ
  rfl

/-- The original subtype comparison retains a supplied actual inclusion square. -/
theorem subtypeToSubset_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
    (fUV : TopCat.of U ⟶ TopCat.of V)
    (hfUV : fUV ≫ subsetInclusion Y V = subsetInclusion X U ≫ f) :
    subtypeToSubset X U ≫ subsetMap f U V h =
      TopCat.toSSet.map fUV ≫ subtypeToSubset Y V := by
  apply (cancel_mono (subsetSingular Y V).ι).mp
  simpa only [Category.assoc, subsetMap_ι, subtypeToSubset_ι,
    subtypeToSubset_ι_assoc, Functor.map_comp] using
    congrArg TopCat.toSSet.map hfUV.symm

/-- The forward cohomology comparison is native pullback on the original subtype simplices. -/
theorem chartCohomologyIso_hom (X : TopCat.{0}) (U : Set X) (n : ℕ) :
    (SingularMayerVietoris.chartCohomologyIso X U n).hom =
      homologyMap (SubcomplexCochains.pullback (subtypeToSubset X U)) n := rfl

/-- Contained-simplex and native subtype pullback are the same actual cohomology square. -/
@[reassoc]
theorem chartCohomologyIso_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
    (fUV : TopCat.of U ⟶ TopCat.of V)
    (hfUV : fUV ≫ subsetInclusion Y V = subsetInclusion X U ≫ f) (n : ℕ) :
    homologyMap (SubcomplexCochains.pullback (subsetMap f U V h)) n ≫
        (SingularMayerVietoris.chartCohomologyIso X U n).hom =
      (SingularMayerVietoris.chartCohomologyIso Y V n).hom ≫
        SingularCochains.cohomologyPullback fUV n := by
  rw [chartCohomologyIso_hom, chartCohomologyIso_hom]
  change homologyMap (SubcomplexCochains.pullback (subsetMap f U V h)) n ≫
      homologyMap (SubcomplexCochains.pullback (subtypeToSubset X U)) n =
    homologyMap (SubcomplexCochains.pullback (subtypeToSubset Y V)) n ≫
      homologyMap (SubcomplexCochains.pullback (TopCat.toSSet.map fUV)) n
  rw [← homologyMap_comp, ← homologyMap_comp,
    ← SubcomplexCochains.pullback_comp, ← SubcomplexCochains.pullback_comp,
    subtypeToSubset_naturality f U V h fUV hfUV]

/-- Native subtype boundary naturality, before any choice of a local orientation class. -/
@[reassoc]
theorem connecting_subtype_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
    (fUV : TopCat.of U ⟶ TopCat.of V)
    (hfUV : fUV ≫ subsetInclusion Y V = subsetInclusion X U ≫ f) (n : ℕ) :
    (SingularMayerVietoris.chartCohomologyIso Y V n).inv ≫
        connecting (subsetSingular Y V) n ≫
          homologyMap (pullback (TopCat.toSSet.map f) (subsetCondition f U V h)) (n + 1) =
      SingularCochains.cohomologyPullback fUV n ≫
        (SingularMayerVietoris.chartCohomologyIso X U n).inv ≫
          connecting (subsetSingular X U) n := by
  have hchart : (SingularMayerVietoris.chartCohomologyIso Y V n).inv ≫
        homologyMap (SubcomplexCochains.pullback (subsetMap f U V h)) n =
      SingularCochains.cohomologyPullback fUV n ≫
        (SingularMayerVietoris.chartCohomologyIso X U n).inv := by
    apply (cancel_mono (SingularMayerVietoris.chartCohomologyIso X U n).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [chartCohomologyIso_naturality f U V h fUV hfUV n]
    simp
  rw [connecting_naturality (TopCat.toSSet.map f) (subsetCondition f U V h) n,
    subcomplexMap_subsetCondition f U V h]
  rw [← Category.assoc, hchart, Category.assoc]

end Topological

end HodgeConjecture.RelativeCochains

end
