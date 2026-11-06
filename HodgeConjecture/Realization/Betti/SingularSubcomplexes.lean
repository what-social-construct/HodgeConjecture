module

public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

@[expose] public section

/-!
# Singular simplices contained in a subset

For a subset of a topological space, the singular simplices whose entire
image is in that subset form a simplicial subcomplex. Its simplicial set
is identified with the singular set of the actual subtype space.
For two subsets their union as simplicial subcomplexes consists of the
simplices contained in one member. No small-chain comparison is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubcomplexes

open CategoryTheory Opposite Simplicial

universe u

/-- The actual lifted topological simplex underlying a singular simplex. -/
def simplexMap (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) : SimplexCategory.toTop.{u}.obj n.unop ⟶ X := σ.down

/-- Actual singular simplices whose whole image lies in the given subset. -/
def subsetSingular (X : TopCat.{u}) (U : Set X) : (TopCat.toSSet.obj X).Subcomplex where
  obj n := {σ | ∀ t, simplexMap X n σ t ∈ U}
  map f _σ hσ t := hσ ((SimplexCategory.toTop.{u}.map f.unop) t)

@[simp]
theorem mem_subsetSingular (X : TopCat.{u}) (U : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (subsetSingular X U).obj n ↔ ∀ t, simplexMap X n σ t ∈ U := Iff.rfl

/-- The raw lifted simplices and ordinary continuous standard simplices have the same image. -/
theorem mem_subsetSingular_iff_range (X : TopCat.{u}) (U : Set X)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (subsetSingular X U).obj n ↔
      Set.range (TopCat.toSSetObjEquiv X n σ) ⊆ U := by
  constructor
  · intro h y hy
    obtain ⟨t, ht⟩ := hy
    rw [← ht]
    exact h (ULift.up t)
  · intro h t
    exact h ⟨t.down, rfl⟩

theorem subsetSingular_mono (X : TopCat.{u}) {U V : Set X} (h : U ⊆ V) :
    subsetSingular X U ≤ subsetSingular X V :=
  fun _ _ hσ t ↦ h (hσ t)

/-- An actual continuous map carrying one subset into another acts on the contained simplices. -/
def subsetMap {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Set X) (V : Set Y)
    (h : Set.MapsTo f U V) : (subsetSingular X U).toSSet ⟶ (subsetSingular Y V).toSSet where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map f).app n σ.val, fun t ↦ h (σ.property t)⟩
  naturality _ _ _ := by ext σ; rfl

@[reassoc (attr := simp)]
theorem subsetMap_ι {X Y : TopCat.{u}} (f : X ⟶ Y) (U : Set X) (V : Set Y)
    (h : Set.MapsTo f U V) :
    subsetMap f U V h ≫ (subsetSingular Y V).ι =
      (subsetSingular X U).ι ≫ TopCat.toSSet.map f := rfl

@[simp]
theorem subsetSingular_inter (X : TopCat.{u}) (U V : Set X) :
    subsetSingular X (U ∩ V) = subsetSingular X U ⊓ subsetSingular X V := by
  ext n σ
  constructor
  · intro h
    exact ⟨fun t ↦ (h t).1, fun t ↦ (h t).2⟩
  · rintro ⟨hU, hV⟩ t
    exact ⟨hU t, hV t⟩

@[simp]
theorem subsetSingular_univ (X : TopCat.{u}) : subsetSingular X Set.univ = ⊤ := by
  ext n σ
  simp

@[simp]
theorem subsetSingular_empty (X : TopCat.{u}) : subsetSingular X ∅ = ⊥ := by
  ext n σ
  change (∀ t : SimplexCategory.toTop.{u}.obj n.unop, False) ↔ False
  constructor
  · intro h
    exact h (Classical.choice inferInstance)
  · intro h
    exact h.elim

/-- The usual continuous inclusion of the actual subtype space. -/
def subsetInclusion (X : TopCat.{u}) (U : Set X) : TopCat.of U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Regard a singular simplex of the subtype as a simplex of the original space. -/
def subtypeToSubset (X : TopCat.{u}) (U : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶ (subsetSingular X U).toSSet where
  app n := ↾fun σ ↦ ⟨(TopCat.toSSet.map (subsetInclusion X U)).app n σ,
    fun t ↦ (simplexMap (TopCat.of U) n σ t).property⟩
  naturality _ _ f := by ext σ; rfl

/-- Restrict the codomain of a simplex whose entire image lies in the subset. -/
def subsetToSubtype (X : TopCat.{u}) (U : Set X) :
    (subsetSingular X U).toSSet ⟶ TopCat.toSSet.obj (TopCat.of U) where
  app n := ↾fun σ ↦ ⟨TopCat.ofHom
    ⟨fun t ↦ ⟨simplexMap X n σ.val t, σ.property t⟩,
      (simplexMap X n σ.val).hom.continuous.subtype_mk (fun t ↦ σ.property t)⟩⟩
  naturality _ _ f := by ext σ; rfl

/-- The contained simplices are precisely the singular simplices of the original subtype topology. -/
def subsetSingularIso (X : TopCat.{u}) (U : Set X) :
    (subsetSingular X U).toSSet ≅ TopCat.toSSet.obj (TopCat.of U) where
  hom := subsetToSubtype X U
  inv := subtypeToSubset X U
  hom_inv_id := by ext n σ; rfl
  inv_hom_id := by ext n σ; rfl

@[reassoc (attr := simp)]
theorem subtypeToSubset_ι (X : TopCat.{u}) (U : Set X) :
    subtypeToSubset X U ≫ (subsetSingular X U).ι = TopCat.toSSet.map (subsetInclusion X U) := rfl

/-- The small singular simplices for two cover members, as an actual simplicial union. -/
def smallSingular (X : TopCat.{u}) (U V : Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  subsetSingular X U ⊔ subsetSingular X V

@[simp]
theorem mem_smallSingular (X : TopCat.{u}) (U V : Set X) (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (smallSingular X U V).obj n ↔
      (∀ t, simplexMap X n σ t ∈ U) ∨ (∀ t, simplexMap X n σ t ∈ V) := Iff.rfl

theorem smallSingular_le_union (X : TopCat.{u}) (U V : Set X) :
    smallSingular X U V ≤ subsetSingular X (U ∪ V) :=
  sup_le (subsetSingular_mono X Set.subset_union_left)
    (subsetSingular_mono X Set.subset_union_right)

/-- A two-set cover contains every actual zero-simplex in one of its members. -/
theorem zeroSimplex_mem_smallSingular (X : TopCat.{u}) (U V : Set X)
    (hUV : U ∪ V = Set.univ) (σ : (TopCat.toSSet.obj X).obj (op ⦋0⦌)) :
    σ ∈ (smallSingular X U V).obj (op ⦋0⦌) := by
  have h : simplexMap X (op ⦋0⦌) σ default ∈ U ∪ V := by rw [hUV]; trivial
  rcases h with hU | hV
  · exact Or.inl (fun t ↦ (Subsingleton.elim t default) ▸ hU)
  · exact Or.inr (fun t ↦ (Subsingleton.elim t default) ▸ hV)

/-- Intersection and union give the genuine simplicial pushout of the contained subcomplexes. -/
theorem smallSingular_isPushout (X : TopCat.{u}) (U V : Set X) :
    CategoryTheory.IsPushout
      (SSet.Subcomplex.homOfLE
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X U from inf_le_left))
      (SSet.Subcomplex.homOfLE
        (show subsetSingular X U ⊓ subsetSingular X V ≤ subsetSingular X V from inf_le_right))
      (SSet.Subcomplex.homOfLE
        (show subsetSingular X U ≤ smallSingular X U V from le_sup_left))
      (SSet.Subcomplex.homOfLE
        (show subsetSingular X V ≤ smallSingular X U V from le_sup_right)) :=
  SSet.Subcomplex.BicartSq.isPushout ⟨rfl, rfl⟩

end HodgeConjecture.SingularSubcomplexes
