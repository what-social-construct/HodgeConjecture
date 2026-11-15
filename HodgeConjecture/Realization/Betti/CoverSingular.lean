module

public import HodgeConjecture.Realization.Betti.SingularSubcomplexes
public import HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates

@[expose] public section

/-!
# Small singular chains for an arbitrary indexed family

The small simplicial subcomplex is the native supremum of the existing
subset singular subcomplexes. Its chains, inclusion and supported range
are the original native constructions. No openness or covering condition
is required to define them.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubcomplexes

open CategoryTheory Opposite Simplicial

universe u v

variable {ι : Type v}

/-- Actual singular simplices contained in a single member of the indexed family. -/
def coverSingular (X : TopCat.{u}) (U : ι → Set X) : (TopCat.toSSet.obj X).Subcomplex :=
  ⨆ i, subsetSingular X (U i)

@[simp]
theorem mem_coverSingular (X : TopCat.{u}) (U : ι → Set X)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (coverSingular X U).obj n ↔ ∃ i, σ ∈ (subsetSingular X (U i)).obj n := by
  simp only [coverSingular, Subfunctor.iSup_obj, Set.mem_iUnion]

theorem mem_coverSingular_iff_range (X : TopCat.{u}) (U : ι → Set X)
    (n : SimplexCategoryᵒᵖ) (σ : (TopCat.toSSet.obj X).obj n) :
    σ ∈ (coverSingular X U).obj n ↔ ∃ i, Set.range (TopCat.toSSetObjEquiv X n σ) ⊆ U i := by
  simp only [mem_coverSingular, mem_subsetSingular_iff_range]

/-- Refining a family gives the original native subcomplex inclusion. -/
theorem coverSingular_le_of_refinement {τ : Type*} (X : TopCat.{u})
    (U : ι → Set X) (V : τ → Set X) (h : ∀ i, ∃ j, U i ⊆ V j) :
    coverSingular X U ≤ coverSingular X V := by
  apply iSup_le
  intro i
  obtain ⟨j, hj⟩ := h i
  exact (subsetSingular_mono X hj).trans (le_iSup (fun j ↦ subsetSingular X (V j)) j)

/-- The indexed family of two sets gives exactly the existing two-open subcomplex. -/
@[simp]
theorem coverSingular_bool (X : TopCat.{u}) (U V : Set X) :
    coverSingular X (fun b : Bool ↦ if b then V else U) = smallSingular X U V := by
  ext n σ
  simp only [mem_coverSingular, Bool.exists_bool, Bool.false_eq_true, ite_false, ite_true,
    mem_smallSingular, mem_subsetSingular]

/-- Every original zero-simplex belongs to a member of a genuine indexed cover. -/
theorem zeroSimplex_mem_coverSingular (X : TopCat.{u}) (U : ι → Set X)
    (hcover : ⋃ i, U i = Set.univ) (σ : (TopCat.toSSet.obj X).obj (op ⦋0⦌)) :
    σ ∈ (coverSingular X U).obj (op ⦋0⦌) := by
  have hx : simplexMap X (op ⦋0⦌) σ default ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact (mem_coverSingular X U _ σ).mpr ⟨i, fun t ↦ (Subsingleton.elim t default) ▸ hi⟩

/-- The original native chain complex of this native simplicial supremum. -/
abbrev coverComplex (X : TopCat.{0}) (U : ι → Set X) :=
  (coverSingular X U : SSet).chainComplex (ModuleCat.of ℚ ℚ)

/-- The original native chain inclusion, with no replacement chain carrier. -/
abbrev coverInclusion (X : TopCat.{0}) (U : ι → Set X) :=
  SubcomplexChainCoordinates.inclusion (coverSingular X U)

/-- Small chains are the already constructed supported range of that inclusion. -/
abbrev coverChains (X : TopCat.{0}) (U : ι → Set X) (n : ℕ) :=
  SubcomplexChainCoordinates.chainSubmodule (coverSingular X U) n

end HodgeConjecture.SingularSubcomplexes
