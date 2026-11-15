module

public import HodgeConjecture.Realization.Betti.SingularSubdivisionIteration
public import HodgeConjecture.Realization.Betti.SingularSupportedChains
public import HodgeConjecture.Realization.Betti.CoverSingular

@[expose] public section

/-!
# Actual subdivision becomes small for an arbitrary open cover

The original mesh estimate on the native standard simplex and its actual
Lebesgue number provide smallness for each simplex. Subdivision preserves
smallness without a cover assumption; a maximum of finitely many iteration
counts therefore works for the entire original finite singular chain.
The index type need not be finite or countable.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.CoverSubdivision

open CategoryTheory Opposite Convexity AffineSimplexChains SingularSubdivision
open SingularSubdivisionSmallness SingularSubcomplexes SubcomplexChainCoordinates
open scoped Simplicial

universe u v

/-- Actual native subdivided cells lie in members of any genuine indexed open cover. -/
theorem exists_nativeIteration_small {κ : Type} [Fintype κ] {ι : Type v}
    (n : ℕ) (c : Chain (StdSimplex ℝ κ) (n + 1))
    (U : ι → Set (StdSimplex ℝ κ)) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) :
    ∃ k : ℕ, ∀ w ∈ (nativeIteration n k c).support,
      ∃ i, Set.range (NativeSimplexGeometry.realization w) ⊆ U i := by
  obtain ⟨ε, hε, hsmall⟩ := NativeSimplexGeometry.lebesgue_number_diam U hU hcover
  obtain ⟨k, hk⟩ := exists_nativeIteration_mesh_lt n c ε hε
  exact ⟨k, fun w hw ↦ hsmall _ (Set.range_nonempty _) (hk w hw)⟩

variable {ι : Type v}

/-- Original affine subcells give actual small simplices in the indexed native subcomplex. -/
theorem simplex_mem_cover (X : TopCat.{u}) (U : ι → Set X) {κ : Type} [Finite κ]
    (f : C(StdSimplex ℝ κ, X)) (n : ℕ)
    (w : Vertices (StdSimplex ℝ κ) (n + 1))
    (hw : ∃ i, Set.range (NativeSimplexGeometry.realization w) ⊆ f ⁻¹' U i) :
    simplex f n w ∈ (coverSingular X U).obj (op ⦋n⦌) := by
  rw [mem_coverSingular_iff_range]
  obtain ⟨i, hi⟩ := hw
  refine ⟨i, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact hi ⟨t, rfl⟩

variable (X : TopCat.{0}) (U : ι → Set X)

theorem realize_mem_coverChains {κ : Type} [Finite κ]
    (f : C(StdSimplex ℝ κ, X)) (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1))
    (hc : ∀ w ∈ c.support,
      ∃ i, Set.range (NativeSimplexGeometry.realization w) ⊆ f ⁻¹' U i) :
    realize f n c ∈ coverChains X U n :=
  realize_mem_chainSubmodule f (coverSingular X U) n c
    (fun w hw ↦ simplex_mem_cover X U f n w (hc w hw))

/-- Every original singular simplex becomes small after actual repeated subdivision. -/
theorem exists_iteration_simplex_small (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    ∃ k : ℕ, iteration X n k
      (((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) 1) ∈ coverChains X U n := by
  let f := TopCat.toSSetObjEquiv X (op ⦋n⦌) σ
  have hcover' : ⋃ i, f ⁻¹' U i = Set.univ := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨k, hk⟩ := exists_nativeIteration_small n (reference n) (fun i ↦ f ⁻¹' U i)
    (fun i ↦ (hU i).preimage f.continuous) hcover'
  refine ⟨k, ?_⟩
  rw [← realize_reference, iteration_realize]
  exact realize_mem_coverChains X U f n _ hk

/-- The actual subdivision stays in the same family member for every supported simplex. -/
theorem subdivisionComponent_mem_coverChains (n : ℕ) (c : (complex X).X n)
    (hc : c ∈ coverChains X U n) : subdivisionComponent X n c ∈ coverChains X U n := by
  apply map_mem_chainSubmodule (coverSingular X U) (coverSingular X U) n n
    (subdivisionComponent X n) ?_ c hc
  intro σ hσ
  rw [subdivisionComponent_coordinates_single, one_smul, subdividedSimplex]
  apply realize_mem_coverChains
  obtain ⟨i, hi⟩ := (mem_coverSingular_iff_range X U _ σ).mp hσ
  intro w _
  exact ⟨i, fun q _ ↦ hi ⟨q, rfl⟩⟩

theorem iteration_mem_coverChains (n k : ℕ) (c : (complex X).X n)
    (hc : c ∈ coverChains X U n) : iteration X n k c ∈ coverChains X U n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    simpa only [iteration, Function.iterate_succ_apply'] using
      subdivisionComponent_mem_coverChains X U n _ ih

theorem iteration_mem_coverChains_of_le (n k l : ℕ) (hkl : k ≤ l) (c : (complex X).X n)
    (hc : iteration X n k c ∈ coverChains X U n) : iteration X n l c ∈ coverChains X U n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [Nat.add_comm k r]
  change (subdivisionComponent X n)^[r + k] c ∈ _
  rw [Function.iterate_add_apply]
  exact iteration_mem_coverChains X U n r _ hc

/-- One actual iteration count works for the whole finite support of an original chain. -/
theorem exists_iteration_small (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (c : (complex X).X n) :
    ∃ k : ℕ, iteration X n k c ∈ coverChains X U n := by
  obtain ⟨c, rfl⟩ := (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).surjective c
  induction c using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, ?_⟩
    simpa only [map_zero, iteration, Function.iterate_zero_apply] using
      (coverChains X U n).zero_mem
  | add c d hc hd =>
    obtain ⟨k, hk⟩ := hc
    obtain ⟨l, hl⟩ := hd
    refine ⟨max k l, ?_⟩
    rw [map_add, iteration_add]
    exact (coverChains X U n).add_mem
      (iteration_mem_coverChains_of_le X U n k (max k l) (le_max_left _ _) _ hk)
      (iteration_mem_coverChains_of_le X U n l (max k l) (le_max_right _ _) _ hl)
  | single σ a =>
    obtain ⟨k, hk⟩ := exists_iteration_simplex_small X U hU hcover n σ
    refine ⟨k, ?_⟩
    have hsingle : SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
        (Finsupp.single σ a) =
        a • SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
          (Finsupp.single σ 1) := by
      rw [← map_smul]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, iteration_smul, SingularChainCoordinates.coordinates_single]
    exact (coverChains X U n).smul_mem a hk

end HodgeConjecture.CoverSubdivision
