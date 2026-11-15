module

public import HodgeConjecture.Realization.Betti.CoverSubdivisionSmallness

@[expose] public section

/-!
# The existing two-open smallness API

These names specialize the shared indexed-cover smallness proof. The
original mesh, affine naturality and iteration APIs are re-exported from
`SingularSubdivisionIteration`. Supported chains use the shared native
subcomplex inclusion range.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularSubdivisionSmallness

open CategoryTheory Opposite Convexity AffineSimplexChains SingularSubdivision
open scoped Simplicial

private theorem two_iUnion {T : Type} (U V : Set T) :
    (⋃ b : Bool, if b then V else U) = U ∪ V := by
  ext p
  simp only [Set.mem_iUnion, Bool.exists_bool, Bool.false_eq_true, ite_false,
    ite_true, Set.mem_union]

/-- Every actual native cell eventually lies in one member of the genuine open cover. -/
theorem exists_nativeIteration_small {κ : Type} [Fintype κ] (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1))
    (U V : Set (StdSimplex ℝ κ)) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    ∃ k : ℕ, ∀ v ∈ (nativeIteration n k c).support,
      Set.range (NativeSimplexGeometry.realization v) ⊆ U ∨
        Set.range (NativeSimplexGeometry.realization v) ⊆ V := by
  have hW : ∀ b : Bool, IsOpen (if b then V else U) := by
    intro b; cases b <;> assumption
  obtain ⟨k, hk⟩ := CoverSubdivision.exists_nativeIteration_small n c
    (fun b : Bool ↦ if b then V else U) hW ((two_iUnion U V).trans hcover)
  refine ⟨k, fun w hw ↦ ?_⟩
  obtain ⟨b, hb⟩ := hk w hw
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

/-- Actual finite singular chains supported on simplices contained in one cover member. -/
def smallChains (X : TopCat) (U V : Set X) (n : ℕ) : Submodule ℚ ((complex X).X n) :=
  SubcomplexChainCoordinates.chainSubmodule (SingularSubcomplexes.smallSingular X U V) n

theorem coordinates_mem_smallChains (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) →₀ ℚ) :
    SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n c ∈ smallChains X U V n ↔
      c ∈ Finsupp.supported ℚ ℚ
        ((SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌)) := by
  rw [smallChains, SubcomplexChainCoordinates.mem_chainSubmodule_iff,
    LinearEquiv.symm_apply_apply]
  rfl

/-- A realized native tuple lies in the small singular set whenever its whole cell lands
in one member of the original cover. -/
theorem simplex_mem_small {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (U V : Set X) (n : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1))
    (hv : Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' U ∨
      Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' V) :
    simplex f n v ∈ (SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌) := by
  rw [← SingularSubcomplexes.coverSingular_bool X U V]
  exact CoverSubdivision.simplex_mem_cover X (fun b : Bool ↦ if b then V else U) f n v
    (hv.elim (fun h ↦ ⟨false, h⟩) (fun h ↦ ⟨true, h⟩))

/-- Linear realization of an actual finite native chain retains proved whole-cell smallness. -/
theorem realize_mem_smallChains {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (U V : Set X) (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1))
    (hc : ∀ v ∈ c.support,
      Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' U ∨
        Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' V) :
    realize f n c ∈ smallChains X U V n := by
  exact realize_mem_chainSubmodule f (SingularSubcomplexes.smallSingular X U V) n c
    (fun v hv ↦ simplex_mem_small f U V n v (hc v hv))

/-- Every actual singular simplex becomes a small finite chain after enough repetitions
of the constructed singular-chain endomorphism. -/
theorem exists_iteration_simplex_small (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    ∃ k : ℕ, iteration X n k
      (((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) 1) ∈ smallChains X U V n := by
  have hW : ∀ b : Bool, IsOpen (if b then V else U) := by
    intro b; cases b <;> assumption
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.exists_iteration_simplex_small X
      (fun b : Bool ↦ if b then V else U) hW ((two_iUnion U V).trans hcover) n σ

/-- Once a singular chain is small, the actual subdivision keeps it small. -/
theorem subdivisionComponent_mem_smallChains (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (complex X).X n) (hc : c ∈ smallChains X U V n) :
    subdivisionComponent X n c ∈ smallChains X U V n := by
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.subdivisionComponent_mem_coverChains X
      (fun b : Bool ↦ if b then V else U) n c (by
        simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
          smallChains] using hc)

theorem iteration_mem_smallChains (X : TopCat) (U V : Set X) (n k : ℕ)
    (c : (complex X).X n) (hc : c ∈ smallChains X U V n) :
    iteration X n k c ∈ smallChains X U V n := by
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.iteration_mem_coverChains X
      (fun b : Bool ↦ if b then V else U) n k c (by
        simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
          smallChains] using hc)

/-- Every larger iteration count works after a chain has become small. -/
theorem iteration_mem_smallChains_of_le (X : TopCat) (U V : Set X) (n k l : ℕ)
    (hkl : k ≤ l) (c : (complex X).X n) (hc : iteration X n k c ∈ smallChains X U V n) :
    iteration X n l c ∈ smallChains X U V n := by
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.iteration_mem_coverChains_of_le X
      (fun b : Bool ↦ if b then V else U) n k l hkl c (by
        simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
          smallChains] using hc)

/-- One actual iteration count works for the entire finite support of any original singular
chain. This is the small-chain shrinking theorem, without a homology-equivalence premise. -/
theorem exists_iteration_small (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (c : (complex X).X n) :
    ∃ k : ℕ, iteration X n k c ∈ smallChains X U V n := by
  have hW : ∀ b : Bool, IsOpen (if b then V else U) := by
    intro b; cases b <;> assumption
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.exists_iteration_small X
      (fun b : Bool ↦ if b then V else U) hW ((two_iUnion U V).trans hcover) n c

end HodgeConjecture.SingularSubdivisionSmallness
