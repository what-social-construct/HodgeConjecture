module

public import HodgeConjecture.Realization.Betti.CoverSubdivisionHomotopy
public import HodgeConjecture.Realization.Betti.SingularSubdivisionSmallness
public import HodgeConjecture.Realization.Betti.SubcomplexChainCoordinates

@[expose] public section

/-!
# The singular homotopy preserves small chains

Every new simplex in the explicit homotopy is the original singular map
composed with a continuous map into its own native domain. A simplex
already contained in one cover member therefore has its entire homotopy
chain contained in that same member. No openness or covering condition is
needed for this locality statement.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularSubdivision

open CategoryTheory Opposite Convexity SingularSubdivisionSmallness
open scoped Simplicial

/-- Smallness is exactly the range of the actual native subcomplex inclusion. -/
theorem smallChains_eq_chainSubmodule (X : TopCat) (U V : Set X) (n : ℕ) :
    smallChains X U V n =
      SubcomplexChainCoordinates.chainSubmodule (SingularSubcomplexes.smallSingular X U V) n := by
  rfl

/-- An original small simplex has its entire original continuous image in one member. -/
theorem original_range_small (X : TopCat) (U V : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌)) :
    Set.range (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ) ⊆ U ∨
      Set.range (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ) ⊆ V := by
  change σ ∈ (SingularSubcomplexes.subsetSingular X U).obj (op ⦋n⦌) ∨
    σ ∈ (SingularSubcomplexes.subsetSingular X V).obj (op ⦋n⦌) at hσ
  exact hσ.imp
    ((SingularSubcomplexes.mem_subsetSingular_iff_range X U _ σ).mp)
    ((SingularSubcomplexes.mem_subsetSingular_iff_range X V _ σ).mp)

/-- The constructed homotopy of an actual small simplex stays small. -/
theorem homotopySimplex_mem_small (X : TopCat) (U V : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌)) :
    homotopySimplex X n σ ∈ smallChains X U V (n + 1) := by
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.homotopySimplex_mem_cover X
      (fun b : Bool ↦ if b then V else U) n σ (by
        simpa only [SingularSubcomplexes.coverSingular_bool] using hσ)

/-- The actual singular homotopy preserves the whole small-chain subcomplex. -/
theorem homotopyComponent_mem_small (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (complex X).X n) (hc : c ∈ smallChains X U V n) :
    homotopyComponent X n c ∈ smallChains X U V (n + 1) := by
  simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
    smallChains] using CoverSubdivision.homotopyComponent_mem_cover X
      (fun b : Bool ↦ if b then V else U) n c (by
        simpa only [SingularSubcomplexes.coverChains, SingularSubcomplexes.coverSingular_bool,
          smallChains] using hc)

end HodgeConjecture.SingularSubdivision
