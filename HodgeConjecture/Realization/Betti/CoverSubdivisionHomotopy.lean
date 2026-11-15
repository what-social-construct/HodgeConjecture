module

public import HodgeConjecture.Realization.Betti.CoverSubdivisionSmallness
public import HodgeConjecture.Realization.Betti.SingularSubdivisionHomology

@[expose] public section

/-!
# The existing subdivision homotopy on indexed small chains

Every realized homotopy cell stays inside the image of its original
simplex. The original operators and native chain homotopy therefore
restrict through the shared supported-range construction. No openness
or covering hypothesis is required for these restrictions.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.CoverSubdivision

open CategoryTheory Opposite Convexity SingularSubcomplexes SubcomplexChainCoordinates
open SingularSubdivision
open scoped Simplicial

universe v

variable {ι : Type v} (X : TopCat.{0}) (U : ι → Set X)

theorem homotopySimplex_mem_cover (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌))
    (hσ : σ ∈ (coverSingular X U).obj (op ⦋n⦌)) :
    homotopySimplex X n σ ∈ coverChains X U (n + 1) := by
  apply realize_mem_coverChains
  obtain ⟨i, hi⟩ := (mem_coverSingular_iff_range X U _ σ).mp hσ
  intro w _
  exact ⟨i, fun q _ ↦ hi ⟨q, rfl⟩⟩

theorem homotopyComponent_mem_cover (n : ℕ) (c : (complex X).X n)
    (hc : c ∈ coverChains X U n) : homotopyComponent X n c ∈ coverChains X U (n + 1) := by
  apply map_mem_chainSubmodule (coverSingular X U) (coverSingular X U) n (n + 1)
    (homotopyComponent X n) ?_ c hc
  intro σ hσ
  rw [homotopyComponent_coordinates_single, one_smul]
  exact homotopySimplex_mem_cover X U n σ hσ

theorem homotopyDegree_mem_cover (i j : ℕ) (c : (complex X).X i)
    (hc : c ∈ coverChains X U i) : homotopyDegree X i j c ∈ coverChains X U j := by
  by_cases hij : i + 1 = j
  · subst j
    rw [homotopyDegree_succ]
    exact homotopyComponent_mem_cover X U i c hc
  · rw [homotopyDegree, dite_eq_right hij]
    exact (coverChains X U j).zero_mem

/-- The original subdivision restricted to the original indexed small subcomplex. -/
def subdivision : coverComplex X U ⟶ coverComplex X U :=
  restrictMap (coverSingular X U) (coverSingular X U) (SingularSubdivision.subdivision X)
    (fun n c hc ↦ subdivisionComponent_mem_coverChains X U n c hc)

theorem subdivision_inclusion : subdivision X U ≫ coverInclusion X U =
    coverInclusion X U ≫ SingularSubdivision.subdivision X :=
  restrictMap_inclusion _ _ _ _

/-- Restriction of the already constructed native singular chain homotopy. -/
def subdivisionHomotopy : Homotopy (𝟙 (coverComplex X U)) (subdivision X U) := by
  have h := restrictHomotopy (coverSingular X U) (coverSingular X U)
    (fun _ _ hc ↦ hc) (fun n c hc ↦ subdivisionComponent_mem_coverChains X U n c hc)
    (SingularSubdivision.subdivisionHomotopy X)
    (fun i j c hc ↦ homotopyDegree_mem_cover X U i j c hc)
  rw [restrictMap_id] at h
  exact h

theorem homologyMap_subdivision (n : ℕ) :
    HomologicalComplex.homologyMap (subdivision X U) n =
      𝟙 ((coverComplex X U).homology n) := by
  simpa only [HomologicalComplex.homologyMap_id] using
    ((subdivisionHomotopy X U).homologyMap_eq n).symm

def subdivisionPower (k : ℕ) : coverComplex X U ⟶ coverComplex X U :=
  ((End.of (subdivision X U)) ^ k).asHom

@[simp]
theorem subdivisionPower_zero : subdivisionPower X U 0 = 𝟙 (coverComplex X U) := rfl

@[simp]
theorem subdivisionPower_succ (k : ℕ) :
    subdivisionPower X U (k + 1) = subdivision X U ≫ subdivisionPower X U k := by
  simp only [subdivisionPower, pow_succ, End.mul_asHom]

theorem subdivisionPower_inclusion (k : ℕ) :
    subdivisionPower X U k ≫ coverInclusion X U =
      coverInclusion X U ≫ SingularSubdivision.subdivisionPower X k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [subdivisionPower_succ, Category.assoc, ih, ← Category.assoc,
      subdivision_inclusion, Category.assoc, ← SingularSubdivision.subdivisionPower_succ]

theorem homologyMap_subdivisionPower (k n : ℕ) :
    HomologicalComplex.homologyMap (subdivisionPower X U k) n =
      𝟙 ((coverComplex X U).homology n) := by
  induction k with
  | zero => rw [subdivisionPower_zero, HomologicalComplex.homologyMap_id]
  | succ k ih =>
    rw [subdivisionPower_succ, HomologicalComplex.homologyMap_comp,
      homologyMap_subdivision, ih, Category.id_comp]

end HodgeConjecture.CoverSubdivision
