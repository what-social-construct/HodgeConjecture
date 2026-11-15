module

public import HodgeConjecture.Realization.Betti.CoverSubdivisionHomotopy
public import HodgeConjecture.Realization.Betti.ChainHomologyClasses

@[expose] public section

/-!
# Small-chain comparison for arbitrary indexed open covers

Actual subdivision eventually places each original finite chain in the
indexed small subcomplex. The restricted original homotopy proves that
the native inclusion is a quasi-isomorphism, in every degree. Refinement
maps are the original native subcomplex inclusions and commute with this
comparison. No finiteness or separation hypothesis is imposed on the cover.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.CoverSmallChains

open CategoryTheory HomologicalComplex SingularSubcomplexes

universe v w

variable {ι : Type v} (X : TopCat.{0}) (U : ι → Set X)

/-- The original indexed small-chain inclusion computes rational singular homology. -/
theorem inclusion_quasiIso (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    QuasiIso (coverInclusion X U) := by
  apply ChainHomologyClasses.quasiIso_of_eventual_image (coverInclusion X U)
    (fun n ↦ SubcomplexChainCoordinates.inclusion_injective (coverSingular X U) n)
    (CoverSubdivision.subdivisionPower X U) (SingularSubdivision.subdivisionPower X)
    (CoverSubdivision.homologyMap_subdivisionPower X U)
    (SingularSubdivision.homologyMap_subdivision_pow X)
    (fun k ↦ (CoverSubdivision.subdivisionPower_inclusion X U k).symm)
  intro n c
  obtain ⟨k, hk⟩ := CoverSubdivision.exists_iteration_small X U hU hcover n c
  change SingularSubdivisionSmallness.iteration X n k c ∈
    SubcomplexChainCoordinates.chainSubmodule (coverSingular X U) n at hk
  rw [← SubcomplexChainCoordinates.range_inclusion] at hk
  obtain ⟨a, ha⟩ := hk
  exact ⟨k, a, ha.trans (SingularSubdivision.subdivisionPower_apply X k n c).symm⟩

/-- The comparison is the actual homology map of the original inclusion. -/
def homologyIso (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (coverComplex X U).homology n ≅ (SingularSubdivision.complex X).homology n := by
  letI := inclusion_quasiIso X U hU hcover
  exact isoOfQuasiIsoAt (coverInclusion X U) n

@[simp]
theorem homologyIso_hom (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (homologyIso X U hU hcover n).hom = homologyMap (coverInclusion X U) n := rfl

variable {τ : Type w} (V : τ → Set X) (h : ∀ i, ∃ j, U i ⊆ V j)

/-- A refinement acts by the native simplicial subcomplex inclusion. -/
def refinementMap : coverComplex X U ⟶ coverComplex X V :=
  SSet.chainComplexMap
    (SSet.Subcomplex.homOfLE (coverSingular_le_of_refinement X U V h)) (ModuleCat.of ℚ ℚ)

@[reassoc]
theorem refinementMap_inclusion : refinementMap X U V h ≫ coverInclusion X V =
    coverInclusion X U := by
  let F := (SSet.chainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
  change F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  rfl

theorem refinementMap_quasiIso (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ) :
    QuasiIso (refinementMap X U V h) := by
  let := inclusion_quasiIso X V hV hcoverV
  have hcomp : QuasiIso (refinementMap X U V h ≫ coverInclusion X V) := by
    rw [refinementMap_inclusion]
    exact inclusion_quasiIso X U hU hcoverU
  exact (quasiIso_iff_comp_right (refinementMap X U V h) (coverInclusion X V)).mp hcomp

end HodgeConjecture.CoverSmallChains
