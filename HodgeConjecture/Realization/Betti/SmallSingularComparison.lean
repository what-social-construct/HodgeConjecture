module

public import HodgeConjecture.Realization.Betti.ChainHomologyClasses
public import HodgeConjecture.Realization.Betti.SmallSingularSubdivisionHomotopy

@[expose] public section

/-!
# Actual small-chain comparison for a two-open cover

Barycentric subdivision eventually places each finite singular chain into
the actual small singular subcomplex. Its constructed homotopy preserves
that subcomplex. These facts prove that the original native inclusion
induces an isomorphism in every degree of rational singular homology.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SmallSingularComparison

open CategoryTheory HomologicalComplex
open SingularSubdivision SingularSubdivisionSmallness SingularSubcomplexes

/-- The inclusion of actual small singular chains is a quasi-isomorphism for a genuine two-open cover. -/
theorem inclusion_quasiIso (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (smallInclusion X U V) := by
  apply ChainHomologyClasses.quasiIso_of_eventual_image (smallInclusion X U V)
    (fun n ↦ SubcomplexChainCoordinates.inclusion_injective (smallSingular X U V) n)
    (smallSubdivisionPower X U V) (subdivisionPower X)
    (homologyMap_smallSubdivision_pow X U V) (homologyMap_subdivision_pow X)
    (fun k ↦ (smallSubdivisionPower_inclusion X U V k).symm)
  intro n c
  obtain ⟨k, hk⟩ := exists_iteration_small X U V hU hV hcover n c
  rw [smallChains_eq_chainSubmodule, ← SubcomplexChainCoordinates.range_inclusion] at hk
  obtain ⟨a, ha⟩ := hk
  exact ⟨k, a, ha.trans (subdivisionPower_apply X k n c).symm⟩

/-- The original native homology map of the inclusion is an isomorphism in every degree. -/
theorem isIso_homologyMap_inclusion (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (homologyMap (smallInclusion X U V) n) := by
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
    ((inclusion_quasiIso X U V hU hV hcover).quasiIsoAt n)

/-- A comparison fixed by the actual small-chain inclusion, with no comparison premise supplied. -/
def homologyIso (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (smallComplex X U V).homology n ≅ (complex X).homology n := by
  letI := inclusion_quasiIso X U V hU hV hcover
  exact isoOfQuasiIsoAt (smallInclusion X U V) n

@[simp]
theorem homologyIso_hom (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (homologyIso X U V hU hV hcover n).hom = homologyMap (smallInclusion X U V) n := rfl

end HodgeConjecture.SmallSingularComparison
