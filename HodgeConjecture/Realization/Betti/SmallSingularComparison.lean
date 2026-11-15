module

public import HodgeConjecture.Realization.Betti.CoverSmallChains
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
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SmallSingularComparison

open CategoryTheory HomologicalComplex
open SingularSubdivision SingularSubdivisionSmallness SingularSubcomplexes

/-- The inclusion of actual small singular chains is a quasi-isomorphism for a genuine two-open cover. -/
theorem inclusion_quasiIso (X : TopCat.{0}) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (smallInclusion X U V) := by
  have hW : ∀ b : Bool, IsOpen (if b then V else U) := by
    intro b; cases b <;> assumption
  have hcoverW : (⋃ b : Bool, if b then V else U) = Set.univ := by
    have h : (⋃ b : Bool, if b then V else U) = U ∪ V := by
      ext p
      simp only [Set.mem_iUnion, Bool.exists_bool, Bool.false_eq_true, ite_false,
        ite_true, Set.mem_union]
    exact h.trans hcover
  change QuasiIso (SubcomplexChainCoordinates.inclusion (smallSingular X U V))
  rw [← coverSingular_bool X U V]
  exact CoverSmallChains.inclusion_quasiIso X (fun b : Bool ↦ if b then V else U) hW hcoverW


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
