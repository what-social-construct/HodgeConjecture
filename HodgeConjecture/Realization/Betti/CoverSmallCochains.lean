module

public import HodgeConjecture.Realization.Betti.CoverSmallChains
public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import HodgeConjecture.Realization.Betti.RelativeCochains

@[expose] public section

/-!
# Original rational cochains and arbitrary open-cover smallness

Exact rational dualization carries the constructed chain comparison to
the original simplex-function restriction. Its degreewise surjectivity
reuses extension by zero from the relative cochain layer. The original
kernel of this restriction is acyclic, including degree zero.
No finite-dimensionality assumption or new cochain model is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.CoverSmallCochains

open CategoryTheory HomologicalComplex Opposite SingularSubcomplexes
open scoped Simplicial

universe v w

variable {ι : Type v} (X : TopCat.{0}) (U : ι → Set X)

/-- The original simplex-function complex on the native indexed small subcomplex. -/
abbrev complex := SubcomplexCochains.complex (coverSingular X U).toSSet

/-- Literal restriction of the original global singular cochains. -/
def restriction : SingularCochains.complex X ⟶ complex X U :=
  RelativeCochains.restriction (coverSingular X U)

@[simp]
theorem restriction_apply (n : ℕ) (φ : SingularCochains.Cochain X n)
    (σ : (coverSingular X U).obj (op ⦋n⦌)) :
    (restriction X U).f n φ σ = φ σ.val := rfl

theorem restriction_surjective (n : ℕ) : Function.Surjective ((restriction X U).f n) :=
  RelativeCochains.restrictionLinear_surjective (coverSingular X U) n

/-- The actual restriction computes rational singular cohomology in every degree. -/
theorem restriction_quasiIso (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    QuasiIso (restriction X U) :=
  @CochainDualComparison.pullback_quasiIso _ _ (coverSingular X U).ι
    (CoverSmallChains.inclusion_quasiIso X U hU hcover)

def cohomologyIso (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    SingularCochains.Cohomology X n ≅ (complex X U).homology n := by
  letI := restriction_quasiIso X U hU hcover
  exact isoOfQuasiIsoAt (restriction X U) n

@[simp]
theorem cohomologyIso_hom (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) (n : ℕ) :
    (cohomologyIso X U hU hcover n).hom = homologyMap (restriction X U) n := rfl

/-- Cochains vanishing on cover-small simplices use the existing relative kernel complex. -/
abbrev vanishingComplex := RelativeCochains.complex (coverSingular X U)

/-- The kernel of the original surjective quasi-isomorphism is acyclic in all degrees. -/
theorem vanishingComplex_acyclic (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) : (vanishingComplex X U).Acyclic :=
  (RelativeCochains.shortComplex_shortExact (coverSingular X U)).acyclic_X₁
    (restriction_quasiIso X U hU hcover)

/-- Actual closed vanishing cochains have primitives vanishing on the same cover. -/
theorem exists_vanishing_primitive (hU : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (z : RelativeCochains.Cochain (coverSingular X U) (n + 1))
    (hz : RelativeCochains.differential (coverSingular X U) (n + 1) z = 0) :
    ∃ b : RelativeCochains.Cochain (coverSingular X U) n,
      RelativeCochains.differential (coverSingular X U) n b = z := by
  have hex := vanishingComplex_acyclic X U hU hcover (n + 1)
  rw [(vanishingComplex X U).exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)] at hex
  change (ShortComplex.mk ((RelativeCochains.complex (coverSingular X U)).d n (n + 1))
    ((RelativeCochains.complex (coverSingular X U)).d (n + 1) (n + 2)) _).Exact at hex
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hz' : (RelativeCochains.complex (coverSingular X U)).d (n + 1) (n + 2) z = 0 := by
    rw [RelativeCochains.complex_d]
    exact hz
  obtain ⟨b, hb⟩ := hex z hz'
  refine ⟨b, ?_⟩
  change (RelativeCochains.complex (coverSingular X U)).d n (n + 1) b = z at hb
  rw [RelativeCochains.complex_d] at hb
  exact hb

variable {τ : Type w} (V : τ → Set X) (h : ∀ i, ∃ j, U i ⊆ V j)

/-- Refinement restriction is the original simplicial cochain pullback. -/
def refinementRestriction : complex X V ⟶ complex X U :=
  SubcomplexCochains.restriction (coverSingular_le_of_refinement X U V h)

@[reassoc]
theorem restriction_refinement : restriction X V ≫ refinementRestriction X U V h =
    restriction X U := by
  change SubcomplexCochains.pullback _ ≫ SubcomplexCochains.pullback _ =
    SubcomplexCochains.pullback _
  rw [← SubcomplexCochains.pullback_comp]
  rfl

theorem refinementRestriction_quasiIso
    (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ) :
    QuasiIso (refinementRestriction X U V h) :=
  @CochainDualComparison.pullback_quasiIso _ _
    (SSet.Subcomplex.homOfLE (coverSingular_le_of_refinement X U V h))
      (CoverSmallChains.refinementMap_quasiIso X U V h hU hcoverU hV hcoverV)

end HodgeConjecture.CoverSmallCochains
