module

public import HodgeConjecture.Realization.Betti.SingularPresheaf
public import HodgeConjecture.Realization.Betti.CoverSmallCochains
public import HodgeConjecture.SheafCohomology.SheafifyKernel

@[expose] public section

/-!
# Locally zero original singular cochains

Local vanishing is a predicate on the original cochains. The actual
global sheafification map kills exactly these cochains. Equivalently,
they lie in one of the existing relative kernels for an open cover.
The proved cover comparison supplies primitives retaining local vanishing.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory TopologicalSpace Opposite SingularSubcomplexes
open scoped Simplicial

variable (X : TopCat.{0})

/-- Local vanishing of the original cochain under the original open inclusions. -/
def LocallyZero (n : ℕ) (φ : Cochain X n) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ (pullback (Opens.inclusion' U)).f n φ = 0

/-- The kernel criterion applies to the existing global cochain map itself. -/
theorem globalCochainsToSheaf_eq_zero_iff (n : ℕ) (φ : Cochain X n) :
    (globalCochainsToSheaf X).f n φ = 0 ↔ LocallyZero X n φ := by
  rw [globalCochainsToSheaf_apply, SheafCohomology.toSheafify_app_eq_zero_iff]
  constructor
  · intro h x
    obtain ⟨U, hU, hx, hφ⟩ := h x trivial
    exact ⟨U, hx, (restrict_top_cochain X U n φ) ▸ hφ⟩
  · intro h x _
    obtain ⟨U, hx, hφ⟩ := h x
    exact ⟨U, le_top, hx, (restrict_top_cochain X U n φ).trans hφ⟩

/-- The original open pullback and native subset restriction have the same kernel. -/
theorem restrict_open_eq_zero_iff_subset (U : Opens X) (n : ℕ) (φ : Cochain X n) :
    (pullback (Opens.inclusion' U)).f n φ = 0 ↔
      RelativeCochains.restrictionLinear (subsetSingular X U) n φ = 0 := by
  constructor
  · intro h
    funext σ
    exact congrFun h ((subsetToSubtype X U).app (op ⦋n⦌) σ)
  · intro h
    funext σ
    exact congrFun h ((subtypeToSubset X U).app (op ⦋n⦌) σ)

theorem point_cover_eq_univ (U : X → Opens X) (hx : ∀ x, x ∈ U x) :
    ⋃ x, (U x : Set X) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr ⟨x, hx x⟩

/-- A cochain vanishing on all small simplices is zero on a neighborhood of each point. -/
theorem locallyZero_of_cover {ι : Type*} (U : ι → Opens X)
    (hcover : ⋃ i, (U i : Set X) = Set.univ) (n : ℕ) (φ : Cochain X n)
    (hφ : (CoverSmallCochains.restriction X (fun i ↦ (U i : Set X))).f n φ = 0) :
    LocallyZero X n φ := by
  intro x
  have hx : x ∈ ⋃ i, (U i : Set X) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  refine ⟨U i, hi, (restrict_open_eq_zero_iff_subset X (U i) n φ).mpr ?_⟩
  funext σ
  exact congrFun hφ ⟨σ.val, (mem_coverSingular X _ _ σ.val).mpr ⟨i, σ.property⟩⟩

/-- Original local witnesses give an actual open cover with a vanishing restriction. -/
theorem exists_point_cover_of_locallyZero (n : ℕ) (φ : Cochain X n) (hφ : LocallyZero X n φ) :
    ∃ U : X → Opens X, (∀ x, x ∈ U x) ∧
      (CoverSmallCochains.restriction X (fun x ↦ (U x : Set X))).f n φ = 0 := by
  classical
  choose U hx hU using hφ
  refine ⟨U, hx, ?_⟩
  funext σ
  obtain ⟨x, hxσ⟩ := (mem_coverSingular X _ _ σ.val).mp σ.property
  have h := (restrict_open_eq_zero_iff_subset X (U x) n φ).mp (hU x)
  exact congrFun h ⟨σ.val, hxσ⟩

theorem globalCochainsToSheaf_eq_zero_iff_cover (n : ℕ) (φ : Cochain X n) :
    (globalCochainsToSheaf X).f n φ = 0 ↔
      ∃ U : X → Opens X, (∀ x, x ∈ U x) ∧
        (CoverSmallCochains.restriction X (fun x ↦ (U x : Set X))).f n φ = 0 := by
  rw [globalCochainsToSheaf_eq_zero_iff]
  constructor
  · exact exists_point_cover_of_locallyZero X n φ
  · rintro ⟨U, hx, hU⟩
    exact locallyZero_of_cover X U (point_cover_eq_univ X U hx) n φ hU

/-- The actual linear kernel is the join of the existing cover restriction kernels. -/
theorem globalCochainsToSheaf_ker_eq_iSup (n : ℕ) :
    LinearMap.ker ((globalCochainsToSheaf X).f n).hom =
      ⨆ (U : X → Opens X) (_hx : ∀ x, x ∈ U x),
        LinearMap.ker ((CoverSmallCochains.restriction X (fun x ↦ (U x : Set X))).f n).hom := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨U, hx, hU⟩ := (globalCochainsToSheaf_eq_zero_iff_cover X n φ).mp hφ
    apply Submodule.mem_iSup_of_mem U
    exact Submodule.mem_iSup_of_mem hx hU
  · refine iSup_le fun U ↦ iSup_le fun hx ↦ ?_
    intro φ hφ
    apply (globalCochainsToSheaf_eq_zero_iff X n φ).mpr
    exact locallyZero_of_cover X U (point_cover_eq_univ X U hx) n φ hφ

/-- Local vanishing is preserved by the original singular differential. -/
theorem LocallyZero.differential {n : ℕ} {φ : Cochain X n} (hφ : LocallyZero X n φ) :
    LocallyZero X (n + 1) (differential X n φ) := by
  intro x
  obtain ⟨U, hx, hU⟩ := hφ x
  refine ⟨U, hx, ?_⟩
  rw [← differential_pullback, hU, map_zero]

/-- A locally zero zero-cochain is zero on every original zero-simplex. -/
theorem LocallyZero.eq_zero {φ : Cochain X 0} (hφ : LocallyZero X 0 φ) : φ = 0 := by
  obtain ⟨U, hx, hU⟩ := exists_point_cover_of_locallyZero X 0 φ hφ
  funext σ
  exact congrFun hU ⟨σ, zeroSimplex_mem_coverSingular X _ (point_cover_eq_univ X U hx) σ⟩

/-- Every closed locally zero positive cochain has an actual locally zero primitive. -/
theorem exists_locallyZero_primitive (n : ℕ) (φ : Cochain X (n + 1))
    (hφ : LocallyZero X (n + 1) φ) (hclosed : differential X (n + 1) φ = 0) :
    ∃ b : Cochain X n, LocallyZero X n b ∧ differential X n b = φ := by
  obtain ⟨U, hx, hU⟩ := exists_point_cover_of_locallyZero X (n + 1) φ hφ
  let z : RelativeCochains.Cochain (coverSingular X (fun x ↦ (U x : Set X))) (n + 1) := ⟨φ, hU⟩
  obtain ⟨b, hb⟩ := CoverSmallCochains.exists_vanishing_primitive X
    (fun x ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (point_cover_eq_univ X U hx) n z
      (Subtype.ext hclosed)
  exact ⟨b.val, locallyZero_of_cover X U (point_cover_eq_univ X U hx) n b.val b.property,
    congrArg Subtype.val hb⟩

end HodgeConjecture.SingularCochains
