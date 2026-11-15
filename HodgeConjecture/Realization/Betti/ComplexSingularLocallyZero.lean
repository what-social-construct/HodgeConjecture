module

public import HodgeConjecture.Realization.Betti.ComplexCoverSmallCochains
public import HodgeConjecture.Realization.Betti.ComplexSingularOpenExtension
public import HodgeConjecture.Realization.Betti.SingularLocallyZero
public import HodgeConjecture.SheafCohomology.SheafifyKernel

@[expose] public noncomputable section

/-!
# Locally zero unrestricted complex-valued singular cochains

The actual sheafification unit kills exactly cochains whose original
open-subspace pullback vanishes near every point. Such a cochain vanishes
on the small simplices of one actual point-indexed cover. The complex
small-cover quasi-isomorphism will supply primitives retaining that
same local vanishing condition.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

namespace HodgeConjecture.SingularCoefficientChange

open CategoryTheory CategoryTheory.Limits HomologicalComplex TopologicalSpace Opposite Simplicial
open SingularSubcomplexes

variable (X : TopCat.{0})

/-- Actual local vanishing of the original unrestricted complex simplex functional. -/
def LocallyZero (n : ℕ) (φ : (complexCochains X).X n) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ (pullback (Opens.inclusion' U)).f n φ = 0

@[simp]
theorem globalCochainsToSheaf_apply (n : ℕ) (φ : (complexCochains X).X n) :
    (globalCochainsToSheaf X).f n φ =
      (toSheafify (Opens.grothendieckTopology X) (presheaf X n)).app (op ⊤)
        ((pullback (Opens.inclusion' (⊤ : Opens X))).f n φ) := rfl

theorem restrict_top_cochain (U : Opens X) (n : ℕ) (φ : (complexCochains X).X n) :
    (presheaf X n).map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((pullback (Opens.inclusion' (⊤ : Opens X))).f n φ) =
        (pullback (Opens.inclusion' U)).f n φ := by
  apply (complexCoordinates ((Opens.toTopCat X).obj U) n).injective
  funext σ
  change complexCoordinates ((Opens.toTopCat X).obj U) n
      ((pullback ((Opens.toTopCat X).map (homOfLE (show U ≤ ⊤ from le_top)))).f n
        ((pullback (Opens.inclusion' (⊤ : Opens X))).f n φ)) σ = _
  rw [pullback_coordinates, pullback_coordinates, pullback_coordinates]
  congr 1

/-- The native global unit's actual kernel is the locally zero complex cochains. -/
theorem globalCochainsToSheaf_eq_zero_iff (n : ℕ) (φ : (complexCochains X).X n) :
    (globalCochainsToSheaf X).f n φ = 0 ↔ LocallyZero X n φ := by
  rw [globalCochainsToSheaf_apply, SheafCohomology.toSheafify_app_eq_zero_iff]
  constructor
  · intro h x
    obtain ⟨U, hU, hx, hφ⟩ := h x trivial
    exact ⟨U, hx, (restrict_top_cochain X U n φ) ▸ hφ⟩
  · intro h x _
    obtain ⟨U, hx, hφ⟩ := h x
    exact ⟨U, le_top, hx, (restrict_top_cochain X U n φ).trans hφ⟩

/-- Vanishing after original open pullback is pointwise vanishing on each contained simplex. -/
theorem restrict_open_eq_zero_iff (U : Opens X) (n : ℕ)
    (φ : (complexCochains X).X n) :
    (pullback (Opens.inclusion' U)).f n φ = 0 ↔
      ∀ σ : (subsetSingular X U).obj (op ⦋n⦌), complexCoordinates X n φ σ.val = 0 := by
  constructor
  · intro h σ
    have he := congrArg (fun z ↦ complexCoordinates ((Opens.toTopCat X).obj U) n z
      ((subsetToSubtype X U).app (op ⦋n⦌) σ)) h
    rw [pullback_coordinates] at he
    change complexCoordinates X n φ σ.val =
      complexCoordinates ((Opens.toTopCat X).obj U) n (0 : (complexCochains _).X n)
        ((subsetToSubtype X U).app (op ⦋n⦌) σ) at he
    simpa only [map_zero, Pi.zero_apply] using he
  · intro h
    apply (complexCoordinates ((Opens.toTopCat X).obj U) n).injective
    funext σ
    rw [pullback_coordinates]
    have hσ : ((TopCat.toSSet.map (Opens.inclusion' U)).app (op ⦋n⦌) σ) ∈
        (subsetSingular X U).obj (op ⦋n⦌) := by
      intro t
      exact (simplexMap ((Opens.toTopCat X).obj U) (op ⦋n⦌) σ t).property
    simpa only [map_zero, Pi.zero_apply] using
      h ⟨(TopCat.toSSet.map (Opens.inclusion' U)).app (op ⦋n⦌) σ, hσ⟩

/-- An actual small-cover vanishing cochain vanishes on an open neighborhood of each point. -/
theorem locallyZero_of_cover {ι : Type*} (U : ι → Opens X)
    (hcover : ⋃ i, (U i : Set X) = Set.univ) (n : ℕ)
    (φ : (complexCochains X).X n)
    (hφ : (ComplexCoverSmallCochains.restriction X (fun i ↦ (U i : Set X))).f n φ = 0) :
    LocallyZero X n φ := by
  intro x
  have hx : x ∈ ⋃ i, (U i : Set X) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hsmall := (ComplexCoverSmallCochains.restriction_eq_zero_iff X
    (fun i ↦ (U i : Set X)) n φ).mp hφ
  have hUi : (pullback (Opens.inclusion' (U i))).f n φ = 0 := by
    apply (restrict_open_eq_zero_iff X (U i) n φ).mpr
    intro σ
    exact hsmall ⟨σ.val, (mem_coverSingular X _ _ σ.val).mpr ⟨i, σ.property⟩⟩
  exact ⟨U i, hi, hUi⟩

/-- Local witnesses form one actual point-indexed cover on which the cochain vanishes. -/
theorem exists_point_cover_of_locallyZero (n : ℕ)
    (φ : (complexCochains X).X n) (hφ : LocallyZero X n φ) :
    ∃ U : X → Opens X, (∀ x, x ∈ U x) ∧
      (ComplexCoverSmallCochains.restriction X (fun x ↦ (U x : Set X))).f n φ = 0 := by
  classical
  choose U hx hU using hφ
  refine ⟨U, hx, (ComplexCoverSmallCochains.restriction_eq_zero_iff X
    (fun x ↦ (U x : Set X)) n φ).mpr ?_⟩
  intro σ
  obtain ⟨x, hxσ⟩ := (mem_coverSingular X _ _ σ.val).mp σ.property
  exact (restrict_open_eq_zero_iff X (U x) n φ).mp (hU x) ⟨σ.val, hxσ⟩

/-- A complex zero-cochain vanishing near every point is zero on every zero-simplex. -/
theorem LocallyZero.eq_zero {φ : (complexCochains X).X 0}
    (hφ : LocallyZero X 0 φ) : φ = 0 := by
  obtain ⟨U, hx, hU⟩ := exists_point_cover_of_locallyZero X 0 φ hφ
  apply (complexCoordinates X 0).injective
  funext σ
  have hcover := SingularCochains.point_cover_eq_univ X U hx
  have hσ := (ComplexCoverSmallCochains.restriction_eq_zero_iff X
    (fun x ↦ (U x : Set X)) 0 φ).mp hU
      ⟨σ, zeroSimplex_mem_coverSingular X _ hcover σ⟩
  simpa only [map_zero, Pi.zero_apply] using hσ

/-- Original complex singular differential preserves local vanishing. -/
theorem LocallyZero.differential {n : ℕ} {φ : (complexCochains X).X n}
    (hφ : LocallyZero X n φ) :
    LocallyZero X (n + 1) ((complexCochains X).d n (n + 1) φ) := by
  intro x
  obtain ⟨U, hx, hU⟩ := hφ x
  refine ⟨U, hx, ?_⟩
  have hcomm := congrArg (fun f ↦ f φ) ((pullback (Opens.inclusion' U)).comm n (n + 1))
  change (complexCochains ((Opens.toTopCat X).obj U)).d n (n + 1)
    ((pullback (Opens.inclusion' U)).f n φ) =
      (pullback (Opens.inclusion' U)).f (n + 1)
        ((complexCochains X).d n (n + 1) φ) at hcomm
  rw [hU, map_zero] at hcomm
  exact hcomm.symm

/-- A closed locally zero complex cochain has a primitive that remains locally zero. -/
theorem exists_locallyZero_primitive (n : ℕ)
    (φ : (complexCochains X).X (n + 1))
    (hφ : LocallyZero X (n + 1) φ)
    (hclosed : (complexCochains X).d (n + 1) (n + 2) φ = 0) :
    ∃ b : (complexCochains X).X n,
      LocallyZero X n b ∧ (complexCochains X).d n (n + 1) b = φ := by
  obtain ⟨U, hx, hU⟩ := exists_point_cover_of_locallyZero X (n + 1) φ hφ
  let C := ComplexCoverSmallCochains.restriction X (fun x ↦ (U x : Set X))
  let K := kernel C
  obtain ⟨z, hz⟩ := SheafCohomology.ComplexKernel.exists_preimage C (n + 1) φ hU
  have hzclosed : K.d (n + 1) (n + 2) z = 0 := by
    apply SheafCohomology.ComplexKernel.inclusion_injective C (n + 2)
    rw [SheafCohomology.ComplexKernel.inclusion_d, hz, hclosed, map_zero]
  have hcover := SingularCochains.point_cover_eq_univ X U hx
  have hacyclic : K.Acyclic :=
    ComplexCoverSmallCochains.vanishingComplex_acyclic X (fun x ↦ (U x : Set X))
      (fun x ↦ (U x).isOpen) hcover
  have hex := hacyclic (n + 1)
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp)] at hex
  change (ShortComplex.mk (K.d n (n + 1)) (K.d (n + 1) (n + 2)) _).Exact at hex
  rw [ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨a, ha⟩ := hex z hzclosed
  refine ⟨(kernel.ι C).f n a, ?_, ?_⟩
  · exact locallyZero_of_cover X U hcover n _
      (SheafCohomology.ComplexKernel.map_inclusion_eq_zero C n a)
  · rw [← SheafCohomology.ComplexKernel.inclusion_d, ha, hz]

end HodgeConjecture.SingularCoefficientChange
