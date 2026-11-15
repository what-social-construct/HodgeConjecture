module

public import HodgeConjecture.Realization.Betti.SingularLocallyZero
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section

/-!
# Patching the original singular cochains

Extension reuses the existing relative extension by zero. Locally finite
closed covers allow locally agreeing original cochains to be patched,
by choosing a representative at an actual point of each original simplex.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.SingularCochains

open CategoryTheory TopologicalSpace Opposite SingularSubcomplexes
open scoped Topology Simplicial

variable (X : TopCat.{0})

/-- The original relative extension by zero, applied to an open subspace. -/
def openExtension (U : Opens X) (n : ℕ)
    (φ : Cochain ((Opens.toTopCat X).obj U) n) : Cochain X n :=
  RelativeCochains.extension (subsetSingular X U) n
    (fun σ ↦ φ ((subsetToSubtype X U).app (op ⦋n⦌) σ))

theorem pullback_openExtension (U : Opens X) (n : ℕ)
    (φ : Cochain ((Opens.toTopCat X).obj U) n) :
    (pullback (Opens.inclusion' U)).f n (openExtension X U n φ) = φ := by
  funext σ
  change RelativeCochains.restrictionLinear (subsetSingular X U) n
    (openExtension X U n φ) ((subtypeToSubset X U).app (op ⦋n⦌) σ) = _
  rw [openExtension, RelativeCochains.restriction_extension]
  rfl

/-- A genuine open cover has a locally finite closed refinement on these spaces. -/
theorem exists_locallyFinite_closed_refinement [ParacompactSpace X] [T2Space X]
    {ι : Type*} (U : ι → Opens X) (hcover : ⋃ i, (U i : Set X) = Set.univ) :
    ∃ C : ι → Set X, (∀ i, IsClosed (C i)) ∧ LocallyFinite C ∧
      (∀ x : X, ∃ i, x ∈ C i) ∧ (∀ i, C i ⊆ U i) := by
  obtain ⟨V, hVo, hVc, hVf, hVU⟩ := precise_refinement (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).isOpen) hcover
  obtain ⟨C, hCc, hCclosed, hCV⟩ := exists_iUnion_eq_closed_subset hVo hVf.point_finite hVc
  refine ⟨C, hCclosed, hVf.subset hCV, ?_, fun i ↦ (hCV i).trans (hVU i)⟩
  intro x
  have hx : x ∈ ⋃ i, C i := by rw [hCc]; trivial
  exact Set.mem_iUnion.mp hx

/-- Local agreement along a locally finite closed cover produces one actual cochain. -/
theorem exists_cochain_locally_eq_of_closed_cover {ι : Type*} (C : ι → Set X)
    (hclosed : ∀ i, IsClosed (C i)) (hfinite : LocallyFinite C)
    (hcover : ∀ x : X, ∃ i, x ∈ C i) (n : ℕ) (φ : ι → Cochain X n)
    (hcompat : ∀ (x : X) (i j : ι), x ∈ C i → x ∈ C j →
      ∃ V : Opens X, x ∈ V ∧
        (pullback (Opens.inclusion' V)).f n (φ i) =
          (pullback (Opens.inclusion' V)).f n (φ j)) :
    ∃ ψ : Cochain X n, ∀ (x : X) (i : ι), x ∈ C i →
      ∃ V : Opens X, x ∈ V ∧
        (pullback (Opens.inclusion' V)).f n ψ =
          (pullback (Opens.inclusion' V)).f n (φ i) := by
  classical
  let base : SimplexCategory.toTop.{0}.obj (unop (op ⦋n⦌)) := Classical.choice inferInstance
  let select (σ : Simplex X n) : ι :=
    (hcover (simplexMap X (op ⦋n⦌) σ base)).choose
  let ψ : Cochain X n := fun σ ↦ φ (select σ) σ
  refine ⟨ψ, ?_⟩
  intro x i hxi
  let I := {j : ι // x ∈ C j}
  let : Fintype I := (hfinite.point_finite x).fintype
  have hc (j : I) := hcompat x j.val i j.property hxi
  choose V hxV hV using hc
  have hN : (⋂ j : I, (V j : Set X)) ∈ 𝓝 x :=
    Filter.iInter_mem.mpr (fun j ↦ (V j).isOpen.mem_nhds (hxV j))
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp
    (Filter.inter_mem hN (hfinite.iInter_compl_mem_nhds hclosed x))
  refine ⟨⟨W, hWo⟩, hxW, ?_⟩
  funext σ
  let τ : Simplex X n := (TopCat.toSSet.map (Opens.inclusion' ⟨W, hWo⟩)).app (op ⦋n⦌) σ
  have hτ (t) : simplexMap X (op ⦋n⦌) τ t ∈ W :=
    (simplexMap ((Opens.toTopCat X).obj ⟨W, hWo⟩) (op ⦋n⦌) σ t).property
  have hjx : x ∈ C (select τ) := by
    by_contra h
    have hn := Set.mem_iInter₂.mp (hWsub (hτ base)).2 (select τ) h
    exact hn (hcover (simplexMap X (op ⦋n⦌) τ base)).choose_spec
  have hτV : τ ∈ (subsetSingular X (V ⟨select τ, hjx⟩)).obj (op ⦋n⦌) :=
    fun t ↦ Set.mem_iInter.mp (hWsub (hτ t)).1 ⟨select τ, hjx⟩
  have he := congrFun (hV ⟨select τ, hjx⟩)
    ((subsetToSubtype X (V ⟨select τ, hjx⟩)).app (op ⦋n⦌) ⟨τ, hτV⟩)
  change φ (select τ) τ = φ i τ
  exact he

end HodgeConjecture.SingularCochains
