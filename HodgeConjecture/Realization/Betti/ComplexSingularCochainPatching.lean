module

public import HodgeConjecture.Realization.Betti.ComplexSingularLocallyZero
public import HodgeConjecture.Realization.Betti.SingularCochainPatching

@[expose] public noncomputable section

/-!
# Patching unrestricted complex singular cochains

We select a local representative using a point on each simplex. A locally
finite closed refinement ensures that all such choices agree on a smaller
neighborhood of each point.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace HodgeConjecture.SingularCoefficientChange

open CategoryTheory TopologicalSpace Opposite SingularSubcomplexes Simplicial
open scoped Topology

variable (X : TopCat.{0})

/-- Local agreement along a locally finite closed cover produces an actual complex cochain. -/
theorem exists_cochain_locally_eq_of_closed_cover {ι : Type*} (C : ι → Set X)
    (hclosed : ∀ i, IsClosed (C i)) (hfinite : LocallyFinite C)
    (hcover : ∀ x : X, ∃ i, x ∈ C i) (n : ℕ)
    (φ : ι → (complexCochains X).X n)
    (hcompat : ∀ (x : X) (i j : ι), x ∈ C i → x ∈ C j →
      ∃ V : Opens X, x ∈ V ∧
        (pullback (Opens.inclusion' V)).f n (φ i) =
          (pullback (Opens.inclusion' V)).f n (φ j)) :
    ∃ ψ : (complexCochains X).X n, ∀ (x : X) (i : ι), x ∈ C i →
      ∃ V : Opens X, x ∈ V ∧
        (pullback (Opens.inclusion' V)).f n ψ =
          (pullback (Opens.inclusion' V)).f n (φ i) := by
  classical
  let base : SimplexCategory.toTop.{0}.obj (unop (op ⦋n⦌)) := Classical.choice inferInstance
  let select (σ : SingularCochains.Simplex X n) : ι :=
    (hcover (simplexMap X (op ⦋n⦌) σ base)).choose
  let ψ : (complexCochains X).X n :=
    (complexCoordinates X n).symm (fun σ ↦ complexCoordinates X n (φ (select σ)) σ)
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
  apply (complexCoordinates ((Opens.toTopCat X).obj ⟨W, hWo⟩) n).injective
  funext σ
  rw [pullback_coordinates, pullback_coordinates]
  let τ : SingularCochains.Simplex X n :=
    (TopCat.toSSet.map (Opens.inclusion' ⟨W, hWo⟩)).app (op ⦋n⦌) σ
  have hτ (t) : simplexMap X (op ⦋n⦌) τ t ∈ W :=
    (simplexMap ((Opens.toTopCat X).obj ⟨W, hWo⟩) (op ⦋n⦌) σ t).property
  have hjx : x ∈ C (select τ) := by
    by_contra h
    have hn := Set.mem_iInter₂.mp (hWsub (hτ base)).2 (select τ) h
    exact hn (hcover (simplexMap X (op ⦋n⦌) τ base)).choose_spec
  have hτV : τ ∈ (subsetSingular X (V ⟨select τ, hjx⟩)).obj (op ⦋n⦌) :=
    fun t ↦ Set.mem_iInter.mp (hWsub (hτ t)).1 ⟨select τ, hjx⟩
  have he := congrArg
    (fun z ↦ complexCoordinates ((Opens.toTopCat X).obj (V ⟨select τ, hjx⟩)) n z
      ((subsetToSubtype X (V ⟨select τ, hjx⟩)).app (op ⦋n⦌) ⟨τ, hτV⟩))
    (hV ⟨select τ, hjx⟩)
  rw [pullback_coordinates, pullback_coordinates] at he
  change complexCoordinates X n (φ (select τ)) τ =
    complexCoordinates X n (φ i) τ at he
  change complexCoordinates X n
    ((complexCoordinates X n).symm (fun σ ↦ complexCoordinates X n (φ (select σ)) σ)) τ =
      complexCoordinates X n (φ i) τ
  rw [(complexCoordinates X n).apply_symm_apply]
  exact he

end HodgeConjecture.SingularCoefficientChange
