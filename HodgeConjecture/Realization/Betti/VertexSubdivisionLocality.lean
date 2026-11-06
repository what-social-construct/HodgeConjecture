module

public import HodgeConjecture.Realization.Betti.VertexSubdivision

@[expose] public section

/-!
# Locality of the constructed subdivision and homotopy

Vertex deletion preserves any subset of vertices. Coning preserves it when
the cone vertex belongs to the subset. Consequently the explicit recursive
subdivision and its homotopy preserve supported chains whenever their
chosen centers remain in that subset. Barycentric centers in a convex
subset will provide this center condition geometrically.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.VertexSubdivision

open AffineSimplexChains

universe u v

variable {E : Type u}

/-- Finite chains all of whose occurring tuples have every vertex in the given subset. -/
def Supported (U : Set E) (m : ℕ) : Submodule ℚ (Chain E m) :=
  Finsupp.supported ℚ ℚ {v | ∀ i, v i ∈ U}

theorem supported_single (U : Set E) (m : ℕ) (v : Vertices E m) (a : ℚ)
    (hv : ∀ i, v i ∈ U) : Finsupp.single v a ∈ Supported U m :=
  Finsupp.single_mem_supported ℚ a hv

/-- To preserve finite support in a subset it suffices to check its actual tuple generators. -/
theorem supported_map_le {M : Type v} [AddCommGroup M] [Module ℚ M]
    (U : Set E) (m : ℕ) (f : Chain E m →ₗ[ℚ] M) (T : Submodule ℚ M)
    (h : ∀ v : Vertices E m, (∀ i, v i ∈ U) → f (Finsupp.single v 1) ∈ T) :
    Supported U m ≤ T.comap f := by
  rw [Supported, Finsupp.supported_eq_span_single]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

theorem boundary_mem_supported (U : Set E) (m : ℕ) (c : Chain E (m + 1))
    (hc : c ∈ Supported U (m + 1)) : boundary E m c ∈ Supported U m := by
  apply supported_map_le U (m + 1) (boundary E m) (Supported U m) ?_ hc
  intro v hv
  rw [boundary_single, one_smul, boundarySimplex]
  exact Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ _ (supported_single U m (face v i) 1 (fun j ↦ hv (i.succAbove j)))

theorem cone_mem_supported (U : Set E) (p : E) (hp : p ∈ U) (m : ℕ) (c : Chain E m)
    (hc : c ∈ Supported U m) : cone p m c ∈ Supported U (m + 1) := by
  apply supported_map_le U m (cone p m) (Supported U (m + 1)) ?_ hc
  intro v hv
  rw [cone_single]
  apply supported_single
  intro i
  cases i using Fin.cases with
  | zero => exact hp
  | succ i => exact hv i

/-- No term introduced by the actual subdivision leaves a subset preserved by its centers. -/
theorem subdivide_mem_supported (center : Centers E) (U : Set E)
    (hcenter : ∀ m (v : Vertices E (m + 1)), (∀ i, v i ∈ U) → center m v ∈ U)
    (m : ℕ) (c : Chain E m) (hc : c ∈ Supported U m) :
    subdivide center m c ∈ Supported U m := by
  induction m with
  | zero => exact hc
  | succ m ih =>
    apply supported_map_le U (m + 1) (subdivide center (m + 1)) (Supported U (m + 1)) ?_ hc
    intro v hv
    rw [subdivide_single, one_smul]
    apply cone_mem_supported U _ (hcenter m v hv) m
    apply ih
    simpa only [boundary_single, one_smul] using
      boundary_mem_supported U m (Finsupp.single v 1) (supported_single U _ v 1 hv)

/-- The constructed homotopy also stays inside the original subset, rather than merely
providing a homotopy after forgetting support. -/
theorem homotopy_mem_supported (center : Centers E) (U : Set E)
    (hcenter : ∀ m (v : Vertices E (m + 1)), (∀ i, v i ∈ U) → center m v ∈ U)
    (m : ℕ) (c : Chain E m) (hc : c ∈ Supported U m) :
    homotopy center m c ∈ Supported U (m + 1) := by
  induction m with
  | zero => exact (Supported U 1).zero_mem
  | succ m ih =>
    apply supported_map_le U (m + 1) (homotopy center (m + 1)) (Supported U (m + 2)) ?_ hc
    intro v hv
    rw [homotopy_single, one_smul]
    apply cone_mem_supported U _ (hcenter m v hv) (m + 1)
    apply Submodule.sub_mem
    · exact Submodule.sub_mem _ (supported_single U _ v 1 hv)
        (subdivide_mem_supported center U hcenter _ _ (supported_single U _ v 1 hv))
    · apply ih
      simpa only [boundary_single, one_smul] using
        boundary_mem_supported U m (Finsupp.single v 1) (supported_single U _ v 1 hv)

end HodgeConjecture.VertexSubdivision
