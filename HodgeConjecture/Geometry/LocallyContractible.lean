module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

/-!
# Contractible neighborhood bases for the existing manifold topology

The basis is transported through the original charts. No separation,
countability, or compactness hypothesis on the manifold is required.
-/

set_option autoImplicit false

noncomputable section

open Topology Filter Set

namespace HodgeConjecture

universe u v

/-- Normed real vector spaces have a basis of contractible balls. -/
theorem normedSpace_stronglyLocallyContractible
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E :=
  .of_bases (fun _ ↦ Metric.nhds_basis_ball) (fun _ _ hr ↦ Metric.contractibleSpace_ball hr)

/-- Strong local contractibility is inherited through the original manifold charts. -/
theorem chartedSpace_stronglyLocallyContractible
    (H : Type u) (M : Type v) [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] [StronglyLocallyContractibleSpace H] :
    StronglyLocallyContractibleSpace M := by
  have hb : ∀ x : M, (𝓝 x).HasBasis
      (fun s : Set H ↦ s ∈ 𝓝 (chartAt H x x) ∧ ContractibleSpace s ∧
        s ⊆ (chartAt H x).target) (fun s ↦ (chartAt H x).symm '' s) := fun x ↦ by
    rw [← (chartAt H x).symm_map_nhds_eq (mem_chart_source H x)]
    exact ((contractible_basis (chartAt H x x)).hasBasis_self_subset
      (chart_target_mem_nhds H x)).map _
  refine .of_bases hb ?_
  intro x s hs
  let : ContractibleSpace s := hs.2.1
  exact ((chartAt H x).symm.homeomorphOfImageSubsetSource hs.2.2 rfl).symm.contractibleSpace

end HodgeConjecture
