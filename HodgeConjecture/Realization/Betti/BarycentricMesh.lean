module

public import HodgeConjecture.Realization.Betti.VertexSubdivision
public import HodgeConjecture.Realization.Betti.VertexSubdivisionLocality
public import HodgeConjecture.Realization.Betti.SubdivisionGeometry
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

/-!
# Barycentric flags in the actual recursive subdivision

The recursive chain operator with the original equal-weight centers has
only tuples of nested nonempty face barycenters in its support. This is
proved from its cone and boundary recursion. The geometric flag estimate
therefore bounds the mesh of every tuple in the actual chain operator.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.BarycentricMesh

open AffineSimplexChains VertexSubdivision SubdivisionGeometry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual equal-weight center used by recursive barycentric subdivision. -/
def barycentricCenters (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] : Centers E :=
  fun _ v ↦ mean v Finset.univ

/-- A tuple is represented by a nested family of nonempty faces of the original vertices. -/
def IsFlag {ι : Type v} {m : ℕ} (v : ι → E) (w : Vertices E m) : Prop :=
  ∃ s : Fin m → Finset ι,
    (∀ i, (s i).Nonempty) ∧
    (∀ i j, s i ⊆ s j ∨ s j ⊆ s i) ∧
    ∀ i, w i = mean v (s i)

/-- Chains supported on actual nested face-barycenter tuples. -/
def flagChains {ι : Type v} (v : ι → E) (m : ℕ) : Submodule ℚ (Chain E m) :=
  Finsupp.supported ℚ ℚ {w | IsFlag v w}

theorem mean_comp_injective {ι : Type v} {κ : Type w} [DecidableEq κ]
    (v : κ → E) (f : ι → κ)
    (hf : Function.Injective f) (s : Finset ι) :
    mean (v ∘ f) s = mean v (s.image f) := by
  classical
  simp only [mean, Finset.card_image_of_injective _ hf]
  rw [Finset.sum_image]
  · rfl
  · exact fun _ _ _ _ h ↦ hf h

theorem IsFlag.embed {ι : Type v} {κ : Type w} {m : ℕ} (v : κ → E)
    (f : ι → κ) (hf : Function.Injective f) {w : Vertices E m}
    (hw : IsFlag (v ∘ f) w) : IsFlag v w := by
  classical
  obtain ⟨s, hs, hnest, hw⟩ := hw
  refine ⟨fun i ↦ (s i).image f, fun i ↦ (hs i).image f, ?_, ?_⟩
  · intro i j
    exact (hnest i j).imp Finset.image_subset_image Finset.image_subset_image
  · intro i
    rw [hw i, mean_comp_injective v f hf]

theorem IsFlag.cons {ι : Type v} [Fintype ι] [Nonempty ι] {m : ℕ} (v : ι → E)
    {w : Vertices E m} (hw : IsFlag v w) :
    IsFlag v (Fin.cons (mean v Finset.univ) w) := by
  obtain ⟨s, hs, hnest, hw⟩ := hw
  refine ⟨Fin.cons Finset.univ s, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.cases with
    | zero => exact Finset.univ_nonempty
    | succ i => exact hs i
  · intro i j
    cases i using Fin.cases with
    | zero => exact Or.inr (Finset.subset_univ _)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact Or.inl (Finset.subset_univ _)
      | succ j => exact hnest i j
  · intro i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact hw i

theorem cone_mem_flagChains {ι : Type v} [Fintype ι] [Nonempty ι]
    (v : ι → E) (m : ℕ) (c : Chain E m) (hc : c ∈ flagChains v m) :
    cone (mean v Finset.univ) m c ∈ flagChains v (m + 1) := by
  classical
  have h : flagChains v m ≤ (flagChains v (m + 1)).comap (cone (mean v Finset.univ) m) := by
    rw [flagChains, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change cone (mean v Finset.univ) m (Finsupp.single w 1) ∈ flagChains v (m + 1)
    rw [cone_single]
    exact Finsupp.single_mem_supported ℚ 1 (IsFlag.cons v hw)
  exact h hc

/-- Every nonzero tuple actually occurring in recursive subdivision is a nested
face-barycenter tuple of the original simplex. -/
theorem subdivide_single_mem_flagChains (m : ℕ) (v : Vertices E m) :
    subdivide (barycentricCenters E) m (Finsupp.single v 1) ∈ flagChains v m := by
  classical
  induction m with
  | zero =>
    rw [subdivide_zero]
    apply Finsupp.single_mem_supported ℚ 1
    exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
      fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ m ih =>
    rw [subdivide_single, one_smul]
    apply cone_mem_flagChains v m
    rw [boundarySimplex, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    have hface := ih (face v i)
    change (subdivide (barycentricCenters E) m (Finsupp.single (face v i) 1)) ∈
      Finsupp.supported ℚ ℚ {w | IsFlag (face v i) w} at hface
    change (subdivide (barycentricCenters E) m (Finsupp.single (face v i) 1)) ∈
      Finsupp.supported ℚ ℚ {w | IsFlag v w}
    rw [Finsupp.mem_supported] at hface ⊢
    intro w hw
    exact IsFlag.embed v i.succAbove Fin.succAbove_right_injective (hface hw)

/-- The actual recursive-chain support has the geometric mesh contraction, without
an assumed characterization of the subdivision terms. -/
theorem mesh_subdivide_single_le (n : ℕ) (v : Vertices E (n + 1))
    (w : Vertices E (n + 1))
    (hw : w ∈ (subdivide (barycentricCenters E) (n + 1) (Finsupp.single v 1)).support) :
    Metric.diam (Set.range (realization w)) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  have h := subdivide_single_mem_flagChains (n + 1) v
  change _ ∈ Finsupp.supported ℚ ℚ {w | IsFlag v w} at h
  have hflag := (Finsupp.mem_supported ℚ _).mp h hw
  obtain ⟨s, hs, hnest, hvertices⟩ := hflag
  have hw' : w = fun i ↦ mean v (s i) := funext hvertices
  rw [hw']
  have h := diam_range_flagRealization_le v s hs hnest
  have hc : (1 - 1 / (Fintype.card (Fin (n + 1)) : ℝ)) = (n : ℝ) / (n + 1) := by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simpa only [flagRealization, hc] using h

theorem vertex_mesh_subdivide_single_le (n : ℕ) (v : Vertices E (n + 1))
    (w : Vertices E (n + 1))
    (hw : w ∈ (subdivide (barycentricCenters E) (n + 1) (Finsupp.single v 1)).support) :
    Metric.diam (Set.range w) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  have hsubset : Set.range w ⊆ Set.range (realization w) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨.single i, realization_single w i⟩
  exact (Metric.diam_mono hsubset (isCompact_range (realization w).continuous).isBounded).trans
    (mesh_subdivide_single_le n v w hw)

/-- Finite chains with a uniform vertex-diameter bound on every occurring tuple. -/
def MeshBound (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (r : ℝ) :
    Submodule ℚ (Chain E m) := Finsupp.supported ℚ ℚ {w | Metric.diam (Set.range w) ≤ r}

/-- One actual recursive subdivision multiplies any uniform input mesh bound by `n/(n+1)`. -/
theorem subdivide_mem_meshBound (n : ℕ) (r : ℝ) (c : Chain E (n + 1))
    (hc : c ∈ MeshBound E (n + 1) r) :
    subdivide (barycentricCenters E) (n + 1) c ∈
      MeshBound E (n + 1) (((n : ℝ) / (n + 1)) * r) := by
  have h : MeshBound E (n + 1) r ≤
      (MeshBound E (n + 1) (((n : ℝ) / (n + 1)) * r)).comap
        (subdivide (barycentricCenters E) (n + 1)) := by
    rw [MeshBound, Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, hv, rfl⟩
    change subdivide (barycentricCenters E) (n + 1) (Finsupp.single v 1) ∈
      MeshBound E (n + 1) (((n : ℝ) / (n + 1)) * r)
    change _ ∈ Finsupp.supported ℚ ℚ _
    rw [Finsupp.mem_supported]
    intro w hw
    exact (vertex_mesh_subdivide_single_le n v w hw).trans
      (mul_le_mul_of_nonneg_left hv (by positivity))
  exact h hc

/-- Actual iteration of the constructed recursive barycentric chain operator. -/
def iteratedSubdivision (n k : ℕ) (c : Chain E (n + 1)) : Chain E (n + 1) :=
  ((subdivide (barycentricCenters E) (n + 1) : Chain E (n + 1) → Chain E (n + 1))^[k]) c

theorem iteratedSubdivision_mem_meshBound (n k : ℕ) (r : ℝ) (c : Chain E (n + 1))
    (hc : c ∈ MeshBound E (n + 1) r) :
    iteratedSubdivision n k c ∈
      MeshBound E (n + 1) (((n : ℝ) / (n + 1)) ^ k * r) := by
  induction k with
  | zero => simpa only [iteratedSubdivision, Function.iterate_zero_apply, pow_zero, one_mul] using hc
  | succ k ih =>
    have h := subdivide_mem_meshBound n _ _ ih
    have hfactor : ((n : ℝ) / (n + 1)) * (((n : ℝ) / (n + 1)) ^ k * r) =
        ((n : ℝ) / (n + 1)) ^ (k + 1) * r := by rw [pow_succ]; ring
    simpa only [iteratedSubdivision, Function.iterate_succ_apply', hfactor] using h

/-- A finite rational chain has a finite uniform initial mesh bound. -/
theorem exists_meshBound (m : ℕ) (c : Chain E m) :
    ∃ r : ℝ, 0 ≤ r ∧ c ∈ MeshBound E m r := by
  refine ⟨∑ w ∈ c.support, Metric.diam (Set.range w),
    Finset.sum_nonneg (fun _ _ ↦ Metric.diam_nonneg), ?_⟩
  change c ∈ Finsupp.supported ℚ ℚ _
  rw [Finsupp.mem_supported]
  intro w hw
  exact Finset.single_le_sum (fun _ _ ↦ Metric.diam_nonneg) hw

/-- Every actual finite chain becomes uniformly small after enough repetitions of the
constructed recursive subdivision. The same iteration count works for its entire support. -/
theorem exists_iteratedSubdivision_mesh_lt (n : ℕ) (c : Chain E (n + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ w ∈ (iteratedSubdivision n k c).support,
      Metric.diam (Set.range (realization w)) < ε := by
  obtain ⟨r, _, hc⟩ := exists_meshBound (n + 1) c
  obtain ⟨k, hk⟩ := exists_barycentric_power_mul_lt n r ε hε
  refine ⟨k, fun w hw ↦ ?_⟩
  have h := iteratedSubdivision_mem_meshBound n k r c hc
  change _ ∈ Finsupp.supported ℚ ℚ _ at h
  have hbound := (Finsupp.mem_supported ℚ _).mp h hw
  exact (diam_range_realization_le_vertices w).trans_lt (hbound.trans_lt hk)

/-- Equal-weight barycentric centers remain in every convex subset containing the vertices. -/
theorem barycentricCenters_mem_convex (U : Set E) (hU : Convex ℝ U) (m : ℕ)
    (v : Vertices E (m + 1)) (hv : ∀ i, v i ∈ U) : barycentricCenters E m v ∈ U := by
  have hsub : Set.range v ⊆ U := by rintro _ ⟨i, rfl⟩; exact hv i
  apply convexHull_min hsub hU
  simpa only [barycentricCenters, Finset.coe_univ, Set.image_univ] using
    mean_mem_convexHull v Finset.univ Finset.univ_nonempty

theorem subdivide_mem_supported_convex (U : Set E) (hU : Convex ℝ U) (m : ℕ)
    (c : Chain E m) (hc : c ∈ Supported U m) :
    subdivide (barycentricCenters E) m c ∈ Supported U m :=
  subdivide_mem_supported (barycentricCenters E) U (barycentricCenters_mem_convex U hU) m c hc

theorem homotopy_mem_supported_convex (U : Set E) (hU : Convex ℝ U) (m : ℕ)
    (c : Chain E m) (hc : c ∈ Supported U m) :
    homotopy (barycentricCenters E) m c ∈ Supported U (m + 1) :=
  homotopy_mem_supported (barycentricCenters E) U (barycentricCenters_mem_convex U hU) m c hc

end HodgeConjecture.BarycentricMesh
