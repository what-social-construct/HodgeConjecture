module

public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-!
# Continuous affine vertex tuples inside the native standard simplex

The target is Mathlib's original topological standard simplex, viewed as a
finite probability distribution. Convex flattening realizes arbitrary
vertex tuples inside that same simplex. Continuity is proved from its
native weights embedding, by a finite coordinate sum. Reindexing gives the
original simplicial face maps, and the original vertices realize the
identity. These maps therefore apply directly on domains of actual
singular simplices, without transporting their topology.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.NativeSimplexGeometry

open Convexity

universe u v w

/-- The actual coordinate formula for flattening a finite family of native simplices. -/
theorem weights_affineMapMk {ι : Type u} {κ : Type v}
    (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) :
    (StdSimplex.affineMapMk v t).weights =
      t.weights.sum (fun i r ↦ r • (v i).weights) := by
  simp [StdSimplex.affineMapMk_apply, iConvexComb, Finsupp.sum_mapDomain_index, add_smul]

theorem weights_affineMapMk_apply {ι : Type u} {κ : Type v} [Fintype ι]
    (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) (j : κ) :
    (StdSimplex.affineMapMk v t).weights j = ∑ i, t.weights i * (v i).weights j := by
  rw [weights_affineMapMk, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    smul_eq_mul]

/-- Continuity follows from the native finite-coordinate weights embedding. -/
theorem continuous_affineMapMk {ι : Type u} {κ : Type v} [Fintype ι] [Finite κ]
    (v : ι → StdSimplex ℝ κ) : Continuous (StdSimplex.affineMapMk (R := ℝ) v) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ κ).continuous_iff]
  apply continuous_pi
  intro j
  change Continuous (fun t : StdSimplex ℝ ι ↦ (StdSimplex.affineMapMk v t).weights j)
  simp_rw [weights_affineMapMk_apply]
  fun_prop

/-- Actual continuous affine realization of a finite tuple in a native simplex. -/
def realization {ι : Type u} {κ : Type v} [Fintype ι] [Finite κ]
    (v : ι → StdSimplex ℝ κ) : C(StdSimplex ℝ ι, StdSimplex ℝ κ) where
  toFun := StdSimplex.affineMapMk (R := ℝ) v
  continuous_toFun := continuous_affineMapMk v

@[simp]
theorem realization_single {ι : Type u} {κ : Type v} [Fintype ι] [Finite κ]
    (v : ι → StdSimplex ℝ κ) (i : ι) : realization v (.single i) = v i := by
  simp [realization]

/-- The coefficient formula retains every original simplex coordinate. -/
theorem realization_weights {ι : Type u} {κ : Type v} [Fintype ι] [Finite κ]
    (v : ι → StdSimplex ℝ κ) (t : StdSimplex ℝ ι) (j : κ) :
    (realization v t).weights j = ∑ i, t.weights i * (v i).weights j :=
  weights_affineMapMk_apply v t j

/-- Reindexing vertices is precomposition by the original native simplex map. -/
theorem realization_map {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Fintype κ] [Finite τ]
    (v : κ → StdSimplex ℝ τ) (f : ι → κ) (t : StdSimplex ℝ ι) :
    realization v (StdSimplex.map f t) = realization (v ∘ f) t :=
  iConvexComb_map t f v

/-- Native vertex tuples evaluate to the identity on the native topological simplex. -/
@[simp]
theorem realization_vertices {ι : Type u} [Fintype ι] :
    realization (StdSimplex.single (R := ℝ) (X := ι)) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro t
  exact StdSimplex.iConvexComb_single t

/-- In particular deleting a vertex is the original singular face restriction. -/
theorem realization_face {κ : Type v} [Finite κ] (n : ℕ)
    (v : Fin (n + 2) → StdSimplex ℝ κ) (i : Fin (n + 2))
    (t : StdSimplex ℝ (Fin (n + 1))) :
    realization v (StdSimplex.map i.succAbove t) = realization (i.removeNth v) t :=
  realization_map v i.succAbove t

/-- Composition of actual affine realizations is realization of the composite vertex tuple. -/
theorem realization_comp {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Fintype κ] [Finite τ]
    (v : ι → StdSimplex ℝ κ) (w : κ → StdSimplex ℝ τ) (t : StdSimplex ℝ ι) :
    realization w (realization v t) = realization (fun i ↦ realization w (v i)) t :=
  (StdSimplex.affineMapMk (R := ℝ) w).isAffineMap.map_iConvexComb t v

/-- Applying a native simplex map to the target commutes with actual realization. -/
theorem realization_target_map {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Finite κ] [Finite τ]
    (v : ι → StdSimplex ℝ κ) (f : κ → τ) (t : StdSimplex ℝ ι) :
    StdSimplex.map f (realization v t) = realization (fun i ↦ StdSimplex.map f (v i)) t :=
  map_iConvexComb t v

/-- The equal-weight barycentric center of a nonempty finite tuple inside the native simplex. -/
def center {ι : Type u} {κ : Type v} [Fintype ι] [Nonempty ι] [Finite κ]
    (v : ι → StdSimplex ℝ κ) : StdSimplex ℝ κ := realization v StdSimplex.barycenter

/-- The actual native center has the expected arithmetic-mean coordinates. -/
theorem center_weights {ι : Type u} {κ : Type v} [Fintype ι] [Nonempty ι] [Finite κ]
    (v : ι → StdSimplex ℝ κ) (j : κ) :
    (center v).weights j = (Fintype.card ι : ℝ)⁻¹ * ∑ i, (v i).weights j := by
  simp only [center, realization_weights, StdSimplex.weights_barycenter_apply, Finset.mul_sum]

/-- The same center formula in the actual finite-dimensional coordinate vector space. -/
theorem center_weights_vector {ι : Type u} {κ : Type v}
    [Fintype ι] [Nonempty ι] [Finite κ] (v : ι → StdSimplex ℝ κ) :
    ((center v).weights : κ → ℝ) =
      (Fintype.card ι : ℝ)⁻¹ • ∑ i, ((v i).weights : κ → ℝ) := by
  funext j
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using center_weights v j

@[simp]
theorem center_vertices {ι : Type u} [Fintype ι] [Nonempty ι] :
    center (StdSimplex.single (R := ℝ) (X := ι)) = StdSimplex.barycenter := by
  exact congrArg (fun f : C(StdSimplex ℝ ι, StdSimplex ℝ ι) ↦ f StdSimplex.barycenter)
    realization_vertices

/-- Native simplex maps preserve the actual chosen barycentric centers. -/
theorem center_target_map {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Nonempty ι] [Finite κ] [Finite τ]
    (v : ι → StdSimplex ℝ κ) (f : κ → τ) :
    StdSimplex.map f (center v) = center (fun i ↦ StdSimplex.map f (v i)) :=
  realization_target_map v f StdSimplex.barycenter

/-- Affine realization preserves the actual chosen barycentric centers. -/
theorem center_realization {ι : Type u} {κ : Type v} {τ : Type w}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Finite τ]
    (v : ι → StdSimplex ℝ κ) (w : κ → StdSimplex ℝ τ) :
    realization w (center v) = center (fun i ↦ realization w (v i)) :=
  realization_comp v w StdSimplex.barycenter

/-- The native simplex and its actual weights-coordinate range have the same topology. -/
def coordinateHomeomorph {κ : Type v} [Finite κ] :
    StdSimplex ℝ κ ≃ₜ Set.range (fun t : StdSimplex ℝ κ ↦ (t.weights : κ → ℝ)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ κ).toHomeomorph

@[simp]
theorem coordinateHomeomorph_val {κ : Type v} [Finite κ] (t : StdSimplex ℝ κ) :
    (coordinateHomeomorph t).val = (t.weights : κ → ℝ) := rfl

/-- A genuine Lebesgue number for an open cover of the native simplex, measured in
the sup-norm distance of its original finite weights coordinates. -/
theorem lebesgue_number {κ : Type v} [Fintype κ] {ι : Type u}
    (U : ι → Set (StdSimplex ℝ κ)) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) :
    ∃ ε > 0, ∀ p : StdSimplex ℝ κ, ∃ i : ι,
      {q : StdSimplex ℝ κ | dist (q.weights : κ → ℝ) (p.weights : κ → ℝ) < ε} ⊆ U i := by
  let e := coordinateHomeomorph (κ := κ)
  let T := Set.range (fun t : StdSimplex ℝ κ ↦ (t.weights : κ → ℝ))
  let : CompactSpace T := e.compactSpace
  let W : ι → Set T := fun i ↦ e.symm ⁻¹' U i
  have hW : ∀ i, IsOpen (W i) := fun i ↦ (hU i).preimage e.symm.continuous
  have hcoverW : (Set.univ : Set T) ⊆ ⋃ i, W i := by
    intro p _
    have h : e.symm p ∈ ⋃ i, U i := by rw [hcover]; trivial
    rcases Set.mem_iUnion.mp h with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hW hcoverW
  refine ⟨ε, hε, fun p ↦ ?_⟩
  obtain ⟨i, hi⟩ := hball (e p) (Set.mem_univ _)
  refine ⟨i, fun q hq ↦ ?_⟩
  have hdist : e q ∈ Metric.ball (e p) ε := by
    change dist ((e q).val) ((e p).val) < ε
    exact hq
  have h := hi hdist
  change e.symm (e q) ∈ U i at h
  simpa only [Homeomorph.symm_apply_apply] using h

/-- The two-open form needed for small singular chains, using the actual cover topology. -/
theorem lebesgue_number_two {κ : Type v} [Fintype κ]
    (U V : Set (StdSimplex ℝ κ)) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    ∃ ε > 0, ∀ p : StdSimplex ℝ κ,
      ({q : StdSimplex ℝ κ | dist (q.weights : κ → ℝ) (p.weights : κ → ℝ) < ε} ⊆ U) ∨
      ({q : StdSimplex ℝ κ | dist (q.weights : κ → ℝ) (p.weights : κ → ℝ) < ε} ⊆ V) := by
  let W : Bool → Set (StdSimplex ℝ κ) := fun b ↦ if b then U else V
  have hW : ∀ b, IsOpen (W b) := by intro b; cases b <;> assumption
  have hcoverW : ⋃ b, W b = Set.univ := by
    ext p
    constructor
    · intro _
      trivial
    · intro _
      have h : p ∈ U ∪ V := by rw [hcover]; trivial
      rcases h with hu | hv
      · exact Set.mem_iUnion.mpr ⟨true, hu⟩
      · exact Set.mem_iUnion.mpr ⟨false, hv⟩
  obtain ⟨ε, hε, hball⟩ := lebesgue_number W hW hcoverW
  refine ⟨ε, hε, fun p ↦ ?_⟩
  obtain ⟨b, hb⟩ := hball p
  cases b
  · exact Or.inr hb
  · exact Or.inl hb

/-- A subset with sufficiently small actual coordinate diameter lies in one member of an
arbitrary indexed open cover. The bound uses the original topology and compactness. -/
theorem lebesgue_number_diam {κ : Type v} [Fintype κ] {ι : Type u}
    (U : ι → Set (StdSimplex ℝ κ)) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) :
    ∃ ε > 0, ∀ s : Set (StdSimplex ℝ κ), s.Nonempty →
      Metric.diam ((fun t : StdSimplex ℝ κ ↦ (t.weights : κ → ℝ)) '' s) < ε →
        ∃ i, s ⊆ U i := by
  obtain ⟨ε, hε, hballs⟩ := lebesgue_number U hU hcover
  refine ⟨ε, hε, fun s hs hdiam ↦ ?_⟩
  obtain ⟨p, hp⟩ := hs
  have hb : Bornology.IsBounded
      ((fun t : StdSimplex ℝ κ ↦ (t.weights : κ → ℝ)) '' s) :=
    (StdSimplex.isBounded_range_toFun_comp_weights κ).subset (by
      rintro _ ⟨q, _, rfl⟩
      exact ⟨q, rfl⟩)
  have hsub : s ⊆
      {q : StdSimplex ℝ κ | dist (q.weights : κ → ℝ) (p.weights : κ → ℝ) < ε} := by
    intro q hq
    exact lt_of_le_of_lt
      (Metric.dist_le_diam_of_mem hb ⟨q, hq, rfl⟩ ⟨p, hp, rfl⟩) hdiam
  obtain ⟨i, hi⟩ := hballs p
  exact ⟨i, hsub.trans hi⟩

/-- The existing two-open diameter bound is a specialization of the indexed-cover bound. -/
theorem lebesgue_number_two_diam {κ : Type v} [Fintype κ]
    (U V : Set (StdSimplex ℝ κ)) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    ∃ ε > 0, ∀ s : Set (StdSimplex ℝ κ), s.Nonempty →
      Metric.diam ((fun t : StdSimplex ℝ κ ↦ (t.weights : κ → ℝ)) '' s) < ε →
        s ⊆ U ∨ s ⊆ V := by
  let W : Bool → Set (StdSimplex ℝ κ) := fun b ↦ if b then V else U
  have hW : ∀ b, IsOpen (W b) := by intro b; cases b <;> assumption
  have hcoverW : ⋃ b, W b = Set.univ := by
    have h : ⋃ b, W b = U ∪ V := by
      ext p
      simp only [Set.mem_iUnion, Bool.exists_bool, W, Bool.false_eq_true, ite_false,
        ite_true, Set.mem_union]
    exact h.trans hcover
  obtain ⟨ε, hε, hs⟩ := lebesgue_number_diam W hW hcoverW
  refine ⟨ε, hε, fun s hne hd ↦ ?_⟩
  obtain ⟨b, hb⟩ := hs s hne hd
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

end HodgeConjecture.NativeSimplexGeometry
