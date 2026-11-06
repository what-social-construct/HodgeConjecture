module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Geometry of affine simplices and barycentric subdivision

The maps here evaluate actual standard simplices in real normed spaces.
Their vertices and face restrictions are the original affine vertex data.
Equal-weight centers of nested faces satisfy the quantitative diameter
bound used by barycentric subdivision; no shrinking premise is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SubdivisionGeometry

open Convexity

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] ConvexSpace.ofModule

/-- The actual continuous affine simplex with the given finite vertex family. -/
def realization {ι : Type v} [Fintype ι] (v : ι → E) : C(StdSimplex ℝ ι, E) where
  toFun := StdSimplex.affineMapMk v
  continuous_toFun := by
    simp only [StdSimplex.coe_affineMapMk_of_fintype]
    fun_prop

@[simp]
theorem realization_single {ι : Type v} [Fintype ι] (v : ι → E) (i : ι) :
    realization v (.single i) = v i := by simp [realization]

/-- Changing the vertex indexing is exactly precomposition by the native simplex map. -/
theorem realization_map {ι κ : Type v} [Fintype ι] [Fintype κ]
    (v : κ → E) (f : ι → κ) (t : StdSimplex ℝ ι) :
    realization v (StdSimplex.map f t) = realization (v ∘ f) t := by
  exact iConvexComb_map t f v

theorem realization_mem_convexHull {ι : Type v} [Fintype ι]
    (v : ι → E) (t : StdSimplex ℝ ι) :
    realization v t ∈ convexHull ℝ (Set.range v) := by
  have h := Finset.univ.centerMass_mem_convexHull
    (R := ℝ) (z := v) (fun i _ ↦ t.weights_nonneg i)
    (by simp)
    (fun i _ ↦ Set.mem_range_self i)
  simpa [realization, StdSimplex.affineMapMk_apply_eq_sum_of_fintype,
    Finset.centerMass, t.total_of_fintype] using h

/-- Equal-weight center of a finite vertex family, defined also for the empty face. -/
def mean {ι : Type v} (v : ι → E) (s : Finset ι) : E :=
  (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i

@[simp]
theorem mean_singleton {ι : Type v} (v : ι → E) (i : ι) : mean v {i} = v i := by
  simp [mean]

theorem card_smul_mean {ι : Type v} (v : ι → E) (s : Finset ι) (hs : s.Nonempty) :
    (s.card : ℝ) • mean v s = ∑ i ∈ s, v i := by
  rw [mean, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hs.card_ne_zero), one_smul]

theorem mean_mem_convexHull {ι : Type v} (v : ι → E) (s : Finset ι) (hs : s.Nonempty) :
    mean v s ∈ convexHull ℝ (v '' (s : Set ι)) := by
  have h := s.centerMass_mem_convexHull (R := ℝ) (z := v)
    (fun _ _ ↦ zero_le_one) (by simpa using (show (0 : ℝ) < s.card by exact_mod_cast hs.card_pos))
    (fun i hi ↦ Set.mem_image_of_mem v hi)
  simpa [mean, Finset.centerMass] using h

/-- The distance from a face barycenter to any vertex of a containing face is at most
the diameter of that containing face. -/
theorem dist_mean_vertex_le_diam {ι : Type v} (v : ι → E) (s t : Finset ι)
    (hs : s.Nonempty) (hst : s ⊆ t) (i : ι) (hi : i ∈ t) :
    dist (mean v s) (v i) ≤ Metric.diam (v '' (t : Set ι)) := by
  have hb : Bornology.IsBounded (convexHull ℝ (v '' (t : Set ι))) :=
    isBounded_convexHull.mpr (t.finite_toSet.image v).isBounded
  have hmean : mean v s ∈ convexHull ℝ (v '' (t : Set ι)) :=
    convexHull_mono (Set.image_mono hst) (mean_mem_convexHull v s hs)
  have hvert : v i ∈ convexHull ℝ (v '' (t : Set ι)) :=
    subset_convexHull ℝ _ (Set.mem_image_of_mem v hi)
  simpa using Metric.dist_le_diam_of_mem hb hmean hvert

/-- The difference of two nested barycenters is an average of the displacements to
the vertices newly added to the larger face. -/
theorem mean_sub_mean {ι : Type v} [DecidableEq ι] (v : ι → E) (s t : Finset ι)
    (hs : s.Nonempty) (hst : s ⊆ t) :
    mean v s - mean v t =
      (t.card : ℝ)⁻¹ • ∑ i ∈ t \ s, (mean v s - v i) := by
  have ht : (t.card : ℝ) ≠ 0 := by exact_mod_cast (hs.mono hst).card_ne_zero
  have hz : ∑ i ∈ s, (mean v s - v i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
      card_smul_mean v s hs, sub_self]
  have hsum : ∑ i ∈ t \ s, (mean v s - v i) =
      ∑ i ∈ t, (mean v s - v i) := by
    have h := Finset.sum_sdiff hst (f := fun i ↦ mean v s - v i)
    simpa [hz] using h
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul, mean]
  rfl

/-- A nested pair of nonempty face barycenters is strictly closer than the original
diameter, with the exact cardinality factor. -/
theorem dist_mean_mean_le {ι : Type v} [DecidableEq ι] (v : ι → E) (s t : Finset ι)
    (hs : s.Nonempty) (hst : s ⊆ t) :
    dist (mean v s) (mean v t) ≤
      (1 - (s.card : ℝ) / t.card) * Metric.diam (v '' (t : Set ι)) := by
  have ht : (t.card : ℝ) ≠ 0 := by exact_mod_cast (hs.mono hst).card_ne_zero
  rw [dist_eq_norm, mean_sub_mean v s t hs hst, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ (t.card : ℝ)⁻¹ * ∑ i ∈ t \ s, ‖mean v s - v i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (t.card : ℝ)⁻¹ * ∑ _i ∈ t \ s, Metric.diam (v '' (t : Set ι)) := by
      gcongr with i hi
      simpa only [dist_eq_norm] using
        dist_mean_vertex_le_diam v s t hs hst i (Finset.mem_sdiff.mp hi).1
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff_of_subset hst,
        Nat.cast_sub (Finset.card_le_card hst)]
      field_simp

/-- The native barycenter of the standard simplex evaluates to the equal-weight
center of its original vertices. -/
theorem realization_barycenter {ι : Type v} [Fintype ι] [Nonempty ι] (v : ι → E) :
    realization v StdSimplex.barycenter = mean v Finset.univ := by
  simp only [realization, ContinuousMap.coe_mk,
    StdSimplex.affineMapMk_apply_eq_sum_of_fintype, StdSimplex.weights_barycenter_apply,
    mean, Finset.card_univ, Finset.smul_sum]

/-- A uniform diameter bound on the vertices bounds the diameter of the whole
actual affine simplex. -/
theorem diam_range_realization_le {ι : Type v} [Fintype ι] (v : ι → E) (r : ℝ)
    (hr : 0 ≤ r) (hv : ∀ i j, dist (v i) (v j) ≤ r) :
    Metric.diam (Set.range (realization v)) ≤ r := by
  refine Metric.diam_le_of_forall_dist_le hr ?_
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, h⟩ := convexHull_exists_dist_ge2
    (realization_mem_convexHull v x) (realization_mem_convexHull v y)
  exact h.trans (hv i j)

/-- Nested nonempty faces give the universal barycentric contraction factor for
an ambient finite vertex family. -/
theorem dist_mean_mean_le_uniform {ι : Type v} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] (v : ι → E) (s t : Finset ι) (hs : s.Nonempty) (hst : s ⊆ t) :
    dist (mean v s) (mean v t) ≤
      (1 - 1 / (Fintype.card ι : ℝ)) * Metric.diam (Set.range v) := by
  have ht : (0 : ℝ) < t.card := by exact_mod_cast (hs.mono hst).card_pos
  have hc : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hstcard : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have htcard : (t.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ t
  have hratio : (1 : ℝ) / Fintype.card ι ≤ (s.card : ℝ) / t.card := by
    calc
      _ ≤ 1 / (t.card : ℝ) := one_div_le_one_div_of_le ht htcard
      _ ≤ _ := div_le_div_of_nonneg_right hstcard ht.le
  have hq : 0 ≤ 1 - 1 / (Fintype.card ι : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hc)
  have hdiam : Metric.diam (v '' (t : Set ι)) ≤ Metric.diam (Set.range v) :=
    Metric.diam_mono (by rintro _ ⟨i, _, rfl⟩; exact Set.mem_range_self i)
      (Set.finite_range v).isBounded
  exact (dist_mean_mean_le v s t hs hst).trans
    (mul_le_mul (by linarith) hdiam Metric.diam_nonneg hq)

/-- The actual affine simplex whose vertices are the barycenters of a finite family
of nonempty faces. The flag condition is supplied to the diameter theorem below. -/
def flagRealization {ι κ : Type v} [Fintype κ] (v : ι → E) (s : κ → Finset ι) :
    C(StdSimplex ℝ κ, E) := realization (fun i ↦ mean v (s i))

/-- Every simplex of a nested barycentric flag has the strict mesh contraction
factor `1 - 1/m`, where `m` is the number of original vertices. -/
theorem diam_range_flagRealization_le {ι κ : Type v} [Fintype ι] [Nonempty ι]
    [DecidableEq ι] [Fintype κ] (v : ι → E) (s : κ → Finset ι)
    (hs : ∀ i, (s i).Nonempty)
    (hflag : ∀ i j, s i ⊆ s j ∨ s j ⊆ s i) :
    Metric.diam (Set.range (flagRealization v s)) ≤
      (1 - 1 / (Fintype.card ι : ℝ)) * Metric.diam (Set.range v) := by
  apply diam_range_realization_le
  · have hc : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    exact mul_nonneg (sub_nonneg.mpr ((div_le_one (by positivity)).mpr hc)) Metric.diam_nonneg
  · intro i j
    rcases hflag i j with hij | hji
    · exact dist_mean_mean_le_uniform v (s i) (s j) (hs i) hij
    · rw [dist_comm]
      exact dist_mean_mean_le_uniform v (s j) (s i) (hs j) hji

/-- The nested nonempty faces selected by an ordering of the original vertices. -/
def permutationFlag {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : Finset (Fin (n + 1)) := (Finset.Iic i).image e

theorem permutationFlag_nonempty {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) : (permutationFlag e i).Nonempty := by
  exact ⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩

theorem permutationFlag_nested {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i j : Fin (n + 1)) : permutationFlag e i ⊆ permutationFlag e j ∨
      permutationFlag e j ⊆ permutationFlag e i := by
  rcases le_total i j with hij | hji
  · exact Or.inl (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij))
  · exact Or.inr (Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hji))

/-- An actual top-dimensional barycentric subsimplex, specified by a vertex ordering. -/
def barycentricSimplex {n : ℕ} (v : Fin (n + 1) → E)
    (e : Equiv.Perm (Fin (n + 1))) : C(StdSimplex ℝ (Fin (n + 1)), E) :=
  flagRealization v (permutationFlag e)

@[simp]
theorem barycentricSimplex_single {n : ℕ} (v : Fin (n + 1) → E)
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    barycentricSimplex v e (.single i) = mean v (permutationFlag e i) :=
  realization_single _ _

/-- Every actual barycentric subsimplex contracts mesh by the usual `n/(n+1)` factor. -/
theorem diam_range_barycentricSimplex_le {n : ℕ} (v : Fin (n + 1) → E)
    (e : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (barycentricSimplex v e)) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  have h := diam_range_flagRealization_le v (permutationFlag e)
    (permutationFlag_nonempty e) (permutationFlag_nested e)
  have hc : (1 - 1 / (Fintype.card (Fin (n + 1)) : ℝ)) = (n : ℝ) / (n + 1) := by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simpa only [barycentricSimplex, hc] using h

/-- Repeated use of the proved mesh contraction can make any finite initial diameter
smaller than any positive threshold. -/
theorem exists_barycentric_power_mul_lt (n : ℕ) (d ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ((n : ℝ) / (n + 1)) ^ k * d < ε := by
  have hq0 : (0 : ℝ) ≤ (n : ℝ) / (n + 1) := by positivity
  have hq1 : (n : ℝ) / (n + 1) < 1 := by
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const d
  have hevent : ∀ᶠ k in Filter.atTop, ((n : ℝ) / (n + 1)) ^ k * d < ε := by
    exact (show Filter.Tendsto _ _ (nhds (0 * d)) from hlim).eventually
      (eventually_lt_nhds (by simpa using hε))
  exact hevent.exists

/-- The vertices of one actual barycentric subsimplex. -/
def subdividedVertices {n : ℕ} (v : Fin (n + 1) → E)
    (e : Equiv.Perm (Fin (n + 1))) : Fin (n + 1) → E :=
  fun i ↦ mean v (permutationFlag e i)

theorem diam_range_subdividedVertices_le {n : ℕ} (v : Fin (n + 1) → E)
    (e : Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (subdividedVertices v e)) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (Set.range v) := by
  have hc : (1 - 1 / (Fintype.card (Fin (n + 1)) : ℝ)) = (n : ℝ) / (n + 1) := by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rcases permutationFlag_nested e i j with hij | hji
  · simpa only [subdividedVertices, hc] using
      dist_mean_mean_le_uniform v _ _ (permutationFlag_nonempty e i) hij
  · rw [dist_comm]
    simpa only [subdividedVertices, hc] using
      dist_mean_mean_le_uniform v _ _ (permutationFlag_nonempty e j) hji

/-- Successively choose an actual barycentric subsimplex at each stage. -/
def iteratedVertices {n : ℕ} (v : Fin (n + 1) → E) :
    List (Equiv.Perm (Fin (n + 1))) → (Fin (n + 1) → E)
  | [] => v
  | e :: es => iteratedVertices (subdividedVertices v e) es

/-- The actual diameter of every iterated barycentric cell has the geometric mesh bound. -/
theorem diam_range_iteratedVertices_le {n : ℕ} (v : Fin (n + 1) → E)
    (es : List (Equiv.Perm (Fin (n + 1)))) :
    Metric.diam (Set.range (iteratedVertices v es)) ≤
      ((n : ℝ) / (n + 1)) ^ es.length * Metric.diam (Set.range v) := by
  induction es generalizing v with
  | nil => simp [iteratedVertices]
  | cons e es ih =>
    calc
      _ ≤ ((n : ℝ) / (n + 1)) ^ es.length *
          Metric.diam (Set.range (subdividedVertices v e)) := ih _
      _ ≤ ((n : ℝ) / (n + 1)) ^ es.length *
          (((n : ℝ) / (n + 1)) * Metric.diam (Set.range v)) :=
        mul_le_mul_of_nonneg_left (diam_range_subdividedVertices_le v e) (by positivity)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

theorem diam_range_realization_le_vertices {ι : Type v} [Fintype ι] (v : ι → E) :
    Metric.diam (Set.range (realization v)) ≤ Metric.diam (Set.range v) := by
  apply diam_range_realization_le _ _ Metric.diam_nonneg
  intro i j
  exact Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
    (Set.mem_range_self i) (Set.mem_range_self j)

/-- Uniform shrinking of actual iterated affine barycentric cells: the same number
of subdivisions works for every sequence of vertex orderings. -/
theorem exists_iterated_mesh_lt {n : ℕ} (v : Fin (n + 1) → E) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ es : List (Equiv.Perm (Fin (n + 1))), es.length = k →
      Metric.diam (Set.range (realization (iteratedVertices v es))) < ε := by
  obtain ⟨k, hk⟩ := exists_barycentric_power_mul_lt n (Metric.diam (Set.range v)) ε hε
  refine ⟨k, fun es hes ↦ ?_⟩
  exact (diam_range_realization_le_vertices _).trans_lt
    ((diam_range_iteratedVertices_le v es).trans_lt (by simpa only [hes] using hk))


end HodgeConjecture.SubdivisionGeometry
