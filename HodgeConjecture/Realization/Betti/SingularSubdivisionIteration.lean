module

public import HodgeConjecture.Realization.Betti.SingularSubdivision
public import HodgeConjecture.Realization.Betti.BarycentricMesh

@[expose] public section

/-!
# Shared native singular subdivision iteration

The original weights-coordinate mesh bound, affine naturality, reference
simplex realization and finite iteration laws are independent of a cover.
These definitions retain their existing namespace and public names.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubdivisionSmallness

open CategoryTheory Opposite Convexity AffineSimplexChains SingularSubdivision
open scoped Simplicial

/-- Original finite weights coordinates of a native standard simplex. -/
def weights {κ : Type} (t : StdSimplex ℝ κ) : κ → ℝ := t.weights

theorem weights_injective {κ : Type} : Function.Injective (weights (κ := κ)) := by
  intro p q h
  apply StdSimplex.ext
  exact Finsupp.ext (congrFun h)

/-- The native tuple centers map to the actual arithmetic centers in coordinate space. -/
theorem centers_weights {κ : Type} [Fintype κ] (m : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (m + 1)) :
    BarycentricMesh.barycentricCenters (κ → ℝ) m (weights ∘ v) = weights (centers κ m v) := by
  simpa only [BarycentricMesh.barycentricCenters, SubdivisionGeometry.mean,
    Finset.card_univ, Function.comp_def, weights, centers] using
      (NativeSimplexGeometry.center_weights_vector v).symm

/-- Actual finite-chain native subdivision in a fixed degree. -/
def nativeIteration {κ : Type} [Finite κ] (n k : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1)) : Chain (StdSimplex ℝ κ) (n + 1) :=
  ((VertexSubdivision.subdivide (centers κ) (n + 1) :
    Chain (StdSimplex ℝ κ) (n + 1) → Chain (StdSimplex ℝ κ) (n + 1))^[k]) c

theorem weights_nativeIteration {κ : Type} [Fintype κ] (n k : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1)) :
    AffineSimplexChains.map weights (n + 1) (nativeIteration n k c) =
      BarycentricMesh.iteratedSubdivision n k (AffineSimplexChains.map weights (n + 1) c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [nativeIteration, BarycentricMesh.iteratedSubdivision,
      Function.iterate_succ_apply'] at ih ⊢
    rw [← VertexSubdivision.subdivide_map (centers κ)
      (BarycentricMesh.barycentricCenters (κ → ℝ)) weights centers_weights, ih]

/-- Native affine realization in weights coordinates is exactly the normed affine simplex. -/
theorem weights_realization {κ : Type} [Fintype κ] (n : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1)) (t : StdSimplex ℝ (Fin (n + 1))) :
    weights (NativeSimplexGeometry.realization v t) =
      SubdivisionGeometry.realization (weights ∘ v) t := by
  funext j
  change (NativeSimplexGeometry.realization v t).weights j = _
  rw [NativeSimplexGeometry.realization_weights]
  simp only [SubdivisionGeometry.realization, ContinuousMap.coe_mk,
    StdSimplex.affineMapMk_apply_eq_sum_of_fintype, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply, weights]

/-- Injectivity of original coordinates prevents a nonzero native cell disappearing under
the passage to coordinates. -/
theorem map_weights_support {κ : Type} (m : ℕ) (c : Chain (StdSimplex ℝ κ) m)
    (v : Vertices (StdSimplex ℝ κ) m) (hv : v ∈ c.support) :
    weights ∘ v ∈ (AffineSimplexChains.map weights m c).support := by
  classical
  have hinj : Function.Injective (fun v : Vertices (StdSimplex ℝ κ) m ↦ weights ∘ v) := by
    intro v w h
    funext i
    exact weights_injective (congrFun h i)
  change _ ∈ (Finsupp.mapDomain (fun v : Vertices (StdSimplex ℝ κ) m ↦ weights ∘ v) c).support
  rw [Finsupp.mapDomain_support_of_injective hinj]
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Every actual native finite chain acquires arbitrarily small whole-cell coordinate
diameter under enough actual recursive subdivision steps. -/
theorem exists_nativeIteration_mesh_lt {κ : Type} [Fintype κ] (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ v ∈ (nativeIteration n k c).support,
      Metric.diam (weights '' Set.range (NativeSimplexGeometry.realization v)) < ε := by
  obtain ⟨k, hk⟩ := BarycentricMesh.exists_iteratedSubdivision_mesh_lt n
    (AffineSimplexChains.map weights (n + 1) c) ε hε
  refine ⟨k, fun v hv ↦ ?_⟩
  have hv' := map_weights_support (n + 1) (nativeIteration n k c) v hv
  rw [weights_nativeIteration] at hv'
  have h := hk (weights ∘ v) hv'
  have hrange : weights '' Set.range (NativeSimplexGeometry.realization v) =
      Set.range (SubdivisionGeometry.realization (weights ∘ v)) := by
    rw [← Set.range_comp]
    congr 1
    funext t
    exact weights_realization n v t
  rwa [hrange]

/-- Native affine realization preserves the actual barycentric centers of every tuple. -/
theorem centers_realization {κ : Type} [Finite κ] (n : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1)) (m : ℕ)
    (w : Vertices (StdSimplex ℝ (Fin (n + 1))) (m + 1)) :
    centers κ m (NativeSimplexGeometry.realization v ∘ w) =
      NativeSimplexGeometry.realization v (centers (Fin (n + 1)) m w) :=
  (NativeSimplexGeometry.center_realization w v).symm

theorem simplex_realization_comp {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n m : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1))
    (w : Vertices (StdSimplex ℝ (Fin (n + 1))) (m + 1)) :
    simplex (f.comp (NativeSimplexGeometry.realization v)) m w =
      simplex f m (NativeSimplexGeometry.realization v ∘ w) := by
  apply (TopCat.toSSetObjEquiv X (op ⦋m⦌)).injective
  apply ContinuousMap.ext
  intro t
  exact congrArg f (NativeSimplexGeometry.realization_comp w v t)

theorem realize_realization_comp {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n m : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1))
    (c : Chain (StdSimplex ℝ (Fin (n + 1))) (m + 1)) :
    realize (f.comp (NativeSimplexGeometry.realization v)) m c =
      realize f m (AffineSimplexChains.map (NativeSimplexGeometry.realization v) (m + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a => simp only [AffineSimplexChains.map_single, realize_single,
      simplex_realization_comp]

theorem map_realization_reference {κ : Type} [Finite κ] (n : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1)) :
    AffineSimplexChains.map (NativeSimplexGeometry.realization v) (n + 1) (reference n) =
      Finsupp.single v 1 := by
  rw [reference, AffineSimplexChains.map_single]
  congr 1
  funext i
  exact NativeSimplexGeometry.realization_single v i

/-- Subdivision of an actual affine subcell agrees with subdividing its actual native vertices. -/
theorem subdivisionComponent_realize {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n : ℕ) (c : Chain (StdSimplex ℝ κ) (n + 1)) :
    subdivisionComponent X n (realize f n c) =
      realize f n (VertexSubdivision.subdivide (centers κ) (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [realize_single, ← SingularChainCoordinates.coordinates_single,
      subdivisionComponent_coordinates_single, subdividedSimplex]
    have hs : TopCat.toSSetObjEquiv X (op ⦋n⦌) (simplex f n v) =
        f.comp (NativeSimplexGeometry.realization v) := Equiv.apply_symm_apply _ _
    rw [hs, realize_realization_comp,
      ← VertexSubdivision.subdivide_map (centers (Fin (n + 1))) (centers κ)
        (NativeSimplexGeometry.realization v) (centers_realization n v),
      map_realization_reference]
    simp only [← map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Iteration of the actual singular-chain endomorphism, degree by degree. -/
def iteration (X : TopCat) (n k : ℕ) (c : (complex X).X n) : (complex X).X n :=
  ((subdivisionComponent X n : (complex X).X n → (complex X).X n)^[k]) c

/-- Repeated singular subdivision is the realization of the repeated native-domain operator. -/
theorem iteration_realize {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n k : ℕ) (c : Chain (StdSimplex ℝ κ) (n + 1)) :
    iteration X n k (realize f n c) = realize f n (nativeIteration n k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iteration, nativeIteration, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, subdivisionComponent_realize]

theorem iteration_add (X : TopCat) (n k : ℕ) (c d : (complex X).X n) :
    iteration X n k (c + d) = iteration X n k c + iteration X n k d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [iteration, Function.iterate_succ_apply', ih, map_add] using
      congrArg (subdivisionComponent X n) ih

theorem iteration_smul (X : TopCat) (n k : ℕ) (a : ℚ) (c : (complex X).X n) :
    iteration X n k (a • c) = a • iteration X n k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [iteration, Function.iterate_succ_apply', ih, map_smul] using
      congrArg (subdivisionComponent X n) ih

end HodgeConjecture.SingularSubdivisionSmallness
