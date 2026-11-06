module

public import HodgeConjecture.Realization.Betti.SingularSubdivision
public import HodgeConjecture.Realization.Betti.BarycentricMesh
public import HodgeConjecture.Realization.Betti.SingularSubcomplexes

@[expose] public section

/-!
# Actual singular subdivision becomes small for an open cover

The native standard-simplex subdivision is compared with the same recursive
operator in its original weights coordinates. The proved barycentric mesh
bound and native compact-cover Lebesgue number make its actual subcells
small. Affine naturality identifies repeated domain subdivision with
iteration of the original singular-chain endomorphism.
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

/-- Every actual native cell eventually lies in one member of the genuine open cover. -/
theorem exists_nativeIteration_small {κ : Type} [Fintype κ] (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1))
    (U V : Set (StdSimplex ℝ κ)) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    ∃ k : ℕ, ∀ v ∈ (nativeIteration n k c).support,
      Set.range (NativeSimplexGeometry.realization v) ⊆ U ∨
        Set.range (NativeSimplexGeometry.realization v) ⊆ V := by
  obtain ⟨ε, hε, hsmall⟩ := NativeSimplexGeometry.lebesgue_number_two_diam U V hU hV hcover
  obtain ⟨k, hk⟩ := exists_nativeIteration_mesh_lt n c ε hε
  refine ⟨k, fun v hv ↦ hsmall _ (Set.range_nonempty _) (hk v hv)⟩

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

/-- Actual finite singular chains supported on simplices contained in one cover member. -/
def smallChains (X : TopCat) (U V : Set X) (n : ℕ) : Submodule ℚ ((complex X).X n) :=
  (Finsupp.supported ℚ ℚ ((SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌))).comap
    (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm.toLinearMap

theorem coordinates_mem_smallChains (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj X).obj (op ⦋n⦌) →₀ ℚ) :
    SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n c ∈ smallChains X U V n ↔
      c ∈ Finsupp.supported ℚ ℚ
        ((SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌)) := by
  simp only [smallChains, Submodule.mem_comap, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- A realized native tuple lies in the small singular set whenever its whole cell lands
in one member of the original cover. -/
theorem simplex_mem_small {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (U V : Set X) (n : ℕ)
    (v : Vertices (StdSimplex ℝ κ) (n + 1))
    (hv : Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' U ∨
      Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' V) :
    simplex f n v ∈ (SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌) := by
  change simplex f n v ∈ (SingularSubcomplexes.subsetSingular X U).obj (op ⦋n⦌) ∨
    simplex f n v ∈ (SingularSubcomplexes.subsetSingular X V).obj (op ⦋n⦌)
  have h {W : Set X} (hW : Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' W) :
      simplex f n v ∈ (SingularSubcomplexes.subsetSingular X W).obj (op ⦋n⦌) := by
    rw [SingularSubcomplexes.mem_subsetSingular_iff_range]
    rintro _ ⟨t, rfl⟩
    exact hW ⟨t, rfl⟩
  exact hv.imp h h

/-- Linear realization of an actual finite native chain retains proved whole-cell smallness. -/
theorem realize_mem_smallChains {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (U V : Set X) (n : ℕ)
    (c : Chain (StdSimplex ℝ κ) (n + 1))
    (hc : ∀ v ∈ c.support,
      Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' U ∨
        Set.range (NativeSimplexGeometry.realization v) ⊆ f ⁻¹' V) :
    realize f n c ∈ smallChains X U V n := by
  classical
  change SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
    (Finsupp.lmapDomain ℚ ℚ (simplex f n) c) ∈ _
  rw [coordinates_mem_smallChains, Finsupp.mem_supported]
  intro σ hσ
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hσ)
  exact simplex_mem_small f U V n v (hc v hv)

/-- Every actual singular simplex becomes a small finite chain after enough repetitions
of the constructed singular-chain endomorphism. -/
theorem exists_iteration_simplex_small (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    ∃ k : ℕ, iteration X n k
      (((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) 1) ∈ smallChains X U V n := by
  let f := TopCat.toSSetObjEquiv X (op ⦋n⦌) σ
  have hcover' : f ⁻¹' U ∪ f ⁻¹' V = Set.univ := by
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  obtain ⟨k, hk⟩ := exists_nativeIteration_small n (reference n) (f ⁻¹' U) (f ⁻¹' V)
    (hU.preimage f.continuous) (hV.preimage f.continuous) hcover'
  refine ⟨k, ?_⟩
  rw [← realize_reference, iteration_realize]
  exact realize_mem_smallChains f U V n _ hk

/-- Once a singular chain is small, the actual subdivision keeps it small. -/
theorem subdivisionComponent_mem_smallChains (X : TopCat) (U V : Set X) (n : ℕ)
    (c : (complex X).X n) (hc : c ∈ smallChains X U V n) :
    subdivisionComponent X n c ∈ smallChains X U V n := by
  let e := SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
  obtain ⟨c, rfl⟩ := e.surjective c
  rw [coordinates_mem_smallChains] at hc
  have h : Finsupp.supported ℚ ℚ
      ((SingularSubcomplexes.smallSingular X U V).obj (op ⦋n⦌)) ≤
      (smallChains X U V n).comap ((subdivisionComponent X n).comp e.toLinearMap) := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨σ, hσ, rfl⟩
    change subdivisionComponent X n (e (Finsupp.single σ 1)) ∈ smallChains X U V n
    rw [subdivisionComponent_coordinates_single, one_smul, subdividedSimplex]
    apply realize_mem_smallChains
    intro v _
    change σ ∈ (SingularSubcomplexes.subsetSingular X U).obj (op ⦋n⦌) ∨
      σ ∈ (SingularSubcomplexes.subsetSingular X V).obj (op ⦋n⦌) at hσ
    have hf : Set.range (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ) ⊆ U ∨
        Set.range (TopCat.toSSetObjEquiv X (op ⦋n⦌) σ) ⊆ V := by
      simpa only [SingularSubcomplexes.mem_subsetSingular_iff_range] using hσ
    exact hf.imp (fun h q _ ↦ h ⟨q, rfl⟩) (fun h q _ ↦ h ⟨q, rfl⟩)
  exact h hc

theorem iteration_mem_smallChains (X : TopCat) (U V : Set X) (n k : ℕ)
    (c : (complex X).X n) (hc : c ∈ smallChains X U V n) :
    iteration X n k c ∈ smallChains X U V n := by
  induction k with
  | zero => exact hc
  | succ k ih =>
    simpa only [iteration, Function.iterate_succ_apply'] using
      subdivisionComponent_mem_smallChains X U V n _ ih

/-- Every larger iteration count works after a chain has become small. -/
theorem iteration_mem_smallChains_of_le (X : TopCat) (U V : Set X) (n k l : ℕ)
    (hkl : k ≤ l) (c : (complex X).X n) (hc : iteration X n k c ∈ smallChains X U V n) :
    iteration X n l c ∈ smallChains X U V n := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [Nat.add_comm k r]
  change (subdivisionComponent X n)^[r + k] c ∈ _
  rw [Function.iterate_add_apply]
  exact iteration_mem_smallChains X U V n r _ hc

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

/-- One actual iteration count works for the entire finite support of any original singular
chain. This is the small-chain shrinking theorem, without a homology-equivalence premise. -/
theorem exists_iteration_small (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (c : (complex X).X n) :
    ∃ k : ℕ, iteration X n k c ∈ smallChains X U V n := by
  obtain ⟨c, rfl⟩ := (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).surjective c
  induction c using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, ?_⟩
    simpa only [map_zero, iteration, Function.iterate_zero_apply] using
      (smallChains X U V n).zero_mem
  | add c d hc hd =>
    obtain ⟨k, hk⟩ := hc
    obtain ⟨l, hl⟩ := hd
    refine ⟨max k l, ?_⟩
    rw [map_add, iteration_add]
    exact (smallChains X U V n).add_mem
      (iteration_mem_smallChains_of_le X U V n k (max k l) (le_max_left _ _) _ hk)
      (iteration_mem_smallChains_of_le X U V n l (max k l) (le_max_right _ _) _ hl)
  | single σ a =>
    obtain ⟨k, hk⟩ := exists_iteration_simplex_small X U V hU hV hcover n σ
    refine ⟨k, ?_⟩
    have hsingle : SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
        (Finsupp.single σ a) =
        a • SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n
          (Finsupp.single σ 1) := by
      rw [← map_smul]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle, iteration_smul, SingularChainCoordinates.coordinates_single]
    exact (smallChains X U V n).smul_mem a hk

end HodgeConjecture.SingularSubdivisionSmallness
