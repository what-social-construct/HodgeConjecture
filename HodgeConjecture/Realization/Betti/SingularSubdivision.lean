module

public import HodgeConjecture.Realization.Betti.NativeSimplexGeometry
public import HodgeConjecture.Realization.Betti.VertexSubdivisionNaturality
public import HodgeConjecture.Realization.Betti.SingularChainCoordinates
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits

@[expose] public section

/-!
# Barycentric subdivision on actual singular chains

Each original continuous singular simplex is subdivided inside its native
standard-simplex domain using the explicit finite vertex-chain recursion.
All realized subcells are composed with that original continuous map.
The target is Mathlib's original rational singular chain complex.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubdivision

open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial

/-- Mathlib's original rational singular chains, with literal rational coefficients. -/
abbrev complex (X : TopCat) := (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)

/-- Actual barycentric centers within a native finite standard simplex. -/
def centers (κ : Type) [Finite κ] : VertexSubdivision.Centers (StdSimplex ℝ κ) :=
  fun _ v ↦ NativeSimplexGeometry.center v

theorem centers_map {κ τ : Type} [Finite κ] [Finite τ] (f : κ → τ)
    (m : ℕ) (v : AffineSimplexChains.Vertices (StdSimplex ℝ κ) (m + 1)) :
    centers τ m (StdSimplex.map f ∘ v) = StdSimplex.map f (centers κ m v) :=
  (NativeSimplexGeometry.center_target_map v f).symm

/-- The native continuous simplex map induced by a map of its vertices. -/
def simplexMap {κ τ : Type} [Finite κ] (f : κ → τ) :
    C(StdSimplex ℝ κ, StdSimplex ℝ τ) :=
  ⟨StdSimplex.map f, StdSimplex.continuous_map ℝ f⟩

/-- Realize a tuple in a native simplex, then compose with the original continuous singular map. -/
def simplex {κ : Type} [Finite κ] {X : TopCat} (f : C(StdSimplex ℝ κ, X)) (n : ℕ)
    (v : Fin (n + 1) → StdSimplex ℝ κ) : (TopCat.toSSet.obj X).obj (op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv X (op ⦋n⦌)).symm (f.comp (NativeSimplexGeometry.realization v))

theorem simplex_face {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n : ℕ) (v : Fin (n + 2) → StdSimplex ℝ κ)
    (i : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ i (simplex f (n + 1) v) =
      simplex f n (AffineSimplexChains.face v i) := by
  apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective
  ext t
  exact congrArg f (NativeSimplexGeometry.realization_face n v i t)

/-- Actual finite vertex chains realized in the native singular coproduct. -/
def realize {κ : Type} [Finite κ] {X : TopCat} (f : C(StdSimplex ℝ κ, X)) (n : ℕ) :
    AffineSimplexChains.Chain (StdSimplex ℝ κ) (n + 1) →ₗ[ℚ] (complex X).X n :=
  (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).toLinearMap.comp
    (Finsupp.lmapDomain ℚ ℚ (simplex f n))

@[simp]
theorem realize_single {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n : ℕ) (v : Fin (n + 1) → StdSimplex ℝ κ) (a : ℚ) :
    realize f n (Finsupp.single v a) =
      ((TopCat.toSSet.obj X).ιChainComplex (simplex f n v) (R := ModuleCat.of ℚ ℚ)) a := by
  simp [realize]

theorem realize_boundary {κ : Type} [Finite κ] {X : TopCat}
    (f : C(StdSimplex ℝ κ, X)) (n : ℕ)
    (c : AffineSimplexChains.Chain (StdSimplex ℝ κ) (n + 2)) :
    (complex X).d (n + 1) n (realize f (n + 1) c) =
      realize f n (AffineSimplexChains.boundary (StdSimplex ℝ κ) (n + 1) c) := by
  change (complex X).d (n + 1) n
    (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) (n + 1)
      (Finsupp.lmapDomain ℚ ℚ (simplex f (n + 1)) c)) = _
  rw [SingularChainCoordinates.coordinates_boundary]
  apply congrArg (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n)
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using congrArg₂ (· + ·) hc hd
  | single v a =>
    simp [AffineSimplexChains.boundarySimplex, simplex_face,
      SingularChainCoordinates.boundary_single, Finset.smul_sum, mul_comm]

theorem simplex_target_map {κ τ : Type} [Finite κ] [Finite τ] {X : TopCat}
    (f : C(StdSimplex ℝ τ, X)) (g : κ → τ) (n : ℕ)
    (v : Fin (n + 1) → StdSimplex ℝ κ) :
    simplex (f.comp (simplexMap g)) n v = simplex f n (StdSimplex.map g ∘ v) := by
  apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective
  ext t
  exact congrArg f (NativeSimplexGeometry.realization_target_map v g t)

theorem realize_target_map {κ τ : Type} [Finite κ] [Finite τ] {X : TopCat}
    (f : C(StdSimplex ℝ τ, X)) (g : κ → τ) (n : ℕ)
    (c : AffineSimplexChains.Chain (StdSimplex ℝ κ) (n + 1)) :
    realize (f.comp (simplexMap g)) n c =
      realize f n (AffineSimplexChains.map (StdSimplex.map g) (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a => simp only [AffineSimplexChains.map_single, realize_single, simplex_target_map]

/-- The original vertex chain of the native reference simplex. -/
def reference (n : ℕ) : AffineSimplexChains.Chain (StdSimplex ℝ (Fin (n + 1))) (n + 1) :=
  Finsupp.single (StdSimplex.single (R := ℝ)) 1

theorem realize_reference {X : TopCat} (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    realize (TopCat.toSSetObjEquiv X _ σ) n (reference n) =
      ((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) 1 := by
  rw [reference, realize_single]
  have hs : simplex (TopCat.toSSetObjEquiv X _ σ) n (StdSimplex.single (R := ℝ)) = σ := by
    apply (TopCat.toSSetObjEquiv X (op ⦋n⦌)).injective
    ext t
    simp [simplex]
  rw [hs]

theorem boundary_reference (n : ℕ) :
    AffineSimplexChains.boundary (StdSimplex ℝ (Fin (n + 2))) (n + 1) (reference (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) •
        AffineSimplexChains.map (StdSimplex.map i.succAbove) (n + 1) (reference n) := by
  simp only [reference, AffineSimplexChains.boundary_single, one_smul,
    AffineSimplexChains.boundarySimplex, AffineSimplexChains.map_single]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ext j
  simp [AffineSimplexChains.face, Fin.removeNth]

/-- Subdivide one original continuous singular simplex in its own native domain. -/
def subdividedSimplex (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (complex X).X n :=
  realize (TopCat.toSSetObjEquiv X _ σ) n
    (VertexSubdivision.subdivide (centers (Fin (n + 1))) (n + 1) (reference n))

/-- Barycentric subdivision on the original singular chain module. -/
def subdivisionComponent (X : TopCat) (n : ℕ) : (complex X).X n →ₗ[ℚ] (complex X).X n :=
  (Finsupp.linearCombination ℚ (subdividedSimplex X n)).comp
    (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm.toLinearMap

@[simp]
theorem subdivisionComponent_coordinates_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (a : ℚ) :
    subdivisionComponent X n
      (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ a)) =
        a • subdividedSimplex X n σ := by
  change (Finsupp.linearCombination ℚ (subdividedSimplex X n))
    ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm
      ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n) (Finsupp.single σ a))) = _
  rw [LinearEquiv.symm_apply_apply, Finsupp.linearCombination_single]

theorem original_face_map (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) (i : Fin (n + 2)) :
    TopCat.toSSetObjEquiv X (op ⦋n⦌) ((TopCat.toSSet.obj X).δ i σ) =
      (TopCat.toSSetObjEquiv X _ σ).comp (simplexMap i.succAbove) := by
  ext t
  rfl

/-- The actual singular boundary of a subdivided simplex is its subdivided original faces. -/
theorem boundary_subdividedSimplex (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    (complex X).d (n + 1) n (subdividedSimplex X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) •
        subdividedSimplex X n ((TopCat.toSSet.obj X).δ i σ) := by
  rw [subdividedSimplex, realize_boundary, VertexSubdivision.boundary_subdivide,
    boundary_reference, map_sum]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [VertexSubdivision.subdivide_map (centers (Fin (n + 1)))
    (centers (Fin (n + 2))) (StdSimplex.map i.succAbove) (centers_map i.succAbove)]
  rw [← realize_target_map]
  simp only [subdividedSimplex, original_face_map]

/-- Subdivision commutes with the actual native singular differential on every finite chain. -/
theorem subdivisionComponent_boundary (X : TopCat) (n : ℕ) (c : (complex X).X (n + 1)) :
    (complex X).d (n + 1) n (subdivisionComponent X (n + 1) c) =
      subdivisionComponent X n ((complex X).d (n + 1) n c) := by
  obtain ⟨c, rfl⟩ := (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) (n + 1)).surjective c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    rw [subdivisionComponent_coordinates_single, map_smul, boundary_subdividedSimplex,
      SingularChainCoordinates.coordinates_boundary, SingularChainCoordinates.boundary_single]
    simp only [map_sum, map_smul, subdivisionComponent_coordinates_single, Finset.smul_sum,
      smul_smul, mul_comm]

/-- The constructed barycentric subdivision as an endomorphism of Mathlib's singular complex. -/
def subdivision (X : TopCat) : complex X ⟶ complex X where
  f n := ModuleCat.ofHom (subdivisionComponent X n)
  comm' i j h := by
    obtain rfl : j + 1 = i := h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact subdivisionComponent_boundary X j c

end HodgeConjecture.SingularSubdivision
