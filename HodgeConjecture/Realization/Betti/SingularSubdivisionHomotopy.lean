module

public import HodgeConjecture.Realization.Betti.SingularSubdivision
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section

/-!
# The explicit singular subdivision homotopy

Realize the constructed vertex-chain homotopy inside each original
singular simplex and compose with its continuous map. The resulting
operators on Mathlib's actual singular chain modules satisfy the chain
homotopy identity, including degree zero.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SingularSubdivision

open CategoryTheory Opposite Convexity
open scoped Simplicial

/-- The actual singular homotopy chain of one original simplex. -/
def homotopySimplex (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    (complex X).X (n + 1) :=
  realize (TopCat.toSSetObjEquiv X _ σ) (n + 1)
    (VertexSubdivision.homotopy (centers (Fin (n + 1))) (n + 1) (reference n))

/-- Linear extension on the original native singular chain coproduct. -/
def homotopyComponent (X : TopCat) (n : ℕ) : (complex X).X n →ₗ[ℚ] (complex X).X (n + 1) :=
  (Finsupp.linearCombination ℚ (homotopySimplex X n)).comp
    (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm.toLinearMap

@[simp]
theorem homotopyComponent_coordinates_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) (a : ℚ) :
    homotopyComponent X n
      (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ a)) =
        a • homotopySimplex X n σ := by
  change (Finsupp.linearCombination ℚ (homotopySimplex X n))
    ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).symm
      ((SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n) (Finsupp.single σ a))) = _
  rw [LinearEquiv.symm_apply_apply, Finsupp.linearCombination_single]

theorem realize_homotopy_boundary_reference (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    realize (TopCat.toSSetObjEquiv X _ σ) (n + 1)
      (VertexSubdivision.homotopy (centers (Fin (n + 2))) (n + 1)
        (AffineSimplexChains.boundary (StdSimplex ℝ (Fin (n + 2))) (n + 1) (reference (n + 1)))) =
      ∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) •
        homotopySimplex X n ((TopCat.toSSet.obj X).δ i σ) := by
  rw [boundary_reference]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [VertexSubdivision.homotopy_map (centers (Fin (n + 1)))
    (centers (Fin (n + 2))) (StdSimplex.map i.succAbove) (centers_map i.succAbove)]
  rw [← realize_target_map]
  simp only [homotopySimplex, original_face_map]

/-- The positive-degree homotopy identity on each actual singular generator. -/
theorem boundary_homotopySimplex (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n + 1⦌)) :
    (complex X).d (n + 2) (n + 1) (homotopySimplex X (n + 1) σ) +
      (∑ i : Fin (n + 2), (-1 : ℚ) ^ (i : ℕ) •
        homotopySimplex X n ((TopCat.toSSet.obj X).δ i σ)) =
      ((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) 1 -
        subdividedSimplex X (n + 1) σ := by
  rw [homotopySimplex, realize_boundary, ← realize_homotopy_boundary_reference, ← map_add,
    VertexSubdivision.homotopy_identity, map_sub, realize_reference]
  rfl

/-- At degree zero the augmentation term of the constructed vertex homotopy is zero. -/
theorem boundary_homotopySimplex_zero (X : TopCat)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋0⦌)) :
    (complex X).d 1 0 (homotopySimplex X 0 σ) =
      ((TopCat.toSSet.obj X).ιChainComplex σ (R := ModuleCat.of ℚ ℚ)) 1 -
        subdividedSimplex X 0 σ := by
  have h := VertexSubdivision.homotopy_identity (centers (Fin 1)) 0 (reference 0)
  rw [VertexSubdivision.homotopy_zero, add_zero] at h
  rw [homotopySimplex, realize_boundary, h, map_sub, realize_reference]
  rfl

/-- Linear maps out of the original singular coproduct are determined by its actual generators. -/
theorem chainLinearMap_ext (X : TopCat) (n : ℕ) {M : Type} [AddCommGroup M] [Module ℚ M]
    (f g : (complex X).X n →ₗ[ℚ] M)
    (h : ∀ σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌),
      f (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ 1)) =
        g (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n (Finsupp.single σ 1))) :
    f = g := by
  apply LinearMap.ext
  intro c
  obtain ⟨c, rfl⟩ := (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) n).surjective c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ a =>
    have hs : Finsupp.single σ a = a • Finsupp.single σ (1 : ℚ) := by simp
    rw [hs, map_smul, map_smul, map_smul, h]

/-- The explicit singular homotopy identity on every finite chain in positive degree. -/
theorem homotopyComponent_identity (X : TopCat) (n : ℕ) (c : (complex X).X (n + 1)) :
    (complex X).d (n + 2) (n + 1) (homotopyComponent X (n + 1) c) +
      homotopyComponent X n ((complex X).d (n + 1) n c) =
        c - subdivisionComponent X (n + 1) c := by
  have heq : ((complex X).d (n + 2) (n + 1)).hom.comp (homotopyComponent X (n + 1)) +
      (homotopyComponent X n).comp ((complex X).d (n + 1) n).hom =
        LinearMap.id - subdivisionComponent X (n + 1) := by
    apply chainLinearMap_ext X (n + 1)
    intro σ
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [homotopyComponent_coordinates_single, one_smul,
      SingularChainCoordinates.coordinates_boundary, SingularChainCoordinates.boundary_single]
    simp only [map_sum, map_smul]
    simp only [homotopyComponent_coordinates_single, subdivisionComponent_coordinates_single,
      one_smul]
    rw [SingularChainCoordinates.coordinates_single]
    exact boundary_homotopySimplex X n σ
  exact LinearMap.congr_fun heq c

/-- The same homotopy identity in degree zero, where there is no incoming boundary term. -/
theorem homotopyComponent_identity_zero (X : TopCat) (c : (complex X).X 0) :
    (complex X).d 1 0 (homotopyComponent X 0 c) = c - subdivisionComponent X 0 c := by
  have heq : ((complex X).d 1 0).hom.comp (homotopyComponent X 0) =
      LinearMap.id - subdivisionComponent X 0 := by
    apply chainLinearMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [homotopyComponent_coordinates_single, one_smul,
      subdivisionComponent_coordinates_single, one_smul, SingularChainCoordinates.coordinates_single]
    exact boundary_homotopySimplex_zero X σ
  exact LinearMap.congr_fun heq c

end HodgeConjecture.SingularSubdivision
