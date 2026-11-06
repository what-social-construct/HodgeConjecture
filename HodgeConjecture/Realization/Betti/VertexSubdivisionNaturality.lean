module

public import HodgeConjecture.Realization.Betti.VertexSubdivision

@[expose] public section

/-!
# Naturality of recursive vertex subdivision

A vertex map respecting the chosen centers commutes with both explicit
cone recursions. This will be used for the affine face maps between
reference standard simplices, with their actual barycentric centers.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.VertexSubdivision

open AffineSimplexChains

universe u v

variable {E : Type u} {F : Type v}

/-- Subdivision is natural under maps preserving the actual chosen tuple centers. -/
theorem subdivide_map (centerE : Centers E) (centerF : Centers F) (f : E → F)
    (hcenter : ∀ m (v : Vertices E (m + 1)), centerF m (f ∘ v) = f (centerE m v))
    (m : ℕ) (c : Chain E m) :
    subdivide centerF m (AffineSimplexChains.map f m c) =
      AffineSimplexChains.map f m (subdivide centerE m c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [map_single, subdivide_single, hcenter, subdivide_single, map_smul, map_cone]
      congr 2
      rw [← ih]
      congr 1
      simpa only [boundary_single, one_smul, map_single] using
        boundary_map f m (Finsupp.single v 1)

/-- The explicit homotopy, including its support-preserving cone terms, has the same naturality. -/
theorem homotopy_map (centerE : Centers E) (centerF : Centers F) (f : E → F)
    (hcenter : ∀ m (v : Vertices E (m + 1)), centerF m (f ∘ v) = f (centerE m v))
    (m : ℕ) (c : Chain E m) :
    homotopy centerF m (AffineSimplexChains.map f m c) =
      AffineSimplexChains.map f (m + 1) (homotopy centerE m c) := by
  induction m with
  | zero => simp
  | succ m ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      have hb : boundarySimplex m (f ∘ v) =
          AffineSimplexChains.map f m (boundarySimplex m v) := by
        simpa only [boundary_single, one_smul, map_single] using
          boundary_map f m (Finsupp.single v 1)
      rw [map_single, homotopy_single, hcenter, homotopy_single, map_smul, map_cone]
      congr 2
      rw [map_sub, map_sub, map_single, ← subdivide_map centerE centerF f hcenter, ← ih]
      rw [hb, map_single]

end HodgeConjecture.VertexSubdivision
