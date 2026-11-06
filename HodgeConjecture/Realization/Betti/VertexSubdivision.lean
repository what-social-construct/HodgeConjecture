module

public import HodgeConjecture.Realization.Betti.AffineSimplexChains

@[expose] public section

/-!
# Recursive subdivision and its explicit chain homotopy

For each nonempty vertex tuple choose a cone center. Subdivide its boundary
recursively, then cone that boundary to the chosen center. The resulting
finite-chain operator commutes with the actual alternating boundary. A
second explicit cone recursion constructs its chain homotopy to identity.
Barycentric centers and geometric locality are separate specializations.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.VertexSubdivision

open AffineSimplexChains

universe u

variable {E : Type u}

/-- An actual vertex chosen for every nonempty ordered tuple. -/
abbrev Centers (E : Type u) := (m : ℕ) → Vertices E (m + 1) → E

/-- Recursively cone the subdivided boundary to the chosen tuple center.
The empty-tuple augmentation is fixed. -/
def subdivide (center : Centers E) : (m : ℕ) → Chain E m →ₗ[ℚ] Chain E m
  | 0 => LinearMap.id
  | m + 1 => Finsupp.linearCombination ℚ fun v ↦
      cone (center m v) m (subdivide center m (boundarySimplex m v))

@[simp]
theorem subdivide_zero (center : Centers E) (c : Chain E 0) :
    subdivide center 0 c = c := rfl

@[simp]
theorem subdivide_single (center : Centers E) (m : ℕ)
    (v : Vertices E (m + 1)) (a : ℚ) :
    subdivide center (m + 1) (Finsupp.single v a) =
      a • cone (center m v) m (subdivide center m (boundarySimplex m v)) := by
  simp only [subdivide, Finsupp.linearCombination_single]

/-- This explicit subdivision commutes with boundary in every degree, including augmentation. -/
theorem boundary_subdivide (center : Centers E) (m : ℕ) (c : Chain E (m + 1)) :
    boundary E m (subdivide center (m + 1) c) =
      subdivide center m (boundary E m c) := by
  induction m with
  | zero =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a => simp [boundary_cone_zero]
  | succ m ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      have hcycle : boundary E m
          (subdivide center (m + 1) (boundarySimplex (m + 1) v)) = 0 := by
        rw [ih]
        have h := boundary_squared E m (Finsupp.single v 1)
        simpa only [boundary_single, one_smul, map_zero] using congrArg (subdivide center m) h
      simp only [subdivide_single, map_smul, boundary_cone, hcycle, map_zero, sub_zero,
        boundary_single]

/-- A constructive homotopy from recursive subdivision to the identity.
The expression coned at each step is a cycle by the previous homotopy identity. -/
def homotopy (center : Centers E) : (m : ℕ) → Chain E m →ₗ[ℚ] Chain E (m + 1)
  | 0 => 0
  | m + 1 => Finsupp.linearCombination ℚ fun v ↦
      cone (center m v) (m + 1)
        (Finsupp.single v 1 - subdivide center (m + 1) (Finsupp.single v 1) -
          homotopy center m (boundarySimplex m v))

@[simp]
theorem homotopy_zero (center : Centers E) (c : Chain E 0) :
    homotopy center 0 c = 0 := rfl

@[simp]
theorem homotopy_single (center : Centers E) (m : ℕ)
    (v : Vertices E (m + 1)) (a : ℚ) :
    homotopy center (m + 1) (Finsupp.single v a) =
      a • cone (center m v) (m + 1)
        (Finsupp.single v 1 - subdivide center (m + 1) (Finsupp.single v 1) -
          homotopy center m (boundarySimplex m v)) := by
  simp only [homotopy, Finsupp.linearCombination_single]

/-- The constructed homotopy identity as an equality of actual linear maps. -/
theorem homotopy_identity_map (center : Centers E) (m : ℕ) :
    (boundary E (m + 1)).comp (homotopy center (m + 1)) +
      (homotopy center m).comp (boundary E m) = LinearMap.id - subdivide center (m + 1) := by
  induction m with
  | zero =>
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change boundary E 1 (homotopy center 1 (Finsupp.single v 1)) +
      homotopy center 0 (boundary E 0 (Finsupp.single v 1)) =
        Finsupp.single v 1 - subdivide center 1 (Finsupp.single v 1)
    have hcycle : boundary E 0
        (Finsupp.single v 1 - subdivide center 1 (Finsupp.single v 1) -
          homotopy center 0 (boundarySimplex 0 v)) = 0 := by
      rw [map_sub, map_sub, boundary_subdivide, subdivide_zero, homotopy_zero,
        map_zero, sub_self, sub_zero]
    rw [homotopy_single, one_smul, boundary_cone, hcycle, map_zero, sub_zero,
      homotopy_zero, homotopy_zero, sub_zero, add_zero]
  | succ m ih =>
    apply Finsupp.lhom_ext'
    intro v
    apply LinearMap.ext_ring
    change boundary E (m + 2) (homotopy center (m + 2) (Finsupp.single v 1)) +
      homotopy center (m + 1) (boundary E (m + 1) (Finsupp.single v 1)) =
        Finsupp.single v 1 - subdivide center (m + 2) (Finsupp.single v 1)
    have hboundary : boundary E m (boundarySimplex (m + 1) v) = 0 := by
      simpa only [boundary_single, one_smul] using
        boundary_squared E m (Finsupp.single v 1)
    have hprevious := LinearMap.congr_fun ih (boundarySimplex (m + 1) v)
    change boundary E (m + 1) (homotopy center (m + 1) (boundarySimplex (m + 1) v)) +
      homotopy center m (boundary E m (boundarySimplex (m + 1) v)) =
        boundarySimplex (m + 1) v - subdivide center (m + 1) (boundarySimplex (m + 1) v)
      at hprevious
    rw [hboundary, map_zero, add_zero] at hprevious
    have hcycle : boundary E (m + 1)
        (Finsupp.single v 1 - subdivide center (m + 2) (Finsupp.single v 1) -
          homotopy center (m + 1) (boundarySimplex (m + 1) v)) = 0 := by
      rw [map_sub, map_sub, boundary_subdivide, boundary_single, one_smul, hprevious]
      abel
    rw [homotopy_single, one_smul, boundary_cone, hcycle, map_zero, sub_zero,
      boundary_single, one_smul]
    abel

/-- The actual chain-homotopy identity, with every term constructed by cone recursion. -/
theorem homotopy_identity (center : Centers E) (m : ℕ) (c : Chain E (m + 1)) :
    boundary E (m + 1) (homotopy center (m + 1) c) +
      homotopy center m (boundary E m c) = c - subdivide center (m + 1) c :=
  LinearMap.congr_fun (homotopy_identity_map center m) c

end HodgeConjecture.VertexSubdivision
