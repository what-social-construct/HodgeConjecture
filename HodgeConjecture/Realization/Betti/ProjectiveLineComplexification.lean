module

public import HodgeConjecture.Realization.Betti.ProjectiveLineOrientation
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

/-!
# The genuine complexification of projective-line singular H²

Scalar extension of the proved rational cover coordinate gives coordinates
on the actual tensor product ℂ ⊗[ℚ] H²(P¹(ℂ),ℚ). Its rational embedding
is the original pure tensor, with injectivity proved. These constructions
retain the independently constructed singular group.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineBettiComplexification

open TensorProduct ProjectiveLineBettiCohomology

abbrev Betti := SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2

/-- Scalar extension of the actual rational singular cohomology group. -/
abbrev Complexification := ℂ ⊗[ℚ] Betti

/-- Scalar extension of the proved rational cover coordinate. -/
def coordinates : Complexification ≃ₗ[ℂ] ℂ :=
  (LinearEquiv.baseChange ℚ ℂ _ _ h2Equiv).trans (AlgebraTensorModule.rid ℚ ℂ ℂ)

@[simp]
theorem coordinates_tmul (c : ℂ) (z : Betti) :
    coordinates (c ⊗ₜ[ℚ] z) = c * (h2Equiv z : ℂ) := by
  change h2Equiv z • c = _
  rw [Algebra.smul_def, mul_comm, eq_ratCast]

/-- The original rational class embeds as its pure tensor with one. -/
def rationalEmbedding : Betti →ₗ[ℚ] Complexification := TensorProduct.mk ℚ ℂ Betti 1

@[simp]
theorem coordinates_rationalEmbedding (z : Betti) :
    coordinates (rationalEmbedding z) = (h2Equiv z : ℂ) := by
  simp [rationalEmbedding]

/-- The tensor coordinate extends actual positive boundary-loop evaluation. -/
theorem coordinates_tmul_boundaryPairing (c : ℂ) (z : Betti) :
    coordinates (c ⊗ₜ[ℚ] z) = c * (ProjectiveLineBettiOrientation.boundaryPairing z : ℂ) := by
  rw [coordinates_tmul, ProjectiveLineBettiOrientation.boundaryPairing_eq_coordinate]

/-- Extend the independently constructed actual positive boundary pairing by scalars. -/
def complexBoundaryPairing : Complexification →ₗ[ℂ] ℂ :=
  (AlgebraTensorModule.rid ℚ ℂ ℂ).toLinearMap.comp
    (ProjectiveLineBettiOrientation.boundaryPairing.baseChange ℂ)

@[simp]
theorem complexBoundaryPairing_tmul (c : ℂ) (z : Betti) :
    complexBoundaryPairing (c ⊗ₜ[ℚ] z) =
      c * (ProjectiveLineBettiOrientation.boundaryPairing z : ℂ) := by
  change ProjectiveLineBettiOrientation.boundaryPairing z • c = _
  rw [Algebra.smul_def, mul_comm, eq_ratCast]

/-- Actual positive boundary evaluation agrees with the computed scalar coordinate. -/
theorem complexBoundaryPairing_eq_coordinates :
    complexBoundaryPairing = coordinates.toLinearMap := by
  apply LinearMap.ext
  intro z
  change complexBoundaryPairing z = coordinates z
  induction z using TensorProduct.inductionOn with
  | tmul c z => rw [complexBoundaryPairing_tmul, coordinates_tmul_boundaryPairing]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem rationalEmbedding_injective : Function.Injective rationalEmbedding := by
  intro x y h
  apply h2Equiv.injective
  have hc := congrArg coordinates h
  simpa using hc

@[simp]
theorem coordinates_symm_apply (c : ℂ) : coordinates.symm c = c ⊗ₜ[ℚ] coverGenerator := by
  apply coordinates.injective
  simp

theorem eq_tmul_coverGenerator (z : Complexification) :
    z = coordinates z ⊗ₜ[ℚ] coverGenerator := by
  rw [← coordinates_symm_apply, LinearEquiv.symm_apply_apply]

end HodgeConjecture.ProjectiveLineBettiComplexification
