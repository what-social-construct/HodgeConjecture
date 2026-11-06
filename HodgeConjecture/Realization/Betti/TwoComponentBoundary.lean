module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The two-component boundary quotient

The quotient of two rational component values by constant pairs is
canonically measured by their difference, with the true-labelled component
minus the false-labelled component. A surjective actual boundary with
exactly this kernel therefore has these proved coordinates.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.TwoComponentBoundary

/-- Constant component values. -/
def diagonal : ℚ →ₗ[ℚ] (Bool → ℚ) where
  toFun q _ := q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The difference between the two actual component values. -/
def jump : (Bool → ℚ) →ₗ[ℚ] ℚ where
  toFun f := f true - f false
  map_add' f g := by change (f true + g true) - (f false + g false) = _; ring
  map_smul' q f := by change q * f true - q * f false = q * (f true - f false); ring

/-- Value `q` on the true component and zero on the false component. -/
def step : ℚ →ₗ[ℚ] (Bool → ℚ) where
  toFun q i := if i then q else 0
  map_add' q r := by ext i; cases i <;> simp
  map_smul' q r := by ext i; cases i <;> simp

@[simp]
theorem jump_step (q : ℚ) : jump (step q) = q := by simp [jump, step]

@[simp]
theorem jump_diagonal (q : ℚ) : jump (diagonal q) = 0 := sub_self q

theorem jump_surjective : Function.Surjective jump := fun q ↦ ⟨step q, jump_step q⟩

/-- The actual kernel consists exactly of equal component values. -/
theorem ker_jump : LinearMap.ker jump = LinearMap.range diagonal := by
  ext f
  constructor
  · intro hf
    have h : f true = f false := sub_eq_zero.mp hf
    refine ⟨f false, ?_⟩
    ext i
    cases i with
    | false => rfl
    | true => exact h.symm
  · rintro ⟨q, rfl⟩
    exact jump_diagonal q

/-- The difference coordinate on the quotient by constant pairs. -/
def quotientEquiv : ((Bool → ℚ) ⧸ LinearMap.range diagonal) ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ ker_jump.symm).trans
    (jump.quotKerEquivOfSurjective jump_surjective)

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- Coordinates on an actual surjective boundary with the proved constant-pair kernel. -/
def boundaryEquiv (δ : (Bool → ℚ) →ₗ[ℚ] H) (hδ : Function.Surjective δ)
    (hker : LinearMap.ker δ = LinearMap.range diagonal) : H ≃ₗ[ℚ] ℚ :=
  (δ.quotKerEquivOfSurjective hδ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans quotientEquiv)

theorem boundaryEquiv_apply (δ : (Bool → ℚ) →ₗ[ℚ] H) (hδ : Function.Surjective δ)
    (hker : LinearMap.ker δ = LinearMap.range diagonal) (f : Bool → ℚ) :
    boundaryEquiv δ hδ hker (δ f) = jump f := by
  have h := (δ.quotKerEquivOfSurjective hδ).symm_apply_apply ((LinearMap.ker δ).mkQ f)
  change (δ.quotKerEquivOfSurjective hδ).symm (δ f) = _ at h
  simp only [boundaryEquiv, LinearEquiv.trans_apply, h]
  rfl

/-- The generator is the actual boundary of the component indicator, not a supplied vector. -/
theorem boundary_step_ne_zero (δ : (Bool → ℚ) →ₗ[ℚ] H) (hδ : Function.Surjective δ)
    (hker : LinearMap.ker δ = LinearMap.range diagonal) : δ (step 1) ≠ 0 := by
  intro hz
  have h := boundaryEquiv_apply δ hδ hker (step 1)
  rw [hz, map_zero, jump_step] at h
  exact zero_ne_one h

end HodgeConjecture.TwoComponentBoundary
