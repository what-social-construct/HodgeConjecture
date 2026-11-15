module

public import HodgeConjecture.Geometry.Holomorphic.LowDegree

@[expose] public section

/-! # The shared holomorphic-function scalar action on coordinate forms -/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open TopologicalSpace
open scoped Manifold ContDiff
open HolomorphicForms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The existing scalar holomorphic-function ring, without a new function carrier. -/
abbrev Functions (U : Opens E) := C^∞⟮𝓘(ℂ, E), U; ℂ⟯

instance functionScalarTower (U : Opens E) (n : ℕ) :
    IsScalarTower ℂ (Functions U) (Sections U n) where
  smul_assoc c f η := by
    apply ContMDiffMap.ext
    intro x
    exact smul_assoc c (f x) (η x)

/-- A scalar as its constant native zero-form section. -/
def constant (U : Opens E) : ℂ →ₗ[ℂ] Sections U 0 where
  toFun c := ContMDiffMap.const (ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) c)
  map_add' c d := by
    apply ContMDiffMap.ext
    intro x
    exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ E ℂ (Fin 0)).map_add c d
  map_smul' c d := by
    apply ContMDiffMap.ext
    intro x
    exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ E ℂ (Fin 0)).map_smul c d

theorem differential_constant (U : Opens E) (c : ℂ) :
    HolomorphicForms.differential U 0 (constant U c) = 0 := by
  apply ContMDiffMap.ext
  intro x
  rw [HolomorphicForms.differential_eq_of_extension (constant U c)
    (fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) c) (fun _ ↦ rfl)]
  simp only [extDeriv, fderiv_fun_const]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ E ℂ).map_zero


end HodgeConjecture.HolomorphicDeRham
