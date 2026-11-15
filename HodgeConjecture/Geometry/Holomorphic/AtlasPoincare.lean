module

public import HodgeConjecture.Geometry.Holomorphic.AtlasCoordinates
public import HodgeConjecture.Geometry.Holomorphic.FunctionAlgebra
public import HodgeConjecture.Geometry.Holomorphic.Poincare

@[expose] public section

/-!
# Local Poincaré exactness for the intrinsic forms

The chart equivalence transports the existing coordinate local primitives
to the original manifold topology. In degree zero it transports local
constancy. Both use the same coordinate forms and exterior derivatives.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicAtlas

open TopologicalSpace
open scoped Manifold ContDiff
open HolomorphicForms

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The same coordinate constant sections, as a compatible intrinsic family. -/
def constant (U : Opens M) : ℂ →ₗ[ℂ] Forms E U 0 where
  toFun c := ⟨fun e ↦ HolomorphicDeRham.constant (domain e U) c, by
    intro e e'
    apply ContMDiffMap.ext
    intro z
    apply ContinuousAlternatingMap.ext
    intro v
    rfl⟩
  map_add' c d := Subtype.ext (funext fun e ↦ map_add _ c d)
  map_smul' c d := Subtype.ext (funext fun e ↦ map_smul _ c d)

@[simp]
theorem inChart_constant (U : Opens M) (e : Chart E M) (c : ℂ) :
    inChart U 0 e (constant U c) = HolomorphicDeRham.constant (domain e U) c := rfl

theorem differential_constant (U : Opens M) (c : ℂ) :
    differential U 0 (constant (E := E) U c) = 0 := by
  apply Subtype.ext
  funext e
  exact HolomorphicDeRham.differential_constant (domain e U) c

theorem restrict_constant {U V : Opens M} (h : V ≤ U) (c : ℂ) :
    restrict h 0 (constant (E := E) U c) = constant V c := by
  apply Subtype.ext
  funext e
  apply ContMDiffMap.ext
  intro z
  rfl

theorem constant_injective (U : Opens M) (hU : (U : Set M).Nonempty) :
    Function.Injective (constant (E := E) U) := by
  obtain ⟨p, hp⟩ := hU
  let e : Chart E M := ⟨chartAt E p, chart_mem_atlas E p⟩
  have hps : p ∈ e.1.source := mem_chart_source E p
  let z : domain e U := ⟨e.1 p, e.1.map_source hps, by
    change e.1.symm (e.1 p) ∈ U
    rw [e.1.left_inv hps]
    exact hp⟩
  intro a b hab
  exact congrArg (fun η : Forms E U 0 ↦ zeroCoeffEquiv (η.1 e z)) hab

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Closed intrinsic forms have actual local primitives in every positive degree. -/
theorem locally_exact_positive {U : Opens M} (n : ℕ) (η : Forms E U (n + 1))
    (hη : differential U (n + 1) η = 0) (p : U) :
    ∃ (W : Opens M) (hWU : W ≤ U), (p : M) ∈ W ∧
      ∃ β : Forms E W n, differential W n β = restrict hWU (n + 1) η := by
  let e : Chart E M := ⟨chartAt E (p : M), chart_mem_atlas E (p : M)⟩
  let U' := U ⊓ source e
  have hps : (p : M) ∈ e.1.source := mem_chart_source E (p : M)
  let η' := restrict (show U' ≤ U from inf_le_left) (n + 1) η
  have hd : differential U' (n + 1) η' = 0 := by
    rw [← restrict_differential, hη, map_zero]
  let z : domain e U' := ⟨e.1 p, e.1.map_source hps, by
    change e.1.symm (e.1 p) ∈ U'
    rw [e.1.left_inv hps]
    exact ⟨p.2, hps⟩⟩
  have hdc : HolomorphicForms.differential (domain e U') (n + 1)
      (inChart U' (n + 1) e η') = 0 := by
    rw [← inChart_differential, hd, map_zero]
  obtain ⟨V, hV, hzV, α, hα⟩ := HolomorphicForms.locally_exact_positive n
    (inChart U' (n + 1) e η') hdc z
  let W := coordinateOpen e V
  have hWU' : W ≤ U' := coordinateOpen_le e hV
  have hWU : W ≤ U := hWU'.trans inf_le_left
  have hWs : W ≤ source e := coordinateOpen_le_source e V
  let hD := domain_coordinateOpen_le e V
  refine ⟨W, hWU, ⟨hps, hzV⟩,
    fromChart e hWs n (HolomorphicForms.restrict hD n α), ?_⟩
  apply inChart_injective e hWs (n + 1)
  rw [inChart_differential, inChart_fromChart]
  rw [← HolomorphicForms.restrict_differential, hα]
  apply ContMDiffMap.ext
  intro q
  rfl

omit [IsScalarTower ℝ ℂ E] in
/-- The intrinsic degree-zero kernel consists locally of the same complex constants. -/
theorem locally_constant_zero {U : Opens M} (η : Forms E U 0)
    (hη : differential U 0 η = 0) (p : U) :
    ∃ (W : Opens M) (hWU : W ≤ U), (p : M) ∈ W ∧
      ∃ c : ℂ, restrict hWU 0 η = constant W c := by
  let e : Chart E M := ⟨chartAt E (p : M), chart_mem_atlas E (p : M)⟩
  let U' := U ⊓ source e
  have hps : (p : M) ∈ e.1.source := mem_chart_source E (p : M)
  let η' := restrict (show U' ≤ U from inf_le_left) 0 η
  have hd : differential U' 0 η' = 0 := by
    rw [← restrict_differential, hη, map_zero]
  let z : domain e U' := ⟨e.1 p, e.1.map_source hps, by
    change e.1.symm (e.1 p) ∈ U'
    rw [e.1.left_inv hps]
    exact ⟨p.2, hps⟩⟩
  have hdc : HolomorphicForms.differential (domain e U') 0 (inChart U' 0 e η') = 0 := by
    rw [← inChart_differential, hd, map_zero]
  obtain ⟨V, hV, hzV, c, hc⟩ := HolomorphicForms.locally_constant_zero (inChart U' 0 e η') hdc z
  let W := coordinateOpen e V
  have hWU' : W ≤ U' := coordinateOpen_le e hV
  have hWU : W ≤ U := hWU'.trans inf_le_left
  have hWs : W ≤ source e := coordinateOpen_le_source e V
  let hD := domain_coordinateOpen_le e V
  refine ⟨W, hWU, ⟨hps, hzV⟩, c, ?_⟩
  apply inChart_injective e hWs 0
  rw [inChart_constant]
  apply (functionsEquiv (domain e W)).injective
  apply ContMDiffMap.ext
  intro q
  exact hc ⟨q.1, hD q.2⟩

end HodgeConjecture.HolomorphicAtlas
