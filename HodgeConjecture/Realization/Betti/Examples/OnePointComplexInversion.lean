module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

/-!
# Inversion on the complex projective line

Complex inversion exchanges zero and infinity in the ordinary one-point
compactification. Continuity follows from the native punctured-neighborhood
and cocompact limits of inversion in the complex plane.
-/

set_option autoImplicit false

namespace HodgeConjecture.OnePointComplex

noncomputable section

open Filter Topology OnePoint

/-- Inversion with its natural values at zero and infinity. -/
def inversion (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ)
    (fun z : ℂ ↦ if z = 0 then ∞ else ((z⁻¹ : ℂ) : OnePoint ℂ))

@[simp]
theorem inversion_infty : inversion ∞ = (0 : ℂ) := rfl

@[simp]
theorem inversion_coe_zero : inversion ((0 : ℂ) : OnePoint ℂ) = ∞ := by
  simp [inversion]

theorem inversion_coe (z : ℂ) :
    inversion (z : OnePoint ℂ) = if z = 0 then ∞ else ↑z⁻¹ := rfl

@[simp]
theorem inversion_coe_of_ne_zero (z : ℂ) (hz : z ≠ 0) :
    inversion (z : OnePoint ℂ) = (z⁻¹ : ℂ) := by
  simp [inversion, hz]

theorem inversion_involutive : Function.Involutive inversion := by
  intro z
  induction z using OnePoint.rec with
  | infty => simp
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp
    · simp [inversion_coe_of_ne_zero, hz]

@[simp]
theorem inversion_inversion (z : OnePoint ℂ) : inversion (inversion z) = z :=
  inversion_involutive z

/-- At a puncture, complex inversion tends to the point at infinity. -/
theorem tendsto_inversion_coe_zero :
    Tendsto (fun z : ℂ ↦ inversion (z : OnePoint ℂ))
      (𝓝[≠] 0) (𝓝 (∞ : OnePoint ℂ)) := by
  have hi : Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ))
      (𝓝[≠] 0) (𝓝 (∞ : OnePoint ℂ)) := by
    apply OnePoint.tendsto_coe_infty.comp
    simpa only [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact]
      using (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ))
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
  simp [hz]

/-- At infinity, complex inversion tends to zero. -/
theorem tendsto_inversion_coe_infty :
    Tendsto (fun z : ℂ ↦ inversion (z : OnePoint ℂ))
      (coclosedCompact ℂ) (𝓝 ((0 : ℂ) : OnePoint ℂ)) := by
  have hi : Tendsto (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ))
      (Bornology.cobounded ℂ) (𝓝 ((0 : ℂ) : OnePoint ℂ)) :=
    OnePoint.continuous_coe.continuousAt.tendsto.comp Filter.tendsto_inv₀_cobounded
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  apply hi.congr'
  filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
  simp [hz]

/-- Inversion is continuous for the native compactification topology. -/
theorem continuous_inversion : Continuous inversion := by
  rw [OnePoint.continuous_iff]
  refine ⟨by simpa using tendsto_inversion_coe_infty,
    continuous_iff_continuousAt.mpr ?_⟩
  intro z
  by_cases hz : z = 0
  · subst z
    simp only [ContinuousAt, inversion_coe_zero]
    rw [← nhdsNE_sup_pure]
    exact tendsto_inversion_coe_zero.sup (by
      simpa using (tendsto_pure_nhds (fun z : ℂ ↦ inversion (z : OnePoint ℂ)) 0))
  · have hi : ContinuousAt (fun z : ℂ ↦ ((z⁻¹ : ℂ) : OnePoint ℂ)) z :=
      OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
    apply hi.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with w hw
    simp [hw]

/-- The second affine chart is continuous, including at its pole. -/
theorem continuous_inversion_coe :
    Continuous (fun z : ℂ ↦ inversion (z : OnePoint ℂ)) :=
  continuous_inversion.comp OnePoint.continuous_coe

/-- The projective chart transition `z ↦ 1 / z`, exchanging zero and infinity. -/
def inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ where
  toFun := inversion
  invFun := inversion
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  continuous_toFun := continuous_inversion
  continuous_invFun := continuous_inversion

@[simp]
theorem inversionHomeomorph_apply (z : OnePoint ℂ) :
    inversionHomeomorph z = inversion z := rfl

@[simp]
theorem inversionHomeomorph_symm : inversionHomeomorph.symm = inversionHomeomorph := rfl

end

end HodgeConjecture.OnePointComplex
