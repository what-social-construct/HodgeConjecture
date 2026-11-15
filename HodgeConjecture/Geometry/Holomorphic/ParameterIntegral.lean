module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.Deriv.Linear

@[expose] public section

/-!
# Complex smoothness of parameter integrals

Integrating a complex smooth family along the fixed real unit interval
preserves complex smoothness in the other variables. The hypotheses are
local along the interval; the family need not extend smoothly everywhere.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open Set Filter MeasureTheory
open scoped Topology ContDiff

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Real restriction of a complex derivative, for vector-valued coefficients. -/
theorem hasDerivAt_comp_ofReal {g : ℂ → V} {g' : V} {t : ℝ}
    (hg : HasDerivAt g g' (t : ℂ)) :
    HasDerivAt (fun s : ℝ ↦ g (s : ℂ)) g' t := by
  simpa only [Complex.ofRealCLM_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, Complex.ofReal_one, one_smul,
    Function.comp_def] using
    (hg.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t Complex.ofRealCLM.hasDerivAt

/-- The complex derivative in the parameter that is not integrated out. -/
def parameterDerivative (F : E × ℂ → V) (p : E × ℂ) : E →L[ℂ] V :=
  (fderiv ℂ F p).comp (ContinuousLinearMap.inl ℂ E ℂ)

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem contDiffAt_parameterDerivative {F : E × ℂ → V} {p : E × ℂ}
    (hF : ContDiffAt ℂ ∞ F p) : ContDiffAt ℂ ∞ (parameterDerivative F) p :=
  (hF.fderiv_right (by simp)).clm_comp contDiffAt_const

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem parameterDerivative_eq_fderiv_slice {F : E × ℂ → V} {p : E × ℂ}
    (hF : DifferentiableAt ℂ F p) :
    parameterDerivative F p = fderiv ℂ (fun y ↦ F (y, p.2)) p.1 := by
  symm
  have he : (ContinuousLinearMap.id ℂ E).prod (0 : E →L[ℂ] ℂ) =
      ContinuousLinearMap.inl ℂ E ℂ := by ext <;> rfl
  simpa only [parameterDerivative, Function.comp_def, id_eq, he] using
    (hF.hasFDerivAt.comp p.1
      ((hasFDerivAt_id (𝕜 := ℂ) p.1).prodMk (hasFDerivAt_const p.2 p.1))).fderiv

omit [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] in
theorem intervalIntegrable_parameterDerivative (F : E × ℂ → V) (x : E)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℂ ∞ F (x, (t : ℂ))) :
    IntervalIntegrable (fun t : ℝ ↦ parameterDerivative F (x, (t : ℂ))) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  intro t ht
  exact ((contDiffAt_parameterDerivative (hF t ht)).continuousAt.comp
    (f := fun s : ℝ ↦ (x, (s : ℂ))) (by fun_prop)).continuousWithinAt

/-- Differentiation under the actual integral, using compactness of the interval. -/
theorem hasFDerivAt_parameterIntegral {U : Set E} (hU : IsOpen U)
    (F : E × ℂ → V)
    (hF : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℂ ∞ F (x, (t : ℂ)))
    {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ t : ℝ in 0..1, F (y, (t : ℂ)))
      (∫ t : ℝ in 0..1, parameterDerivative F (x, (t : ℂ))) x := by
  have hI : uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have hG (y : E) (hy : y ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℂ ∞ (parameterDerivative F) (y, (t : ℂ)) := by
    exact contDiffAt_parameterDerivative (hF y hy t ht)
  have hGc (y : E) (hy : y ∈ U) :
      ContinuousOn (fun t : ℝ ↦ parameterDerivative F (y, (t : ℂ))) (Icc 0 1) := by
    intro t ht
    exact ((hG y hy t ht).continuousAt.comp (f := fun s : ℝ ↦ (y, (s : ℂ)))
      (show ContinuousAt (fun s : ℝ ↦ (y, (s : ℂ))) t by fun_prop)).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hGc x hx)
  have hb : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖parameterDerivative F (y, (t : ℂ))‖ ≤ B + 1 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hc := (hG x hx t ht).continuousAt.comp (f := fun p : E × ℝ ↦ (p.1, (p.2 : ℂ)))
      (show ContinuousAt (fun p : E × ℝ ↦ (p.1, (p.2 : ℂ))) (x, t) by fun_prop)
    exact (hc.norm.eventually_lt_const ((hB t ht).trans_lt (lt_add_one B))).mono
      (fun _ h ↦ h.le)
  let s := U ∩ {y | ∀ t ∈ Icc (0 : ℝ) 1, ‖parameterDerivative F (y, (t : ℂ))‖ ≤ B + 1}
  have hs : s ∈ 𝓝 x := inter_mem (hU.mem_nhds hx) hb
  have hFc (y : E) (hy : y ∈ U) :
      ContinuousOn (fun t : ℝ ↦ F (y, (t : ℂ))) (uIcc 0 1) := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro t ht
    exact ((hF y hy t ht).continuousAt.comp (f := fun s : ℝ ↦ (y, (s : ℂ)))
      (show ContinuousAt (fun s : ℝ ↦ (y, (s : ℂ))) t by fun_prop)).continuousWithinAt
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := s) (bound := fun _ ↦ B + 1) hs
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact ((hFc y hy).aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc
  · exact (hFc x hx).intervalIntegrable
  · exact ((hGc x hx).mono hI).aestronglyMeasurable measurableSet_uIoc
  · exact ae_of_all _ (fun t ht y hy ↦ hy.2 t (hI ht))
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro t ht y hy
    have hd := (hF y hy.1 t (hI ht)).differentiableAt (by simp)
    simpa only [parameterDerivative, ContinuousLinearMap.comp_apply, Function.comp_def] using
      hd.hasFDerivAt.comp y ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (t : ℂ) y))

/-- Fixed-interval integration preserves the original complex C∞ regularity. -/
theorem contDiffOn_parameterIntegral {U : Set E} (hU : IsOpen U)
    (F : E × ℂ → V)
    (hF : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℂ ∞ F (x, (t : ℂ))) :
    ContDiffOn ℂ ∞ (fun y ↦ ∫ t : ℝ in 0..1, F (y, (t : ℂ))) U := by
  rw [contDiffOn_infty]
  intro n
  induction n generalizing V with
  | zero =>
    exact contDiffOn_zero.mpr (fun x hx ↦
      (hasFDerivAt_parameterIntegral hU F hF hx).continuousAt.continuousWithinAt)
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx ↦ (hasFDerivAt_parameterIntegral hU F hF hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hG : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
        ContDiffAt ℂ ∞ (parameterDerivative F) (x, (t : ℂ)) := by
      intro x hx t ht
      exact contDiffAt_parameterDerivative (hF x hx t ht)
    apply (ih (parameterDerivative F) hG).congr
    intro x hx
    exact (hasFDerivAt_parameterIntegral hU F hF hx).fderiv

end HodgeConjecture.HolomorphicForms
