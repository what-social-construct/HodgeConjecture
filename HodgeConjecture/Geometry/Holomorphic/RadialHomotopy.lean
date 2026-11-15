module

public import HodgeConjecture.Geometry.Holomorphic.Contraction
public import HodgeConjecture.Geometry.Holomorphic.ParameterIntegral
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

@[expose] public section

/-!
# The radial homotopy on holomorphic forms

In positive degree `n + 1` the operator is the actual integral
`∫ t in 0..1, t^n • ι_(x-a) η(a+t • (x-a))`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open TopologicalSpace Set Filter ContinuousAlternatingMap
open scoped Manifold ContDiff Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {n : ℕ}

/-- The radial contraction, with a complex parameter for checking holomorphicity. -/
def radialMap (a : E) (p : E × ℂ) : E := a + p.2 • (p.1 - a)

/-- The degree-dependent weight is forced by the original exterior derivative. -/
def radialIntegrand (a : E) (f : E → Coeff E (n + 1)) (p : E × ℂ) : Coeff E n :=
  p.2 ^ n • contraction (p.1 - a) (f (radialMap a p))

/-- The actual radial integral, in the original coefficient space. -/
def radialIntegral (a : E) (f : E → Coeff E (n + 1)) (x : E) : Coeff E n :=
  ∫ t : ℝ in 0..1, radialIntegrand a f (x, (t : ℂ))

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem contDiff_radialMap (a : E) : ContDiff ℂ ∞ (radialMap a) := by
  exact contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem contDiffAt_radialIntegrand (a : E) {f : E → Coeff E (n + 1)} {p : E × ℂ}
    (hf : ContDiffAt ℂ ∞ f (radialMap a p)) :
    ContDiffAt ℂ ∞ (radialIntegrand a f) p := by
  have hc : ContDiffAt ℂ ∞ (fun p : E × ℂ ↦ (f (radialMap a p)).curryLeft) p :=
    contDiff_curryLeft.contDiffAt.comp p (hf.comp p (contDiff_radialMap a).contDiffAt)
  exact (contDiff_snd.contDiffAt.pow n).smul
    (hc.clm_apply (contDiff_fst.contDiffAt.sub contDiffAt_const))

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
/-- Differentiating a radial slice only scales the derivative of the form. -/
theorem hasFDerivAt_radialSlice (a : E) (t : ℂ)
    {f : E → Coeff E (n + 1)} {x : E}
    (hf : DifferentiableAt ℂ f (radialMap a (x, t))) :
    HasFDerivAt (fun y : E ↦ f (radialMap a (y, t)))
      (t • fderiv ℂ f (radialMap a (x, t))) x := by
  have hr : HasFDerivAt (fun y : E ↦ radialMap a (y, t))
      (t • ContinuousLinearMap.id ℂ E) x := by
    simpa only [radialMap, id_eq, Pi.smul_apply] using
      (((hasFDerivAt_id x).sub_const a).const_smul t).const_add a
  have hd := hf.hasFDerivAt.comp x hr
  simpa only [Function.comp_def, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_id] using hd

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
/-- The pointwise homotopy identity before integration. -/
theorem extDeriv_radialIntegrand (a : E) (t : ℂ)
    {f : E → Coeff E (n + 1)} {x : E}
    (hf : DifferentiableAt ℂ f (radialMap a (x, t))) :
    extDeriv (fun y : E ↦ radialIntegrand a f (y, t)) x +
        t ^ (n + 1) • contraction (x - a) (extDeriv f (radialMap a (x, t))) =
      t ^ n • ((n + 1) • f (radialMap a (x, t)) +
        t • fderiv ℂ f (radialMap a (x, t)) (x - a)) := by
  let g : E → Coeff E (n + 1) := fun y ↦ f (radialMap a (y, t))
  have hg := hasFDerivAt_radialSlice a t hf
  have hd : extDeriv g x = t • extDeriv f (radialMap a (x, t)) := by
    rw [extDeriv, hg.fderiv, alternatizeUncurryFin_smul]
    rfl
  have he := extDeriv_eulerContraction hg.differentiableAt a
  rw [hd, hg.fderiv] at he
  change extDeriv (t ^ n • eulerContraction a g) x + _ = _
  rw [extDeriv_smul]
  have h := congrArg (fun α : Coeff E (n + 1) ↦ t ^ n • α) he
  simpa only [map_smul, _root_.smul_apply, smul_add, smul_smul, pow_succ, g] using h

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
/-- The time derivative whose endpoint difference recovers the original form. -/
theorem hasDerivAt_weightedRadial (a x : E) {f : E → Coeff E (n + 1)} {t : ℂ}
    (hf : DifferentiableAt ℂ f (radialMap a (x, t))) :
    HasDerivAt (fun z : ℂ ↦ z ^ (n + 1) • f (radialMap a (x, z)))
      (t ^ n • ((n + 1) • f (radialMap a (x, t)) +
        t • fderiv ℂ f (radialMap a (x, t)) (x - a))) t := by
  have hr : HasDerivAt (fun z : ℂ ↦ radialMap a (x, z)) (x - a) t := by
    simpa only [radialMap, one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const (x - a)).const_add a
  have h := (hasDerivAt_pow (n + 1) t).smul (hf.hasFDerivAt.comp_hasDerivAt t hr)
  convert h using 1
  · rfl
  · simp only [Function.comp_def, Nat.add_sub_cancel, smul_add, smul_smul, pow_succ]
    rw [← Nat.cast_smul_eq_nsmul ℂ (n + 1)]
    simp only [smul_smul]
    module

/-- On the real interval, the complex radial parameter is the native segment parameter. -/
theorem radialMap_ofReal (a x : E) (t : ℝ) :
    radialMap a (x, (t : ℂ)) = AffineMap.lineMap a x t := by
  rw [AffineMap.lineMap_apply_module']
  change a + (t : ℂ) • (x - a) = t • (x - a) + a
  have hs : (t : ℂ) • (x - a) = t • (x - a) :=
    IsScalarTower.algebraMap_smul ℂ t (x - a)
  rw [hs]
  exact add_comm a (t • (x - a))

/-- All points of the real radial segment stay in a convex coordinate open. -/
theorem radialMap_mem {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a x : U) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : radialMap (a : E) ((x : E), (t : ℂ)) ∈ U := by
  rw [radialMap_ofReal]
  exact hU.lineMap_mem a.2 x.2 ht

/-- Integrating the native coefficients gives holomorphic coefficients again. -/
theorem contDiffOn_radialIntegral {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (η : Sections U (n + 1)) :
    ContDiffOn ℂ ∞ (radialIntegral (a : E) (extend η)) U := by
  apply contDiffOn_parameterIntegral U.isOpen
  intro x hx t ht
  exact contDiffAt_radialIntegrand (a : E)
    (contDiffAt_extend η ⟨radialMap (a : E) (x, (t : ℂ)), radialMap_mem hU a ⟨x, hx⟩ ht⟩)

/-- The radial homotopy uses the same bundled holomorphic sections as the complex. -/
def radialHomotopy {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (n : ℕ) (η : Sections U (n + 1)) : Sections U n :=
  ⟨fun x ↦ radialIntegral (a : E) (extend η) x,
    contMDiff_restrict (fun _ hx ↦
      (contDiffOn_radialIntegral hU a η).contDiffAt (U.isOpen.mem_nhds hx))⟩

/-- The radial homotopy identity on the original complex, in every positive degree. -/
theorem differential_radialHomotopy {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (n : ℕ) (η : Sections U (n + 1)) :
    differential U n (radialHomotopy hU a n η) +
      radialHomotopy hU a (n + 1) (differential U (n + 1) η) = η := by
  apply ContMDiffMap.ext
  intro x
  let f := extend η
  let R := radialIntegrand (a : E) f
  let S := radialIntegrand (a : E) (extend (differential U (n + 1) η))
  let A : ℝ → Coeff E (n + 1) := fun t ↦
    alternatizeUncurryFin (parameterDerivative R ((x : E), (t : ℂ)))
  let B : ℝ → Coeff E (n + 1) := fun t ↦ S ((x : E), (t : ℂ))
  have hR (y : E) (hy : y ∈ U) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℂ ∞ R (y, (t : ℂ)) :=
    contDiffAt_radialIntegrand (a : E)
      (contDiffAt_extend η ⟨_, radialMap_mem hU a ⟨y, hy⟩ ht⟩)
  have hS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℂ ∞ S ((x : E), (t : ℂ)) :=
    contDiffAt_radialIntegrand (a : E)
      (contDiffAt_extend (differential U (n + 1) η) ⟨_, radialMap_mem hU a x ht⟩)
  have hAc : ContinuousOn A (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    exact ((alternatizeUncurryFinCLM ℂ E ℂ).continuous.continuousAt.comp
      ((contDiffAt_parameterDerivative (hR x x.2 t ht)).continuousAt.comp
        (f := fun s : ℝ ↦ ((x : E), (s : ℂ))) (by fun_prop))).continuousWithinAt
  have hBc : ContinuousOn B (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    exact ((hS t ht).continuousAt.comp
      (f := fun s : ℝ ↦ ((x : E), (s : ℂ))) (by fun_prop)).continuousWithinAt
  have hdK : differential U n (radialHomotopy hU a n η) x = ∫ t in 0..1, A t := by
    rw [differential_eq_of_extension _ (radialIntegral (a : E) f) (fun _ ↦ rfl)]
    change alternatizeUncurryFin (fderiv ℂ (fun y ↦ ∫ t : ℝ in 0..1, R (y, (t : ℂ))) (x : E)) = _
    rw [(hasFDerivAt_parameterIntegral U.isOpen R hR x.2).fderiv]
    exact ((alternatizeUncurryFinCLM ℂ E ℂ).intervalIntegral_comp_comm
      (intervalIntegrable_parameterDerivative R (x : E) (hR x x.2))).symm
  let q : ℝ → Coeff E (n + 1) := fun t ↦
    (t : ℂ) ^ (n + 1) • f (radialMap (a : E) ((x : E), (t : ℂ)))
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 1 q t := by
    have hp := contDiffAt_extend η ⟨_, radialMap_mem hU a x ht⟩
    have hr : ContDiff ℂ ∞ (fun z : ℂ ↦ radialMap (a : E) ((x : E), z)) :=
      (contDiff_radialMap (a : E)).comp (contDiff_const.prodMk contDiff_id)
    have hh := (contDiff_id.contDiffAt.pow (n + 1)).smul
      (hp.comp (t : ℂ) hr.contDiffAt)
    exact ((hh.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt).of_le (by simp)
  have hAB (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) : A t + B t = deriv q t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hm := radialMap_mem hU a x ht'
    have hf := (contDiffAt_extend η ⟨_, hm⟩).differentiableAt (by simp)
    have hA : A t = extDeriv (fun y : E ↦ R (y, (t : ℂ))) (x : E) := by
      dsimp only [A]
      rw [parameterDerivative_eq_fderiv_slice ((hR x x.2 t ht').differentiableAt (by simp))]
      rfl
    have hB : B t = (t : ℂ) ^ (n + 1) •
        contraction ((x : E) - a) (extDeriv f (radialMap (a : E) ((x : E), (t : ℂ)))) := by
      change (t : ℂ) ^ (n + 1) • contraction ((x : E) - a)
        (extend (differential U (n + 1) η) _) = _
      rw [extend_of_mem _ ⟨_, hm⟩]
      rfl
    rw [hA, hB]
    have htq : HasDerivAt q
        ((t : ℂ) ^ n • ((n + 1) • f (radialMap (a : E) ((x : E), (t : ℂ))) +
          (t : ℂ) • fderiv ℂ f (radialMap (a : E) ((x : E), (t : ℂ))) ((x : E) - a))) t := by
      simpa only [q, f] using
        hasDerivAt_comp_ofReal (hasDerivAt_weightedRadial (a : E) (x : E) (t := (t : ℂ)) hf)
    exact (extDeriv_radialIntegrand (a : E) (t : ℂ) hf).trans htq.deriv.symm
  change differential U n (radialHomotopy hU a n η) x + radialIntegral (a : E)
    (extend (differential U (n + 1) η)) x = η x
  rw [hdK]
  change (∫ t in 0..1, A t) + (∫ t in 0..1, B t) = η x
  rw [← intervalIntegral.integral_add hAc.intervalIntegrable hBc.intervalIntegrable,
    intervalIntegral.integral_congr hAB,
    intervalIntegral.integral_deriv_of_contDiffOn_Icc (fun t ht ↦ (hq t ht).contDiffWithinAt) zero_le_one]
  simp only [q, f, radialMap, Complex.ofReal_one, Complex.ofReal_zero, one_pow,
    zero_pow (Nat.succ_ne_zero n), one_smul, zero_smul, add_sub_cancel,
    add_zero, extend_of_mem]
  have hz : (0 : ℂ) • η a = 0 := by
    ext v
    change (0 : ℂ) * η a v = 0
    exact zero_mul _
  rw [hz, sub_zero]

/-- Every closed positive-degree form has the constructed holomorphic radial primitive. -/
theorem differential_radialHomotopy_of_closed {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (n : ℕ) (η : Sections U (n + 1)) (hη : differential U (n + 1) η = 0) :
    differential U n (radialHomotopy hU a n η) = η := by
  have h := differential_radialHomotopy hU a n η
  have hz : radialHomotopy hU a (n + 1) (0 : Sections U (n + 2)) = 0 := by
    apply ContMDiffMap.ext
    intro x
    simp [radialHomotopy, radialIntegral, radialIntegrand, extend, contraction]
  rw [hη, hz, add_zero] at h
  exact h

/-- Local Poincaré exactness in every positive degree and every coordinate dimension. -/
theorem locally_exact_positive {U : Opens E} (n : ℕ) (η : Sections U (n + 1))
    (hη : differential U (n + 1) η = 0) (x : U) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∃ f : Sections V n, differential V n f = restrict hVU (n + 1) η := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp U.isOpen x x.2
  let V : Opens E := ⟨Metric.ball (x : E) r, Metric.isOpen_ball⟩
  have hVU : V ≤ U := hsub
  have hx : (x : E) ∈ V := Metric.mem_ball_self hr
  have hd : differential V (n + 1) (restrict hVU (n + 1) η) = 0 := by
    rw [← restrict_differential, hη, _root_.map_zero]
  exact ⟨V, hVU, hx, radialHomotopy (convex_ball (x : E) r) ⟨(x : E), hx⟩ n
    (restrict hVU (n + 1) η),
    differential_radialHomotopy_of_closed (convex_ball (x : E) r) ⟨(x : E), hx⟩ n _ hd⟩

end HodgeConjecture.HolomorphicForms
