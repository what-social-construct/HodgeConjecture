module

public import HodgeConjecture.Geometry.Holomorphic.LowDegree
public import HodgeConjecture.Geometry.Holomorphic.RadialHomotopy
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

@[expose] public section

/-!
# Holomorphic primitives from the actual segment integral

On a convex coordinate open, a closed holomorphic one-form admits a
holomorphic primitive. The primitive is the native integral along the
segment from the chosen base point, normalized to vanish there. This
proves local exactness in degree one in every complex dimension.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open TopologicalSpace Filter
open scoped Manifold ContDiff Topology

-- Retain the self-scalar structure used by the original coefficient maps.
local instance : NormedSpace ℂ ℂ := NormedField.toNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The original integral along the actual segment, without a chosen primitive witness. -/
def segmentPrimitive (U : Opens E) (a : E) (η : Sections U 1) (x : E) : ℂ :=
  curveIntegral (extend (oneFormsEquiv U η)) (Path.segment a x)

omit [IsScalarTower ℝ ℂ E] in
@[simp]
theorem segmentPrimitive_self (U : Opens E) (a : E) (η : Sections U 1) :
    segmentPrimitive U a η a = 0 := by
  simp [segmentPrimitive, Path.segment_same, curveIntegral_refl]

/-- The computed segment primitive has the original complex one-form as derivative. -/
theorem hasFDerivAt_segmentPrimitive {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (η : Sections U 1) (hη : differential U 1 η = 0) (x : U) :
    HasFDerivAt (segmentPrimitive U a η) (oneFormsEquiv U η x) x := by
  have hc (y : U) := (contDiffAt_extend (oneFormsEquiv U η) y).differentiableAt (by simp)
  have hd : ∀ y ∈ U, HasFDerivWithinAt (extend (oneFormsEquiv U η))
      (fderiv ℝ (extend (oneFormsEquiv U η)) y) U y := by
    intro y hy
    exact ((hc ⟨y, hy⟩).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hs : ∀ y ∈ U, ∀ v ∈ tangentConeAt ℝ (U : Set E) y,
      ∀ w ∈ tangentConeAt ℝ (U : Set E) y,
      fderiv ℝ (extend (oneFormsEquiv U η)) y v w =
        fderiv ℝ (extend (oneFormsEquiv U η)) y w v := by
    intro y hy v _ w _
    rw [(hc ⟨y, hy⟩).fderiv_restrictScalars ℝ]
    exact closed_one_symmetric η hη ⟨y, hy⟩ v w
  have h := hU.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
    hd hs a.2 x.2
  have hd' := h.hasFDerivAt (U.isOpen.mem_nhds x.2)
  apply HasFDerivAt.of_isLittleO
  simpa only [segmentPrimitive, extend_of_mem] using hd'.isLittleO

/-- The actual primitive is holomorphic on the whole convex coordinate open. -/
theorem contDiffOn_segmentPrimitive {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (η : Sections U 1) (hη : differential U 1 η = 0) :
    ContDiffOn ℂ ∞ (segmentPrimitive U a η) U := by
  rw [contDiffOn_infty_iff_fderiv_of_isOpen U.isOpen]
  refine ⟨fun x hx ↦ (hasFDerivAt_segmentPrimitive hU a η hη ⟨x, hx⟩).differentiableAt.differentiableWithinAt, ?_⟩
  have hc : ContDiffOn ℂ ∞ (extend (oneFormsEquiv U η)) U :=
    fun x hx ↦ (contDiffAt_extend (oneFormsEquiv U η) ⟨x, hx⟩).contDiffWithinAt
  apply hc.congr
  intro x hx
  change fderiv ℂ (segmentPrimitive U a η) x = _
  rw [extend_of_mem _ ⟨x, hx⟩]
  exact (hasFDerivAt_segmentPrimitive hU a η hη ⟨x, hx⟩).fderiv

/-- The normalized primitive as an actual zero-form section of the same complex. -/
def primitive {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (η : Sections U 1) (hη : differential U 1 η = 0) : Sections U 0 :=
  (functionsEquiv U).symm ⟨fun x ↦ segmentPrimitive U a η x,
    contMDiff_restrict (fun _ hx ↦
      (contDiffOn_segmentPrimitive hU a η hη).contDiffAt (U.isOpen.mem_nhds hx))⟩

/-- Poincaré exactness, with the actual integral primitive as the witness. -/
theorem differential_primitive {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (η : Sections U 1) (hη : differential U 1 η = 0) :
    differential U 0 (primitive hU a η hη) = η := by
  apply (oneFormsEquiv U).injective
  apply ContMDiffMap.ext
  intro x
  rw [primitive, oneFormsEquiv_differential]
  change fderiv ℂ (extend (fun y : U ↦ segmentPrimitive U a η y)) (x : E) = _
  have he : extend (fun x : U ↦ segmentPrimitive U a η x) =ᶠ[𝓝 (x : E)]
      segmentPrimitive U a η := extend_eventuallyEq _ x.2 _ (fun _ ↦ rfl)
  have hd : fderiv ℂ (extend (fun y : U ↦ segmentPrimitive U a η y)) (x : E) =
      fderiv ℂ (segmentPrimitive U a η) x := he.fderiv_eq
  exact hd.trans (hasFDerivAt_segmentPrimitive hU a η hη x).fderiv

/-- Every closed one-form is exact after shrinking to a ball in its original open. -/
theorem locally_exact_one {U : Opens E} (η : Sections U 1)
    (hη : differential U 1 η = 0) (x : U) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∃ f : Sections V 0, differential V 0 f = restrict hVU 1 η := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp U.isOpen x x.2
  let V : Opens E := ⟨Metric.ball (x : E) r, Metric.isOpen_ball⟩
  have hVU : V ≤ U := hsub
  have hx : (x : E) ∈ V := Metric.mem_ball_self hr
  have hd : differential V 1 (restrict hVU 1 η) = 0 := by
    rw [← restrict_differential, hη, map_zero]
  exact ⟨V, hVU, hx, primitive (convex_ball (x : E) r) ⟨(x : E), hx⟩ (restrict hVU 1 η) hd,
    differential_primitive (convex_ball (x : E) r) ⟨(x : E), hx⟩ (restrict hVU 1 η) hd⟩

/-- The general radial operator in degree one is the original segment integral. -/
theorem radialIntegral_zero_eq_segmentPrimitive {U : Opens E}
    (hU : Convex ℝ (U : Set E)) (a : U) (η : Sections U 1) (x : U) :
    zeroCoeffEquiv (radialIntegral (a : E) (extend η) x) = segmentPrimitive U a η x := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ radialIntegrand (a : E) (extend η) ((x : E), (t : ℂ)))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    intro t ht
    have hc := contDiffAt_radialIntegrand (a : E)
      (contDiffAt_extend η ⟨_, radialMap_mem hU a x ht⟩)
    exact (hc.continuousAt.comp (f := fun s : ℝ ↦ ((x : E), (s : ℂ)))
      (by fun_prop)).continuousWithinAt
  change zeroCoeffEquiv.toContinuousLinearMap
    (∫ t : ℝ in 0..1, radialIntegrand (a : E) (extend η) ((x : E), (t : ℂ))) = _
  rw [← zeroCoeffEquiv.toContinuousLinearMap.intervalIntegral_comp_comm hi,
    segmentPrimitive, curveIntegral_segment]
  apply intervalIntegral.integral_congr
  intro t _
  have he : extend (oneFormsEquiv U η) = oneCoeffEquiv ∘ extend η :=
    extend_coefficientEquiv U oneCoeffEquiv η
  rw [he]
  change zeroCoeffEquiv (radialIntegrand (a : E) (extend η) ((x : E), (t : ℂ))) =
    oneCoeffEquiv (extend η (AffineMap.lineMap (a : E) (x : E) t)) ((x : E) - a)
  rw [← radialMap_ofReal]
  change zeroCoeffEquiv ((t : ℂ) ^ 0 • contraction ((x : E) - a) _) =
    oneCoeffEquiv _ ((x : E) - a)
  rw [pow_zero, one_smul, oneCoeffEquiv_apply, zeroCoeffEquiv_apply,
    contraction_apply, ContinuousAlternatingMap.curryLeft_apply_apply]

/-- The previous normalized primitive and the general radial primitive are the same section. -/
theorem radialHomotopy_zero_eq_primitive {U : Opens E} (hU : Convex ℝ (U : Set E))
    (a : U) (η : Sections U 1) (hη : differential U 1 η = 0) :
    radialHomotopy hU a 0 η = primitive hU a η hη := by
  apply (functionsEquiv U).injective
  apply ContMDiffMap.ext
  intro x
  exact radialIntegral_zero_eq_segmentPrimitive hU a η x

omit [IsScalarTower ℝ ℂ E] in
/-- The degree-zero kernel consists locally of constants, without a connected-open assumption. -/
theorem locally_constant_zero {U : Opens E} (η : Sections U 0)
    (hη : differential U 0 η = 0) (x : U) :
    ∃ (V : Opens E) (hVU : V ≤ U), (x : E) ∈ V ∧
      ∃ c : ℂ, ∀ y : V, functionsEquiv U η (Set.inclusion hVU y) = c := by
  let f := functionsEquiv U η
  have hd (y : U) : fderiv ℂ (extend f) y = 0 := by
    calc
      fderiv ℂ (extend f) y = oneFormsEquiv U (differential U 0 η) y := by
        simpa only [f, LinearEquiv.symm_apply_apply] using
          (oneFormsEquiv_differential U (functionsEquiv U η) y).symm
      _ = 0 := by rw [hη, map_zero]; rfl
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp U.isOpen x x.2
  let V : Opens E := ⟨Metric.ball (x : E) r, Metric.isOpen_ball⟩
  have hVU : V ≤ U := hsub
  have hx : (x : E) ∈ V := Metric.mem_ball_self hr
  refine ⟨V, hVU, hx, f x, ?_⟩
  intro y
  have he : extend f (y : E) = extend f (x : E) :=
    (convex_ball (x : E) r).is_const_of_fderivWithin_eq_zero
      (fun z hz ↦ (contDiffAt_extend f ⟨z, hVU hz⟩).differentiableAt (by simp)
        |>.differentiableWithinAt)
      (fun z hz ↦ by rw [fderivWithin_of_isOpen Metric.isOpen_ball hz]; exact hd ⟨z, hVU hz⟩)
      y.2 hx
  simpa only [extend_of_mem f (Set.inclusion hVU y), extend_of_mem f x] using he

end HodgeConjecture.HolomorphicForms
