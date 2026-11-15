module

public import HodgeConjecture.Geometry.Holomorphic.Forms
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

/-!
# Contraction and the Euler identity

These are operations on the existing continuous alternating coefficients.
The Euler identity is the algebraic input to the radial Poincaré homotopy.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open ContinuousAlternatingMap
open scoped Topology ContDiff

variable {𝕜 E F : Type} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}

/-- Currying is smooth on the original coefficient spaces. -/
theorem contDiff_curryLeft :
    ContDiff 𝕜 ∞ (curryLeft : (E [⋀^Fin (n + 1)]→L[𝕜] F) → E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) := by
  exact LinearIsometry.contDiff (𝕜 := 𝕜)
    (E := E [⋀^Fin (n + 1)]→L[𝕜] F) (F := E →L[𝕜] E [⋀^Fin n]→L[𝕜] F)
    curryLeftLI

/-- Insertion of a fixed vector in the first slot of the original form. -/
def contraction (v : E) : (E [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] (E [⋀^Fin n]→L[𝕜] F) :=
  (ContinuousLinearMap.apply 𝕜 ((E [⋀^Fin n]→L[𝕜] F)) v).comp curryLeftLI.toContinuousLinearMap

@[simp]
theorem contraction_apply (v : E) (α : (E [⋀^Fin (n + 1)]→L[𝕜] F)) :
    contraction v α = α.curryLeft v := rfl

/-- Alternation and insertion obey the signed Leibniz identity. -/
theorem contraction_alternatize (L : E →L[𝕜] (E [⋀^Fin (n + 1)]→L[𝕜] F)) (v : E) :
    contraction v (alternatizeUncurryFin L) =
      L v - alternatizeUncurryFin ((contraction v).comp L) := by
  ext w
  simp only [contraction_apply, curryLeft_apply_apply, alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero,
    Fin.removeNth_zero, Matrix.cons_val_succ, Fin.val_succ]
  have hr (i : Fin (n + 1)) :
      i.succ.removeNth (Matrix.vecCons v w) = Matrix.vecCons v (i.removeNth w) := by
    funext j
    cases j using Fin.cases
    · rfl
    · simp only [Fin.removeNth, Fin.succ_succAbove_succ, Matrix.cons_val_succ]
  simp only [hr, pow_succ, mul_neg_one, neg_smul]
  rw [Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 2

/-- Contraction with the Euler vector field based at `a`. -/
def eulerContraction (a : E) (f : E → (E [⋀^Fin (n + 1)]→L[𝕜] F)) (x : E) : (E [⋀^Fin n]→L[𝕜] F) :=
  contraction (x - a) (f x)

theorem hasFDerivAt_eulerContraction {f : E → (E [⋀^Fin (n + 1)]→L[𝕜] F)} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (a : E) :
    HasFDerivAt (eulerContraction a f)
      ((f x).curryLeft + (contraction (x - a)).comp (fderiv 𝕜 f x)) x := by
  let C : (E [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] (E →L[𝕜] (E [⋀^Fin n]→L[𝕜] F)) :=
    curryLeftLI.toContinuousLinearMap
  have hc : HasFDerivAt (fun y ↦ (f y).curryLeft)
      (C.comp (fderiv 𝕜 f x)) x := by
    simpa only [Function.comp_def, C, LinearIsometry.coe_toContinuousLinearMap,
      curryLeftLI_apply] using
      (HasFDerivAt.comp (𝕜 := 𝕜) (g := C) x C.hasFDerivAt hf.hasFDerivAt)
  have h := hc.clm_apply ((hasFDerivAt_id x).sub_const a)
  apply HasFDerivAt.of_isLittleO
  simpa only [Function.comp_def, eulerContraction, contraction_apply,
    ContinuousLinearMap.comp_id, id_eq, _root_.add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, C,
    LinearIsometry.coe_toContinuousLinearMap, curryLeftLI_apply] using h.isLittleO

/-- Cartan's homotopy identity for the Euler vector field, in every positive degree. -/
theorem extDeriv_eulerContraction {f : E → (E [⋀^Fin (n + 1)]→L[𝕜] F)} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (a : E) :
    extDeriv (eulerContraction a f) x + contraction (x - a) (extDeriv f x) =
      (n + 1) • f x + fderiv 𝕜 f x (x - a) := by
  rw [extDeriv, (hasFDerivAt_eulerContraction hf a).fderiv,
    alternatizeUncurryFin_add, alternatizeUncurryFin_curryLeft,
    extDeriv, contraction_alternatize]
  abel

end HodgeConjecture.HolomorphicForms
