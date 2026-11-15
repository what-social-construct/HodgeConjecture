module

public import HodgeConjecture.Geometry.Holomorphic.Forms
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

@[expose] public section

/-!
# Pullback of the existing coordinate forms

The coefficient at x is the original form at f(x), precomposed in every
argument with the actual complex derivative of f. Naturality of d uses
Mathlib's exterior-derivative pullback theorem.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open TopologicalSpace Filter
open scoped Manifold ContDiff Topology

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem contDiffAt_formPullback {n : ℕ} {a : F → Coeff F n} {f : E → F} {x : E}
    (ha : ContDiffAt ℂ ∞ a (f x)) (hf : ContDiffAt ℂ ∞ f x) :
    ContDiffAt ℂ ∞ (fun y ↦ (a (f y)).compContinuousLinearMap (fderiv ℂ f y)) x := by
  have hd := hf.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  exact ((hd.contMDiffAt.compContinuousLinearMapCLM).clm_apply
    (ha.comp x hf).contMDiffAt).contDiffAt

/-- Pullback on native holomorphic sections of coordinate opens. -/
def pullback {U : Opens E} {V : Opens F} (f : E → F)
    (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V) (n : ℕ) :
    Sections V n →ₗ[ℂ] Sections U n where
  toFun a := ⟨fun x ↦ (a ⟨f x, hUV x.2⟩).compContinuousLinearMap (fderiv ℂ f x), by
    have hs := contMDiff_restrict (U := U)
      (fun x hx ↦ contDiffAt_formPullback (contDiffAt_extend a ⟨f x, hUV hx⟩)
        (hf.contDiffAt (U.isOpen.mem_nhds hx)))
    exact hs.congr (fun x ↦ by rw [extend_of_mem a ⟨f x, hUV x.2⟩])⟩
  map_add' a b := by
    apply ContMDiffMap.ext; intro x
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℂ f x)).map_add _ _
  map_smul' c a := by
    apply ContMDiffMap.ext; intro x
    exact (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℂ f x)).map_smul c _

@[simp]
theorem pullback_apply {U : Opens E} {V : Opens F} (f : E → F)
    (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V) (n : ℕ)
    (a : Sections V n) (x : U) :
    pullback f hf hUV n a x =
      (a ⟨f x, hUV x.2⟩).compContinuousLinearMap (fderiv ℂ f x) := rfl

/-- Computing d after pullback is independent of the auxiliary extensions. -/
theorem pullback_differential {U : Opens E} {V : Opens F} (f : E → F)
    (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V) (n : ℕ) (a : Sections V n) :
    differential U n (pullback f hf hUV n a) =
      pullback f hf hUV (n + 1) (differential V n a) := by
  apply ContMDiffMap.ext
  intro x
  rw [differential_eq_of_extension _
    (fun y ↦ (extend a (f y)).compContinuousLinearMap (fderiv ℂ f y))
    (fun y ↦ by simp only [pullback_apply, extend_of_mem a ⟨f y, hUV y.2⟩])]
  change extDeriv (fun y ↦ (extend a (f y)).compContinuousLinearMap (fderiv ℂ f y)) (x : E) =
    (extDeriv (extend a) (f x)).compContinuousLinearMap (fderiv ℂ f x)
  exact extDeriv_pullback (f := f) («ω» := extend a)
    ((contDiffAt_extend a ⟨f x, hUV x.2⟩).differentiableAt (by simp))
    (hf.contDiffAt (U.isOpen.mem_nhds x.2)) (by simp)

@[simp]
theorem pullback_id (U : Opens E) (n : ℕ) (a : Sections U n) :
    pullback (U := U) (V := U) id contDiffOn_id (fun _ h ↦ h) n a = a := by
  apply ContMDiffMap.ext; intro x
  simp only [pullback_apply, fderiv_id]
  ext v
  rfl

theorem pullback_inclusion {U V : Opens E} (h : U ≤ V) (n : ℕ) (a : Sections V n) :
    pullback (U := U) (V := V) id contDiffOn_id (fun _ hx ↦ h hx) n a = restrict h n a := by
  apply ContMDiffMap.ext; intro x
  simp only [pullback_apply, fderiv_id]
  ext v
  rfl

/-- Equal coordinate maps on the open have the same actual derivative pullback. -/
theorem pullback_congr {U : Opens E} {V : Opens F} {f g : E → F}
    (hf : ContDiffOn ℂ ∞ f U) (hg : ContDiffOn ℂ ∞ g U)
    (hUV : Set.MapsTo f U V) (hUV' : Set.MapsTo g U V)
    (hfg : Set.EqOn f g U) (n : ℕ) (a : Sections V n) :
    pullback f hf hUV n a = pullback g hg hUV' n a := by
  apply ContMDiffMap.ext
  intro x
  have he : f =ᶠ[𝓝 (x : E)] g := by
    filter_upwards [U.isOpen.mem_nhds x.2] with y hy
    exact hfg hy
  change (a ⟨f x, hUV x.2⟩).compContinuousLinearMap (fderiv ℂ f x) =
    (a ⟨g x, hUV' x.2⟩).compContinuousLinearMap (fderiv ℂ g x)
  rw [he.fderiv_eq]
  exact congrArg (fun b : Coeff F n ↦ b.compContinuousLinearMap (fderiv ℂ g x))
    (congrArg a (Subtype.ext (hfg x.2)))

theorem restrict_pullback {U W : Opens E} {V : Opens F} (h : W ≤ U) (f : E → F)
    (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V) (n : ℕ) (a : Sections V n) :
    restrict h n (pullback f hf hUV n a) =
      pullback f (hf.mono h) (fun _ hx ↦ hUV (h hx)) n a := by
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Composition uses the actual chain rule, including every alternating argument. -/
theorem pullback_comp {U : Opens E} {V : Opens F} {W : Opens G}
    (f : E → F) (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V)
    (g : F → G) (hg : ContDiffOn ℂ ∞ g V) (hVW : Set.MapsTo g V W)
    (n : ℕ) (a : Sections W n) :
    pullback f hf hUV n (pullback g hg hVW n a) =
      pullback (g ∘ f) (hg.comp hf hUV) (hVW.comp hUV) n a := by
  apply ContMDiffMap.ext; intro x
  have hfx := (hf.contDiffAt (U.isOpen.mem_nhds x.2)).differentiableAt (by simp)
  have hgx := (hg.contDiffAt (V.isOpen.mem_nhds (hUV x.2))).differentiableAt (by simp)
  simp only [pullback_apply, fderiv_comp (x : E) hgx hfx]
  ext v
  rfl

end HodgeConjecture.HolomorphicForms
