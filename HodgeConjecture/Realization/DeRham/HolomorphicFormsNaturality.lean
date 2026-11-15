module

public import HodgeConjecture.Realization.DeRham.HolomorphicFormsMap

@[expose] public section

/-! # Naturality of the all-degree forms map

The derivative chain rule on the shared algebraic spanning generators
proves compatibility with coordinate changes and with restriction.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicDeRham

open TopologicalSpace Filter KaehlerDifferential
open scoped Manifold ContDiff Topology
open HolomorphicForms

variable {E F A : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CommRing A] [Algebra ℂ A]

/-- Precomposition reuses the existing functorial algebraic forms map. -/
theorem algebraicFormsMap_precomp {B : Type} [CommRing B] [Algebra ℂ B]
    (U : Opens E) (f : A →ₐ[ℂ] B) (φ : B →ₐ[ℂ] Functions U) (n : ℕ) :
    (algebraicFormsMap U φ n).comp (AlgebraDeRham.formsMap ℂ f n) =
      algebraicFormsMap U (φ.comp f) n := by
  unfold algebraicFormsMap
  rw [LinearMap.comp_assoc, AlgebraDeRham.formsMap_comp]

theorem fderiv_extend_comp {U : Opens E} {V : Opens F} (f : E → F)
    (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V)
    (g : Functions V) (h : Functions U) (heq : ∀ x : U, h x = g ⟨f x, hUV x.2⟩) (x : U) :
    fderiv ℂ (extend h) x = (fderiv ℂ (extend g) (f x)).comp (fderiv ℂ f x) := by
  have he : extend h =ᶠ[𝓝 (x : E)] extend g ∘ f :=
    extend_eventuallyEq h x.2 _ (fun z ↦ (heq z).trans (extend_of_mem g ⟨f z, hUV z.2⟩).symm)
  rw [he.fderiv_eq]
  exact fderiv_comp (x : E)
    ((contDiffAt_extend g ⟨f x, hUV x.2⟩).differentiableAt (by simp))
    ((hf.contDiffAt (U.isOpen.mem_nhds x.2)).differentiableAt (by simp))

/-- All-degree realization commutes with actual holomorphic coordinate pullback. -/
theorem algebraicFormsMap_pullback {U : Opens E} {V : Opens F} (f : E → F)
    (hf : ContDiffOn ℂ ∞ f U) (hUV : Set.MapsTo f U V)
    (φ : A →ₐ[ℂ] Functions V) (ψ : A →ₐ[ℂ] Functions U)
    (heq : ∀ a (x : U), ψ a x = φ a ⟨f x, hUV x.2⟩) (n : ℕ) :
    (pullback f hf hUV n).comp (algebraicFormsMap V φ n) = algebraicFormsMap U ψ n := by
  apply AlgebraDeRham.forms_linearMap_ext ℂ n
  intro a
  apply ContMDiffMap.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  change algebraicFormsMap V φ n
    (a 0 • exteriorPower.ιMulti A n (fun i ↦ D ℂ A (a i.succ)))
      ⟨f x, hUV x.2⟩ (fun i ↦ fderiv ℂ f x (v i)) = _
  rw [algebraicFormsMap_generator, algebraicFormsMap_generator, heq]
  congr 2
  funext i j
  rw [fderiv_extend_comp f hf hUV (φ (a j.succ)) (ψ (a j.succ)) (heq (a j.succ)) x]
  rfl

/-- Inclusions use the original restriction of coordinate forms. -/
theorem algebraicFormsMap_restrict {U V : Opens E} (h : U ≤ V)
    (φ : A →ₐ[ℂ] Functions V) (ψ : A →ₐ[ℂ] Functions U)
    (heq : ∀ a (x : U), ψ a x = φ a (Set.inclusion h x)) (n : ℕ) :
    (HolomorphicForms.restrict h n).comp (algebraicFormsMap V φ n) =
      algebraicFormsMap U ψ n := by
  have hnat := algebraicFormsMap_pullback (U := U) (V := V) id contDiffOn_id
    (fun _ hx ↦ h hx) φ ψ heq n
  apply LinearMap.ext
  intro a
  exact (pullback_inclusion h n (algebraicFormsMap V φ n a)).symm.trans
    (LinearMap.congr_fun hnat a)

end HodgeConjecture.HolomorphicDeRham
