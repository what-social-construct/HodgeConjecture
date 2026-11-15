module

public import HodgeConjecture.Geometry.Holomorphic.Forms
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section

/-!
# Native function and linear-map coordinates for holomorphic zero- and one-forms

The coefficient equivalences are the existing empty/subsingleton
continuous alternating-map equivalences. In these coordinates the
degree-zero arrow is the actual complex Fréchet derivative and closedness
in degree one is symmetry of the coefficient derivative.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open TopologicalSpace Filter
open scoped Manifold ContDiff Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Pointwise application of a native coefficient equivalence on the same sections. -/
def coefficientEquiv (U : Opens E) (e : V ≃L[ℂ] W) :
    C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, V), V⟯ ≃ₗ[ℂ] C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, W), W⟯ where
  toFun f := ⟨fun x ↦ e (f x), e.toContinuousLinearMap.contMDiff.comp f.contMDiff⟩
  invFun f := ⟨fun x ↦ e.symm (f x), e.symm.toContinuousLinearMap.contMDiff.comp f.contMDiff⟩
  left_inv f := by apply ContMDiffMap.ext; intro x; exact e.symm_apply_apply (f x)
  right_inv f := by apply ContMDiffMap.ext; intro x; exact e.apply_symm_apply (f x)
  map_add' f g := by apply ContMDiffMap.ext; intro x; exact e.map_add (f x) (g x)
  map_smul' c f := by apply ContMDiffMap.ext; intro x; exact e.map_smul c (f x)

theorem extend_coefficientEquiv (U : Opens E) (e : V ≃L[ℂ] W)
    (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, V), V⟯) :
    extend (coefficientEquiv U e f) = e ∘ extend f := by
  classical
  funext x
  by_cases hx : x ∈ U <;> simp [extend, hx, coefficientEquiv]

/-- Native zero-form evaluation, with inverse the actual constant empty alternating map. -/
abbrev zeroCoeffEquiv : Coeff E 0 ≃L[ℂ] ℂ :=
  (ContinuousAlternatingMap.constOfIsEmptyLIE ℂ E ℂ (Fin 0)).symm.toContinuousLinearEquiv

@[simp]
theorem zeroCoeffEquiv_apply (α : Coeff E 0) : zeroCoeffEquiv α = α ![] := by
  let e := ContinuousAlternatingMap.constOfIsEmptyLIE ℂ E ℂ (Fin 0)
  calc
    zeroCoeffEquiv α = (e (e.symm α)) ![] := rfl
    _ = α ![] := congrArg (fun β : Coeff E 0 ↦ β ![]) (e.apply_symm_apply α)

/-- Native one-form identification with continuous linear maps. -/
abbrev oneCoeffEquiv : Coeff E 1 ≃L[ℂ] (E →L[ℂ] ℂ) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ)
    (0 : Fin 1)).symm.toContinuousLinearEquiv

@[simp]
theorem oneCoeffEquiv_apply (α : Coeff E 1) (v : E) : oneCoeffEquiv α v = α ![v] := by
  let e := ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ) (0 : Fin 1)
  calc
    oneCoeffEquiv α v = (e (e.symm α)) ![v] := rfl
    _ = α ![v] := congrArg (fun β : Coeff E 1 ↦ β ![v]) (e.apply_symm_apply α)

/-- The coefficient function of a zero-form. -/
abbrev functionsEquiv (U : Opens E) : Sections U 0 ≃ₗ[ℂ] C^∞⟮𝓘(ℂ, E), U; ℂ⟯ :=
  coefficientEquiv U zeroCoeffEquiv

/-- The coefficient linear-map function of a one-form. -/
abbrev oneFormsEquiv (U : Opens E) :
    Sections U 1 ≃ₗ[ℂ] C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, E →L[ℂ] ℂ), E →L[ℂ] ℂ⟯ :=
  coefficientEquiv U oneCoeffEquiv

/-- The actual zero-form differential is the original Fréchet derivative. -/
theorem oneFormsEquiv_differential (U : Opens E)
    (f : C^∞⟮𝓘(ℂ, E), U; ℂ⟯) (x : U) :
    oneFormsEquiv U (differential U 0 ((functionsEquiv U).symm f)) x =
      fderiv ℂ (extend f) x := by
  change oneCoeffEquiv (differential U 0 ((functionsEquiv U).symm f) x) = _
  rw [differential_eq_of_extension ((functionsEquiv U).symm f)
    (fun y ↦ ContinuousAlternatingMap.constOfIsEmpty ℂ E (Fin 0) (extend f y))
    (fun y ↦ by simp only [extend_of_mem]; rfl)]
  rw [extDeriv_constOfIsEmpty]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := E) (F := ℂ)
    (0 : Fin 1)).symm_apply_apply _

/-- The sign and normalization of the native degree-one differential. -/
theorem extDeriv_one_apply (f : E → Coeff E 1) (x v w : E) :
    extDeriv f x ![v, w] =
      oneCoeffEquiv (fderiv ℂ f x v) w - oneCoeffEquiv (fderiv ℂ f x w) v := by
  rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  have hrem : Fin.removeNth (1 : Fin 2) (Matrix.vecCons v (fun _ : Fin 1 ↦ w)) =
      (fun _ : Fin 1 ↦ v) := by
    funext i
    fin_cases i
    rfl
  have hconst (y : E) : (![y] : Fin 1 → E) = fun _ ↦ y := by
    funext i
    fin_cases i
    rfl
  simp [Fin.sum_univ_two, hrem, sub_eq_add_neg, hconst]

/-- Complex closedness implies the symmetry used by the actual curve-integral primitive. -/
theorem closed_one_symmetric {U : Opens E} (η : Sections U 1)
    (hη : differential U 1 η = 0) (x : U) (v w : E) :
    fderiv ℂ (extend (oneFormsEquiv U η)) x v w =
      fderiv ℂ (extend (oneFormsEquiv U η)) x w v := by
  have hz := congrArg (fun η : Sections U 2 ↦ η x ![v, w]) hη
  change extDeriv (extend η) x ![v, w] = 0 at hz
  rw [extDeriv_one_apply, sub_eq_zero] at hz
  rw [extend_coefficientEquiv]
  rw [(oneCoeffEquiv (E := E)).comp_fderiv (𝕜 := ℂ)]
  exact hz

end HodgeConjecture.HolomorphicForms
