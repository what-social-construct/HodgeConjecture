module

public import HodgeConjecture.Geometry.Holomorphic.FunctionAlgebra
public import HodgeConjecture.Geometry.Holomorphic.Pullback
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Algebra.Module.Alternating.Topology

@[expose] public section

/-!
# Determinant wedges of holomorphic one-forms

The alternating coefficient is the unnormalized antisymmetrization of
the product of covectors: its value is exactly the determinant, in every
degree including zero. The construction uses native continuous maps.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.HolomorphicForms

open TopologicalSpace
open scoped Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The continuous multilinear determinant construction on covectors. -/
def covectorWedgeMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ E →L[ℂ] ℂ) (Coeff E n) :=
  (ContinuousMultilinearMap.alternatizationL (𝕜 := ℂ)).compContinuousMultilinearMap
    ((ContinuousLinearMap.apply ℂ _ (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ)).compContinuousMultilinearMap
        (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℂ
          (fun _ : Fin n ↦ E) (fun _ ↦ ℂ) ℂ))

theorem covectorWedgeMultilinear_apply (n : ℕ) (a : Fin n → E →L[ℂ] ℂ) (v : Fin n → E) :
    covectorWedgeMultilinear n a v = Matrix.det (fun i j ↦ a j (v i)) := by
  simp [covectorWedgeMultilinear, ContinuousMultilinearMap.alternatizationL_apply,
    Matrix.det_apply,
    Function.comp_def]

/-- Wedges alternate in the covectors as well as in the tangent arguments. -/
def covectorWedge (n : ℕ) : (E →L[ℂ] ℂ) [⋀^Fin n]→L[ℂ] Coeff E n where
  toContinuousMultilinearMap := covectorWedgeMultilinear n
  map_eq_zero_of_eq' a i j hij hne := by
    ext v
    change covectorWedgeMultilinear n a v = 0
    rw [covectorWedgeMultilinear_apply]
    exact Matrix.det_zero_of_column_eq hne (fun k ↦ congrArg (fun l ↦ l (v k)) hij)

@[simp]
theorem covectorWedge_apply (n : ℕ) (a : Fin n → E →L[ℂ] ℂ) (v : Fin n → E) :
    covectorWedge n a v = Matrix.det (fun i j ↦ a j (v i)) :=
  covectorWedgeMultilinear_apply n a v

/-- The determinant wedge on the original spaces of holomorphic one-forms. -/
def wedgeOneForms (U : Opens E) (n : ℕ) :
    (Sections U 1) [⋀^Fin n]→ₗ[HolomorphicDeRham.Functions U] Sections U n where
  toFun a := ⟨fun x ↦ covectorWedge n (fun i ↦ oneCoeffEquiv (a i x)), by
    exact ((covectorWedge (E := E) n).toContinuousMultilinearMap.contDiff.contMDiff).comp
      (contMDiff_pi_module_iff.mpr (fun i ↦ (oneFormsEquiv U (a i)).contMDiff))⟩
  map_update_add' a i b c := by
    apply ContMDiffMap.ext; intro x
    change covectorWedge n (fun j ↦ oneCoeffEquiv (Function.update a i (b + c) j x)) =
      covectorWedge n (fun j ↦ oneCoeffEquiv (Function.update a i b j x)) +
        covectorWedge n (fun j ↦ oneCoeffEquiv (Function.update a i c j x))
    have hupd (b : Sections U 1) :
        (fun j ↦ oneCoeffEquiv (Function.update a i b j x)) =
          Function.update (fun j ↦ oneCoeffEquiv (a j x)) i (oneCoeffEquiv (b x)) := by
      funext j; by_cases h : j = i <;> simp [h]
    simp only [hupd, ContMDiffMap.coe_add, Pi.add_apply, map_add]
    exact (covectorWedge (E := E) n).map_update_add _ i _ _
  map_update_smul' a i c b := by
    apply ContMDiffMap.ext; intro x
    have hupd : (fun j ↦ oneCoeffEquiv (Function.update a i (c • b) j x)) =
        Function.update (fun j ↦ oneCoeffEquiv (a j x)) i (c x • oneCoeffEquiv (b x)) := by
      funext j
      by_cases h : j = i
      · subst j; simp only [Function.update_self]; exact oneCoeffEquiv.map_smul (c x) (b x)
      · simp [h]
    change covectorWedge n (fun j ↦ oneCoeffEquiv (Function.update a i (c • b) j x)) = _
    rw [hupd, (covectorWedge (E := E) n).map_update_smul]
    change c x • covectorWedge n _ =
      c x • covectorWedge n (fun j ↦ oneCoeffEquiv (Function.update a i b j x))
    congr 2
    funext j
    by_cases h : j = i <;> simp [h]
  map_eq_zero_of_eq' a i j hij hne := by
    apply ContMDiffMap.ext; intro x
    exact (covectorWedge (E := E) n).map_eq_zero_of_eq _ (congrArg (fun b ↦ oneCoeffEquiv (b x)) hij) hne

@[simp]
theorem wedgeOneForms_apply (U : Opens E) (n : ℕ) (a : Fin n → Sections U 1)
    (x : U) (v : Fin n → E) :
    wedgeOneForms U n a x v = Matrix.det (fun i j ↦ oneCoeffEquiv (a j x) (v i)) :=
  covectorWedge_apply n _ v

/-- Degree one recovers the original one-form rather than a new normalization. -/
theorem wedgeOneForms_one (U : Opens E) (a : Sections U 1) :
    wedgeOneForms U 1 (fun _ ↦ a) = a := by
  apply ContMDiffMap.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  rw [wedgeOneForms_apply, Matrix.det_unique, oneCoeffEquiv_apply]
  congr 1
  funext i
  simpa using congrArg v (Subsingleton.elim 0 i)

end HodgeConjecture.HolomorphicForms
