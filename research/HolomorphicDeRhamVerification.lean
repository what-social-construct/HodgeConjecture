module

public import HodgeConjecture.Realization.DeRham.HolomorphicPoincare
public import HodgeConjecture.Realization.DeRham.HolomorphicKaehler
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The controls use actual native alternating forms, analytic derivatives and
segment integrals. A nonclosed form in dimension two tests that exactness
is not obtained by setting the differential to zero. Polynomial evaluation
tests the original Kähler map, and higher-degree radial primitives test the integral weight and the full
constant-sheaf comparison on spaces of complex dimension at least two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HolomorphicDeRhamVerification

open HodgeConjecture TopologicalSpace CategoryTheory
open HolomorphicForms
open scoped Manifold ContDiff Polynomial

def coefficientMap : (ℂ × ℂ) →L[ℂ] ((ℂ × ℂ) →L[ℂ] ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).smulRight (ContinuousLinearMap.snd ℂ ℂ ℂ)

/-- The actual holomorphic form z₁ dz₂ on the complex plane of dimension two. -/
def nonclosedForm : Sections (⊤ : Opens (ℂ × ℂ)) 1 :=
  (oneFormsEquiv (⊤ : Opens (ℂ × ℂ))).symm
    ⟨fun x ↦ coefficientMap x, coefficientMap.contMDiff.comp contMDiff_subtype_val⟩

theorem nonclosedForm_differential_ne_zero : differential (⊤ : Opens (ℂ × ℂ)) 1 nonclosedForm ≠ 0 := by
  intro h
  have he : extend (oneFormsEquiv (⊤ : Opens (ℂ × ℂ)) nonclosedForm) = coefficientMap := by
    funext x
    rw [extend_of_mem _ (⟨x, trivial⟩ : (⊤ : Opens (ℂ × ℂ)))]
    change oneFormsEquiv (⊤ : Opens (ℂ × ℂ)) ((oneFormsEquiv (⊤ : Opens (ℂ × ℂ))).symm _) _ = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hs := closed_one_symmetric nonclosedForm h ⟨(0, 0), trivial⟩ (1, 0) (0, 1)
  rw [he, coefficientMap.fderiv] at hs
  norm_num [coefficientMap] at hs

/-- The primitive retains its chosen base point and original integral normalization. -/
def constantOneForm : Sections (⊤ : Opens ℂ) 1 :=
  (oneFormsEquiv (⊤ : Opens ℂ)).symm (ContMDiffMap.const (ContinuousLinearMap.id ℂ ℂ))

theorem constantOneForm_segmentPrimitive (a z : ℂ) :
    segmentPrimitive ⊤ a constantOneForm z = z - a := by
  have he : extend (oneFormsEquiv (⊤ : Opens ℂ) constantOneForm) =
      fun _ : ℂ ↦ ContinuousLinearMap.id ℂ ℂ := by
    funext x
    rw [extend_of_mem _ (⟨x, trivial⟩ : (⊤ : Opens ℂ))]
    change oneFormsEquiv (⊤ : Opens ℂ) ((oneFormsEquiv (⊤ : Opens ℂ)).symm _) _ = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [segmentPrimitive, he, curveIntegral_segment_const]
  rfl

theorem polynomialSquare_derivative :
    oneCoeffEquiv
      (HolomorphicDeRham.algebraicOneFormsMap (⊤ : Opens ℂ)
        (HolomorphicDeRham.polynomialEvaluation ⊤)
        (KaehlerDifferential.D ℂ ℂ[X] (Polynomial.X ^ 2)) ⟨3, trivial⟩) 1 = 6 := by
  rw [HolomorphicDeRham.algebraicOneFormsMap_D]
  change oneFormsEquiv (⊤ : Opens ℂ) (differential (⊤ : Opens ℂ) 0 ((functionsEquiv (⊤ : Opens ℂ)).symm _)) _ _ = _
  rw [oneFormsEquiv_differential]
  change fderiv ℂ (extend (HolomorphicDeRham.polynomialEvaluation
    (⊤ : Opens ℂ) (Polynomial.X ^ 2))) (3 : ℂ) 1 = 6
  have he : extend (HolomorphicDeRham.polynomialEvaluation (⊤ : Opens ℂ) (Polynomial.X ^ 2)) =
      fun z : ℂ ↦ z ^ 2 := by
    funext z
    rw [extend_of_mem _ (⟨z, trivial⟩ : (⊤ : Opens ℂ)), HolomorphicDeRham.polynomialEvaluation_apply]
    simp
  rw [he, fderiv_apply_one_eq_deriv, deriv_pow_field]
  norm_num

example : QuasiIsoAt (HolomorphicDeRham.comparison (ℂ × ℂ)) 0 :=
  HolomorphicDeRham.comparison_quasiIsoAt_zero (ℂ × ℂ)

example : QuasiIsoAt (HolomorphicDeRham.comparison (ℂ × ℂ)) 1 :=
  HolomorphicDeRham.comparison_quasiIsoAt_one (ℂ × ℂ)

example : QuasiIso (HolomorphicDeRham.comparison ℂ) :=
  HolomorphicDeRham.complexLine_comparison_quasiIso

/-- The original constant alternating two-form dz₁ ∧ dz₂, with coefficient 1. -/
def areaCoefficient : Coeff (ℂ × ℂ) 2 :=
  ContinuousAlternatingMap.alternatizeUncurryFin
    ((oneCoeffEquiv (E := ℂ × ℂ)).symm.toContinuousLinearMap.comp coefficientMap)

def areaForm : Sections (⊤ : Opens (ℂ × ℂ)) 2 := ContMDiffMap.const areaCoefficient

theorem areaCoefficient_apply (v : Fin 2 → ℂ × ℂ) :
    areaCoefficient v = (v 0).1 * (v 1).2 - (v 1).1 * (v 0).2 := by
  simp [areaCoefficient, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_two, coefficientMap, oneCoeffEquiv, Fin.removeNth, Fin.succAbove, sub_eq_add_neg]

theorem areaForm_closed : differential (⊤ : Opens (ℂ × ℂ)) 2 areaForm = 0 := by
  apply ContMDiffMap.ext
  intro x
  rw [differential_eq_of_extension _ (fun _ ↦ areaCoefficient) (fun _ ↦ rfl)]
  simp only [extDeriv, fderiv_fun_const]
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (ℂ × ℂ) ℂ).map_zero

/-- The actual degree-two integral has its required factor 1/2. -/
theorem areaForm_radialPrimitive (z v : ℂ × ℂ) :
    oneCoeffEquiv
      (radialHomotopy (U := (⊤ : Opens (ℂ × ℂ))) (convex_univ : Convex ℝ (Set.univ : Set (ℂ × ℂ)))
        ⟨0, trivial⟩ 1 areaForm ⟨z, trivial⟩) v =
      (1 / 2 : ℂ) * (z.1 * v.2 - v.1 * z.2) := by
  have he : extend areaForm = fun _ : ℂ × ℂ ↦ areaCoefficient := by
    funext x
    rw [extend_of_mem _ (⟨x, trivial⟩ : (⊤ : Opens (ℂ × ℂ)))]
    rfl
  change oneCoeffEquiv (radialIntegral (0 : ℂ × ℂ) (extend areaForm) z) v = _
  rw [he]
  simp only [radialIntegral, radialIntegrand, pow_one, sub_zero]
  rw [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal,
    integral_id]
  norm_num [oneCoeffEquiv_apply, contraction_apply]
  rw [areaCoefficient_apply]
  rfl

/-- Exactness in degree two is witnessed by this same computed primitive. -/
theorem areaForm_radialPrimitive_differential :
    differential (⊤ : Opens (ℂ × ℂ)) 1
      (radialHomotopy (U := (⊤ : Opens (ℂ × ℂ)))
        (convex_univ : Convex ℝ (Set.univ : Set (ℂ × ℂ))) ⟨0, trivial⟩ 1 areaForm) = areaForm :=
  differential_radialHomotopy_of_closed (U := (⊤ : Opens (ℂ × ℂ)))
    convex_univ ⟨0, trivial⟩ 1 areaForm areaForm_closed

theorem areaForm_ne_zero : areaForm ≠ 0 := by
  intro h
  have hh := congrArg (fun η : Sections (⊤ : Opens (ℂ × ℂ)) 2 ↦
    η ⟨0, trivial⟩ ![(1, 0), (0, 1)]) h
  change areaCoefficient ![(1, 0), (0, 1)] = 0 at hh
  norm_num [areaCoefficient_apply] at hh

/-- A two-form on complex three-space with a nonzero exterior derivative. -/
def nonclosedTwoCoefficient : Coeff ((ℂ × ℂ) × ℂ) 2 :=
  areaCoefficient.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)

def nonclosedTwoMap : ((ℂ × ℂ) × ℂ) →L[ℂ] Coeff ((ℂ × ℂ) × ℂ) 2 :=
  (ContinuousLinearMap.snd ℂ (ℂ × ℂ) ℂ).smulRight nonclosedTwoCoefficient

def nonclosedTwoForm : Sections (⊤ : Opens ((ℂ × ℂ) × ℂ)) 2 :=
  ⟨fun x ↦ nonclosedTwoMap x, nonclosedTwoMap.contMDiff.comp contMDiff_subtype_val⟩

theorem nonclosedTwoForm_differential_ne_zero :
    differential (⊤ : Opens ((ℂ × ℂ) × ℂ)) 2 nonclosedTwoForm ≠ 0 := by
  have hd : differential (⊤ : Opens ((ℂ × ℂ) × ℂ)) 2 nonclosedTwoForm ⟨0, trivial⟩
      ![((0, 0), 1), ((1, 0), 0), ((0, 1), 0)] = 1 := by
    rw [differential_eq_of_extension _ nonclosedTwoMap (fun _ ↦ rfl)]
    change ContinuousAlternatingMap.alternatizeUncurryFin
      (fderiv ℂ nonclosedTwoMap (0 : (ℂ × ℂ) × ℂ))
      ![((0, 0), 1), ((1, 0), 0), ((0, 1), 0)] = 1
    rw [nonclosedTwoMap.fderiv]
    norm_num [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      nonclosedTwoMap, nonclosedTwoCoefficient, areaCoefficient_apply,
      Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove]
  intro h
  rw [h] at hd
  norm_num at hd

example : QuasiIso (HolomorphicDeRham.comparison (ℂ × ℂ)) :=
  HolomorphicDeRham.comparison_quasiIso (ℂ × ℂ)

example : QuasiIso (HolomorphicDeRham.comparison (Fin 3 → ℂ)) :=
  HolomorphicDeRham.comparison_quasiIso (Fin 3 → ℂ)

end HolomorphicDeRhamVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.HolomorphicForms.contDiffAt_extend,
      `HodgeConjecture.HolomorphicForms.differential,
      `HodgeConjecture.HolomorphicForms.differential_eq_of_extension,
      `HodgeConjecture.HolomorphicForms.restrict_differential,
      `HodgeConjecture.HolomorphicForms.differential_comp,
      `HodgeConjecture.HolomorphicForms.contDiff_curryLeft,
      `HodgeConjecture.HolomorphicForms.contraction_alternatize,
      `HodgeConjecture.HolomorphicForms.extDeriv_eulerContraction,
      `HodgeConjecture.HolomorphicForms.hasDerivAt_comp_ofReal,
      `HodgeConjecture.HolomorphicForms.hasFDerivAt_parameterIntegral,
      `HodgeConjecture.HolomorphicForms.contDiffOn_parameterIntegral,
      `HodgeConjecture.HolomorphicForms.extDeriv_radialIntegrand,
      `HodgeConjecture.HolomorphicForms.hasDerivAt_weightedRadial,
      `HodgeConjecture.HolomorphicForms.contDiffOn_radialIntegral,
      `HodgeConjecture.HolomorphicForms.radialHomotopy,
      `HodgeConjecture.HolomorphicForms.differential_radialHomotopy,
      `HodgeConjecture.HolomorphicForms.differential_radialHomotopy_of_closed,
      `HodgeConjecture.HolomorphicForms.locally_exact_positive,
      `HodgeConjecture.HolomorphicForms.radialIntegral_zero_eq_segmentPrimitive,
      `HodgeConjecture.HolomorphicForms.radialHomotopy_zero_eq_primitive,
      `HodgeConjecture.HolomorphicForms.oneFormsEquiv_differential,
      `HodgeConjecture.HolomorphicForms.extDeriv_one_apply,
      `HodgeConjecture.HolomorphicForms.closed_one_symmetric,
      `HodgeConjecture.HolomorphicForms.segmentPrimitive_self,
      `HodgeConjecture.HolomorphicForms.hasFDerivAt_segmentPrimitive,
      `HodgeConjecture.HolomorphicForms.contDiffOn_segmentPrimitive,
      `HodgeConjecture.HolomorphicForms.differential_primitive,
      `HodgeConjecture.HolomorphicForms.locally_exact_one,
      `HodgeConjecture.HolomorphicForms.locally_constant_zero,
      `HodgeConjecture.HolomorphicForms.coefficient_eq_zero_of_finrank_lt,
      `HodgeConjecture.HolomorphicForms.complexLine_section_eq_zero,
      `HodgeConjecture.SheafCohomology.LocalExactness.exact_of_exists_local_preimage,
      `HodgeConjecture.HolomorphicDeRham.formsSheaf,
      `HodgeConjecture.HolomorphicDeRham.complex,
      `HodgeConjecture.HolomorphicDeRham.augmentation,
      `HodgeConjecture.HolomorphicDeRham.augmentation_differential,
      `HodgeConjecture.HolomorphicDeRham.augmentation_exact,
      `HodgeConjecture.HolomorphicDeRham.augmentation_mono,
      `HodgeConjecture.HolomorphicDeRham.exact_one,
      `HodgeConjecture.HolomorphicDeRham.exact_positive,
      `HodgeConjecture.HolomorphicDeRham.complex_exactAt_positive,
      `HodgeConjecture.HolomorphicDeRham.comparison_quasiIsoAt_positive,
      `HodgeConjecture.HolomorphicDeRham.comparison_quasiIso,
      `HodgeConjecture.HolomorphicDeRham.comparison,
      `HodgeConjecture.HolomorphicDeRham.comparison_quasiIsoAt_zero,
      `HodgeConjecture.HolomorphicDeRham.comparison_quasiIsoAt_one,
      `HodgeConjecture.HolomorphicDeRham.complexLine_formsSheaf_isZero,
      `HodgeConjecture.HolomorphicDeRham.complexLine_comparison_quasiIso,
      `HodgeConjecture.HolomorphicDeRham.holomorphicDerivation,
      `HodgeConjecture.HolomorphicDeRham.kaehlerRealization_D,
      `HodgeConjecture.HolomorphicDeRham.algebraicOneFormsMap_D,
      `HodgeConjecture.HolomorphicDeRham.polynomialEvaluation_apply,
      `HolomorphicDeRhamVerification.nonclosedForm_differential_ne_zero,
      `HolomorphicDeRhamVerification.constantOneForm_segmentPrimitive,
      `HolomorphicDeRhamVerification.polynomialSquare_derivative,
      `HolomorphicDeRhamVerification.areaForm_closed,
      `HolomorphicDeRhamVerification.areaForm_radialPrimitive,
      `HolomorphicDeRhamVerification.areaForm_radialPrimitive_differential,
      `HolomorphicDeRhamVerification.areaForm_ne_zero,
      `HolomorphicDeRhamVerification.nonclosedTwoForm_differential_ne_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
