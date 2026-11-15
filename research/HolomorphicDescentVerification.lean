module

public import HodgeConjecture.Realization.DeRham.SchemeHolomorphicForms
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HolomorphicDescentVerification

open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open HodgeConjecture HolomorphicForms HolomorphicDeRham
open scoped Manifold ContDiff

/-- The differential really detects a nonclosed one-form in dimension two. -/
theorem volume_two_value :
    HolomorphicForms.differential (⊤ : Opens (Fin 2 → ℂ)) 1 (coordinateGenerator 1)
      ⟨![0, 0], trivial⟩ ![![1, 0], ![0, 1]] = 1 := by
  rw [differential_coordinateGenerator]
  change covectorWedge 2 (fun i ↦ ContinuousLinearMap.proj i) ![![1, 0], ![0, 1]] = 1
  rw [covectorWedge_apply]
  norm_num [Matrix.det_fin_two]

theorem coordinate_one_form_not_closed :
    HolomorphicForms.differential (⊤ : Opens (Fin 2 → ℂ)) 1 (coordinateGenerator 1) ≠ 0 := by
  intro h
  have he := congrArg (fun a : Sections (⊤ : Opens (Fin 2 → ℂ)) 2 ↦
    a ⟨![0, 0], trivial⟩ ![![1, 0], ![0, 1]]) h
  rw [volume_two_value] at he
  exact one_ne_zero he

def coordinateFunction (d : ℕ) (i : Fin d) : Functions (⊤ : Opens (Fin d → ℂ)) :=
  ⟨fun z ↦ z.1 i, (ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).contMDiff.comp contMDiff_subtype_val⟩

def polynomialEvaluation (d : ℕ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] Functions (⊤ : Opens (Fin d → ℂ)) :=
  MvPolynomial.aeval (coordinateFunction d)

theorem fderiv_coordinateFunction (d : ℕ) (i : Fin d) (z : Fin d → ℂ) :
    fderiv ℂ (extend (coordinateFunction d i)) z = ContinuousLinearMap.proj i := by
  have he : extend (coordinateFunction d i) = ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ) : (Fin d → ℂ) → ℂ) := by
    funext w
    exact extend_of_mem (coordinateFunction d i) ⟨w, trivial⟩
  rw [he, ContinuousLinearMap.fderiv]

/-- A genuine algebraic two-form has determinant-one analytic value. -/
theorem algebraic_two_form_value :
    HolomorphicDeRham.algebraicFormsMap (⊤ : Opens (Fin 2 → ℂ)) (polynomialEvaluation 2) 2
      (1 • exteriorPower.ιMulti (MvPolynomial (Fin 2) ℂ) 2
        (fun i ↦ D ℂ (MvPolynomial (Fin 2) ℂ) (MvPolynomial.X i)))
      ⟨![3, 5], trivial⟩ ![![1, 0], ![0, 1]] = 1 := by
  have h := algebraicFormsMap_generator (⊤ : Opens (Fin 2 → ℂ)) (polynomialEvaluation 2) 2
    ![1, MvPolynomial.X 0, MvPolynomial.X 1] ⟨![3, 5], trivial⟩ ![![1, 0], ![0, 1]]
  have hi (i : Fin 2) :
      (![1, MvPolynomial.X 0, MvPolynomial.X 1] : Fin 3 → MvPolynomial (Fin 2) ℂ) i.succ =
        MvPolynomial.X i := by
    fin_cases i <;> rfl
  simpa [polynomialEvaluation, hi, fderiv_coordinateFunction, Matrix.det_fin_two] using h

/-- The universal degree-two generator differentiates correctly in three coordinates. -/
example :
    HolomorphicForms.differential (⊤ : Opens (Fin 3 → ℂ)) 2 (coordinateGenerator 2) =
      (ContMDiffMap.const (covectorWedge 3 (fun i ↦ ContinuousLinearMap.proj i)) :
        Sections (⊤ : Opens (Fin 3 → ℂ)) 3) := differential_coordinateGenerator 2

def punctured : Opens ℂ := ⟨{z | z ≠ 0}, isOpen_ne⟩

theorem inversion_smooth : ContDiffOn ℂ ∞ (fun z : ℂ ↦ z⁻¹) punctured := by
  intro z hz
  exact (contDiffAt_inv ℂ hz).contDiffWithinAt

def dz : Sections (⊤ : Opens ℂ) 1 :=
  ContMDiffMap.const ((oneCoeffEquiv (E := ℂ)).symm (ContinuousLinearMap.id ℂ ℂ))

/-- On the actual P¹ reciprocal-coordinate function, dz acquires the required Jacobian. -/
theorem reciprocal_one_form (z : ℂ) (hz : z ≠ 0) :
    pullback (V := ⊤) (fun z : ℂ ↦ z⁻¹) inversion_smooth (fun _ _ ↦ trivial) 1 dz
      ⟨z, hz⟩ ![1] = -(z ^ 2)⁻¹ := by
  change (oneCoeffEquiv (E := ℂ)).symm (ContinuousLinearMap.id ℂ ℂ)
    (fun i ↦ fderiv ℂ (fun z : ℂ ↦ z⁻¹) z (![1] i)) = _
  have ht : (fun i : Fin 1 ↦ fderiv ℂ (fun z : ℂ ↦ z⁻¹) z (![1] i)) =
      ![fderiv ℂ (fun z : ℂ ↦ z⁻¹) z 1] := by
    funext i
    fin_cases i
    rfl
  rw [ht, ← oneCoeffEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]
  change fderiv ℂ (fun z : ℂ ↦ z⁻¹) z 1 = _
  rw [fderiv_apply_one_eq_deriv, deriv_inv]

/-- These reciprocal coordinates identify the same original canonical projective-line point. -/
theorem original_projectiveLine_overlap (z : ℂ) (hz : z ≠ 0) :
    ProjectiveLineComplexPoints.canonicalHomeomorph (ProjectiveLineComplexPoints.finite z) =
      ProjectiveLineComplexPoints.canonicalHomeomorph (ProjectiveLineComplexPoints.reciprocal z⁻¹) :=
  congrArg ProjectiveLineComplexPoints.canonicalHomeomorph
    (ProjectiveLineComplexPoints.finite_eq_reciprocal_inv z hz)

abbrev polynomialBase (d : ℕ) :=
  AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

/-- The genuine polynomial scheme realizes every degree with the shared section algebra. -/
def affineFormsMap (d n : ℕ) :
    letI := Scheme.ComplexPoints.regularFunctionsAlgebra (x := polynomialBase d) ⊤
    ⋀[Γ(Spec (.of (MvPolynomial (Fin d) ℂ)), ⊤)]^n
      Ω[Γ(Spec (.of (MvPolynomial (Fin d) ℂ)), ⊤)⁄ℂ] →ₗ[ℂ]
        HolomorphicAtlas.Forms (Fin d → ℂ)
          (Scheme.ComplexPoints.analyticOpen (x := polynomialBase d) ⊤) n :=
  Scheme.ComplexPoints.algebraicFormsMap (x := polynomialBase d) d ⊤ n

/-- The same construction applies to the original glued projective line in every degree. -/
def projectiveLineFormsMap (n : ℕ) :
    letI := Scheme.ComplexPoints.regularFunctionsAlgebra
      (x := projectiveLine ℂ ↘ Spec (.of ℂ)) ⊤
    ⋀[Γ(projectiveLine ℂ, ⊤)]^n Ω[Γ(projectiveLine ℂ, ⊤)⁄ℂ] →ₗ[ℂ]
      HolomorphicAtlas.Forms (Fin 1 → ℂ)
        (Scheme.ComplexPoints.analyticOpen (x := projectiveLine ℂ ↘ Spec (.of ℂ)) ⊤) n :=
  Scheme.ComplexPoints.algebraicFormsMap (x := projectiveLine ℂ ↘ Spec (.of ℂ)) 1 ⊤ n

example (d : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℂ)
    (TopCat.of (Scheme.ComplexPoints (polynomialBase d))) :=
  HolomorphicAtlas.formsSheaf (Fin d → ℂ) (Scheme.ComplexPoints (polynomialBase d)) 2

example : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ)
    (TopCat.of (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))))) ℕ :=
  HolomorphicAtlas.complex (Fin 1 → ℂ)
    (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ)))

end HolomorphicDescentVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.HolomorphicForms.pullback,
      `HodgeConjecture.HolomorphicForms.pullback_comp,
      `HodgeConjecture.HolomorphicForms.pullback_differential,
      `HodgeConjecture.HolomorphicForms.pullback_inclusion,
      `HodgeConjecture.HolomorphicForms.covectorWedge,
      `HodgeConjecture.HolomorphicForms.covectorWedge_apply,
      `HodgeConjecture.HolomorphicForms.wedgeOneForms,
      `HodgeConjecture.HolomorphicForms.wedgeOneForms_one,
      `HodgeConjecture.HolomorphicAtlas.transition_contDiffOn,
      `HodgeConjecture.HolomorphicAtlas.differential,
      `HodgeConjecture.HolomorphicAtlas.differential_comp,
      `HodgeConjecture.HolomorphicAtlas.restrict_differential,
      `HodgeConjecture.HolomorphicAtlas.formsPresheaf_isSheaf,
      `HodgeConjecture.HolomorphicAtlas.formsSheaf,
      `HodgeConjecture.HolomorphicAtlas.complex,
      `HodgeConjecture.HolomorphicDeRham.formsRealization,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap_generator,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap_one,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap_precomp,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap_pullback,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap_restrict,
      `HodgeConjecture.HolomorphicDeRham.extDeriv_coordinateGenerator,
      `HodgeConjecture.HolomorphicDeRham.algebraicFormsMap_differential,
      `HodgeConjecture.HolomorphicDeRham.algebraicComplexMap,
      `AlgebraicGeometry.Scheme.ComplexPoints.smoothIsManifold,
      `AlgebraicGeometry.Scheme.ComplexPoints.chartFormsMap,
      `AlgebraicGeometry.Scheme.ComplexPoints.chartFormsMap_compatible,
      `AlgebraicGeometry.Scheme.ComplexPoints.algebraicFormsMap,
      `AlgebraicGeometry.Scheme.ComplexPoints.algebraicFormsMap_differential,
      `AlgebraicGeometry.Scheme.ComplexPoints.algebraicFormsMap_restrict,
      `AlgebraicGeometry.Scheme.ComplexPoints.algebraicFormsComparison,
      `AlgebraicGeometry.Scheme.ComplexPoints.algebraicFormsComparison_differential,
      `AlgebraicGeometry.Scheme.ComplexPoints.analyticPresheafComplex,
      `AlgebraicGeometry.Scheme.ComplexPoints.algebraicComplexComparison,
      `HolomorphicDescentVerification.affineFormsMap,
      `HolomorphicDescentVerification.projectiveLineFormsMap,
      `HolomorphicDescentVerification.volume_two_value,
      `HolomorphicDescentVerification.coordinate_one_form_not_closed,
      `HolomorphicDescentVerification.algebraic_two_form_value,
      `HolomorphicDescentVerification.reciprocal_one_form,
      `HolomorphicDescentVerification.original_projectiveLine_overlap] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
