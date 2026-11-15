module

public import HodgeConjecture.Geometry.Holomorphic.SchemeEvaluation
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

namespace AnalyticChartsVerification

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.ComplexPoints
open HodgeConjecture
open scoped Manifold ContDiff

abbrev A (d : ℕ) := MvPolynomial (Fin d) ℂ
abbrev base (d : ℕ) := AffineComplexPoints.structureMorphism (A d)

example (d : ℕ) : ChartedSpace (Fin d → ℂ) (Scheme.ComplexPoints (base d)) := inferInstance
example (d : ℕ) : IsManifold 𝓘(ℂ, Fin d → ℂ) ω (Scheme.ComplexPoints (base d)) := inferInstance
example : IsManifold 𝓘(ℂ, Fin 1 → ℂ) ω
    (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) := inferInstance

/-- A genuinely implicit analytic root with two independent complex parameters. -/
theorem analytic_square_root_family :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (1, 0) ∈ W ∧
      ∃ ψ : (ℂ × ℂ) → ℂ, ψ (1, 0) = 1 ∧
        ∀ c ∈ W, (ψ c) ^ 2 = c.1 + c.2 ∧ ContDiffAt ℂ ω ψ c := by
  have hF : ContDiff ℂ ω (fun p : (ℂ × ℂ) × ℂ ↦ p.2 ^ 2 - (p.1.1 + p.1.2)) := by
    fun_prop
  have hd : deriv (fun t : ℂ ↦ t ^ 2 - ((1 : ℂ) + 0)) 1 ≠ 0 := by
    rw [((hasDerivAt_pow 2 (1 : ℂ)).sub_const ((1 : ℂ) + 0)).deriv]
    norm_num
  obtain ⟨W, D, ψ, hW, hc, hD, ht, hψ, hψW, huniq⟩ :=
    exists_analyticImplicitFunction hF (c₀ := ((1, 0) : ℂ × ℂ)) (t₀ := (1 : ℂ))
      (by norm_num) hd isOpen_univ (Set.mem_univ _)
  refine ⟨W, hW, hc, ψ, hψ, fun c hc ↦ ?_⟩
  exact ⟨sub_eq_zero.mp (hψW c hc).2.1, (hψW c hc).2.2.2⟩

/-- The native algebra map evaluates the same original polynomial at the same original point. -/
theorem regularEvaluation_polynomial (d : ℕ) (P : A d) (z : Fin d → ℂ) :
    regularEvaluation (x := base d) d ⊤ ((Scheme.ΓSpecIso (.of (A d))).inv P)
      ⟨(PolynomialComplexPoints.homeomorph d).symm z, mem_top _⟩ = MvPolynomial.eval z P := by
  rw [regularEvaluation_apply, PolynomialComplexPoints.homeomorph_symm_apply,
    AffineComplexPoints.eval_ofAlgHom]
  simp

/-- A concrete nonconstant regular function on canonical complex two-space. -/
theorem polynomial_value_control :
    regularEvaluation (x := base 2) 2 ⊤
      ((Scheme.ΓSpecIso (.of (A 2))).inv (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1))
      ⟨(PolynomialComplexPoints.homeomorph 2).symm ![3, 5], mem_top _⟩ = 14 := by
  rw [regularEvaluation_polynomial]
  norm_num

/-- An actual nonlinear morphism from two-dimensional affine space to the affine line. -/
def coordinateRingMap : A 1 →ₐ[ℂ] A 2 :=
  MvPolynomial.aeval (fun _ ↦ MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1)

def polynomialMorphism : Spec (.of (A 2)) ⟶ Spec (.of (A 1)) :=
  Spec.map (CommRingCat.ofHom coordinateRingMap.toRingHom)

theorem polynomialMorphism_over : polynomialMorphism ≫ base 1 = base 2 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact coordinateRingMap.commutes c

theorem polynomialMorphism_analytic :
    ContMDiff 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (map polynomialMorphism polynomialMorphism_over) :=
  contMDiff_map 2 1 polynomialMorphism polynomialMorphism_over

theorem polynomialMorphism_point (z : Fin 2 → ℂ) :
    map polynomialMorphism polynomialMorphism_over
      (AffineComplexPoints.ofAlgHom (A 2) (MvPolynomial.aeval z)) =
    AffineComplexPoints.ofAlgHom (A 1) ((MvPolynomial.aeval z).comp coordinateRingMap) := by
  apply Scheme.ComplexPoints.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The analytic scheme map retains the actual nonlinear coordinate value. -/
theorem polynomialMorphism_value_control :
    PolynomialComplexPoints.homeomorph 1
      (map polynomialMorphism polynomialMorphism_over
        ((PolynomialComplexPoints.homeomorph 2).symm ![3, 5])) 0 = 14 := by
  rw [PolynomialComplexPoints.homeomorph_symm_apply, polynomialMorphism_point,
    PolynomialComplexPoints.homeomorph_apply, AffineComplexPoints.eval_ofAlgHom]
  norm_num [PolynomialComplexPoints.coordinateSections, coordinateRingMap]

/-- The original finite affine chart is analytic for the constructed scheme atlas. -/
theorem projectiveLineXChart_analytic :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (map (projectiveLineXChart ℂ) (projectiveLineXChart_comp_structureMorphism ℂ)) :=
  contMDiff_map 1 1 (projectiveLineXChart ℂ) (projectiveLineXChart_comp_structureMorphism ℂ)

/-- The original infinity chart is analytic as well. -/
theorem projectiveLineYChart_analytic :
    ContMDiff 𝓘(ℂ, Fin 1 → ℂ) 𝓘(ℂ, Fin 1 → ℂ) ω
      (map (projectiveLineYChart ℂ) (projectiveLineYChart_comp_structureMorphism ℂ)) :=
  contMDiff_map 1 1 (projectiveLineYChart ℂ) (projectiveLineYChart_comp_structureMorphism ℂ)

/-- The original two chart evaluations still give the same canonical scheme point on overlaps. -/
theorem projectiveLine_original_overlap (z : ℂ) (hz : z ≠ 0) :
    ProjectiveLineComplexPoints.canonicalHomeomorph (ProjectiveLineComplexPoints.finite z) =
    ProjectiveLineComplexPoints.canonicalHomeomorph (ProjectiveLineComplexPoints.reciprocal z⁻¹) :=
  congrArg ProjectiveLineComplexPoints.canonicalHomeomorph
    (ProjectiveLineComplexPoints.finite_eq_reciprocal_inv z hz)

/-- The actual reciprocal coordinate change is complex analytic on the overlap. -/
theorem reciprocal_overlap_analytic : ContDiffOn ℂ ω (fun z : ℂ ↦ z⁻¹) {z | z ≠ 0} := by
  intro z hz
  exact (contDiffAt_inv ℂ hz).contDiffWithinAt

end AnalyticChartsVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `AlgebraicGeometry.Scheme.ComplexPoints.exists_analyticImplicitFunction,
      `AlgebraicGeometry.Scheme.ComplexPoints.exists_analyticOpenPartialHomeomorph_of_etale,
      `HodgeConjecture.PolynomialComplexPoints.smoothOfRelativeDimension,
      `HodgeConjecture.PolynomialComplexPoints.homeomorph,
      `HodgeConjecture.PolynomialComplexPoints.homeomorph_ofAlgHom,
      `HodgeConjecture.PolynomialComplexPoints.homeomorph_symm_apply,
      `AlgebraicGeometry.Scheme.ComplexPoints.exists_etaleCoordinates,
      `AlgebraicGeometry.Scheme.ComplexPoints.exists_isAlgebraicChart,
      `AlgebraicGeometry.Scheme.ComplexPoints.analyticChartedSpace,
      `AlgebraicGeometry.Scheme.ComplexPoints.analyticIsManifold,
      `AlgebraicGeometry.Scheme.ComplexPoints.contDiffAt_evalOrZero_comp_chartAt_symm,
      `AlgebraicGeometry.Scheme.ComplexPoints.contMDiffOn_evalOrZero,
      `AlgebraicGeometry.Scheme.ComplexPoints.contMDiff_map,
      `AlgebraicGeometry.Scheme.ComplexPoints.regularFunctionsAlgebra,
      `AlgebraicGeometry.Scheme.ComplexPoints.regularEvaluation,
      `AlgebraicGeometry.Scheme.ComplexPoints.regularEvaluation_restrict,
      `AlgebraicGeometry.Scheme.ComplexPoints.chartEvaluation,
      `AlgebraicGeometry.Scheme.ComplexPoints.chartEvaluation_eq_regularEvaluation,
      `AlgebraicGeometry.Scheme.ComplexPoints.regularEvaluation_map,
      `AlgebraicGeometry.projectiveLineAffineStructureMorphism_smoothOfRelativeDimension,
      `AlgebraicGeometry.projectiveLine_smoothOfRelativeDimension,
      `AnalyticChartsVerification.analytic_square_root_family,
      `AnalyticChartsVerification.regularEvaluation_polynomial,
      `AnalyticChartsVerification.polynomial_value_control,
      `AnalyticChartsVerification.polynomialMorphism_analytic,
      `AnalyticChartsVerification.polynomialMorphism_value_control,
      `AnalyticChartsVerification.projectiveLineXChart_analytic,
      `AnalyticChartsVerification.projectiveLineYChart_analytic,
      `AnalyticChartsVerification.projectiveLine_original_overlap,
      `AnalyticChartsVerification.reciprocal_overlap_analytic] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
