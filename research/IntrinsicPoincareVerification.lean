module

public import HodgeConjecture.Realization.DeRham.SchemeHolomorphicForms
public import HodgeConjecture.Realization.DeRham.HolomorphicPoincare
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace IntrinsicPoincareVerification

open AlgebraicGeometry CategoryTheory TopologicalSpace
open HodgeConjecture
open scoped Manifold ContDiff

abbrev base (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

def origin (d : ℕ) : Scheme.ComplexPoints (base d) :=
  AffineComplexPoints.ofAlgHom _ (MvPolynomial.aeval (fun _ : Fin d ↦ (0 : ℂ)))

def coordinateChart (d : ℕ) : HolomorphicAtlas.Chart (Fin d → ℂ) (Scheme.ComplexPoints (base d)) :=
  ⟨chartAt (Fin d → ℂ) (origin d), chart_mem_atlas (Fin d → ℂ) (origin d)⟩

def chartOpen (d : ℕ) : Opens (Scheme.ComplexPoints (base d)) :=
  HolomorphicAtlas.source (coordinateChart d)

theorem origin_mem_chartOpen (d : ℕ) : origin d ∈ chartOpen d :=
  mem_chart_source (Fin d → ℂ) (origin d)

def markedCoordinate (d : ℕ) : HolomorphicAtlas.domain (coordinateChart d) (chartOpen d) :=
  ⟨(coordinateChart d).1 (origin d),
    (coordinateChart d).1.map_source (origin_mem_chartOpen d), by
      change (coordinateChart d).1.symm ((coordinateChart d).1 (origin d)) ∈ chartOpen d
      rw [(coordinateChart d).1.left_inv (origin_mem_chartOpen d)]
      exact origin_mem_chartOpen d⟩

/-- A genuine intrinsic form on the original polynomial scheme's canonical analytic open. -/
def intrinsicGenerator (n : ℕ) :
    HolomorphicAtlas.Forms (Fin (n + 1) → ℂ) (chartOpen (n + 1)) n :=
  HolomorphicAtlas.fromChart (U := chartOpen (n + 1)) (coordinateChart (n + 1)) le_rfl n
    (HolomorphicForms.restrict
      (U := HolomorphicAtlas.domain (coordinateChart (n + 1)) (chartOpen (n + 1))) le_top n
        (HolomorphicDeRham.coordinateGenerator n))

/-- Its derivative is the same determinant volume form, in every degree. -/
theorem intrinsic_generator_derivative (n : ℕ) :
    HolomorphicAtlas.inChart (chartOpen (n + 1)) (n + 1) (coordinateChart (n + 1))
      (HolomorphicAtlas.differential (chartOpen (n + 1)) n (intrinsicGenerator n)) =
        (ContMDiffMap.const (HolomorphicForms.covectorWedge (n + 1)
          (fun i ↦ ContinuousLinearMap.proj i)) :
            HolomorphicForms.Sections
              (HolomorphicAtlas.domain (coordinateChart (n + 1)) (chartOpen (n + 1))) (n + 1)) := by
  rw [HolomorphicAtlas.inChart_differential]
  dsimp only [intrinsicGenerator]
  rw [HolomorphicAtlas.inChart_fromChart, ← HolomorphicForms.restrict_differential,
    HolomorphicDeRham.differential_coordinateGenerator]
  rfl

/-- The intrinsic two-form is nonzero on the actual canonical complex two-space. -/
theorem intrinsic_two_form_value :
    HolomorphicAtlas.inChart (chartOpen 2) 2 (coordinateChart 2)
      (HolomorphicAtlas.differential (chartOpen 2) 1 (intrinsicGenerator 1))
        (markedCoordinate 2) ![![1, 0], ![0, 1]] = 1 := by
  rw [intrinsic_generator_derivative]
  change HolomorphicForms.covectorWedge 2 (fun i ↦ ContinuousLinearMap.proj i)
    ![![1, 0], ![0, 1]] = 1
  rw [HolomorphicForms.covectorWedge_apply]
  norm_num [Matrix.det_fin_two]

theorem intrinsic_one_form_not_closed :
    HolomorphicAtlas.differential (chartOpen 2) 1 (intrinsicGenerator 1) ≠ 0 := by
  intro h
  have he := congrArg (fun η : HolomorphicAtlas.Forms (Fin 2 → ℂ) (chartOpen 2) 2 ↦
    HolomorphicAtlas.inChart (chartOpen 2) 2 (coordinateChart 2) η
      (markedCoordinate 2) ![![1, 0], ![0, 1]]) h
  rw [intrinsic_two_form_value] at he
  exact one_ne_zero he

/-- A higher-degree control prevents collapse to the curve-only comparison. -/
theorem intrinsic_three_form_value :
    HolomorphicAtlas.inChart (chartOpen 3) 3 (coordinateChart 3)
      (HolomorphicAtlas.differential (chartOpen 3) 2 (intrinsicGenerator 2))
        (markedCoordinate 3) ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] = 1 := by
  rw [intrinsic_generator_derivative]
  change HolomorphicForms.covectorWedge 3 (fun i ↦ ContinuousLinearMap.proj i)
    ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] = 1
  rw [HolomorphicForms.covectorWedge_apply]
  norm_num [Matrix.det_fin_three]

/-- The proved local construction produces a primitive of this nonzero intrinsic two-form. -/
theorem actual_local_primitive :
    ∃ (W : Opens (Scheme.ComplexPoints (base 2))) (hW : W ≤ chartOpen 2), origin 2 ∈ W ∧
      ∃ β : HolomorphicAtlas.Forms (Fin 2 → ℂ) W 1,
        HolomorphicAtlas.differential W 1 β = HolomorphicAtlas.restrict hW 2
          (HolomorphicAtlas.differential (chartOpen 2) 1 (intrinsicGenerator 1)) := by
  exact HolomorphicAtlas.locally_exact_positive (E := Fin 2 → ℂ) 1 _
    (LinearMap.congr_fun (HolomorphicAtlas.differential_comp (E := Fin 2 → ℂ) (chartOpen 2) 1) (intrinsicGenerator 1))
    ⟨origin 2, origin_mem_chartOpen 2⟩

theorem distinct_intrinsic_constants :
    HolomorphicAtlas.constant (E := Fin 2 → ℂ) (chartOpen 2) 0 ≠
      HolomorphicAtlas.constant (chartOpen 2) 1 := by
  intro h
  exact zero_ne_one (HolomorphicAtlas.constant_injective (E := Fin 2 → ℂ) (chartOpen 2)
    ⟨origin 2, origin_mem_chartOpen 2⟩ h)

/-- All degrees on the actual canonical affine scheme, including dimension zero. -/
theorem affine_comparison (d : ℕ) :
    QuasiIso (Scheme.ComplexPoints.holomorphicComparison (x := base d) d) :=
  Scheme.ComplexPoints.holomorphicComparison_quasiIso (x := base d) d

/-- The comparison applies to the original glued projective line. -/
theorem projectiveLine_comparison : QuasiIso (Scheme.ComplexPoints.holomorphicComparison
    (x := projectiveLine ℂ ↘ Spec (.of ℂ)) 1) :=
  Scheme.ComplexPoints.holomorphicComparison_quasiIso (x := projectiveLine ℂ ↘ Spec (.of ℂ)) 1

example : QuasiIso (Scheme.ComplexPoints.holomorphicComparison (x := base 0) 0) :=
  affine_comparison 0

end IntrinsicPoincareVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.HolomorphicForms.pullback_congr,
      `HodgeConjecture.HolomorphicAtlas.chartPullback_compatible,
      `HodgeConjecture.HolomorphicAtlas.fromChart,
      `HodgeConjecture.HolomorphicAtlas.fromChart_inChart,
      `HodgeConjecture.HolomorphicAtlas.inChart_fromChart,
      `HodgeConjecture.HolomorphicAtlas.chartEquiv,
      `HodgeConjecture.HolomorphicAtlas.fromChart_differential,
      `HodgeConjecture.HolomorphicAtlas.chartComplexIso,
      `HodgeConjecture.HolomorphicAtlas.constant,
      `HodgeConjecture.HolomorphicAtlas.constant_injective,
      `HodgeConjecture.HolomorphicAtlas.locally_constant_zero,
      `HodgeConjecture.HolomorphicAtlas.locally_exact_positive,
      `HodgeConjecture.SheafCohomology.ConstantLift.mono,
      `HodgeConjecture.SheafCohomology.AugmentedComplex.quasiIso,
      `HodgeConjecture.HolomorphicDeRham.comparison_quasiIso,
      `HodgeConjecture.HolomorphicAtlas.augmentation,
      `HodgeConjecture.HolomorphicAtlas.augmentation_mono,
      `HodgeConjecture.HolomorphicAtlas.augmentation_exact,
      `HodgeConjecture.HolomorphicAtlas.exact_positive,
      `HodgeConjecture.HolomorphicAtlas.comparison,
      `HodgeConjecture.HolomorphicAtlas.comparison_quasiIsoAt_zero,
      `HodgeConjecture.HolomorphicAtlas.comparison_quasiIsoAt_positive,
      `HodgeConjecture.HolomorphicAtlas.comparison_quasiIso,
      `AlgebraicGeometry.Scheme.ComplexPoints.holomorphicComparison,
      `AlgebraicGeometry.Scheme.ComplexPoints.holomorphicComparison_quasiIso,
      `IntrinsicPoincareVerification.intrinsic_generator_derivative,
      `IntrinsicPoincareVerification.intrinsic_two_form_value,
      `IntrinsicPoincareVerification.intrinsic_one_form_not_closed,
      `IntrinsicPoincareVerification.intrinsic_three_form_value,
      `IntrinsicPoincareVerification.actual_local_primitive,
      `IntrinsicPoincareVerification.distinct_intrinsic_constants,
      `IntrinsicPoincareVerification.affine_comparison,
      `IntrinsicPoincareVerification.projectiveLine_comparison] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
