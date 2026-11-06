module

import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
import Lean.Util.CollectAxioms

/-!
Regression checks for actual `Spec ℂ`-valued points of the glued projective
line. The source point type retains its scheme morphism and base equation;
its topology is defined by the original affine evaluation charts. The
one-point compactification comparison is a proved homeomorphism.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Filter Topology OnePoint
open HodgeConjecture HodgeConjecture.ProjectiveLineComplexPoints

noncomputable section

-- The point type includes the genuine scheme-valued point over the complex base.
example (p : Point) :
    schemeMorphism p ≫ (projectiveLine ℂ ↘ Spec (.of ℂ)) = 𝟙 _ :=
  schemeMorphism_toBase p

-- Classification comes from the actual two affine scheme charts.
example (p : Point) :
    (∃ a, xChart a = p) ∨ (∃ a, yChart a = p) := charts_cover p

example (p : Point) : (∃! z, finite z = p) ∨ p = infinity := by
  rcases finite_or_infinity p with ⟨z, hz⟩ | hp
  · exact Or.inl ⟨z, hz, fun w hw ↦ finite_injective (hw.trans hz.symm)⟩
  · exact Or.inr hp

-- A genuinely complex coordinate retains the original inversion transition.
example : finite Complex.I = reciprocal (-Complex.I) := by
  simpa using finite_eq_reciprocal_inv Complex.I Complex.I_ne_zero

example (z : ℂ) (hz : z ≠ 0) :
    overlapMorphism z hz ≫ (projectiveLineInversionIso ℂ).hom ≫
        projectiveLinePuncturedChart ℂ =
      affineMorphism (AffineLineComplexPoints.evalPoint z⁻¹) := overlapMorphism_y z hz

-- Infinity is the actual origin in the second scheme chart and lies outside the first.
example (q : Spec (.of ℂ)) :
    schemeMorphism infinity q = projectiveLineInfinity ℂ := infinity_base q

example : infinity ∉ Set.range finite := by
  rw [range_finite]
  simp

example : finite 0 ≠ infinity := finite_ne_infinity 0

-- Both original affine evaluation charts are continuous by the defining final topology.
example : Continuous xChart ∧ Continuous yChart :=
  ⟨continuous_xChart, continuous_yChart⟩

example {T : Type*} [TopologicalSpace T] (f : Point → T) :
    Continuous f ↔ Continuous (f ∘ xChart) ∧ Continuous (f ∘ yChart) :=
  continuous_iff_charts f

-- The analytic charts are proved open and cover all actual complex-valued points.
example : IsOpenEmbedding finite ∧ IsOpenEmbedding reciprocal :=
  ⟨isOpenEmbedding_finite, isOpenEmbedding_reciprocal⟩

example : Set.range finite ∪ Set.range reciprocal = Set.univ :=
  range_finite_union_reciprocal

-- The native compactification topology, including infinity, agrees with chart evaluation.
example : onePointHomeomorph (finite Complex.I) = (Complex.I : OnePoint ℂ) := by simp

example : onePointHomeomorph infinity = ∞ := by simp

example : onePointHomeomorph (reciprocal 0) = ∞ := by
  simp

example : Tendsto finite (coclosedCompact ℂ) (𝓝 infinity) := by
  have h : ContinuousAt fromOnePoint (∞ : OnePoint ℂ) := continuous_fromOnePoint.continuousAt
  simpa only [Function.comp_def, fromOnePoint_coe, fromOnePoint_infty] using
    h.tendsto.comp OnePoint.tendsto_coe_infty

example : CompactSpace Point := inferInstance

example : T2Space Point := inferInstance

end

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.OnePointComplex.inversion_involutive,
      `HodgeConjecture.OnePointComplex.continuous_inversion,
      `HodgeConjecture.OnePointComplex.inversionHomeomorph,
      `HodgeConjecture.ProjectiveLineComplexPoints.exists_affinePoint,
      `HodgeConjecture.ProjectiveLineComplexPoints.charts_cover,
      `HodgeConjecture.ProjectiveLineComplexPoints.overlapMorphism_y,
      `HodgeConjecture.ProjectiveLineComplexPoints.finite_eq_reciprocal_inv,
      `HodgeConjecture.ProjectiveLineComplexPoints.finite_ne_infinity,
      `HodgeConjecture.ProjectiveLineComplexPoints.finite_or_infinity,
      `HodgeConjecture.ProjectiveLineComplexPoints.onePointEquiv,
      `HodgeConjecture.ProjectiveLineComplexPoints.continuous_iff_charts,
      `HodgeConjecture.ProjectiveLineComplexPoints.continuous_fromOnePoint,
      `HodgeConjecture.ProjectiveLineComplexPoints.onePointHomeomorph,
      `HodgeConjecture.ProjectiveLineComplexPoints.isOpenEmbedding_finite,
      `HodgeConjecture.ProjectiveLineComplexPoints.isOpenEmbedding_reciprocal,
      `HodgeConjecture.ProjectiveLineComplexPoints.range_finite_union_reciprocal,
      `HodgeConjecture.ProjectiveLineComplexPoints.pointCompactSpace,
      `HodgeConjecture.ProjectiveLineComplexPoints.pointT2Space] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
