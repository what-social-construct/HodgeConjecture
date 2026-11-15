module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace SingularSheavesVerification

open AlgebraicGeometry CategoryTheory TopologicalSpace HodgeConjecture

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

theorem affine_comparison (d : ℕ) : QuasiIso
    (Scheme.ComplexPoints.singularSheafComparison (x := affineBase d)) :=
  Scheme.ComplexPoints.singularSheafComparison_quasiIso d

theorem projectiveLine_comparison : QuasiIso
    (Scheme.ComplexPoints.singularSheafComparison
      (x := projectiveLine ℂ ↘ Spec (.of ℂ))) :=
  Scheme.ComplexPoints.singularSheafComparison_quasiIso 1

example : QuasiIso (Scheme.ComplexPoints.singularSheafComparison (x := affineBase 0)) :=
  affine_comparison 0

/-- The raw presheaf has literally the original cochains on the original open subtype. -/
example (X : TopCat.{0}) (U : Opens X) (n : ℕ) :
    (SingularCochains.presheaf X n).obj (Opposite.op U) =
      ModuleCat.of ℚ (SingularCochains.Cochain ((Opens.toTopCat X).obj U) n) := rfl

/-- Unrestricted cochains are not silently replaced by continuous point functions. -/
def discontinuousCochain : SingularCochains.Cochain (TopCat.of ℝ) 0 :=
  (SingularCochains.continuousCochainEquiv ℝ 0).symm
    (fun σ ↦ if σ default = 0 then 0 else 1)

def intervalSimplex : SingularDegreeZero.Simplex ℝ 1 :=
  SingularDegreeZero.pathSimplex (Path.segment (0 : ℝ) 1)

/-- The actual coboundary is nonzero on the original oriented interval. -/
theorem actual_coboundary_value :
    SingularCochains.continuousCochainEquiv ℝ 1
      (SingularCochains.differential (TopCat.of ℝ) 0 discontinuousCochain) intervalSimplex = 1 := by
  rw [SingularCochains.differential_zero_coordinates]
  simp [discontinuousCochain, intervalSimplex, SingularDegreeZero.coboundary_apply,
    SingularDegreeZero.face_pathSimplex_zero, SingularDegreeZero.face_pathSimplex_one]

theorem actual_coboundary_nonzero :
    SingularCochains.differential (TopCat.of ℝ) 0 discontinuousCochain ≠ 0 := by
  intro h
  have he := actual_coboundary_value
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Local exactness produces a primitive for this nonzero closed cochain. -/
theorem actual_local_primitive :
    ∃ (V : Opens ℝ) (hV : V ≤ ⊤), (0 : ℝ) ∈ V ∧
      ∃ b : SingularCochains.Cochain ((Opens.toTopCat (TopCat.of ℝ)).obj V) 0,
        SingularCochains.differential _ 0 b =
          (SingularCochains.presheaf (TopCat.of ℝ) 1).map (homOfLE hV).op
            ((SingularCochains.pullback (Opens.inclusionTopIso (TopCat.of ℝ)).hom).f 1
              (SingularCochains.differential (TopCat.of ℝ) 0 discontinuousCochain)) := by
  let : StronglyLocallyContractibleSpace ℝ := normedSpace_stronglyLocallyContractible ℝ
  let f := (Opens.inclusionTopIso (TopCat.of ℝ)).hom
  exact SingularCochains.locally_exact_positive (TopCat.of ℝ) 0 ⊤
    ((SingularCochains.pullback f).f 1
      (SingularCochains.differential (TopCat.of ℝ) 0 discontinuousCochain)) (by
        rw [SingularCochains.differential_pullback,
          SingularCochains.differential_squared, map_zero]) 0 trivial

theorem distinct_constants :
    SingularCochains.constantCochain (TopCat.of ℝ) 0 ≠
      SingularCochains.constantCochain (TopCat.of ℝ) 1 := by
  intro h
  exact zero_ne_one (SingularCochains.constantCochain_injective (TopCat.of ℝ) h)

end SingularSheavesVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafCohomology.sheafification,
      `HodgeConjecture.SheafCohomology.sheafifyComplex,
      `HodgeConjecture.SheafHypercohomology.globalSections,
      `HodgeConjecture.SheafCohomology.LocalExactness.stalk_exact_of_exists_local_preimage,
      `HodgeConjecture.SheafCohomology.LocalExactness.sheafifyStalkIso,
      `HodgeConjecture.SheafCohomology.LocalExactness.sheafify_exact_of_exists_local_preimage,
      `HodgeConjecture.SheafCohomology.ConstantLift.map_mono,
      `HodgeConjecture.normedSpace_stronglyLocallyContractible,
      `HodgeConjecture.chartedSpace_stronglyLocallyContractible,
      `HodgeConjecture.SingularContractible.exists_primitive,
      `HodgeConjecture.SingularCochains.presheaf,
      `HodgeConjecture.SingularCochains.sectionComplexIso,
      `HodgeConjecture.SingularCochains.globalCochainsToSheaf,
      `HodgeConjecture.SingularCochains.locally_exact_positive,
      `HodgeConjecture.SingularCochains.locally_constant_zero,
      `HodgeConjecture.SingularCochains.augmentation_mono,
      `HodgeConjecture.SingularCochains.augmentation_exact,
      `HodgeConjecture.SingularCochains.sheaf_exact_positive,
      `HodgeConjecture.SingularCochains.comparison_quasiIso,
      `AlgebraicGeometry.Scheme.ComplexPoints.stronglyLocallyContractibleSpace,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularSheafComparison_quasiIso,
      `SingularSheavesVerification.affine_comparison,
      `SingularSheavesVerification.projectiveLine_comparison,
      `SingularSheavesVerification.actual_coboundary_value,
      `SingularSheavesVerification.actual_coboundary_nonzero,
      `SingularSheavesVerification.actual_local_primitive,
      `SingularSheavesVerification.distinct_constants] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
