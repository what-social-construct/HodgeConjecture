module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import HodgeConjecture.Realization.DeRham.SheafHypercohomology
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace SingularDerivedComparisonVerification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HodgeConjecture
open scoped Classical

attribute [local instance] HasDerivedCategory.standard

theorem real_comparison :
    IsIso (SheafHypercohomology.comparison ℚ (TopCat.of ℝ)
      (SingularCochains.sheafComplex (TopCat.of ℝ))) :=
  SingularCochains.derivedComparison_isIso _

theorem real_homology (n : ℤ) :
    IsIso (SheafHypercohomology.comparisonFromComplexHomology ℚ (TopCat.of ℝ)
      (SingularCochains.sheafComplex (TopCat.of ℝ)) n) :=
  SingularCochains.derivedComparisonFromComplexHomology_isIso _ n

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

theorem affine_comparison (d : ℕ) :
    IsIso (SheafHypercohomology.comparison ℚ (SchemeBetti.space (affineBase d))
      (SingularCochains.sheafComplex (SchemeBetti.space (affineBase d)))) := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : LocallyCompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.locallyCompactSpace d
  let : SecondCountableTopology (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.secondCountableTopology d
  exact Scheme.ComplexPoints.singularSheafDerivedComparison_isIso

theorem projectiveLine_comparison :
    IsIso (SheafHypercohomology.comparison ℚ
      (SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ)))
      (SingularCochains.sheafComplex (SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ))))) := by
  let : T2Space (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalT2Space
  let : LocallyCompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
  let : SecondCountableTopology (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalSecondCountableTopology
  exact Scheme.ComplexPoints.singularSheafDerivedComparison_isIso

theorem empty_comparison :
    IsIso (SheafHypercohomology.comparison ℚ (TopCat.of Empty)
      (SingularCochains.sheafComplex (TopCat.of Empty))) :=
  SingularCochains.derivedComparison_isIso _

/-- The general fixed-ring comparison also handles integer coefficients. -/
theorem integer_skyscraper_comparison :
    IsIso (SheafHypercohomology.comparison ℤ (TopCat.of ℝ)
      ((CochainComplex.single₀ _).obj (skyscraperSheaf (0 : ℝ) (ModuleCat.of ℤ ℤ)))) := by
  apply SheafHypercohomology.comparison_isIso_of_flasqueTerms
  intro q
  by_cases hq : q = 0
  · subst q
    exact isFlasque_skyscraperSheaf_of_hasZeroObject (X := TopCat.of ℝ) (0 : ℝ) (ModuleCat.of ℤ ℤ)
  · exact SheafCohomology.FlasqueComplex.isFlasque_of_isZero (TopCat.of ℝ) _
      (HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 _ q hq)

/-- The exported isomorphism is induced by the original comparison, in every integer degree. -/
theorem original_comparison_hom (n : ℤ) :
    (SingularCochains.sheafSectionsHomologyIsoHypercohomology (TopCat.of ℝ) n).hom =
      SheafHypercohomology.comparisonFromComplexHomology ℚ (TopCat.of ℝ)
        (SingularCochains.sheafComplex (TopCat.of ℝ)) n := rfl

/-- The old de Rham entry point still exports the same actual derived-functor unit. -/
theorem original_unit :
    SheafHypercohomology.comparison ℚ (TopCat.of ℝ)
      (SingularCochains.sheafComplex (TopCat.of ℝ)) =
    (SheafHypercohomology.globalSections ℚ (TopCat.of ℝ)).rightDerivedFunctorPlusUnit.app
      (SheafHypercohomology.nonnegativeToPlus ℚ (TopCat.of ℝ)
        (SingularCochains.sheafComplex (TopCat.of ℝ))) := rfl

/-- Whole-complex comparison retains the original nonzero total degree-two class. -/
theorem projectiveLine_total_h2_nonzero : ProjectiveLineBettiCohomology.coverGenerator ≠ 0 :=
  ProjectiveLineBettiCohomology.coverGenerator_ne_zero

example : IsIso (SheafHypercohomology.comparisonFromComplexHomology ℚ (TopCat.of ℝ)
    (SingularCochains.sheafComplex (TopCat.of ℝ)) (-1)) := real_homology (-1)

example : IsIso (SheafHypercohomology.comparison ℚ (SchemeBetti.space (affineBase 0))
    (SingularCochains.sheafComplex (SchemeBetti.space (affineBase 0)))) := affine_comparison 0

end SingularDerivedComparisonVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafCohomology.FlasqueComplex.epi_toCycles,
      `HodgeConjecture.SheafCohomology.FlasqueComplex.cycles_shortExact,
      `HodgeConjecture.SheafCohomology.FlasqueComplex.isFlasque_of_isZero,
      `HodgeConjecture.SheafCohomology.FlasqueComplex.cycles_isFlasque,
      `HodgeConjecture.SheafCohomology.FlasqueComplex.sections_acyclic,
      `HodgeConjecture.SheafCohomology.FlasqueComplex.sections_quasiIso_of_mono,
      `HodgeConjecture.SheafHypercohomology.globalSections_quasiIso_of_mono,
      `HodgeConjecture.SheafHypercohomology.isIso_comparison_of_flasqueTerms,
      `HodgeConjecture.SheafHypercohomology.nonnegativeToPlus_flasqueTerms,
      `HodgeConjecture.SheafHypercohomology.comparison_isIso_of_flasqueTerms,
      `HodgeConjecture.SheafHypercohomology.comparisonFromComplexHomology_isIso_of_flasqueTerms,
      `HodgeConjecture.SheafHypercohomology.complexHomologyIsoHypercohomology,
      `HodgeConjecture.SheafHypercohomology.complexHomologyIsoHypercohomology_hom,
      `HodgeConjecture.SingularCochains.derivedComparison_isIso_of_flasqueTerms,
      `HodgeConjecture.SingularCochains.derivedComparison_isIso_of_open_paracompact,
      `HodgeConjecture.SingularCochains.derivedComparison_isIso,
      `HodgeConjecture.SingularCochains.derivedComparisonFromComplexHomology_isIso,
      `HodgeConjecture.SingularCochains.sheafSectionsHomologyIsoHypercohomology,
      `HodgeConjecture.SingularCochains.sheafSectionsHomologyIsoHypercohomology_hom,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularSheafDerivedComparison_isIso,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularSheafSectionsHomologyIsoHypercohomology,
      `SingularDerivedComparisonVerification.real_comparison,
      `SingularDerivedComparisonVerification.real_homology,
      `SingularDerivedComparisonVerification.affine_comparison,
      `SingularDerivedComparisonVerification.projectiveLine_comparison,
      `SingularDerivedComparisonVerification.empty_comparison,
      `SingularDerivedComparisonVerification.integer_skyscraper_comparison,
      `SingularDerivedComparisonVerification.original_comparison_hom,
      `SingularDerivedComparisonVerification.original_unit,
      `SingularDerivedComparisonVerification.projectiveLine_total_h2_nonzero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
