module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import HodgeConjecture.Realization.DeRham.AffineSheafAcyclicity
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace FlasqueDerivedVerification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HodgeConjecture
open scoped Classical

/-- The generic theorem applies to a native skyscraper on an arbitrary topological space. -/
theorem skyscraper_higher (k : Type) [CommRing k] (X : TopCat.{0}) (p : X)
    (A : ModuleCat k) (n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections k X).rightDerived n).obj
      (skyscraperSheaf p A)) := by
  classical
  let : (skyscraperSheaf p A).IsFlasque :=
    isFlasque_skyscraperSheaf_of_hasZeroObject p A
  exact SheafCohomology.LinearCoefficients.isZero_rightDerived_globalSections_of_isFlasque
    k X _ n hn

example : IsZero (((SheafHypercohomology.globalSections ℤ (TopCat.of ℝ)).rightDerived 1).obj
    (skyscraperSheaf (0 : ℝ) (ModuleCat.of ℤ ℤ))) :=
  skyscraper_higher ℤ (TopCat.of ℝ) 0 (ModuleCat.of ℤ ℤ) 1 (by decide)

theorem real_terms (q n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections ℚ (TopCat.of ℝ)).rightDerived n).obj
      (SingularCochains.cochainSheaf (TopCat.of ℝ) q)) :=
  SingularCochains.isZero_cochainSheaf_derivedGlobalSections _ q n hn

theorem real_open_terms (U : Opens (TopCat.of ℝ)) (q n : ℕ) (hn : 0 < n) :
    IsZero (SheafCohomology.TwoOpenModules.Hobj ℚ (𝟭 _) U n
      (SingularCochains.cochainSheaf (TopCat.of ℝ) q)) :=
  SingularCochains.isZero_cochainSheaf_cohomology _ q U n hn

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

/-- All affine dimensions, sheaf degrees and positive derived degrees use the original topology. -/
theorem affine_terms (d q n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections ℚ (SchemeBetti.space (affineBase d))).rightDerived n).obj
      (SingularCochains.cochainSheaf (SchemeBetti.space (affineBase d)) q)) := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : LocallyCompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.locallyCompactSpace d
  let : SecondCountableTopology (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.secondCountableTopology d
  exact Scheme.ComplexPoints.singularCochainSheaf_derivedGlobalSections_isZero q n hn

theorem projectiveLine_terms (q n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections ℚ
      (SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ)))).rightDerived n).obj
        (SingularCochains.cochainSheaf (SchemeBetti.space (projectiveLine ℂ ↘ Spec (.of ℂ))) q)) := by
  let : T2Space (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalT2Space
  let : LocallyCompactSpace (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
  let : SecondCountableTopology (Scheme.ComplexPoints (projectiveLine ℂ ↘ Spec (.of ℂ))) :=
    ProjectiveLineComplexPoints.canonicalSecondCountableTopology
  exact Scheme.ComplexPoints.singularCochainSheaf_derivedGlobalSections_isZero q n hn

/-- Termwise acyclicity retains the original nonzero total singular degree-two class. -/
theorem projectiveLine_total_h2_nonzero : ProjectiveLineBettiCohomology.coverGenerator ≠ 0 :=
  ProjectiveLineBettiCohomology.coverGenerator_ne_zero

/-- The original de Rham public helper delegates to the same shared native comparison. -/
theorem legacy_forget_comparison (k : Type) [CommRing k] (X : Scheme)
    (M : TopCat.Sheaf (ModuleCat k) X) (U : X.Opens) (n : ℕ) :
    (SchemeDeRham.moduleCohomologyForgetIso k X M U n).hom =
      (SheafCohomology.LinearCoefficients.cohomologyForgetIso k X M U n).hom := rfl

theorem empty_terms (q n : ℕ) (hn : 0 < n) :
    IsZero (((SheafHypercohomology.globalSections ℚ (TopCat.of Empty)).rightDerived n).obj
      (SingularCochains.cochainSheaf (TopCat.of Empty) q)) :=
  SingularCochains.isZero_cochainSheaf_derivedGlobalSections _ q n hn

example : IsZero (((SheafHypercohomology.globalSections ℚ (SchemeBetti.space (affineBase 0))).rightDerived 1).obj
    (SingularCochains.cochainSheaf (SchemeBetti.space (affineBase 0)) 0)) := affine_terms 0 0 1 (by decide)

end FlasqueDerivedVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.BoundedBelowDerived.rightDerivedPostcomposeIso,
      `HodgeConjecture.SheafCohomology.Cohomology.BasisCycles.isZero_Hobj_of_isFlasque,
      `HodgeConjecture.SheafCohomology.LinearCoefficients.underlying_isFlasque_of_isFlasque,
      `HodgeConjecture.SheafCohomology.LinearCoefficients.cohomologyForgetIso,
      `HodgeConjecture.SheafCohomology.LinearCoefficients.isZero_cohomology_of_isFlasque,
      `HodgeConjecture.SheafCohomology.LinearCoefficients.isZero_rightDerived_globalSections_of_isFlasque,
      `HodgeConjecture.SingularCochains.isZero_cochainSheaf_cohomology_of_open_paracompact,
      `HodgeConjecture.SingularCochains.isZero_cochainSheaf_cohomology,
      `HodgeConjecture.SingularCochains.isZero_cochainSheaf_derivedGlobalSections,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCochainSheaf_cohomology_isZero,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCochainSheaf_derivedGlobalSections_isZero,
      `FlasqueDerivedVerification.skyscraper_higher,
      `FlasqueDerivedVerification.real_terms,
      `FlasqueDerivedVerification.real_open_terms,
      `FlasqueDerivedVerification.affine_terms,
      `FlasqueDerivedVerification.projectiveLine_terms,
      `FlasqueDerivedVerification.projectiveLine_total_h2_nonzero,
      `FlasqueDerivedVerification.legacy_forget_comparison,
      `FlasqueDerivedVerification.empty_terms] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
