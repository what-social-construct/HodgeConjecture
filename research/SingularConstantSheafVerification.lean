module

public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace SingularConstantSheafVerification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HodgeConjecture

attribute [local instance] HasDerivedCategory.standard

local instance : StronglyLocallyContractibleSpace ℝ := normedSpace_stronglyLocallyContractible ℝ

local instance : StronglyLocallyContractibleSpace Empty where
  contractible_basis x := Empty.elim x

local instance (U : Opens ℝ) : LocallyCompactSpace (TopCat.of U) :=
  U.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace

local instance (U : Opens ℝ) : StronglyLocallyContractibleSpace (TopCat.of U) :=
  U.isOpen.stronglyLocallyContractibleSpace

theorem real_bridge (n : ℕ) :
    IsIso (SingularCochains.cohomologyToConstantSheafDerived (TopCat.of ℝ) n) :=
  SingularCochains.cohomologyToConstantSheafDerived_isIso _ n

/-- The endpoint is the native constant sheaf and ordinary right-derived global sections. -/
def real_iso (n : ℕ) : SingularCochains.Cohomology (TopCat.of ℝ) n ≅
    ((SheafHypercohomology.globalSections ℚ (TopCat.of ℝ)).rightDerived n).obj
      (SheafCohomology.ConstantLift.sheaf ℚ (TopCat.of ℝ)) :=
  SingularCochains.cohomologyIsoConstantSheafDerived _ n

theorem real_iso_hom (n : ℕ) : (real_iso n).hom =
    SingularCochains.cohomologyToConstantSheafDerived (TopCat.of ℝ) n := rfl

theorem real_open_bridge (U : Opens ℝ) (n : ℕ) :
    IsIso (SingularCochains.cohomologyToConstantSheafDerived (TopCat.of U) n) :=
  SingularCochains.cohomologyToConstantSheafDerived_isIso _ n

theorem empty_bridge (n : ℕ) :
    IsIso (SingularCochains.cohomologyToConstantSheafDerived (TopCat.of Empty) n) :=
  SingularCochains.cohomologyToConstantSheafDerived_isIso _ n

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

theorem affine_bridge (d n : ℕ) :
    IsIso (Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived
      (x := affineBase d) d n) := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : LocallyCompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.locallyCompactSpace d
  let : SecondCountableTopology (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.secondCountableTopology d
  exact Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived_isIso d n

abbrev p1Base := projectiveLine ℂ ↘ Spec (.of ℂ)
abbrev p1Space := SchemeBetti.space p1Base

local instance : T2Space p1Space := ProjectiveLineComplexPoints.canonicalT2Space
local instance : LocallyCompactSpace p1Space := ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
local instance : SecondCountableTopology p1Space := ProjectiveLineComplexPoints.canonicalSecondCountableTopology
local instance : StronglyLocallyContractibleSpace p1Space :=
  Scheme.ComplexPoints.stronglyLocallyContractibleSpace (x := p1Base) 1

theorem projectiveLine_bridge (n : ℕ) :
    IsIso (Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived (x := p1Base) 1 n) :=
  Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived_isIso 1 n

/-- The original nonzero class is transported through the already proved canonical homeomorphism. -/
def canonicalGenerator : SingularCochains.Cohomology p1Space 2 :=
  (SingularHomotopy.homeomorphIso ProjectiveLineComplexPoints.canonicalHomeomorph.symm 2).hom
    ProjectiveLineBettiCohomology.coverGenerator

theorem canonicalGenerator_ne_zero : canonicalGenerator ≠ 0 := by
  intro h
  let e := SingularHomotopy.homeomorphIso ProjectiveLineComplexPoints.canonicalHomeomorph.symm 2
  have hinj := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  apply ProjectiveLineBettiCohomology.coverGenerator_ne_zero
  apply hinj
  simpa [canonicalGenerator, e] using h

/-- An actual class of the original derived constant-sheaf target. -/
def derivedGenerator : ((SheafHypercohomology.globalSections ℚ p1Space).rightDerived 2).obj
    (SheafCohomology.ConstantLift.sheaf ℚ p1Space) :=
  SingularCochains.cohomologyToConstantSheafDerived p1Space 2 canonicalGenerator

/-- The assembled bridge retains the nonzero degree-two class in the derived target itself. -/
theorem derivedGenerator_ne_zero : derivedGenerator ≠ 0 := by
  intro h
  exact canonicalGenerator_ne_zero
    ((SingularCochains.cohomologyToConstantSheafDerived_eq_zero_iff p1Space 2 canonicalGenerator).mp h)

theorem original_resolution_square (n : ℕ) :
    SingularCochains.cohomologyToConstantSheafDerived (TopCat.of ℝ) n ≫
        (SheafHypercohomology.singleIsoRightDerived ℚ (TopCat.of ℝ)
          (SingularCochains.constantSheaf (TopCat.of ℝ)) n).inv ≫
        SheafHypercohomology.hypercohomologyMap ℚ (TopCat.of ℝ)
          (SingularCochains.comparison (TopCat.of ℝ)) (n : ℤ) =
      SingularCochains.cohomologyToHypercohomology (TopCat.of ℝ) n :=
  SingularCochains.cohomologyToConstantSheafDerived_resolution _ n

example : IsIso (Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived
    (x := affineBase 0) 0 0) := affine_bridge 0 0

end SingularConstantSheafVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafHypercohomology.nonnegativeSectionsHomologyIso,
      `HodgeConjecture.SheafHypercohomology.derivedGlobalSectionsMap_isIso,
      `HodgeConjecture.SheafHypercohomology.hypercohomologyMap_isIso,
      `HodgeConjecture.SheafHypercohomology.hypercohomologyIsoOfQuasiIso,
      `HodgeConjecture.SheafHypercohomology.hypercohomologyIsoOfQuasiIso_hom,
      `HodgeConjecture.SingularCochains.cohomologyToHypercohomology,
      `HodgeConjecture.SingularCochains.cohomologyToHypercohomology_isIso_of_flasqueTerms,
      `HodgeConjecture.SingularCochains.cohomologyToHypercohomology_isIso,
      `HodgeConjecture.SingularCochains.constantResolutionHypercohomologyIso,
      `HodgeConjecture.SingularCochains.constantResolutionHypercohomologyIso_hom,
      `HodgeConjecture.SingularCochains.cohomologyToConstantSheafDerived,
      `HodgeConjecture.SingularCochains.cohomologyToConstantSheafDerived_isIso,
      `HodgeConjecture.SingularCochains.cohomologyIsoConstantSheafDerived,
      `HodgeConjecture.SingularCochains.cohomologyIsoConstantSheafDerived_hom,
      `HodgeConjecture.SingularCochains.cohomologyToConstantSheafDerived_resolution,
      `HodgeConjecture.SingularCochains.cohomologyToConstantSheafDerived_eq_zero_iff,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCohomologyToConstantSheafDerived_isIso,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCohomologyIsoConstantSheafDerived,
      `AlgebraicGeometry.Scheme.ComplexPoints.singularCohomologyIsoConstantSheafDerived_hom,
      `SingularConstantSheafVerification.real_bridge,
      `SingularConstantSheafVerification.real_iso,
      `SingularConstantSheafVerification.real_iso_hom,
      `SingularConstantSheafVerification.real_open_bridge,
      `SingularConstantSheafVerification.empty_bridge,
      `SingularConstantSheafVerification.affine_bridge,
      `SingularConstantSheafVerification.projectiveLine_bridge,
      `SingularConstantSheafVerification.canonicalGenerator,
      `SingularConstantSheafVerification.canonicalGenerator_ne_zero,
      `SingularConstantSheafVerification.derivedGenerator,
      `SingularConstantSheafVerification.derivedGenerator_ne_zero,
      `SingularConstantSheafVerification.original_resolution_square] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
