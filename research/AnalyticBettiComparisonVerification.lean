module

public import HodgeConjecture.Realization.DeRham.AnalyticBettiComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import HodgeConjecture.Geometry.PolynomialComplexPoints
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace AnalyticBettiComparisonVerification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HodgeConjecture
open scoped Manifold ContDiff TensorProduct

attribute [local instance] HasDerivedCategory.standard

local instance : StronglyLocallyContractibleSpace ℂ := normedSpace_stronglyLocallyContractible ℂ

/-- Coefficient inclusion retains the ordinary rational-to-complex scalar map. -/
theorem coefficient_one : SheafCohomology.ScalarRestriction.coefficientModuleMap
    (algebraMap ℚ ℂ) (1 : ℚ) = (1 : ℂ) := by
  change (algebraMap ℚ ℂ) (1 : ℚ) = 1
  exact map_one _

theorem native_constant_map (X : TopCat.{0}) :
    SheafCohomology.ScalarRestriction.constantMap (algebraMap ℚ ℂ) X ≫
      (SheafCohomology.ScalarRestriction.constantIso (algebraMap ℚ ℂ) X).hom =
    (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).map
      (SheafCohomology.ScalarRestriction.coefficientModuleMap (algebraMap ℚ ℂ)) := by
  exact (SheafCohomology.ScalarRestriction.constantIso (algebraMap ℚ ℂ) X).eq_comp_inv.mp rfl

/-- Restriction comparison uses the original constant sheaves and original right-derived functors. -/
def restricted_cohomology_iso (X : TopCat.{0}) (n : ℕ) :
    ((SheafHypercohomology.globalSections ℚ X).rightDerived n).obj
        ((SheafCohomology.ScalarRestriction.sheaves (algebraMap ℚ ℂ) X).obj
          (SheafCohomology.ConstantLift.sheaf ℂ X)) ≅
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
        (((SheafHypercohomology.globalSections ℂ X).rightDerived n).obj
          (SheafCohomology.ConstantLift.sheaf ℂ X)) :=
  SheafCohomology.ScalarRestriction.cohomologyIso _ _ _ n

def complexLine_constant_iso (n : ℕ) :
    ((SheafHypercohomology.globalSections ℂ (TopCat.of ℂ)).rightDerived n).obj
        (SheafCohomology.ConstantLift.sheaf ℂ (TopCat.of ℂ)) ≅
      SheafHypercohomology.hypercohomology ℂ (TopCat.of ℂ) (HolomorphicAtlas.complex ℂ ℂ) (n : ℤ) :=
  HolomorphicAtlas.constantSheafDerivedIso ℂ ℂ n

theorem complexLine_rational_mono (n : ℕ) :
    Mono (AnalyticBettiComparison.rationalComparison ℂ ℂ n) :=
  AnalyticBettiComparison.rationalComparison_mono ℂ ℂ n

theorem complexLine_embedding (n : ℕ) (α : SingularCochains.Cohomology (TopCat.of ℂ) n) :
    AnalyticBettiComparison.complexComparison ℂ ℂ n (RationalComplexification.embedding _ α) = 0 ↔ α = 0 :=
  AnalyticBettiComparison.complexComparison_embedding_eq_zero_iff ℂ ℂ n α

theorem complexLine_tmul (n : ℕ) (c : ℂ) (α : SingularCochains.Cohomology (TopCat.of ℂ) n) :
    AnalyticBettiComparison.complexComparison ℂ ℂ n (c ⊗ₜ[ℚ] α) =
      c • (show SheafHypercohomology.hypercohomology ℂ (TopCat.of ℂ)
        (HolomorphicAtlas.complex ℂ ℂ) (n : ℤ) from AnalyticBettiComparison.rationalComparison ℂ ℂ n α) :=
  AnalyticBettiComparison.complexComparison_tmul ℂ ℂ n c α

abbrev affineBase (d : ℕ) := AffineComplexPoints.structureMorphism (MvPolynomial (Fin d) ℂ)

theorem affine_embedding (d n : ℕ) (α : SchemeBetti.Cohomology (affineBase d) n) :
    Scheme.ComplexPoints.holomorphicBettiComparison (x := affineBase d) d n
        (RationalComplexification.embedding _ α) = 0 ↔ α = 0 := by
  let : T2Space (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.t2Space d
  let : LocallyCompactSpace (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.locallyCompactSpace d
  let : SecondCountableTopology (Scheme.ComplexPoints (affineBase d)) := PolynomialComplexPoints.secondCountableTopology d
  exact Scheme.ComplexPoints.holomorphicBettiComparison_embedding_eq_zero_iff d n α

abbrev p1Base := projectiveLine ℂ ↘ Spec (.of ℂ)
abbrev p1Space := SchemeBetti.space p1Base

local instance : T2Space p1Space := ProjectiveLineComplexPoints.canonicalT2Space
local instance : LocallyCompactSpace p1Space := ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
local instance : SecondCountableTopology p1Space := ProjectiveLineComplexPoints.canonicalSecondCountableTopology

/-- The existing canonical P¹ Betti equivalence supplies the original class. -/
def mappedGenerator :
    SheafHypercohomology.hypercohomology ℂ p1Space
      (HolomorphicAtlas.complex (Fin 1 → ℂ) (Scheme.ComplexPoints p1Base)) 2 :=
  Scheme.ComplexPoints.holomorphicBettiComparison (x := p1Base) 1 2
    (RationalComplexification.embedding _
      (ProjectiveLineCanonicalComparison.bettiEquiv 2 ProjectiveLineBettiCohomology.coverGenerator))

/-- The actual holomorphic hypercohomology target retains the original nonzero degree-two class. -/
theorem mappedGenerator_ne_zero : mappedGenerator ≠ 0 := by
  intro h
  have hz := (Scheme.ComplexPoints.holomorphicBettiComparison_embedding_eq_zero_iff
    (x := p1Base) 1 2
    (ProjectiveLineCanonicalComparison.bettiEquiv 2 ProjectiveLineBettiCohomology.coverGenerator)).mp h
  apply ProjectiveLineBettiCohomology.coverGenerator_ne_zero
  apply (ProjectiveLineCanonicalComparison.bettiEquiv 2).injective
  simpa using hz

theorem holomorphic_resolution_square (n : ℕ) :
    (SheafHypercohomology.singleIsoRightDerived ℂ (TopCat.of ℂ)
      (HolomorphicAtlas.constantSheaf ℂ) n).hom ≫
        (HolomorphicAtlas.constantSheafDerivedIso ℂ ℂ n).hom =
      SheafHypercohomology.hypercohomologyMap ℂ (TopCat.of ℂ)
        (HolomorphicAtlas.comparison ℂ ℂ) (n : ℤ) :=
  HolomorphicAtlas.constantSheafDerivedIso_resolution ℂ ℂ n

example (α : SchemeBetti.Cohomology (affineBase 0) 0) :
    Scheme.ComplexPoints.holomorphicBettiComparison (x := affineBase 0) 0 0
      (RationalComplexification.embedding _ α) = 0 ↔ α = 0 := affine_embedding 0 0 α

end AnalyticBettiComparisonVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SheafCohomology.ScalarRestriction.sheaves,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.isFlasque,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.injective_isFlasque,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.coefficientModuleMap,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.constantIso,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.constantMap,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.extendLinear,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.extendLinear_tmul,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.extendLinear_one_tmul,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.cohomologyIso,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.constantCohomologyMap,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.constantMap_isSplitMono,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.constantCohomologyMap_mono,
      `HodgeConjecture.HolomorphicAtlas.constantSheafDerivedIso,
      `HodgeConjecture.HolomorphicAtlas.constantSheafDerivedIso_resolution,
      `HodgeConjecture.AnalyticBettiComparison.rationalComparison,
      `HodgeConjecture.AnalyticBettiComparison.complexComparison,
      `HodgeConjecture.AnalyticBettiComparison.complexComparison_one_tmul,
      `HodgeConjecture.AnalyticBettiComparison.complexComparison_tmul,
      `HodgeConjecture.AnalyticBettiComparison.rationalComparison_mono,
      `HodgeConjecture.AnalyticBettiComparison.complexComparison_embedding_eq_zero_iff,
      `AlgebraicGeometry.Scheme.ComplexPoints.holomorphicBettiComparison,
      `AlgebraicGeometry.Scheme.ComplexPoints.holomorphicBettiComparison_embedding_eq_zero_iff,
      `AnalyticBettiComparisonVerification.coefficient_one,
      `AnalyticBettiComparisonVerification.native_constant_map,
      `AnalyticBettiComparisonVerification.restricted_cohomology_iso,
      `AnalyticBettiComparisonVerification.complexLine_constant_iso,
      `AnalyticBettiComparisonVerification.complexLine_rational_mono,
      `AnalyticBettiComparisonVerification.complexLine_embedding,
      `AnalyticBettiComparisonVerification.complexLine_tmul,
      `AnalyticBettiComparisonVerification.affine_embedding,
      `AnalyticBettiComparisonVerification.mappedGenerator,
      `AnalyticBettiComparisonVerification.mappedGenerator_ne_zero,
      `AnalyticBettiComparisonVerification.holomorphic_resolution_square] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
