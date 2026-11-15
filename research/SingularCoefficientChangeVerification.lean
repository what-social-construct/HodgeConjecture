module

public import HodgeConjecture.Realization.Betti.CoefficientChange
public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

namespace SingularCoefficientChangeVerification

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomologicalComplex HodgeConjecture Simplicial
open scoped TensorProduct

theorem originalFunctor : RationalDual.functor = HomCoefficients.functor ℚ ℚ := rfl

theorem originalComplex (K : ChainComplex (ModuleCat.{0} ℚ) ℕ) :
    RationalDual.dualComplex K = HomCoefficients.dualComplex ℚ ℚ K := rfl

/-- An infinite-dimensional exact sequence remains exact with unrestricted complex coefficients. -/
def infiniteSplit : ShortComplex (ModuleCat.{0} ℚ) :=
  ShortComplex.moduleCatMk
    (LinearMap.inl ℚ ℚ (ℕ →₀ ℚ)) (LinearMap.snd ℚ ℚ (ℕ →₀ ℚ)) (by ext x; rfl)

theorem infiniteSplit_exact : infiniteSplit.Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  rintro ⟨a, v⟩ hv
  exact ⟨a, Prod.ext rfl hv.symm⟩

theorem complexSplit_exact : (infiniteSplit.op.map (HomCoefficients.functor ℚ ℂ)).Exact :=
  HomCoefficients.map_exact ℚ ℂ _ infiniteSplit_exact.op

theorem actualTranspose (X : TopCat.{0}) (i j : ℕ)
    (φ : (SingularCoefficientChange.chains X).X i →ₗ[ℚ] ℂ)
    (v : (SingularCoefficientChange.chains X).X j) :
    (show (SingularCoefficientChange.chains X).X j →ₗ[ℚ] ℂ from
      (SingularCoefficientChange.complexCochains X).d i j φ) v =
        φ ((SingularCoefficientChange.chains X).d j i v) := rfl

/-- Coordinate cochains have the original alternating face differential with complex values. -/
theorem actualDifferential (X : TopCat.{0}) (n : ℕ)
    (φ : (SingularCoefficientChange.chains X).X n →ₗ[ℚ] ℂ)
    (σ : SingularCochains.Simplex X (n + 1)) :
    SingularCoefficientChange.complexCoordinates X (n + 1)
        ((SingularCoefficientChange.complexCochains X).d n (n + 1) φ) σ =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        SingularCoefficientChange.complexCoordinates X n φ ((TopCat.toSSet.obj X).δ i σ) := by
  change φ ((SingularCoefficientChange.chains X).d (n + 1) n
      (SingularChainCoordinates.coordinates (TopCat.toSSet.obj X) (n + 1) (Finsupp.single σ 1))) = _
  rw [SingularChainCoordinates.coordinates_boundary, SingularChainCoordinates.boundary_single]
  simp only [map_sum, map_smul, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rfl

/-- Vanishing in a degree supplies finiteness while the original singular chain modules are unrestricted. -/
theorem contractibleComparison_isIso (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) : IsIso (SingularCoefficientChange.cohomologyComparison (TopCat.of X) (n + 1)) := by
  have : Subsingleton (SingularCochains.Cohomology (TopCat.of X) (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp (SingularContractible.isZero_cohomology X (n + 1) (by omega))
  have : FiniteDimensional ℚ (SingularCochains.Cohomology (TopCat.of X) (n + 1)) := inferInstance
  exact SingularCoefficientChange.cohomologyComparison_isIso _ _

abbrev p1 := TopCat.of ProjectiveLineComplexPoints.Point

theorem p1Comparison_isIso : IsIso (SingularCoefficientChange.cohomologyComparison p1 2) :=
  SingularCoefficientChange.cohomologyComparison_isIso p1 2

theorem canonicalComparison_isIso :
    IsIso (SingularCoefficientChange.cohomologyComparison
      (SchemeBetti.space (AlgebraicGeometry.projectiveLine ℂ ↘ AlgebraicGeometry.Spec (.of ℂ))) 2) := by
  have : FiniteDimensional ℚ (SchemeBetti.Cohomology
      (AlgebraicGeometry.projectiveLine ℂ ↘ AlgebraicGeometry.Spec (.of ℂ)) 2) :=
    (ProjectiveLineCanonicalComparison.bettiEquiv 2).finiteDimensional
  exact SingularCoefficientChange.cohomologyComparison_isIso _ _

/-- The original singular generator, in the actual complex-functional cohomology target. -/
def mappedGenerator : SingularCoefficientChange.ComplexCohomology p1 2 :=
  SingularCoefficientChange.cohomologyComparison p1 2
    (RationalComplexification.embedding _ ProjectiveLineBettiCohomology.coverGenerator)

theorem mappedGenerator_ne_zero : mappedGenerator ≠ 0 := by
  have := p1Comparison_isIso
  have hi := (ModuleCat.mono_iff_injective
    (SingularCoefficientChange.cohomologyComparison p1 2)).mp inferInstance
  intro h
  have hz : RationalComplexification.embedding _ ProjectiveLineBettiCohomology.coverGenerator = 0 := by
    apply hi
    simpa only [mappedGenerator, map_zero] using h
  apply ProjectiveLineBettiCohomology.coverGenerator_ne_zero
  apply RationalComplexification.embedding_injective _
  simpa using hz

example : IsIso (SingularCoefficientChange.cohomologyComparison (TopCat.of ℝ) 4) :=
  contractibleComparison_isIso ℝ 3

end SingularCoefficientChangeVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.HomCoefficients.functor,
      `HodgeConjecture.HomCoefficients.exists_factor,
      `HodgeConjecture.HomCoefficients.map_exact,
      `HodgeConjecture.HomCoefficients.inclusion,
      `HodgeConjecture.HomCoefficients.comparison,
      `HodgeConjecture.HomCoefficients.comparison_tmul,
      `HodgeConjecture.HomCoefficients.comparison_bijective,
      `HodgeConjecture.HomCoefficients.comparisonEquiv,
      `HodgeConjecture.HomCoefficients.tensorFunctor,
      `HodgeConjecture.HomCoefficients.tensorFunctor_map_exact,
      `HodgeConjecture.HomCoefficients.coefficientTransform,
      `HodgeConjecture.HomCoefficients.dualHomologyIso,
      `HodgeConjecture.HomCoefficients.complexComparison,
      `HodgeConjecture.HomCoefficients.complexComparison_apply,
      `HodgeConjecture.HomCoefficients.tensorHomologyIso,
      `HodgeConjecture.HomCoefficients.tensorHomologyIso_naturality,
      `HodgeConjecture.HomCoefficients.cohomologyComparison,
      `HodgeConjecture.HomCoefficients.tensorHomologyIso_cohomologyComparison,
      `HodgeConjecture.HomCoefficients.complexComparison_quasiIsoAt,
      `HodgeConjecture.HomCoefficients.cohomologyComparison_isIso,
      `HodgeConjecture.HomCoefficients.cohomologyIso,
      `HodgeConjecture.RationalDual.functor,
      `HodgeConjecture.RationalDual.map_exact,
      `HodgeConjecture.RationalDual.dualMap_quasiIso,
      `HodgeConjecture.SingularCoefficientChange.rationalComplexIso,
      `HodgeConjecture.SingularCoefficientChange.complexCoordinates,
      `HodgeConjecture.SingularCoefficientChange.cochainComparison,
      `HodgeConjecture.SingularCoefficientChange.cochainComparison_apply,
      `HodgeConjecture.SingularCoefficientChange.cohomologyComparison,
      `HodgeConjecture.SingularCoefficientChange.cohomologyComparison_induced,
      `HodgeConjecture.SingularCoefficientChange.finiteHomology_of_finiteCohomology,
      `HodgeConjecture.SingularCoefficientChange.cohomologyComparison_isIso,
      `HodgeConjecture.SingularCoefficientChange.cohomologyIso,
      `SingularCoefficientChangeVerification.originalFunctor,
      `SingularCoefficientChangeVerification.originalComplex,
      `SingularCoefficientChangeVerification.infiniteSplit,
      `SingularCoefficientChangeVerification.infiniteSplit_exact,
      `SingularCoefficientChangeVerification.complexSplit_exact,
      `SingularCoefficientChangeVerification.actualTranspose,
      `SingularCoefficientChangeVerification.actualDifferential,
      `SingularCoefficientChangeVerification.contractibleComparison_isIso,
      `SingularCoefficientChangeVerification.p1Comparison_isIso,
      `SingularCoefficientChangeVerification.canonicalComparison_isIso,
      `SingularCoefficientChangeVerification.mappedGenerator,
      `SingularCoefficientChangeVerification.mappedGenerator_ne_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
