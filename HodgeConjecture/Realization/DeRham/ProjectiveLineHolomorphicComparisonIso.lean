module

public import HodgeConjecture.Realization.DeRham.AnalyticComplexSingularComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison
public import HodgeConjecture.Geometry.ProjectiveLineSmooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public noncomputable section

/-!
# The original holomorphic Betti comparison on projective-line H²

The original complex-linear map is nonzero on the transported rational
cover generator. Both its source and target have complex dimension one:
the source by the computed singular coordinates, and the target by the
separately constructed cochain-to-holomorphic isomorphism.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct Manifold ContDiff

namespace HodgeConjecture.ProjectiveLineHolomorphicComparisonIso

abbrev x : projectiveLine ℂ ⟶ Spec (.of ℂ) :=
  projectiveLine ℂ ↘ Spec (.of ℂ)

abbrev M := Scheme.ComplexPoints x

abbrev Betti := SchemeBetti.Cohomology x 2
abbrev Source := RationalComplexification.Space Betti
abbrev Target := SheafHypercohomology.hypercohomology ℂ (SchemeBetti.space x)
  (HolomorphicAtlas.complex (Fin 1 → ℂ) M) (2 : ℤ)

/-- The existing canonical scheme-point map, without a chosen substitute. -/
abbrev comparison : Source →ₗ[ℂ] Target :=
  Scheme.ComplexPoints.holomorphicBettiComparison (x := x) 1 2

/-- The transported cover generator in the actual rational scheme-point cohomology. -/
def generator : Betti :=
  ProjectiveLineCanonicalComparison.bettiEquiv 2
    ProjectiveLineBettiCohomology.coverGenerator

theorem generator_ne_zero : generator ≠ 0 := by
  intro h
  apply ProjectiveLineBettiCohomology.coverGenerator_ne_zero
  exact (ProjectiveLineCanonicalComparison.bettiEquiv 2).injective (by simpa [generator] using h)

/-- The original tensor source has the computed one-dimensional coordinate. -/
def sourceCoordinates : Source ≃ₗ[ℂ] ℂ :=
  ProjectiveLineCanonicalComparison.complexificationEquiv.symm.trans
    ProjectiveLineBettiComplexification.coordinates

theorem source_finrank : Module.finrank ℂ Source = 1 := by
  rw [sourceCoordinates.finrank_eq]
  exact Module.finrank_self ℂ

theorem embedded_generator_ne_zero : RationalComplexification.embedding Betti generator ≠ 0 := by
  intro h
  apply generator_ne_zero
  apply RationalComplexification.embedding_injective Betti
  simpa using h

theorem comparison_embedded_generator_ne_zero :
    comparison (RationalComplexification.embedding Betti generator) ≠ 0 := by
  letI : T2Space M := ProjectiveLineComplexPoints.canonicalT2Space
  letI : LocallyCompactSpace M := ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
  letI : SecondCountableTopology M := ProjectiveLineComplexPoints.canonicalSecondCountableTopology
  intro h
  exact generator_ne_zero ((Scheme.ComplexPoints.holomorphicBettiComparison_embedding_eq_zero_iff
    (x := x) 1 2 generator).mp h)

/-- An independently constructed cochain comparison fixes the dimension of the holomorphic target. -/
def targetCoordinates : Target ≃ₗ[ℂ] ℂ := by
  letI : T2Space M := ProjectiveLineComplexPoints.canonicalT2Space
  letI : LocallyCompactSpace M := ProjectiveLineComplexPoints.canonicalLocallyCompactSpace
  letI : SecondCountableTopology M := ProjectiveLineComplexPoints.canonicalSecondCountableTopology
  letI : StronglyLocallyContractibleSpace M :=
    Scheme.ComplexPoints.stronglyLocallyContractibleSpace (x := x) 1
  letI : FiniteDimensional ℚ (SingularCochains.Cohomology (TopCat.of M) 2) :=
    (ProjectiveLineCanonicalComparison.bettiEquiv 2).finiteDimensional
  let f := SingularCoefficientChange.cohomologyComparison (TopCat.of M) 2 ≫
    HodgeConjecture.AnalyticBettiComparison.complexSingularToHolomorphic (Fin 1 → ℂ) M 2
  have hf : IsIso f := by
    letI := SingularCoefficientChange.cohomologyComparison_isIso (TopCat.of M) 2
    letI := HodgeConjecture.AnalyticBettiComparison.complexSingularToHolomorphic_isIso
      (Fin 1 → ℂ) M 2
    dsimp [f]
    infer_instance
  exact (asIso f).toLinearEquiv.symm.trans sourceCoordinates

theorem target_finrank : Module.finrank ℂ Target = 1 := by
  rw [targetCoordinates.finrank_eq]
  exact Module.finrank_self ℂ

/-- The original map in the independently computed one-dimensional coordinates. -/
def scalarComparison : ℂ →ₗ[ℂ] ℂ :=
  targetCoordinates.toLinearMap.comp (comparison.comp sourceCoordinates.symm.toLinearMap)

theorem scalarComparison_apply (z : ℂ) :
    scalarComparison z = z * scalarComparison 1 := by
  conv_lhs => rw [show z = z • (1 : ℂ) by simp]
  rw [map_smul]
  simp [smul_eq_mul]

theorem scalarComparison_one_ne_zero : scalarComparison 1 ≠ 0 := by
  have hg : scalarComparison
      (sourceCoordinates (RationalComplexification.embedding Betti generator)) ≠ 0 := by
    intro h
    apply comparison_embedded_generator_ne_zero
    apply targetCoordinates.injective
    simpa [scalarComparison] using h
  intro h
  apply hg
  rw [scalarComparison_apply, h, mul_zero]

/-- The original canonical P¹ map is bijective in degree two. -/
theorem comparison_bijective : Function.Bijective comparison := by
  let e : ℂ ≃ₗ[ℂ] ℂ :=
    LinearEquiv.smulOfNeZero ℂ ℂ (scalarComparison 1) scalarComparison_one_ne_zero
  have he : scalarComparison = e.toLinearMap := by
    apply LinearMap.ext
    intro z
    change scalarComparison z = scalarComparison 1 • z
    rw [scalarComparison_apply]
    simp [smul_eq_mul, mul_comm]
  have hg : Function.Bijective scalarComparison := by
    rw [he]
    exact e.bijective
  constructor
  · intro a b hab
    apply sourceCoordinates.injective
    apply hg.1
    have h := congrArg targetCoordinates hab
    simpa [scalarComparison] using h
  · intro y
    obtain ⟨z, hz⟩ := hg.2 (targetCoordinates y)
    refine ⟨sourceCoordinates.symm z, ?_⟩
    apply targetCoordinates.injective
    simpa [scalarComparison] using hz

/-- Invertibility of the original canonical scheme-point comparison, as a module morphism. -/
theorem holomorphicBettiComparison_isIso :
    IsIso (ModuleCat.ofHom
      (Scheme.ComplexPoints.holomorphicBettiComparison (x := x) 1 2)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact comparison_bijective

/-- The inverse of the original canonical scheme-point comparison. -/
def comparisonEquiv : Source ≃ₗ[ℂ] Target :=
  LinearEquiv.ofBijective comparison comparison_bijective

@[simp]
theorem comparisonEquiv_apply (z : Source) : comparisonEquiv z = comparison z := rfl

end HodgeConjecture.ProjectiveLineHolomorphicComparisonIso
