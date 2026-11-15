module

public import HodgeConjecture.Realization.DeRham.HolomorphicHypercohomology
public import HodgeConjecture.Realization.Betti.SchemeSingularSheaves
public import HodgeConjecture.Realization.HodgeFiltration
public import HodgeConjecture.SheafCohomology.DerivedScalarRestrictionNaturality

@[expose] public noncomputable section

/-!
# The actual complex Betti-to-holomorphic comparison map

Coefficient inclusion on the original constant sheaves, the original
rational singular comparison, and the existing holomorphic resolution
give a rational comparison. The native tensor universal property extends it to
the existing tensor complexification of rational Betti cohomology.
Invertibility of the complex-linear map is a separate coefficient comparison.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff TensorProduct

namespace HodgeConjecture.AnalyticBettiComparison

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StronglyLocallyContractibleSpace M]

attribute [local instance] HasDerivedCategory.standard

/-- Coefficient inclusion followed by the original holomorphic Poincaré resolution. -/
def rationalComparison (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of M) n ⟶
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj
        (SheafHypercohomology.hypercohomology ℂ (TopCat.of M) (HolomorphicAtlas.complex E M) (n : ℤ)) :=
  SingularCochains.cohomologyToConstantSheafDerived (TopCat.of M) n ≫
    SheafCohomology.ScalarRestriction.constantCohomologyMap (algebraMap ℚ ℂ) (TopCat.of M) n ≫
    ((ModuleCat.restrictScalars (algebraMap ℚ ℂ)).mapIso
      (HolomorphicAtlas.constantSheafDerivedIso E M n)).hom

/-- The original complexification is the source; extension uses the native tensor universal property. -/
def complexComparison (n : ℕ) :
    RationalComplexification.Space (SingularCochains.Cohomology (TopCat.of M) n) →ₗ[ℂ]
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M) (HolomorphicAtlas.complex E M) (n : ℤ) :=
  SheafCohomology.ScalarRestriction.extendLinear (rationalComparison E M n)

/-- The constructed complex-linear map retains the original rational comparison on pure tensors. -/
@[simp]
theorem complexComparison_one_tmul (n : ℕ) (α : SingularCochains.Cohomology (TopCat.of M) n) :
    complexComparison E M n (1 ⊗ₜ[ℚ] α) = rationalComparison E M n α := by
  exact SheafCohomology.ScalarRestriction.extendLinear_one_tmul (rationalComparison E M n) α

@[simp]
theorem complexComparison_tmul (n : ℕ) (c : ℂ)
    (α : SingularCochains.Cohomology (TopCat.of M) n) :
    complexComparison E M n (c ⊗ₜ[ℚ] α) = c •
      (show SheafHypercohomology.hypercohomology ℂ (TopCat.of M)
        (HolomorphicAtlas.complex E M) (n : ℤ) from rationalComparison E M n α) := by
  exact SheafCohomology.ScalarRestriction.extendLinear_tmul (rationalComparison E M n) c α

/-- The rational comparison is injective because coefficient inclusion splits rationally. -/
theorem rationalComparison_mono [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]
    (n : ℕ) : Mono (rationalComparison E M n) := by
  have : IsSplitMono (SheafCohomology.ScalarRestriction.constantMap (algebraMap ℚ ℂ) (TopCat.of M)) :=
    SheafCohomology.ScalarRestriction.constantMap_isSplitMono _ (algebraMap ℚ ℂ).injective _
  have := SheafCohomology.ScalarRestriction.constantCohomologyMap_mono
    (algebraMap ℚ ℂ) (TopCat.of M) n
  have := SingularCochains.cohomologyToConstantSheafDerived_isIso (TopCat.of M) n
  unfold rationalComparison
  infer_instance

/-- Zero-class detection on the existing rational diagonal of the complexification. -/
theorem complexComparison_embedding_eq_zero_iff
    [T2Space M] [LocallyCompactSpace M] [SecondCountableTopology M]
    (n : ℕ) (α : SingularCochains.Cohomology (TopCat.of M) n) :
    complexComparison E M n (RationalComplexification.embedding _ α) = 0 ↔ α = 0 := by
  have := rationalComparison_mono E M n
  have hinj := (ModuleCat.mono_iff_injective (rationalComparison E M n)).mp inferInstance
  change complexComparison E M n (1 ⊗ₜ[ℚ] α) = 0 ↔ α = 0
  rw [complexComparison_one_tmul]
  constructor
  · intro h
    apply hinj
    simpa using h
  · intro h
    simp [h]

end HodgeConjecture.AnalyticBettiComparison

namespace AlgebraicGeometry.Scheme.ComplexPoints

open HodgeConjecture

variable {X : Scheme.{0}} {x : X ⟶ Spec (.of ℂ)} (d : ℕ) [SmoothOfRelativeDimension d x]

attribute [local instance] HasDerivedCategory.standard

/-- The actual complex-linear comparison on the existing canonical scheme point space. -/
def holomorphicBettiComparison (n : ℕ) :
    RationalComplexification.Space (SchemeBetti.Cohomology x n) →ₗ[ℂ]
      SheafHypercohomology.hypercohomology ℂ (SchemeBetti.space x)
        (HolomorphicAtlas.complex (Fin d → ℂ) (ComplexPoints x)) (n : ℤ) := by
  let : StronglyLocallyContractibleSpace (ComplexPoints x) := stronglyLocallyContractibleSpace d
  exact AnalyticBettiComparison.complexComparison (Fin d → ℂ) (ComplexPoints x) n

/-- The original rational Betti classes retain zero-class detection in the analytic derived target. -/
theorem holomorphicBettiComparison_embedding_eq_zero_iff [T2Space (ComplexPoints x)]
    [LocallyCompactSpace (ComplexPoints x)] [SecondCountableTopology (ComplexPoints x)]
    (n : ℕ) (α : SchemeBetti.Cohomology x n) :
    holomorphicBettiComparison (x := x) d n (RationalComplexification.embedding _ α) = 0 ↔ α = 0 := by
  let : StronglyLocallyContractibleSpace (ComplexPoints x) := stronglyLocallyContractibleSpace d
  exact AnalyticBettiComparison.complexComparison_embedding_eq_zero_iff
    (Fin d → ℂ) (ComplexPoints x) n α

end AlgebraicGeometry.Scheme.ComplexPoints
