module

public import HodgeConjecture.Realization.DeRham.AnalyticBettiComparison
public import HodgeConjecture.Realization.Betti.ComplexSingularConstantSheafCohomology

@[expose] public noncomputable section

/-!
# Complex singular cohomology and intrinsic holomorphic hypercohomology

The native complex singular/constant-sheaf comparison and the original
holomorphic Poincaré resolution compose to an isomorphism under the proved
topology hypotheses. Equality with the earlier map from the tensor
complexification of rational Betti cohomology requires the coefficient
naturality square and is treated separately.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff

namespace HodgeConjecture.AnalyticBettiComparison

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StronglyLocallyContractibleSpace M]

attribute [local instance] HasDerivedCategory.standard

/-- The native complex singular group maps to the same intrinsic holomorphic derived target. -/
def complexSingularToHolomorphic (n : ℕ) :
    SingularCoefficientChange.ComplexCohomology (TopCat.of M) n ⟶
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M)
        (HolomorphicAtlas.complex E M) (n : ℤ) :=
  SingularCoefficientChange.cohomologyToConstantSheafDerived (TopCat.of M) n ≫
    (HolomorphicAtlas.constantSheafDerivedIso E M n).hom

/-- The constructed map is invertible on spaces satisfying the original topology hypotheses. -/
theorem complexSingularToHolomorphic_isIso [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M] (n : ℕ) : IsIso (complexSingularToHolomorphic E M n) := by
  have := SingularCoefficientChange.cohomologyToConstantSheafDerived_isIso (TopCat.of M) n
  unfold complexSingularToHolomorphic
  infer_instance

/-- Its isomorphism keeps the original complex singular and holomorphic maps. -/
def complexSingularHolomorphicIso [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M] (n : ℕ) :
    SingularCoefficientChange.ComplexCohomology (TopCat.of M) n ≅
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M)
        (HolomorphicAtlas.complex E M) (n : ℤ) := by
  have := complexSingularToHolomorphic_isIso E M n
  exact asIso (complexSingularToHolomorphic E M n)

@[simp]
theorem complexSingularHolomorphicIso_hom [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M] (n : ℕ) :
    (complexSingularHolomorphicIso E M n).hom = complexSingularToHolomorphic E M n := rfl

/-- The holomorphic map obtained from the original cochain coefficient comparison. -/
def cochainHolomorphicComparison (n : ℕ) :
    ModuleCat.of ℂ
        (RationalComplexification.Space (SingularCochains.Cohomology (TopCat.of M) n)) ⟶
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M)
        (HolomorphicAtlas.complex E M) (n : ℤ) :=
  SingularCoefficientChange.cohomologyComparison (TopCat.of M) n ≫
    complexSingularToHolomorphic E M n

/-- Finite rational cohomology and the topology hypotheses invert this cochain-induced map. -/
theorem cochainHolomorphicComparison_isIso [T2Space M] [LocallyCompactSpace M]
    [SecondCountableTopology M]
    (n : ℕ) [FiniteDimensional ℚ (SingularCochains.Cohomology (TopCat.of M) n)] :
    IsIso (cochainHolomorphicComparison E M n) := by
  have := SingularCoefficientChange.cohomologyComparison_isIso (TopCat.of M) n
  have := complexSingularToHolomorphic_isIso E M n
  unfold cochainHolomorphicComparison
  infer_instance

end HodgeConjecture.AnalyticBettiComparison
