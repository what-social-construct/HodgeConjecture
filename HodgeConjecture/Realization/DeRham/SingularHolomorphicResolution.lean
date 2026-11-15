module

public import HodgeConjecture.Realization.Betti.ComplexSingularResolution
public import HodgeConjecture.Realization.DeRham.HolomorphicHypercohomology

@[expose] public noncomputable section

/-!
# The original complex singular and holomorphic sheaf resolutions

Both original resolutions start at the same native complex constant
sheaf. Their actual maps identify sheaf hypercohomology. The original
complex global-unit map consequently gives a comparison from complex
singular cohomology, without an unproved global-unit isomorphism claim.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory HomologicalComplex
open scoped Manifold ContDiff

namespace HodgeConjecture.HolomorphicAtlas

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [StronglyLocallyContractibleSpace M]

attribute [local instance] HasDerivedCategory.standard

/-- The original singular sheaf complex and intrinsic holomorphic complex resolve the same constant sheaf. -/
def singularSheafHypercohomologyIso (n : ℤ) :
    SheafHypercohomology.hypercohomology ℂ (TopCat.of M)
        (SingularCoefficientChange.sheafComplex (TopCat.of M)) n ≅
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M) (complex E M) n := by
  have := SingularCoefficientChange.comparison_quasiIso (TopCat.of M)
  have := comparison_quasiIso E M
  exact (SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℂ (TopCat.of M)
      (SingularCoefficientChange.comparison (TopCat.of M)) n).symm ≪≫
    SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℂ (TopCat.of M) (comparison E M) n

@[reassoc]
theorem singularSheafHypercohomologyIso_resolution (n : ℤ) :
    SheafHypercohomology.hypercohomologyMap ℂ (TopCat.of M)
        (SingularCoefficientChange.comparison (TopCat.of M)) n ≫
        (singularSheafHypercohomologyIso E M n).hom =
      SheafHypercohomology.hypercohomologyMap ℂ (TopCat.of M) (comparison E M) n := by
  have := SingularCoefficientChange.comparison_quasiIso (TopCat.of M)
  have := comparison_quasiIso E M
  change (SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℂ (TopCat.of M)
    (SingularCoefficientChange.comparison (TopCat.of M)) n).hom ≫ (_ ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

/-- The existing ordinary derived comparison is the map fixed by these same original resolutions. -/
theorem constantSheafDerivedIso_via_singular (n : ℕ) :
    (SheafHypercohomology.singleIsoRightDerived ℂ (TopCat.of M) (constantSheaf M) n).inv ≫
      SheafHypercohomology.hypercohomologyMap ℂ (TopCat.of M)
        (SingularCoefficientChange.comparison (TopCat.of M)) (n : ℤ) ≫
      (singularSheafHypercohomologyIso E M (n : ℤ)).hom =
      (constantSheafDerivedIso E M n).hom := by
  rw [singularSheafHypercohomologyIso_resolution]
  rfl

/-- The actual complex-valued global cochains map to the intrinsic analytic derived target. -/
def singularCohomologyComparison (n : ℕ) :
    SingularCoefficientChange.ComplexCohomology (TopCat.of M) n ⟶
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M) (complex E M) (n : ℤ) :=
  homologyMap (SingularCoefficientChange.globalCochainsToSheaf (TopCat.of M)) n ≫
    (SheafHypercohomology.nonnegativeSectionsHomologyIso ℂ (TopCat.of M)
      (SingularCoefficientChange.sheafComplex (TopCat.of M)) n).hom ≫
    SheafHypercohomology.comparisonFromComplexHomology ℂ (TopCat.of M)
      (SingularCoefficientChange.sheafComplex (TopCat.of M)) (n : ℤ) ≫
    (singularSheafHypercohomologyIso E M (n : ℤ)).hom

end HodgeConjecture.HolomorphicAtlas
