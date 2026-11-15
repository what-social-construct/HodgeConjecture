module

public import HodgeConjecture.Realization.DeRham.HolomorphicAtlasPoincare
public import HodgeConjecture.SheafCohomology.HypercohomologyComparison

@[expose] public noncomputable section

/-!
# The existing holomorphic resolution on actual derived sections

The native complex constant sheaf and original intrinsic holomorphic
complex are compared using the already proved local Poincaré map.
No claim of acyclicity for individual holomorphic form sheaves is used.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff

namespace HodgeConjecture.HolomorphicAtlas

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

attribute [local instance] HasDerivedCategory.standard

/-- The original local Poincaré comparison identifies actual complex constant-sheaf cohomology. -/
def constantSheafDerivedIso (n : ℕ) :
    ((SheafHypercohomology.globalSections ℂ (TopCat.of M)).rightDerived n).obj
        (constantSheaf M) ≅
      SheafHypercohomology.hypercohomology ℂ (TopCat.of M) (complex E M) (n : ℤ) := by
  have : QuasiIso (comparison E M) := comparison_quasiIso E M
  exact (SheafHypercohomology.singleIsoRightDerived ℂ (TopCat.of M) (constantSheaf M) n).symm ≪≫
    SheafHypercohomology.hypercohomologyIsoOfQuasiIso ℂ (TopCat.of M) (comparison E M) (n : ℤ)

/-- The comparison is fixed by the original local-resolution map. -/
@[reassoc]
theorem constantSheafDerivedIso_resolution (n : ℕ) :
    (SheafHypercohomology.singleIsoRightDerived ℂ (TopCat.of M) (constantSheaf M) n).hom ≫
        (constantSheafDerivedIso E M n).hom =
      SheafHypercohomology.hypercohomologyMap ℂ (TopCat.of M) (comparison E M) (n : ℤ) := by
  simp only [constantSheafDerivedIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc,
    SheafHypercohomology.hypercohomologyIsoOfQuasiIso_hom]

end HodgeConjecture.HolomorphicAtlas
