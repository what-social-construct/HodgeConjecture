module

public import HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology

@[expose] public section

/-!
# The positive boundary coordinate of actual projective-line singular H²

The original affine-chart connecting isomorphism identifies H² with H¹
of its actual punctured-plane overlap. After actual radial pullback, its
boundary coordinate is evaluation on the explicitly counterclockwise
circle cycle. This fixes the sign of the cover generator. It does not
construct a singular two-cycle or a Poincaré-duality comparison.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineBettiOrientation

open CategoryTheory

/-- Evaluate the original inverse-boundary class on the actual positive circle cycle. -/
def boundaryPairing :
    SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2 →ₗ[ℚ] ℚ :=
  CircleOrientedPairing.loopPairing.comp ProjectiveLineSingularCohomology.circleIso.inv.hom

/-- The original rational coordinate has the positive boundary-loop normalization. -/
theorem boundaryPairing_eq_coordinate
    (z : SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2) :
    boundaryPairing z = ProjectiveLineBettiCohomology.h2Equiv z := by
  change CircleOrientedPairing.loopPairing
    (ProjectiveLineSingularCohomology.circleIso.inv z) = _
  rw [CircleOrientedPairing.loopPairing_eq_coordinate]
  rfl

/-- The generator is positive for the original radial and connecting conventions. -/
@[simp]
theorem boundaryPairing_coverGenerator :
    boundaryPairing ProjectiveLineBettiCohomology.coverGenerator = 1 := by
  rw [boundaryPairing_eq_coordinate, ProjectiveLineBettiCohomology.h2Equiv_coverGenerator]

end HodgeConjecture.ProjectiveLineBettiOrientation
