module

public import HodgeConjecture.Realization.Betti.Circle
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology

@[expose] public section

/-!
# Actual rational singular H² of the complex projective line

The original affine-chart Mayer–Vietoris connecting isomorphism and the
actual radial overlap pullback carry the proved circle H¹ calculation to
the singular cohomology of the original over-ℂ projective-line points.
The cover generator has rational coordinate one. Its agreement with the
oriented analytic de Rham period remains a separate comparison.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineBettiCohomology

open CategoryTheory

/-- Proved coordinates on the actual rational singular degree-two group. -/
def h2Equiv :
    SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2 ≃ₗ[ℚ] ℚ :=
  ProjectiveLineSingularCohomology.circleIso.toLinearEquiv.symm.trans CircleCohomology.h1Equiv

/-- The original affine-chart boundary of the radial pullback of the circle cover class. -/
def coverGenerator :
    SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2 :=
  ProjectiveLineSingularCohomology.circleIso.hom CircleCohomology.coverGenerator

/-- The actual construction retains the original continuous radial map and native boundary. -/
theorem coverGenerator_eq_connecting : coverGenerator =
    ProjectiveLineSingularCohomology.connecting
      (SingularCochains.cohomologyPullback
        (TopCat.ofHom ProjectiveLineAnalyticCover.overlapCircleHomotopyEquiv.toFun) 1
          CircleCohomology.coverGenerator) := rfl

/-- The two proved coordinates agree along the original radial/connecting isomorphism. -/
theorem h2Equiv_circleIso (z : SingularCochains.Cohomology (TopCat.of Circle) 1) :
    h2Equiv (ProjectiveLineSingularCohomology.circleIso.hom z) = CircleCohomology.h1Equiv z := by
  change CircleCohomology.h1Equiv
    (ProjectiveLineSingularCohomology.circleIso.toLinearEquiv.symm
      (ProjectiveLineSingularCohomology.circleIso.toLinearEquiv z)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp]
theorem h2Equiv_coverGenerator : h2Equiv coverGenerator = 1 := by
  rw [coverGenerator, h2Equiv_circleIso, CircleCohomology.h1Equiv_coverGenerator]

theorem coverGenerator_ne_zero : coverGenerator ≠ 0 := by
  intro hz
  have h := h2Equiv_coverGenerator
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- Every actual singular degree-two class is a unique rational multiple of the cover class. -/
theorem eq_smul_coverGenerator
    (z : SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2) :
    z = h2Equiv z • coverGenerator := by
  apply h2Equiv.injective
  rw [map_smul, h2Equiv_coverGenerator, smul_eq_mul, mul_one]

end HodgeConjecture.ProjectiveLineBettiCohomology
