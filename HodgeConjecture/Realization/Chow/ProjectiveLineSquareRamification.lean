module

public import HodgeConjecture.Realization.Chow.ProjectiveLineSquare
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# The original zero-point cycle under the ramified projective-line square

The ordinary zero class is the class of the original reduced point
support, with its original structural grading. The actual finite-fiber
pullback keeps that support and weights it by the original local scheme
fiber length. Its value two was computed geometrically in the square
adapter. The Chow identity descends this unchanged representative formula;
no Betti realization or degree-injectivity premise is involved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquareRamifiedChow

open AlgebraicGeometry CategoryTheory SchemeCycles ProjectiveLineCycles
open ProjectiveLineSquare ProjectiveLineSquareChow

/-- The original reduced origin cycle in the original degree-zero submodule. -/
abbrev zeroCycle : cyclesOfDegree ℚ (dimensionFunction ℂ) 0 :=
  pointCycle ℂ ℚ (projectiveLineZero ℂ) (zero_ne_genericPoint ℂ)

/-- The original ordinary rational Chow class of the actual zero point. -/
def zeroClass : BaseChow ℂ := rationalClassMap (dimensionFunction ℂ) 0 zeroCycle

theorem zeroClass_degree : rationalChowDegree ℂ zeroClass = 1 :=
  rationalChowDegree_pointCycle ℂ _ _

theorem zeroClass_ne_zero : zeroClass ≠ 0 := by
  intro h
  have hd := zeroClass_degree
  rw [h, map_zero] at hd
  exact zero_ne_one hd

/-- Original finite pullback on raw cycles is weighted by the actual local fiber length. -/
theorem finiteFiberPullback_zero :
    finiteFiberPullback (square ℂ) ℚ
        (fundamentalCycle ℚ (pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ))) =
      finiteFiberMultiplicity (square ℂ) (projectiveLineZero ℂ) •
        fundamentalCycle ℚ (pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)) := by
  classical
  have hp (x : projectiveLine ℂ) :
      finiteFiberPullback (square ℂ) ℚ
          (fundamentalCycle ℚ (pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)))
          (pointSupport (projectiveLine ℂ) x) =
        (finiteFiberMultiplicity (square ℂ) (projectiveLineZero ℂ) •
          fundamentalCycle ℚ (pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)))
          (pointSupport (projectiveLine ℂ) x) := by
    rw [finiteFiberPullback_apply_pointSupport]
    by_cases hx : x = projectiveLineZero ℂ
    · subst x
      simp [zero_fixed, fundamentalCycle, nsmul_eq_mul]
    · have hxy : pointSupport (projectiveLine ℂ) x ≠
          pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ) :=
        fun he => hx ((pointEquivIntegralClosedSubscheme (projectiveLine ℂ)).injective he)
      have hfy : pointSupport (projectiveLine ℂ) (square ℂ x) ≠
          pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ) := by
        intro he
        exact hx ((square_eq_zero_iff ℂ x).mp
          ((pointEquivIntegralClosedSubscheme (projectiveLine ℂ)).injective he))
      simp [fundamentalCycle, hxy, hfy]
  ext W
  simpa only [pointSupport_ambientGenericPoint] using hp (ambientGenericPoint W)

theorem finiteFiberPullback_zero_eq_two :
    finiteFiberPullback (square ℂ) ℚ
        (fundamentalCycle ℚ (pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ))) =
      2 • fundamentalCycle ℚ (pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)) := by
  rw [finiteFiberPullback_zero, zero_finiteFiberMultiplicity]

/-- The original quotient identity is induced by the actual weighted zero-point representative. -/
theorem chowEquiv_pull_zero :
    chowEquiv ℂ (actualPull ℂ zeroClass) = (2 : ℚ) • zeroClass := by
  change chowEquiv ℂ (rationalClassMap (sourceDimension ℂ) 0
    (gradedFiniteFiberPullback (square ℂ) ℂ ℚ (baseStructure ℂ) 0 zeroCycle)) = _
  rw [chowEquiv_classMap]
  change rationalClassMap (dimensionFunction ℂ) 0
      (baseCycle ℂ (gradedFiniteFiberPullback (square ℂ) ℂ ℚ (baseStructure ℂ) 0 zeroCycle)) =
    (2 : ℚ) • rationalClassMap (dimensionFunction ℂ) 0 zeroCycle
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  simpa only [baseCycle, gradedFiniteFiberPullback_val, zeroCycle, pointCycle,
    SetLike.val_smul, Submodule.coe_add, two_smul] using finiteFiberPullback_zero_eq_two

/-- The rational Chow pullback coefficient is the same actual local scheme-fiber multiplicity. -/
theorem chowEquiv_pull_zero_weighted :
    chowEquiv ℂ (actualPull ℂ zeroClass) =
      (finiteFiberMultiplicity (square ℂ) (projectiveLineZero ℂ) : ℚ) • zeroClass := by
  rw [zero_finiteFiberMultiplicity]
  exact chowEquiv_pull_zero

end HodgeConjecture.ProjectiveLineSquareRamifiedChow

end
