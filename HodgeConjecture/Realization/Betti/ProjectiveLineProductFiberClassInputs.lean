module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductSpanning
public import HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriers

/-!
# Geometric and Betti inputs for the product fiber cycle-class comparison

The two integral zero fibers are scheme-theoretic pullbacks of the original
reduced zero point. Independently, the two established Betti basis classes
are pullbacks of that same point's proved Gysin and ordinary Chow class on
the projective line. A codimension-one cycle-class map for the product and
its flat base-change law are still needed to identify the fiber Chow classes
with these Betti pullbacks.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductFiberClassInputs

open AlgebraicGeometry HodgeConjecture.SchemeCycles
open HodgeConjecture.ProjectiveLineProductBetti
open HodgeConjecture.ProjectiveLineProductFibers

/-- The canonical projective-line Betti generator is the ordinary cycle
class of its actual reduced zero point, normalized by its geometric Gysin. -/
theorem lineGenerator_eq_zeroCycleClass :
    lineGenerator =
      canonicalCycleClass ProjectiveLineGysinCycleClass.rationalZeroClass := by
  change canonicalBettiEquiv ProjectiveLineBettiCohomology.coverGenerator =
    canonicalBettiEquiv
      (ProjectiveLineBettiCycleClass.cycleClass
        ProjectiveLineGysinCycleClass.rationalZeroClass)
  rw [← ProjectiveLineGysinCycleClass.gysin_pointUnit_eq_rationalZeroClass,
    ProjectiveLinePointGysin.gysin_pointUnit]

/-- The first product Betti basis class is the genuine projection pullback
of the projective-line zero-point ordinary cycle class. -/
theorem firstClass_eq_pullback_zeroCycleClass :
    firstClass =
      SchemeBetti.pullback (projectiveLineProductFst ℂ)
        (projectiveLineProductFst_comp_structureMorphism ℂ) 2
        (canonicalCycleClass ProjectiveLineGysinCycleClass.rationalZeroClass) := by
  unfold firstClass
  rw [lineGenerator_eq_zeroCycleClass]

/-- The second product Betti basis class is the analogous actual pullback. -/
theorem secondClass_eq_pullback_zeroCycleClass :
    secondClass =
      SchemeBetti.pullback (projectiveLineProductSnd ℂ)
        (projectiveLineProductSnd_comp_structureMorphism ℂ) 2
        (canonicalCycleClass ProjectiveLineGysinCycleClass.rationalZeroClass) := by
  unfold secondClass
  rw [lineGenerator_eq_zeroCycleClass]

/-- The first integral carrier is exactly the scheme-theoretic pullback of
the same reduced zero point whose Gysin class appears above. -/
theorem firstCarrier_ideal_eq_comap_zeroPoint :
    (projectiveLineProductZeroFirstCarrier ℂ).val =
      ((pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)).val).comap
        (projectiveLineProductFst ℂ) := by
  rw [projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal]
  simp only [zeroSectionPoint_eq_projectiveLineZero]
  rfl

/-- The second integral carrier has the corresponding pulled-back ideal. -/
theorem secondCarrier_ideal_eq_comap_zeroPoint :
    (projectiveLineProductZeroSecondCarrier ℂ).val =
      ((pointSupport (projectiveLine ℂ) (projectiveLineZero ℂ)).val).comap
        (projectiveLineProductSnd ℂ) := by
  rw [projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal]
  simp only [zeroSectionPoint_eq_projectiveLineZero]
  rfl

end HodgeConjecture.ProjectiveLineProductFiberClassInputs

end
