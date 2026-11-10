module

public import HodgeConjecture.Realization.Betti.ProjectiveLinePointGysin
public import HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass

@[expose] public section

/-!
# The original zero-point cycle class and its geometric Gysin normalization

The actual local Thom class, inverse excision and forgetting support give
the original zero-point Gysin map. Its unit agrees with the existing
ordinary integral and rational cycle classes of the same scheme point.
The degree-normalized ordinary maps therefore factor through this actual
zero-point Gysin. This statement concerns this distinguished point; it
does not identify a separately constructed Gysin map for every closed
point or assert a general cycle-class construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineGysinCycleClass

open AlgebraicGeometry SchemeCycles ProjectiveLineCycles ProjectiveLinePointSupport
open ProjectiveLinePointGysin

abbrev Source := RationalChowGroup (dimensionFunction ℂ) 0

/-- The original integral Chow class of the actual scheme zero point. -/
def integralZeroClass : ChowGroup (dimensionFunction ℂ) 0 :=
  classMap (dimensionFunction ℂ) 0
    (pointCycle ℂ ℤ (projectiveLineZero ℂ) schemeZero_ne_genericPoint)

/-- The original rational Chow class of that same point. -/
def rationalZeroClass : Source :=
  rationalClassMap (dimensionFunction ℂ) 0
    (pointCycle ℂ ℚ (projectiveLineZero ℂ) schemeZero_ne_genericPoint)

/-- The constant-point class in actual degree-zero cohomology. -/
def pointClass : ℚ →ₗ[ℚ] PointH0 := pointCoordinates.symm.toLinearMap

@[simp]
theorem pointClass_one : pointClass 1 = pointUnit := by
  apply pointCoordinates.injective
  change pointCoordinates (pointCoordinates.symm 1) = _
  rw [LinearEquiv.apply_symm_apply, pointCoordinates_pointUnit]

theorem pointClass_eq_smul (q : ℚ) : pointClass q = q • pointUnit := by
  apply pointCoordinates.injective
  change pointCoordinates (pointCoordinates.symm q) = _
  rw [LinearEquiv.apply_symm_apply, map_smul, pointCoordinates_pointUnit, smul_eq_mul, mul_one]

/-- The actual geometric point Gysin matches the original integral cycle of that point. -/
theorem gysin_pointUnit_eq_integralZeroClass :
    gysin pointUnit = ProjectiveLineBettiCycleClass.integralCycleClass integralZeroClass := by
  rw [gysin_pointUnit, integralZeroClass, ProjectiveLineBettiCycleClass.integralCycleClass_pointCycle]

/-- The actual geometric point Gysin matches the original rational cycle of the same scheme point. -/
theorem gysin_pointUnit_eq_rationalZeroClass :
    gysin pointUnit = ProjectiveLineBettiCycleClass.cycleClass rationalZeroClass := by
  rw [gysin_pointUnit, rationalZeroClass, ProjectiveLineBettiCycleClass.cycleClass_pointCycle]

/-- The ordinary rational map factors through actual point H⁰ and the geometric zero-point Gysin. -/
def cycleClassViaZeroGysin : Source →ₗ[ℚ] AbsoluteH2 :=
  gysin.comp (pointClass.comp (rationalChowDegree ℂ))

theorem cycleClassViaZeroGysin_eq_cycleClass :
    cycleClassViaZeroGysin = ProjectiveLineBettiCycleClass.cycleClass := by
  apply LinearMap.ext
  intro z
  change gysin (pointClass (rationalChowDegree ℂ z)) = rationalChowDegree ℂ z • _
  rw [pointClass_eq_smul, map_smul, gysin_pointUnit]

/-- Every original ordinary rational Chow class retains its actual point-Gysin factorization. -/
theorem cycleClass_factorization (z : Source) :
    ProjectiveLineBettiCycleClass.cycleClass z = gysin (pointClass (rationalChowDegree ℂ z)) :=
  (congrArg (fun f ↦ f z) cycleClassViaZeroGysin_eq_cycleClass).symm

/-- The integral map has the corresponding geometric factorization in rational singular cohomology. -/
theorem integralCycleClass_factorization (z : ChowGroup (dimensionFunction ℂ) 0) :
    ProjectiveLineBettiCycleClass.integralCycleClass z =
      gysin (pointClass (integralChowDegree ℂ z : ℚ)) := by
  rw [pointClass_eq_smul, map_smul, gysin_pointUnit]
  exact (Int.cast_smul_eq_zsmul ℚ (integralChowDegree ℂ z)
    ProjectiveLineBettiCohomology.coverGenerator).symm

end HodgeConjecture.ProjectiveLineGysinCycleClass
