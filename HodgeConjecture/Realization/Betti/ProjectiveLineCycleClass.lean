module

public import HodgeConjecture.Cycles.ProjectiveLineChow
public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# Ordinary projective-line cycles in actual rational singular H²

The source is the original ordinary Chow quotient of actual zero-dimensional
cycles on the projective line over ℂ. The already proved principal-divisor
degree theorem makes its degree well defined. Multiplying the actual
singular cover generator by that degree constructs integral and rational
cycle maps. Every reduced closed point has this stated normalization.

This module imports no de Rham construction or comparison. Its rational
map is onto actual singular H² by the independently proved cohomology
calculation and the original reduced infinity class.
No identification with a separately constructed general topological
Gysin or Poincaré-dual cycle map is asserted here. The separate
`ProjectiveLineGysinCycleClass` module constructs the distinguished
zero-point Gysin and proves its agreement with this normalization.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineBettiCycleClass

open AlgebraicGeometry SchemeCycles ProjectiveLineCycles ProjectiveLineBettiCohomology

/-- The original rational singular degree-two cohomology of the actual complex points. -/
abbrev Target := SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) 2

/-- The original projective-line infinity point is not the generic point. -/
theorem infinity_ne_genericPoint :
    projectiveLineInfinity ℂ ≠ genericPoint (projectiveLine ℂ) := by
  intro h
  apply projectiveLineInfinity_notMem_range_XChart ℂ
  rw [h]
  exact ⟨genericPoint (Spec (.of (Polynomial ℂ))), projectiveLineXChart_genericPoint_eq (k := ℂ)⟩

/-- The original integral ordinary Chow class of the reduced infinity point. -/
def integralInfinityClass : ChowGroup (dimensionFunction ℂ) 0 :=
  classMap (dimensionFunction ℂ) 0 (pointCycle ℂ ℤ (projectiveLineInfinity ℂ)
    infinity_ne_genericPoint)

/-- The original rational ordinary Chow class of the same reduced point. -/
def rationalInfinityClass : RationalChowGroup (dimensionFunction ℂ) 0 :=
  rationalClassMap (dimensionFunction ℂ) 0 (pointCycle ℂ ℚ (projectiveLineInfinity ℂ)
    infinity_ne_genericPoint)

@[simp]
theorem integralChowDegree_infinity : integralChowDegree ℂ integralInfinityClass = 1 :=
  integralChowDegree_pointCycle ℂ _ _

@[simp]
theorem rationalChowDegree_infinity : rationalChowDegree ℂ rationalInfinityClass = 1 :=
  rationalChowDegree_pointCycle ℂ _ _

/-- Integral ordinary cycles, normalized by the actual singular cover generator. -/
def integralCycleClass : ChowGroup (dimensionFunction ℂ) 0 →+ Target where
  toFun z := integralChowDegree ℂ z • coverGenerator
  map_zero' := by simp
  map_add' z w := by rw [map_add, add_zsmul]

/-- The ordinary rational Chow map into the independently constructed singular target. -/
def cycleClass : RationalChowGroup (dimensionFunction ℂ) 0 →ₗ[ℚ] Target where
  toFun z := rationalChowDegree ℂ z • coverGenerator
  map_add' z w := by rw [map_add, add_smul]
  map_smul' q z := by rw [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

theorem integralCycleClass_classMap (c : cyclesOfDegree ℤ (dimensionFunction ℂ) 0) :
    integralCycleClass (classMap (dimensionFunction ℂ) 0 c) = integralDegree ℂ c • coverGenerator := rfl

theorem cycleClass_classMap (c : cyclesOfDegree ℚ (dimensionFunction ℂ) 0) :
    cycleClass (rationalClassMap (dimensionFunction ℂ) 0 c) = rationalDegree ℂ c • coverGenerator := rfl

/-- Each actual reduced closed point has the actual singular cover generator as its class. -/
@[simp]
theorem integralCycleClass_pointCycle (x : projectiveLine ℂ)
    (hx : x ≠ genericPoint (projectiveLine ℂ)) :
    integralCycleClass (classMap (dimensionFunction ℂ) 0 (pointCycle ℂ ℤ x hx)) =
      coverGenerator := by
  change integralChowDegree ℂ _ • coverGenerator = coverGenerator
  rw [integralChowDegree_pointCycle, one_zsmul]

@[simp]
theorem cycleClass_pointCycle (x : projectiveLine ℂ)
    (hx : x ≠ genericPoint (projectiveLine ℂ)) :
    cycleClass (rationalClassMap (dimensionFunction ℂ) 0 (pointCycle ℂ ℚ x hx)) =
      coverGenerator := by
  change rationalChowDegree ℂ _ • coverGenerator = coverGenerator
  rw [rationalChowDegree_pointCycle, one_smul]

@[simp]
theorem integralCycleClass_infinity : integralCycleClass integralInfinityClass = coverGenerator :=
  integralCycleClass_pointCycle _ _

@[simp]
theorem cycleClass_infinity : cycleClass rationalInfinityClass = coverGenerator :=
  cycleClass_pointCycle _ _

/-- The actual rational singular coordinate of every ordinary cycle class is its degree. -/
theorem coordinate_cycleClass (z : RationalChowGroup (dimensionFunction ℂ) 0) :
    h2Equiv (cycleClass z) = rationalChowDegree ℂ z := by
  change h2Equiv (rationalChowDegree ℂ z • coverGenerator) = _
  rw [map_smul, h2Equiv_coverGenerator, smul_eq_mul, mul_one]

/-- Original Chow rationalization intertwines the integral and rational singular maps. -/
theorem cycleClass_chowRationalize (z : ChowGroup (dimensionFunction ℂ) 0) :
    cycleClass (chowRationalize (dimensionFunction ℂ) 0 z) = integralCycleClass z := by
  change rationalChowDegree ℂ (chowRationalize (dimensionFunction ℂ) 0 z) • coverGenerator = _
  rw [rationalChowDegree_chowRationalize]
  exact Int.cast_smul_eq_zsmul ℚ _ _

/-- Actual integral principal-relation generators vanish. -/
theorem integralCycleClass_principalRelation (d : PrincipalRelationData (dimensionFunction ℂ) 0) :
    integralCycleClass (classMap (dimensionFunction ℂ) 0
      (principalRelation (dimensionFunction ℂ) 0 d)) = 0 := by
  rw [classMap_principalRelation, map_zero]

/-- Actual rationalized principal-relation generators vanish in the original quotient. -/
theorem cycleClass_principalRelation (d : PrincipalRelationData (dimensionFunction ℂ) 0) :
    cycleClass (rationalClassMap (dimensionFunction ℂ) 0
      (cyclesOfDegreeRationalize (dimensionFunction ℂ) 0
        (principalRelation (dimensionFunction ℂ) 0 d))) = 0 := by
  rw [rationalClassMap_principalRelation, map_zero]

/-- The ordinary rational cycle map is nonzero on the original reduced infinity class. -/
theorem cycleClass_ne_zero : cycleClass ≠ 0 := by
  intro h
  have he := DFunLike.congr_fun h rationalInfinityClass
  rw [cycleClass_infinity] at he
  exact coverGenerator_ne_zero he

/-- Every actual rational singular degree-two class has an ordinary rational Chow representative. -/
theorem cycleClass_surjective : Function.Surjective cycleClass := by
  intro z
  refine ⟨h2Equiv z • rationalInfinityClass, ?_⟩
  rw [map_smul, cycleClass_infinity]
  exact (eq_smul_coverGenerator z).symm

end HodgeConjecture.ProjectiveLineBettiCycleClass
