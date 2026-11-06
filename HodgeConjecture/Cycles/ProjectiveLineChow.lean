module

public import HodgeConjecture.Cycles.ProjectiveLinePrincipalDegreeZero
public import HodgeConjecture.Cycles.ProjectiveLineCycleDegree
public import HodgeConjecture.Cycles.RationalChow

@[expose] public section

/-!
# Degree on the existing ordinary Chow groups of the projective line

Over an algebraically closed field, the actual coefficient sum kills all
original principal relations. The geometric relation carriers are reduced
to the whole integral curve, and the actual projective-line principal
divisor degree theorem supplies the vanishing. Integral and rational
degree therefore descend to the existing Chow quotients, with the original
homogeneous point cycles retaining degree one.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineCycles

open AlgebraicGeometry SchemeCycles

noncomputable section

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- Every original integral principal relation has actual coefficient degree zero. -/
theorem integralDegree_principalRelation (d : PrincipalRelationData (dimensionFunction k) 0) :
    integralDegree k (principalRelation (dimensionFunction k) 0 d) = 0 := by
  obtain ⟨f, hf⟩ := principalRelation_exists_principalDivisor k d
  change coefficientSum k ℤ (principalRelation (dimensionFunction k) 0 d).val = 0
  rw [hf, coefficientSum_principalDivisor_eq_zero]

/-- The exact existing integral relation span is annihilated by the constructed degree map. -/
theorem principalRelations_le_ker_integralDegree :
    principalRelations (dimensionFunction k) 0 ≤ LinearMap.ker (integralDegree k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact integralDegree_principalRelation k d

/-- The rational relation span is killed by the same geometric calculation and coefficient extension. -/
theorem rationalPrincipalRelations_le_ker_rationalDegree :
    rationalPrincipalRelations (dimensionFunction k) 0 ≤ LinearMap.ker (rationalDegree k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  change rationalDegree k
    (cyclesOfDegreeRationalize (dimensionFunction k) 0 (principalRelation (dimensionFunction k) 0 d)) = 0
  rw [rationalDegree_rationalize, integralDegree_principalRelation, Int.cast_zero]

/-- Integral degree on the original ordinary Chow group, with no supplied relation-invariance premise. -/
def integralChowDegree : ChowGroup (dimensionFunction k) 0 →ₗ[ℤ] ℤ :=
  (principalRelations (dimensionFunction k) 0).liftQ (integralDegree k)
    (principalRelations_le_ker_integralDegree k)

/-- Rational degree on the original ordinary rational Chow group. -/
def rationalChowDegree : RationalChowGroup (dimensionFunction k) 0 →ₗ[ℚ] ℚ :=
  (rationalPrincipalRelations (dimensionFunction k) 0).liftQ (rationalDegree k)
    (rationalPrincipalRelations_le_ker_rationalDegree k)

@[simp]
theorem integralChowDegree_classMap (c : cyclesOfDegree ℤ (dimensionFunction k) 0) :
    integralChowDegree k (classMap (dimensionFunction k) 0 c) = integralDegree k c := rfl

@[simp]
theorem rationalChowDegree_classMap (c : cyclesOfDegree ℚ (dimensionFunction k) 0) :
    rationalChowDegree k (rationalClassMap (dimensionFunction k) 0 c) = rationalDegree k c := rfl

@[simp]
theorem integralChowDegree_pointCycle (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    integralChowDegree k (classMap (dimensionFunction k) 0 (pointCycle k ℤ x hx)) = 1 :=
  coefficientDegree_pointCycle k ℤ x hx

@[simp]
theorem rationalChowDegree_pointCycle (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    rationalChowDegree k (rationalClassMap (dimensionFunction k) 0 (pointCycle k ℚ x hx)) = 1 :=
  coefficientDegree_pointCycle k ℚ x hx

/-- The two original coefficient quotients retain their actual degree normalization. -/
theorem rationalChowDegree_chowRationalize (z : ChowGroup (dimensionFunction k) 0) :
    rationalChowDegree k (chowRationalize (dimensionFunction k) 0 z) =
      (integralChowDegree k z : ℚ) := by
  obtain ⟨c, rfl⟩ := classMap_surjective (dimensionFunction k) 0 z
  rw [chowRationalize_classMap, rationalChowDegree_classMap,
    integralChowDegree_classMap, rationalDegree_rationalize]

end

end HodgeConjecture.ProjectiveLineCycles
