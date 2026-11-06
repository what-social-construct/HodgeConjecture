module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineSchemeComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCycleClass

@[expose] public noncomputable section

/-!
# Ordinary projective-line cycle classes in actual scheme de Rham cohomology

The source is the original integral or rational Chow quotient. The target
is the actual degree-two derived global sections of the scheme de Rham
sheaf complex. The proved scheme comparison carries the existing Čech
cycle class to this map, with the same point normalization and rational
coefficient bound. No singular or Betti comparison is asserted.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineSchemeCycleClass

open AlgebraicGeometry CategoryTheory SchemeCycles ProjectiveLineCycles ProjectiveLineDeRham

universe u

variable (k : Type u) [Field k] [IsAlgClosed k]

/-- The original integral Chow classes, realized through the actual scheme comparison. -/
def integralCycleClass : ChowGroup (dimensionFunction k) 0 →+ SchemeH2 k where
  toFun z := (schemeComparisonIso k).hom (ProjectiveLineCycleClass.integralCycleClass k z)
  map_zero' := by simp
  map_add' z w := by simp

@[simp]
theorem integralCycleClass_pointCycle (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    integralCycleClass k (classMap (dimensionFunction k) 0 (pointCycle k ℤ x hx)) =
      schemeChernCoordinate k := by
  change (schemeComparisonIso k).hom (ProjectiveLineCycleClass.integralCycleClass k _) = _
  rw [ProjectiveLineCycleClass.integralCycleClass_pointCycle]
  rfl

theorem integralCycleClass_principalRelation (d : PrincipalRelationData (dimensionFunction k) 0) :
    integralCycleClass k (classMap (dimensionFunction k) 0
      (principalRelation (dimensionFunction k) 0 d)) = 0 := by
  change (schemeComparisonIso k).hom (ProjectiveLineCycleClass.integralCycleClass k _) = 0
  rw [ProjectiveLineCycleClass.integralCycleClass_principalRelation, map_zero]

variable [CharZero k]

/-- Restrict only the scalars of the actual scheme cohomology to the rationals. -/
abbrev RationalTarget := RestrictScalars ℚ k (SchemeH2 k)

/-- The original ordinary rational Chow quotient maps to actual scheme de Rham degree two. -/
def cycleClass : RationalChowGroup (dimensionFunction k) 0 →ₗ[ℚ] RationalTarget k where
  toFun z := (rationalChowDegree k z : k) • schemeChernCoordinate k
  map_add' z w := by
    change ((rationalChowDegree k (z + w) : ℚ) : k) • _ = _
    rw [map_add, Rat.cast_add, add_smul]
  map_smul' q z := by
    change ((rationalChowDegree k (q • z) : ℚ) : k) • _ =
      (q : k) • ((rationalChowDegree k z : k) • schemeChernCoordinate k)
    rw [map_smul, smul_eq_mul, Rat.cast_mul, mul_smul]

theorem cycleClass_apply (z : RationalChowGroup (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (SchemeH2 k) (cycleClass k z) =
      (rationalChowDegree k z : k) • schemeChernCoordinate k := rfl

/-- The actual scheme comparison commutes with the original ordinary cycle map. -/
theorem cycleClass_comparison (z : RationalChowGroup (dimensionFunction k) 0) :
    (schemeComparisonIso k).hom
        (RestrictScalars.addEquiv ℚ k (CechH2 k) (ProjectiveLineCycleClass.cycleClass k z)) =
      RestrictScalars.addEquiv ℚ k (SchemeH2 k) (cycleClass k z) := by
  rw [ProjectiveLineCycleClass.cycleClass_apply, cycleClass_apply, map_smul]
  rfl

@[simp]
theorem cycleClass_pointCycle (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    RestrictScalars.addEquiv ℚ k (SchemeH2 k)
        (cycleClass k (rationalClassMap (dimensionFunction k) 0 (pointCycle k ℚ x hx))) =
      schemeChernCoordinate k := by
  rw [cycleClass_apply, rationalChowDegree_pointCycle, Rat.cast_one, one_smul]

/-- The computed scheme residue reads the actual rational degree. -/
theorem residue_cycleClass (z : RationalChowGroup (dimensionFunction k) 0) :
    schemeResidueEquiv k (RestrictScalars.addEquiv ℚ k (SchemeH2 k) (cycleClass k z)) =
      (rationalChowDegree k z : k) := by
  rw [cycleClass_apply, map_smul, schemeResidueEquiv_chernCoordinate, smul_eq_mul, mul_one]

theorem cycleClass_chowRationalize (z : ChowGroup (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (SchemeH2 k)
        (cycleClass k (chowRationalize (dimensionFunction k) 0 z)) = integralCycleClass k z := by
  rw [← cycleClass_comparison, ProjectiveLineCycleClass.cycleClass_chowRationalize]
  rfl

theorem cycleClass_principalRelation (d : PrincipalRelationData (dimensionFunction k) 0) :
    cycleClass k (rationalClassMap (dimensionFunction k) 0
      (cyclesOfDegreeRationalize (dimensionFunction k) 0
        (principalRelation (dimensionFunction k) 0 d))) = 0 := by
  rw [rationalClassMap_principalRelation, map_zero]

theorem cycleClass_ne_zero : cycleClass k ≠ 0 := by
  intro h
  have hz := congrArg (fun f : RationalChowGroup (dimensionFunction k) 0 →ₗ[ℚ] RationalTarget k ↦
    RestrictScalars.addEquiv ℚ k (SchemeH2 k) (f (ProjectiveLineCycleClass.rationalInfinityClass k))) h
  rw [cycleClass_apply, ProjectiveLineCycleClass.rationalChowDegree_infinity,
    Rat.cast_one, one_smul] at hz
  exact schemeChernCoordinate_ne_zero k hz

/-- Irrational field multiples are not introduced by the rational Chow source. -/
theorem scalar_chernCoordinate_not_mem_cycleClass_range (a : k)
    (ha : a ∉ Set.range (algebraMap ℚ k)) :
    (RestrictScalars.addEquiv ℚ k (SchemeH2 k)).symm (a • schemeChernCoordinate k) ∉
      Set.range (cycleClass k) := by
  rintro ⟨z, hz⟩
  apply ha
  refine ⟨rationalChowDegree k z, ?_⟩
  have h := congrArg (fun w : RationalTarget k ↦
    schemeResidueEquiv k (RestrictScalars.addEquiv ℚ k (SchemeH2 k) w)) hz
  simpa only [residue_cycleClass, AddEquiv.apply_symm_apply, map_smul,
    schemeResidueEquiv_chernCoordinate, smul_eq_mul, mul_one, eq_ratCast] using h

end HodgeConjecture.ProjectiveLineSchemeCycleClass
