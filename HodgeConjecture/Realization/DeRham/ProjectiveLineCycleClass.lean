module

public import HodgeConjecture.Cycles.ProjectiveLineChow
public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCohomology
public import Mathlib.Algebra.Algebra.RestrictScalars

@[expose] public section

/-!
# Ordinary projective-line cycle classes in total degree two

The source is the existing ordinary Chow quotient of actual homogeneous
zero-cycles on the actual projective line. The proved actual principal
divisor degree theorem, not a supplied realization premise, makes degree
well defined. Its multiple of the constructed Čech first-Chern class gives
the ordinary algebraic degree-two cycle map with point normalization.

The rational map uses standard scalar restriction on the same Čech
cohomology target. The target remains the stated coordinate-ring Čech
de Rham realization; no singular/Hodge comparison or higher-codimension
generation theorem is asserted.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineCycleClass

open AlgebraicGeometry SchemeCycles ProjectiveLineCycles ProjectiveLineDeRham

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Infinity is an actual closed point rather than the ambient generic point. -/
theorem infinity_ne_genericPoint :
    projectiveLineInfinity k ≠ genericPoint (projectiveLine k) :=
  ProjectiveLineCycles.Infinity.ne_genericPoint k

variable [IsAlgClosed k]

/-- Compatibility name for the shared integral infinity Chow class. -/
def integralInfinityClass : ChowGroup (dimensionFunction k) 0 :=
  ProjectiveLineCycles.Infinity.integralClass k

/-- Compatibility name for the shared rational infinity Chow class. -/
def rationalInfinityClass : RationalChowGroup (dimensionFunction k) 0 :=
  ProjectiveLineCycles.Infinity.rationalClass k

@[simp]
theorem integralChowDegree_infinity : integralChowDegree k (integralInfinityClass k) = 1 :=
  ProjectiveLineCycles.Infinity.integralChowDegree_eq_one k

@[simp]
theorem rationalChowDegree_infinity : rationalChowDegree k (rationalInfinityClass k) = 1 :=
  ProjectiveLineCycles.Infinity.rationalChowDegree_eq_one k

/-- Integral ordinary cycle classes, constructed from the proved degree and actual first Chern class. -/
def integralCycleClass : ChowGroup (dimensionFunction k) 0 →+ CechH2 k where
  toFun z := integralChowDegree k z • chernCoordinate k
  map_zero' := by simp
  map_add' z w := by rw [map_add, add_zsmul]

@[simp]
theorem integralCycleClass_pointCycle (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    integralCycleClass k (classMap (dimensionFunction k) 0 (pointCycle k ℤ x hx)) =
      chernCoordinate k := by
  change integralChowDegree k (classMap (dimensionFunction k) 0 (pointCycle k ℤ x hx)) •
    chernCoordinate k = chernCoordinate k
  rw [integralChowDegree_pointCycle, one_zsmul]

/-- In particular the actual infinity cycle has the constructed coordinate first-Chern class. -/
theorem integralCycleClass_infinity : integralCycleClass k (integralInfinityClass k) =
    firstChern k (transitionClass k (Additive.ofMul (LaurentDeRham.variableUnit k))) := by
  change integralCycleClass k (classMap (dimensionFunction k) 0
    (pointCycle k ℤ (projectiveLineInfinity k) (infinity_ne_genericPoint k))) = chernCoordinate k
  exact integralCycleClass_pointCycle k _ _

/-- Actual integral principal relations vanish under the ordinary degree-two cycle map. -/
theorem integralCycleClass_principalRelation (d : PrincipalRelationData (dimensionFunction k) 0) :
    integralCycleClass k (classMap (dimensionFunction k) 0
      (principalRelation (dimensionFunction k) 0 d)) = 0 := by
  change integralDegree k (principalRelation (dimensionFunction k) 0 d) • chernCoordinate k = 0
  rw [integralDegree_principalRelation, zero_zsmul]

variable [CharZero k]

/-- The same actual Čech H², with its canonical rational scalar restriction. -/
abbrev RationalTarget := RestrictScalars ℚ k (CechH2 k)

/-- The ordinary rational cycle-class map from the original rational Chow quotient. -/
def cycleClass : RationalChowGroup (dimensionFunction k) 0 →ₗ[ℚ] RationalTarget k where
  toFun z := (rationalChowDegree k z : k) • chernCoordinate k
  map_add' z w := by
    change ((rationalChowDegree k (z + w) : ℚ) : k) • _ = _
    rw [map_add, Rat.cast_add, add_smul]
  map_smul' q z := by
    change ((rationalChowDegree k (q • z) : ℚ) : k) • _ =
      (q : k) • ((rationalChowDegree k z : k) • chernCoordinate k)
    rw [map_smul, smul_eq_mul, Rat.cast_mul, mul_smul]

/-- Scalar restriction retains the original Čech cohomology element and its representative. -/
theorem cycleClass_apply (z : RationalChowGroup (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (CechH2 k) (cycleClass k z) =
      (rationalChowDegree k z : k) • chernCoordinate k := rfl

/-- The map on an original cycle representative is its actual coefficient degree times the first-Chern class. -/
theorem cycleClass_classMap (c : cyclesOfDegree ℚ (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (CechH2 k)
        (cycleClass k (rationalClassMap (dimensionFunction k) 0 c)) =
      (rationalDegree k c : k) • chernCoordinate k := rfl

/-- Every original coefficient-one closed point cycle has the expected nonzero normalization. -/
@[simp]
theorem cycleClass_pointCycle (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    RestrictScalars.addEquiv ℚ k (CechH2 k)
        (cycleClass k (rationalClassMap (dimensionFunction k) 0 (pointCycle k ℚ x hx))) =
      chernCoordinate k := by
  rw [cycleClass_apply, rationalChowDegree_pointCycle, Rat.cast_one, one_smul]

/-- The ordinary rational point class is detected by the independent residue functional. -/
theorem residue_cycleClass (z : RationalChowGroup (dimensionFunction k) 0) :
    cechResidue k (RestrictScalars.addEquiv ℚ k (CechH2 k) (cycleClass k z)) =
      (rationalChowDegree k z : k) := by
  rw [cycleClass_apply, map_smul, cechResidue_chernCoordinate, smul_eq_mul, mul_one]

/-- The rational cycle map agrees with the integral one under the original Chow rationalization. -/
theorem cycleClass_chowRationalize (z : ChowGroup (dimensionFunction k) 0) :
    RestrictScalars.addEquiv ℚ k (CechH2 k)
        (cycleClass k (chowRationalize (dimensionFunction k) 0 z)) =
      integralCycleClass k z := by
  rw [cycleClass_apply, rationalChowDegree_chowRationalize]
  change (((integralChowDegree k z : ℤ) : ℚ) : k) • chernCoordinate k =
    integralChowDegree k z • chernCoordinate k
  rw [Rat.cast_intCast, Int.cast_smul_eq_zsmul]

/-- Scalar restriction has not enlarged rational cycle coefficients to all field coefficients. -/
theorem scalar_chernCoordinate_not_mem_cycleClass_range (a : k)
    (ha : a ∉ Set.range (algebraMap ℚ k)) :
    (RestrictScalars.addEquiv ℚ k (CechH2 k)).symm (a • chernCoordinate k) ∉
      Set.range (cycleClass k) := by
  rintro ⟨z, hz⟩
  apply ha
  refine ⟨rationalChowDegree k z, ?_⟩
  have h := congrArg (fun w : RationalTarget k ↦
    cechResidue k (RestrictScalars.addEquiv ℚ k (CechH2 k) w)) hz
  simpa only [residue_cycleClass, AddEquiv.apply_symm_apply, map_smul,
    cechResidue_chernCoordinate, smul_eq_mul, mul_one, eq_ratCast] using h

/-- The actual ordinary rational cycle map is nonzero. -/
theorem cycleClass_ne_zero : cycleClass k ≠ 0 := by
  intro h
  have hz := DFunLike.congr_fun h (rationalInfinityClass k)
  have hz' := congrArg (RestrictScalars.addEquiv ℚ k (CechH2 k)) hz
  rw [cycleClass_apply, rationalChowDegree_infinity, Rat.cast_one, one_smul] at hz'
  exact chernCoordinate_ne_zero k hz'

/-- All original rational principal generators map to zero. -/
theorem cycleClass_principalRelation (d : PrincipalRelationData (dimensionFunction k) 0) :
    cycleClass k (rationalClassMap (dimensionFunction k) 0
      (cyclesOfDegreeRationalize (dimensionFunction k) 0 (principalRelation (dimensionFunction k) 0 d))) =
      0 := by
  rw [rationalClassMap_principalRelation, map_zero]

end

end HodgeConjecture.ProjectiveLineCycleClass
