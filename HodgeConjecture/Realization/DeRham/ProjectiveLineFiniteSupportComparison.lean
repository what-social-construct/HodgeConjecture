module

public import HodgeConjecture.Realization.Betti.ProjectiveLineFiniteSupportGysin
public import HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification
public import HodgeConjecture.Realization.Chow.ProjectiveLineFinitePoint
public import HodgeConjecture.Realization.Chow.ProjectiveLineSquare
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

@[expose] public section

/-!
# Original weighted point cycles and finite-support geometric Gysin

Actual finite-support H⁰ supplies rational coefficients on the same actual
points. Their reduced scheme-image cycles are summed before the original
ordinary Chow quotient. Native supported Gysin is the actual local direct sum;
its original support forgetting compares with the unchanged cycle-class map.

The average of the original unit cycle for a nonempty finite support yields
an accepted certificate for the same full Hodge target. Empty supports and
balanced zero-total classes cannot supply that target column. Original square
maps, global finite-flat rank and the earlier zero-supported push are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFiniteSupportComparison

open AlgebraicGeometry CategoryTheory SchemeCycles ProjectiveLineCycles ProjectiveLineComplexPoints
open scoped BigOperators

abbrev scheme := projectiveLine ℂ
abbrev cover := ProjectiveLineSquare.square ℂ
abbrev BaseChow := ProjectiveLineSquareChow.BaseChow ℂ
abbrev CoverChow := ProjectiveLineSquareChow.CoverChow ℂ
abbrev Betti := ProjectiveLineBettiComplexification.Betti
abbrev model := ProjectiveLineCoverageCertificate.model
abbrev basis := ProjectiveLineCoverageCertificate.basis
abbrev sourceComparison := ProjectiveLineSquareChow.chowEquiv ℂ
abbrev actualPull := ProjectiveLineSquareChow.actualPull ℂ
abbrev actualPush := ProjectiveLineSquareChow.actualPush ℂ
abbrev Support (S : Finset Point) := SingularFiniteSupport.Support S
abbrev H0 (S : Finset Point) := SingularFiniteSupport.H0 S
abbrev Cycle := cyclesOfDegree ℚ (dimensionFunction ℂ) 0

/-- Original scheme image, before forming any representative or quotient. -/
def schemePoint (p : Point) : scheme := schemeMorphism p (default : Spec (.of ℂ))

theorem schemePoint_ne_genericPoint (p : Point) : schemePoint p ≠ genericPoint scheme := by
  rcases finite_or_infinity p with ⟨a, rfl⟩ | rfl
  · change schemeMorphism (finite a) default ≠ _
    rw [show schemeMorphism (finite a) default = ProjectiveLineAffineChart.center ℂ a from
      ProjectiveLineFinitePointGysin.pointSupport_scheme_base a
        (ProjectiveLineFinitePointSupport.point a) default]
    exact ProjectiveLineAffineChart.center_ne_genericPoint ℂ a
  · change schemeMorphism infinity default ≠ _
    rw [infinity_base]
    exact Infinity.ne_genericPoint ℂ

def pointRepresentative (p : Point) : Cycle :=
  ProjectiveLineCycles.pointCycle ℂ ℚ (schemePoint p) (schemePoint_ne_genericPoint p)

def pointClass (p : Point) : BaseChow :=
  rationalClassMap (dimensionFunction ℂ) 0 (pointRepresentative p)

/-- The literal original homogeneous weighted cycle of the same support points. -/
def cycle (S : Finset Point) : H0 S →ₗ[ℚ] Cycle :=
  ∑ p : Support S, (((LinearMap.proj p : (Support S → ℚ) →ₗ[ℚ] ℚ).comp
    (SingularFiniteSupport.coordinates S).toLinearMap).smulRight (pointRepresentative p.val))

theorem cycle_apply (S : Finset Point) (z : H0 S) :
    cycle S z = ∑ p : Support S, SingularFiniteSupport.coordinates S z p •
      pointRepresentative p.val := by
  simp [cycle]

def classMap (S : Finset Point) : H0 S →ₗ[ℚ] BaseChow :=
  (rationalClassMap (dimensionFunction ℂ) 0).comp (cycle S)

theorem classMap_apply (S : Finset Point) (z : H0 S) :
    classMap S z = ∑ p : Support S, SingularFiniteSupport.coordinates S z p • pointClass p.val := by
  simp [classMap, cycle_apply, pointClass, map_sum, map_smul]

theorem pointGysin_unit_cycleClass (p : Point) :
    ProjectiveLineSupportedPoint.gysin p (ProjectiveLineSupportedPoint.pointUnit p) =
      model.cycleClass (pointClass p) := by
  rw [ProjectiveLineSupportedPoint.gysin_pointUnit]
  exact (ProjectiveLineBettiCycleClass.cycleClass_pointCycle _ _).symm

theorem pointClass_cycleClass (p : Point) :
    model.cycleClass (pointClass p) = ProjectiveLineBettiCohomology.coverGenerator := by
  rw [← pointGysin_unit_cycleClass, ProjectiveLineSupportedPoint.gysin_pointUnit]

private theorem weighted_cycleClass (S : Finset Point) (z : H0 S) :
    model.cycleClass (classMap S z) = SingularFiniteSupport.sumCoordinates S z •
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [classMap_apply, map_sum]
  simp_rw [map_smul, pointClass_cycleClass]
  rw [← Finset.sum_smul, SingularFiniteSupport.sumCoordinates_apply]

/-- Comparison uses the actual supported isomorphism, not an absolute coordinate definition. -/
theorem supported_cycleClass_comparison (S : Finset Point) (z : H0 S) :
    SingularSupports.forget Point (S : Set Point) 2
      (ProjectiveLineFiniteSupportGysin.gysinEquiv S z) = model.cycleClass (classMap S z) := by
  rw [ProjectiveLineFiniteSupportGysin.gysinEquiv_apply]
  change ProjectiveLineFiniteSupportGysin.gysin S z = _
  rw [ProjectiveLineFiniteSupportGysin.gysin_apply, weighted_cycleClass]

theorem classMap_cycleClass (S : Finset Point) (z : H0 S) :
    model.cycleClass (classMap S z) = SingularFiniteSupport.sumCoordinates S z •
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [← supported_cycleClass_comparison, ProjectiveLineFiniteSupportGysin.gysinEquiv_apply]
  exact ProjectiveLineFiniteSupportGysin.gysin_apply S z

/-- The original constant one class on the entire actual finite support. -/
def supportUnit (S : Finset Point) : H0 S :=
  SingularDegreeZeroNaturality.constantClass (Support S) 1

theorem mass_supportUnit (S : Finset Point) :
    SingularFiniteSupport.sumCoordinates S (supportUnit S) = (S.card : ℚ) := by
  simpa only [supportUnit, mul_one] using SingularFiniteSupport.sumCoordinates_constantClass S 1

/-- The raw original unit cycle, normalized by its actual finite support cardinality. -/
def averageCycle (S : Finset Point) : Cycle := (S.card : ℚ)⁻¹ • cycle S (supportUnit S)

def averageClass (S : Finset Point) : BaseChow :=
  rationalClassMap (dimensionFunction ℂ) 0 (averageCycle S)

theorem averageClass_eq (S : Finset Point) :
    averageClass S = (S.card : ℚ)⁻¹ • classMap S (supportUnit S) := by
  rw [averageClass, averageCycle, map_smul]
  rfl

theorem card_ne_zero (S : Finset Point) (hS : S.Nonempty) : (S.card : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)

theorem averageClass_cycleClass (S : Finset Point) (hS : S.Nonempty) :
    model.cycleClass (averageClass S) = ProjectiveLineBettiCohomology.coverGenerator := by
  rw [averageClass_eq, map_smul, classMap_cycleClass, mass_supportUnit, smul_smul,
    inv_mul_cancel₀ (card_ne_zero S hS), one_smul]

/-- A support point is used only to evaluate the same original GLOBAL cover rank. -/
def selectedPoint (S : Finset Point) (hS : S.Nonempty) : Point := Classical.choose hS

theorem selectedPoint_mem (S : Finset Point) (hS : S.Nonempty) : selectedPoint S hS ∈ S :=
  Classical.choose_spec hS

/-- Actual global degree at the selected target point, with the already constructed native maps. -/
def transfer (S : Finset Point) (hS : S.Nonempty) : RationalDegreeTransfer Betti Betti where
  pull := ProjectiveLineSquareRamification.degreeTransfer.pull
  push := ProjectiveLineSquareRamification.degreeTransfer.push
  degree := cover.finrank (schemePoint (selectedPoint S hS))
  degree_ne_zero := by rw [ProjectiveLineSquare.square_finrank]; decide
  push_comp_pull := by
    rw [ProjectiveLineSquare.square_finrank]
    exact ProjectiveLineSquareRamification.degreeTransfer.push_comp_pull

theorem degree_eq_two (S : Finset Point) (hS : S.Nonempty) : (transfer S hS).degree = 2 :=
  ProjectiveLineSquare.square_finrank ℂ (schemePoint (selectedPoint S hS))

theorem degree_eq_geometric_rank (S : Finset Point) (hS : S.Nonempty) (x : scheme) :
    (transfer S hS).degree = cover.finrank x := by
  rw [degree_eq_two, ProjectiveLineSquare.square_finrank]

def upstairsCycleClass : CoverChow →ₗ[ℚ] Betti :=
  model.cycleClass.comp sourceComparison.toLinearMap

theorem pull_comparison (S : Finset Point) (hS : S.Nonempty) :
    upstairsCycleClass.comp actualPull = (transfer S hS).pull.comp model.cycleClass := by
  apply LinearMap.ext
  intro z
  change ProjectiveLineBettiCycleClass.cycleClass (sourceComparison (actualPull z)) =
    SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2
      (ProjectiveLineBettiCycleClass.cycleClass z)
  rw [ProjectiveLineSquareRamification.cohomologyPullback_square]
  change rationalChowDegree ℂ (sourceComparison (actualPull z)) •
      ProjectiveLineBettiCohomology.coverGenerator =
    (2 : ℚ) • (rationalChowDegree ℂ z • ProjectiveLineBettiCohomology.coverGenerator)
  rw [ProjectiveLineSquareChow.degree_pull, smul_smul]

theorem push_comparison (S : Finset Point) (hS : S.Nonempty) :
    model.cycleClass.comp actualPush = (transfer S hS).push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  dsimp only [LinearMap.comp_apply, transfer, ProjectiveLineSquareRamification.degreeTransfer]
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply]
  change rationalChowDegree ℂ (actualPush z) • ProjectiveLineBettiCohomology.coverGenerator =
    rationalChowDegree ℂ (sourceComparison z) • ProjectiveLineBettiCohomology.coverGenerator
  rw [ProjectiveLineSquareChow.degree_push]

def upstairsCycles (S : Finset Point) (_ : Unit) : CoverChow := actualPull (averageClass S)

theorem target_column (j : Unit) :
    (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [Module.Basis.equivFun_symm_apply]
  cases j
  simpa using ProjectiveLineCoverageCertificate.basis_vector ()

theorem upstairs_columns (S : Finset Point) (hS : S.Nonempty) (j : Unit) :
    upstairsCycleClass (upstairsCycles S j) =
      (transfer S hS).pull (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) := by
  have h := LinearMap.congr_fun (pull_comparison S hS) (averageClass S)
  change upstairsCycleClass (upstairsCycles S j) = (transfer S hS).pull
    (model.cycleClass (averageClass S)) at h
  rw [averageClass_cycleClass S hS] at h
  simpa only [target_column] using h

theorem geometric_chow_push_pull (S : Finset Point) (hS : S.Nonempty) (z : BaseChow) :
    actualPush (actualPull z) = ((transfer S hS).degree : ℚ) • z := by
  rw [degree_eq_two]
  simpa only [Nat.cast_ofNat, two_smul] using ProjectiveLineSquareChow.push_pull ℂ z

def certificate (S : Finset Point) (hS : S.Nonempty) : FiniteCoverageCertificate.Certificate model basis :=
  FiniteCoverageCertificate.of_degree_transfer model basis upstairsCycleClass (transfer S hS)
    actualPush (push_comparison S hS) (upstairsCycles S) 1
    ProjectiveLineCoverageCertificate.arithmetic (upstairs_columns S hS)

theorem accepted (S : Finset Point) (hS : S.Nonempty) : FiniteCoverageCertificate.check (certificate S hS) = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ)
    ProjectiveLineCoverageCertificate.arithmetic = true
  decide +kernel

/-- Normalized original geometric pushforward recovers the same original average class. -/
theorem normalized_cycles (S : Finset Point) (hS : S.Nonempty) (j : Unit) :
    (certificate S hS).cycles j = averageClass S := by
  change ((transfer S hS).degree : ℚ)⁻¹ • actualPush (actualPull (averageClass S)) = _
  rw [geometric_chow_push_pull S hS, smul_smul, degree_eq_two]
  norm_num

theorem averageClass_empty : averageClass ∅ = 0 := by
  simp [averageClass_eq]

theorem empty_does_not_supply_target :
    model.cycleClass (averageClass ∅) ≠ ProjectiveLineBettiCohomology.coverGenerator := by
  rw [averageClass_empty, map_zero]
  exact ProjectiveLineBettiCohomology.coverGenerator_ne_zero.symm

theorem zero_mass_does_not_supply_target (S : Finset Point) (z : H0 S)
    (hz : SingularFiniteSupport.sumCoordinates S z = 0) :
    model.cycleClass (classMap S z) ≠ ProjectiveLineBettiCohomology.coverGenerator := by
  rw [classMap_cycleClass, hz, zero_smul]
  exact ProjectiveLineBettiCohomology.coverGenerator_ne_zero.symm

theorem model_satisfies_from_nonempty_finite_support (S : Finset Point) (hS : S.Nonempty) :
    RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check (certificate S hS) (accepted S hS)

end HodgeConjecture.ProjectiveLineFiniteSupportComparison

end
