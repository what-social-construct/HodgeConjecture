module

public import HodgeConjecture.Realization.Betti.ProjectiveLineInfinityGysin
public import HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification
public import HodgeConjecture.Realization.Chow.ProjectiveLineFinitePoint
public import HodgeConjecture.Realization.Chow.ProjectiveLineSquare
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

@[expose] public section

/-!
# Original point cycles and full-target certificates at every complex-valued point

The actual scheme image of each original native point defines its ordinary
reduced cycle, with the original grading and Chow quotient. The actual finite
or reciprocal Thom/excision Gysin construction gives its positive cycle class.
The complete point dichotomy includes infinity; no ordinary class is replaced.

The certificate family uses the same original full Hodge model and basis,
original square-cover maps and GLOBAL finite-flat rank. Its native push remains
the earlier zero-supported trace. This adds point Gysin and positive
normalization, not general proper trace or nonlinear coordinate naturality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLinePointGysinComparison

open AlgebraicGeometry CategoryTheory SchemeCycles ProjectiveLineCycles ProjectiveLineComplexPoints

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

/-- The actual underlying scheme image, before choosing any cycle. -/
def schemePoint (p : Point) : scheme := schemeMorphism p (default : Spec (.of ℂ))

theorem schemePoint_finite (a : ℂ) :
    schemePoint (finite a) = ProjectiveLineAffineChart.center ℂ a :=
  ProjectiveLineFinitePointGysin.pointSupport_scheme_base a
    (ProjectiveLineFinitePointSupport.point a) default

theorem schemePoint_infinity : schemePoint infinity = projectiveLineInfinity ℂ :=
  ProjectiveLineInfinitySupport.pointSupport_scheme_base ProjectiveLineInfinitySupport.point default

theorem schemePoint_ne_genericPoint (p : Point) : schemePoint p ≠ genericPoint scheme := by
  rcases finite_or_infinity p with ⟨a, rfl⟩ | rfl
  · rw [schemePoint_finite]
    exact ProjectiveLineAffineChart.center_ne_genericPoint ℂ a
  · rw [schemePoint_infinity]
    exact Infinity.ne_genericPoint ℂ

/-- The literal original ordinary quotient map on the cycle of this same point. -/
def pointClass (p : Point) : BaseChow :=
  rationalClassMap (dimensionFunction ℂ) 0
    (pointCycle ℂ ℚ (schemePoint p) (schemePoint_ne_genericPoint p))

private theorem pointCycle_congr {x y : scheme} (h : x = y)
    (hx : x ≠ genericPoint scheme) (hy : y ≠ genericPoint scheme) :
    pointCycle ℂ ℚ x hx = pointCycle ℂ ℚ y hy := by
  cases h
  rfl

theorem pointClass_finite (a : ℂ) :
    pointClass (finite a) = ProjectiveLineFinitePointChow.pointClass ℂ a := by
  apply congrArg (rationalClassMap (dimensionFunction ℂ) 0)
  exact pointCycle_congr (schemePoint_finite a) _ _

theorem pointClass_infinity : pointClass infinity = Infinity.rationalClass ℂ := by
  apply congrArg (rationalClassMap (dimensionFunction ℂ) 0)
  exact pointCycle_congr schemePoint_infinity _ _

/-- The actual geometric Gysin isomorphism of the same original singleton has
the original ordinary cycle class as unit image, in either original chart. -/
theorem geometric_gysin_unit (p : Point) (u : ℂˣ) :
    ∃ e : ProjectiveLineInfinityGysin.PointH0At p ≅ Betti,
      e.hom (ProjectiveLineInfinityGysin.pointUnitAt p) = model.cycleClass (pointClass p) ∧
      e.hom (ProjectiveLineInfinityGysin.pointUnitAt p) =
        ProjectiveLineBettiCohomology.coverGenerator := by
  obtain ⟨e, he⟩ := ProjectiveLineInfinityGysin.every_point_gysinIso p u
  refine ⟨e, ?_, he⟩
  rw [he]
  exact (ProjectiveLineBettiCycleClass.cycleClass_pointCycle _ _).symm

/-- This normalization consumes both actual geometric chart constructions. -/
theorem pointClass_cycleClass (p : Point) :
    model.cycleClass (pointClass p) = ProjectiveLineBettiCohomology.coverGenerator := by
  obtain ⟨e, hcycle, hpositive⟩ := geometric_gysin_unit p 1
  exact hcycle.symm.trans hpositive

theorem pointClass_ne_zero (p : Point) : pointClass p ≠ 0 := by
  intro h
  have hc := pointClass_cycleClass p
  rw [h, map_zero] at hc
  exact ProjectiveLineBettiCohomology.coverGenerator_ne_zero hc.symm

/-- Actual global degree at the selected target point, with the already constructed native maps. -/
def transfer (p : Point) : RationalDegreeTransfer Betti Betti where
  pull := ProjectiveLineSquareRamification.degreeTransfer.pull
  push := ProjectiveLineSquareRamification.degreeTransfer.push
  degree := cover.finrank (schemePoint p)
  degree_ne_zero := by rw [ProjectiveLineSquare.square_finrank]; decide
  push_comp_pull := by
    rw [ProjectiveLineSquare.square_finrank]
    exact ProjectiveLineSquareRamification.degreeTransfer.push_comp_pull

theorem degree_eq_two (p : Point) : (transfer p).degree = 2 :=
  ProjectiveLineSquare.square_finrank ℂ (schemePoint p)

theorem degree_eq_geometric_rank (p : Point) (x : scheme) :
    (transfer p).degree = cover.finrank x := by
  rw [degree_eq_two, ProjectiveLineSquare.square_finrank]

def upstairsCycleClass : CoverChow →ₗ[ℚ] Betti :=
  model.cycleClass.comp sourceComparison.toLinearMap

theorem pull_comparison (p : Point) :
    upstairsCycleClass.comp actualPull = (transfer p).pull.comp model.cycleClass := by
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

theorem push_comparison (p : Point) :
    model.cycleClass.comp actualPush = (transfer p).push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  dsimp only [LinearMap.comp_apply, transfer, ProjectiveLineSquareRamification.degreeTransfer]
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply]
  change rationalChowDegree ℂ (actualPush z) • ProjectiveLineBettiCohomology.coverGenerator =
    rationalChowDegree ℂ (sourceComparison z) • ProjectiveLineBettiCohomology.coverGenerator
  rw [ProjectiveLineSquareChow.degree_push]

def upstairsCycles (p : Point) (_ : Unit) : CoverChow := actualPull (pointClass p)

theorem target_column (j : Unit) :
    (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [Module.Basis.equivFun_symm_apply]
  cases j
  simpa using ProjectiveLineCoverageCertificate.basis_vector ()

theorem upstairs_columns (p : Point) (j : Unit) :
    upstairsCycleClass (upstairsCycles p j) =
      (transfer p).pull (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) := by
  have h := LinearMap.congr_fun (pull_comparison p) (pointClass p)
  change upstairsCycleClass (upstairsCycles p j) = (transfer p).pull
    (model.cycleClass (pointClass p)) at h
  rw [pointClass_cycleClass] at h
  simpa only [target_column] using h

theorem geometric_chow_push_pull (p : Point) (z : BaseChow) :
    actualPush (actualPull z) = ((transfer p).degree : ℚ) • z := by
  rw [degree_eq_two]
  simpa only [Nat.cast_ofNat, two_smul] using ProjectiveLineSquareChow.push_pull ℂ z

def certificate (p : Point) : FiniteCoverageCertificate.Certificate model basis :=
  FiniteCoverageCertificate.of_degree_transfer model basis upstairsCycleClass (transfer p)
    actualPush (push_comparison p) (upstairsCycles p) 1
    ProjectiveLineCoverageCertificate.arithmetic (upstairs_columns p)

theorem accepted (p : Point) : FiniteCoverageCertificate.check (certificate p) = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ)
    ProjectiveLineCoverageCertificate.arithmetic = true
  decide +kernel

/-- Normalization recovers the original ordinary class at the same actual point. -/
theorem normalized_cycles (p : Point) (j : Unit) : (certificate p).cycles j = pointClass p := by
  change ((transfer p).degree : ℚ)⁻¹ • actualPush (actualPull (pointClass p)) = _
  rw [geometric_chow_push_pull p, smul_smul, degree_eq_two]
  norm_num

theorem normalized_cycles_finite (a : ℂ) (j : Unit) :
    (certificate (finite a)).cycles j = ProjectiveLineFinitePointChow.pointClass ℂ a := by
  rw [normalized_cycles, pointClass_finite]

theorem normalized_cycles_infinity (j : Unit) :
    (certificate infinity).cycles j = Infinity.rationalClass ℂ := by
  rw [normalized_cycles, pointClass_infinity]

theorem model_satisfies_from_every_point (p : Point) : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check (certificate p) (accepted p)

end HodgeConjecture.ProjectiveLinePointGysinComparison

end
