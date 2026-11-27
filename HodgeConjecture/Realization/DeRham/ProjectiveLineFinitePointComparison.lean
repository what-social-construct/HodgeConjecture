module

public import HodgeConjecture.Realization.Betti.ProjectiveLineFinitePointGysin
public import HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification
public import HodgeConjecture.Realization.Chow.ProjectiveLineFinitePoint
public import HodgeConjecture.Realization.Chow.ProjectiveLineSquare
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

@[expose] public section

/-!
# Every finite point retains its original cycle class and full-target certificate

The actual scheme image of the native singleton support defines the original
ordinary point cycle. Its equality with the affine evaluation-center cycle is
proved, and the geometric finite-point Gysin unit agrees with its original
cycle class, for every invertible affine normal coordinate.

The new family of certificates retains the original Hodge model, full basis
and original finite-flat square-cover maps. Its transfer degree is the actual
global finite-flat rank at the selected target point. It is not a claim that
every moved point has local ramification multiplicity two. Normalized original
pushforward recovers the same ordinary finite-point class that was selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFinitePointComparison

open AlgebraicGeometry CategoryTheory SchemeCycles ProjectiveLineCycles

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

/-- The original scheme image of the actual singleton support, before choosing any cycle. -/
def schemePoint (a : ℂ) : scheme :=
  ProjectiveLineComplexPoints.schemeMorphism
    (ProjectiveLineFinitePointSupport.point a).val (default : Spec (.of ℂ))

theorem schemePoint_eq_center (a : ℂ) : schemePoint a = ProjectiveLineAffineChart.center ℂ a :=
  ProjectiveLineFinitePointGysin.pointSupport_scheme_base a _ _

theorem schemePoint_ne_genericPoint (a : ℂ) : schemePoint a ≠ genericPoint scheme := by
  rw [schemePoint_eq_center]
  exact ProjectiveLineAffineChart.center_ne_genericPoint ℂ a

/-- The original quotient map on the actual reduced scheme image of that same native support. -/
def pointClass (a : ℂ) : BaseChow :=
  rationalClassMap (dimensionFunction ℂ) 0
    (pointCycle ℂ ℚ (schemePoint a) (schemePoint_ne_genericPoint a))

private theorem pointCycle_congr {x y : scheme} (h : x = y)
    (hx : x ≠ genericPoint scheme) (hy : y ≠ genericPoint scheme) :
    pointCycle ℂ ℚ x hx = pointCycle ℂ ℚ y hy := by
  cases h
  rfl

theorem pointClass_eq_original (a : ℂ) :
    pointClass a = ProjectiveLineFinitePointChow.pointClass ℂ a := by
  apply congrArg (rationalClassMap (dimensionFunction ℂ) 0)
  exact pointCycle_congr (schemePoint_eq_center a) _ _

/-- Native geometric Gysin agrees with the original ordinary cycle of its same actual support. -/
theorem gysin_pointUnit_eq_cycleClass (a : ℂ) (u : ℂˣ) :
    ProjectiveLineFinitePointGysin.gysin a u (ProjectiveLineFinitePointSupport.pointUnit a) =
      model.cycleClass (pointClass a) := by
  rw [ProjectiveLineFinitePointGysin.gysin_pointUnit]
  exact (ProjectiveLineBettiCycleClass.cycleClass_pointCycle _ _).symm

/-- This normalization explicitly consumes the actual finite-point Gysin construction. -/
theorem pointClass_cycleClass (a : ℂ) :
    model.cycleClass (pointClass a) = ProjectiveLineBettiCohomology.coverGenerator := by
  rw [← gysin_pointUnit_eq_cycleClass a 1, ProjectiveLineFinitePointGysin.gysin_pointUnit]

theorem pointClass_ne_zero (a : ℂ) : pointClass a ≠ 0 := by
  rw [pointClass_eq_original]
  exact ProjectiveLineFinitePointChow.pointClass_ne_zero ℂ a

/-- Actual global degree at the selected target point, with the already constructed native maps. -/
def transfer (a : ℂ) : RationalDegreeTransfer Betti Betti where
  pull := ProjectiveLineSquareRamification.degreeTransfer.pull
  push := ProjectiveLineSquareRamification.degreeTransfer.push
  degree := cover.finrank (schemePoint a)
  degree_ne_zero := by rw [ProjectiveLineSquare.square_finrank]; decide
  push_comp_pull := by
    rw [ProjectiveLineSquare.square_finrank]
    exact ProjectiveLineSquareRamification.degreeTransfer.push_comp_pull

theorem degree_eq_two (a : ℂ) : (transfer a).degree = 2 :=
  ProjectiveLineSquare.square_finrank ℂ (schemePoint a)

theorem degree_eq_geometric_rank (a : ℂ) (x : scheme) :
    (transfer a).degree = cover.finrank x := by
  rw [degree_eq_two, ProjectiveLineSquare.square_finrank]

def upstairsCycleClass : CoverChow →ₗ[ℚ] Betti :=
  model.cycleClass.comp sourceComparison.toLinearMap

theorem pull_comparison (a : ℂ) :
    upstairsCycleClass.comp actualPull = (transfer a).pull.comp model.cycleClass := by
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

theorem push_comparison (a : ℂ) :
    model.cycleClass.comp actualPush = (transfer a).push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  dsimp only [LinearMap.comp_apply, transfer, ProjectiveLineSquareRamification.degreeTransfer]
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply]
  change rationalChowDegree ℂ (actualPush z) • ProjectiveLineBettiCohomology.coverGenerator =
    rationalChowDegree ℂ (sourceComparison z) • ProjectiveLineBettiCohomology.coverGenerator
  rw [ProjectiveLineSquareChow.degree_push]

def upstairsCycles (a : ℂ) (_ : Unit) : CoverChow := actualPull (pointClass a)

theorem target_column (j : Unit) :
    (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [Module.Basis.equivFun_symm_apply]
  cases j
  simpa using ProjectiveLineCoverageCertificate.basis_vector ()

theorem upstairs_columns (a : ℂ) (j : Unit) :
    upstairsCycleClass (upstairsCycles a j) =
      (transfer a).pull (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) := by
  have h := LinearMap.congr_fun (pull_comparison a) (pointClass a)
  change upstairsCycleClass (upstairsCycles a j) = (transfer a).pull
    (model.cycleClass (pointClass a)) at h
  rw [pointClass_cycleClass] at h
  simpa only [target_column] using h

theorem geometric_chow_push_pull (a : ℂ) (z : BaseChow) :
    actualPush (actualPull z) = ((transfer a).degree : ℚ) • z := by
  rw [degree_eq_two]
  simpa only [Nat.cast_ofNat, two_smul] using ProjectiveLineSquareChow.push_pull ℂ z

def certificate (a : ℂ) : FiniteCoverageCertificate.Certificate model basis :=
  FiniteCoverageCertificate.of_degree_transfer model basis upstairsCycleClass (transfer a)
    actualPush (push_comparison a) (upstairsCycles a) 1
    ProjectiveLineCoverageCertificate.arithmetic (upstairs_columns a)

theorem accepted (a : ℂ) : FiniteCoverageCertificate.check (certificate a) = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ)
    ProjectiveLineCoverageCertificate.arithmetic = true
  decide +kernel

/-- Normalization recovers the original class at that same finite point, for every parameter a. -/
theorem normalized_cycles (a : ℂ) (j : Unit) :
    (certificate a).cycles j = ProjectiveLineFinitePointChow.pointClass ℂ a := by
  change ((transfer a).degree : ℚ)⁻¹ • actualPush (actualPull (pointClass a)) = _
  rw [geometric_chow_push_pull a, smul_smul, degree_eq_two]
  norm_num
  exact pointClass_eq_original a

theorem model_satisfies_from_finite_point (a : ℂ) : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check (certificate a) (accepted a)

end HodgeConjecture.ProjectiveLineFinitePointComparison

end
