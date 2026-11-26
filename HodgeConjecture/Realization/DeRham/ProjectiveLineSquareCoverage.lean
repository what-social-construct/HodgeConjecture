module

public import HodgeConjecture.Realization.Betti.ProjectiveLineSquareGysin
public import HodgeConjecture.Realization.Chow.ProjectiveLineSquare
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

@[expose] public section

/-!
# A connected branched projective-line cover in the exact aggregate

The actual scheme squaring map is finite flat of geometric rank two.
Its source Chow group retains the exact composite structure morphism;
the proved equality of structural morphisms identifies its representatives
with those of the original projective-line Chow group.

Native pullback on H² is independently computed by angular singular
triangles and Mayer–Vietoris naturality. The push map is the zero-supported
point-Gysin trace constructed from the actual fixed singleton map. Both
original Chow comparison squares are proved before binding the aggregate.
The independently defined Hodge model, full basis and arithmetic checker
are retained. No general branched trace or new Hodge-conjecture case is claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineSquareCoverage

open AlgebraicGeometry CategoryTheory

abbrev scheme := projectiveLine ℂ
abbrev cover := ProjectiveLineSquare.square ℂ
abbrev BaseChow := ProjectiveLineSquareChow.BaseChow ℂ
abbrev CoverChow := ProjectiveLineSquareChow.CoverChow ℂ
abbrev Betti := ProjectiveLineBettiComplexification.Betti

abbrev model := ProjectiveLineCoverageCertificate.model
abbrev basis := ProjectiveLineCoverageCertificate.basis
abbrev actualPull := ProjectiveLineSquareChow.actualPull ℂ
abbrev actualPush := ProjectiveLineSquareChow.actualPush ℂ
abbrev sourceComparison := ProjectiveLineSquareChow.chowEquiv ℂ
abbrev transfer := ProjectiveLineSquareGysin.degreeTransfer

/-- The original projective-line cycle map, retaining the proved source grading identification. -/
def upstairsCycleClass : CoverChow →ₗ[ℚ] Betti :=
  model.cycleClass.comp sourceComparison.toLinearMap

theorem upstairsCycleClass_sourceComparison (z : BaseChow) :
    upstairsCycleClass (sourceComparison.symm z) = model.cycleClass z := by
  change model.cycleClass (sourceComparison (sourceComparison.symm z)) = _
  rw [sourceComparison.apply_symm_apply]

theorem pull_comparison :
    upstairsCycleClass.comp actualPull = transfer.pull.comp model.cycleClass := by
  apply LinearMap.ext
  intro z
  change ProjectiveLineBettiCycleClass.cycleClass
      (sourceComparison (actualPull z)) =
    SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2
      (ProjectiveLineBettiCycleClass.cycleClass z)
  rw [ProjectiveLineSquarePullback.cohomologyPullback_square]
  change ProjectiveLineCycles.rationalChowDegree ℂ (sourceComparison (actualPull z)) •
      ProjectiveLineBettiCohomology.coverGenerator =
    (2 : ℚ) • (ProjectiveLineCycles.rationalChowDegree ℂ z •
      ProjectiveLineBettiCohomology.coverGenerator)
  rw [ProjectiveLineSquareChow.degree_pull, smul_smul]

theorem push_comparison :
    model.cycleClass.comp actualPush = transfer.push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  dsimp only [LinearMap.comp_apply, transfer, ProjectiveLineSquareGysin.degreeTransfer]
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply]
  change ProjectiveLineCycles.rationalChowDegree ℂ (actualPush z) •
      ProjectiveLineBettiCohomology.coverGenerator =
    ProjectiveLineCycles.rationalChowDegree ℂ (sourceComparison z) •
      ProjectiveLineBettiCohomology.coverGenerator
  rw [ProjectiveLineSquareChow.degree_push]

theorem degree_eq_geometric_rank (x : scheme) : transfer.degree = cover.finrank x :=
  (ProjectiveLineSquare.square_finrank ℂ x).symm

def upstairsCycles (_ : Unit) : CoverChow :=
  actualPull ProjectiveLineBettiCycleClass.rationalInfinityClass

theorem target_column (j : Unit) :
    (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i j) : Betti) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [Module.Basis.equivFun_symm_apply]
  cases j
  simpa using ProjectiveLineCoverageCertificate.basis_vector ()

theorem upstairs_columns (j : Unit) :
    upstairsCycleClass (upstairsCycles j) =
      transfer.pull (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i j) : Betti) := by
  have h := LinearMap.congr_fun pull_comparison
    ProjectiveLineBettiCycleClass.rationalInfinityClass
  have hcycle : model.cycleClass ProjectiveLineBettiCycleClass.rationalInfinityClass =
      ProjectiveLineBettiCohomology.coverGenerator :=
    ProjectiveLineBettiCycleClass.cycleClass_infinity
  change upstairsCycleClass (upstairsCycles j) =
    transfer.pull (model.cycleClass ProjectiveLineBettiCycleClass.rationalInfinityClass) at h
  rw [hcycle] at h
  simpa only [target_column] using h

theorem geometric_chow_push_pull (z : BaseChow) :
    actualPush (actualPull z) = (2 : ℚ) • z := by
  simpa only [two_smul] using ProjectiveLineSquareChow.push_pull ℂ z

def certificate : FiniteCoverageCertificate.Certificate model basis :=
  FiniteCoverageCertificate.of_degree_transfer model basis upstairsCycleClass transfer
    actualPush push_comparison upstairsCycles 1 ProjectiveLineCoverageCertificate.arithmetic
    upstairs_columns

theorem accepted : FiniteCoverageCertificate.check certificate = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ)
    ProjectiveLineCoverageCertificate.arithmetic = true
  decide +kernel

theorem normalized_cycles (j : Unit) :
    certificate.cycles j = ProjectiveLineBettiCycleClass.rationalInfinityClass := by
  change (2 : ℚ)⁻¹ • actualPush
    (actualPull ProjectiveLineBettiCycleClass.rationalInfinityClass) = _
  rw [geometric_chow_push_pull, smul_smul]
  norm_num

theorem model_satisfies_from_square_cover : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

end HodgeConjecture.ProjectiveLineSquareCoverage

end
