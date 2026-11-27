module

public import HodgeConjecture.Realization.Betti.ProjectiveLineSquareRamification
public import HodgeConjecture.Realization.Betti.ProjectiveLineGysinCycleClass
public import HodgeConjecture.Realization.Chow.ProjectiveLineSquareRamification
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

@[expose] public section

/-!
# Original local multiplicity, ramified Gysin pullback and a zero-point aggregate

The original scheme-fiber multiplicity is the coefficient in both the actual
ordinary zero-cycle pullback and the independently constructed relative
Thom/Gysin pullback. The native degree law is obtained from that local proof,
normal-chart/excision naturality and forgetting support. It does not use the
previous global H² square calculation or previous square-cover aggregate.

The same independent Hodge model and full basis are retained. Actual flat
pullback of the original zero class supplies the aggregate column, and
normalized original finite pushforward recovers that same zero class.
The trace remains the existing singleton-supported construction; neither
general branched trace nor a cartesian square of reduced scheme points is
asserted by this ramification comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineRamificationComparison

open AlgebraicGeometry CategoryTheory

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
abbrev zeroClass := ProjectiveLineSquareRamifiedChow.zeroClass

/-- The original local scheme-fiber multiplicity, rather than a new supplied scalar. -/
noncomputable def ramificationIndex : ℕ :=
  SchemeCycles.finiteFiberMultiplicity cover (projectiveLineZero ℂ)

theorem ramificationIndex_eq_two : ramificationIndex = 2 :=
  ProjectiveLineSquareChow.zero_finiteFiberMultiplicity ℂ

theorem ramificationIndex_eq_geometric_rank (x : scheme) :
    ramificationIndex = cover.finrank x := by
  rw [ramificationIndex_eq_two, ProjectiveLineSquare.square_finrank]

theorem zeroClass_eq_original :
    zeroClass = ProjectiveLineGysinCycleClass.rationalZeroClass := rfl

/-- The original zero-point ordinary class retains its actual geometric Gysin normalization. -/
theorem gysin_pointUnit_eq_zeroClass :
    ProjectiveLinePointGysin.gysin ProjectiveLinePointSupport.pointUnit =
      model.cycleClass zeroClass := by
  rw [zeroClass_eq_original]
  exact ProjectiveLineGysinCycleClass.gysin_pointUnit_eq_rationalZeroClass

theorem zeroClass_cycleClass :
    model.cycleClass zeroClass = ProjectiveLineBettiCohomology.coverGenerator :=
  ProjectiveLineBettiCycleClass.cycleClass_pointCycle _ _

/-- The actual reduced point cycle is pulled back with its original local scheme multiplicity. -/
theorem actual_zero_pull :
    sourceComparison (actualPull zeroClass) = (ramificationIndex : ℚ) • zeroClass :=
  ProjectiveLineSquareRamifiedChow.chowEquiv_pull_zero_weighted

/-- The independently computed supported Gysin coefficient is this same original multiplicity. -/
theorem supportedGysin_ramification (z : ProjectiveLinePointGysin.PointH0) :
    ProjectiveLineSquareRamification.supportedPull 2
        (ProjectiveLinePointGysin.supportedGysin z) =
      (ramificationIndex : ℚ) • ProjectiveLinePointGysin.supportedGysin
        (ProjectiveLineSquareRamification.pointPull z) := by
  rw [ramificationIndex_eq_two]
  exact ProjectiveLineSquareRamification.supportedGysin_pullback z

theorem gysin_ramification (z : ProjectiveLinePointGysin.PointH0) :
    SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2
        (ProjectiveLinePointGysin.gysin z) =
      (ramificationIndex : ℚ) • ProjectiveLinePointGysin.gysin
        (ProjectiveLineSquareRamification.pointPull z) := by
  rw [ramificationIndex_eq_two]
  exact ProjectiveLineSquareRamification.gysin_pullback z

/-- The transfer degree is the actual geometric multiplicity in this fully ramified fiber.
Its positive-degree law is supplied by the new local-to-global relative proof. -/
def transfer : RationalDegreeTransfer Betti Betti where
  pull := ProjectiveLineSquareRamification.degreeTransfer.pull
  push := ProjectiveLineSquareRamification.degreeTransfer.push
  degree := ramificationIndex
  degree_ne_zero := by rw [ramificationIndex_eq_two]; decide
  push_comp_pull := by
    rw [ramificationIndex_eq_two]
    exact ProjectiveLineSquareRamification.degreeTransfer.push_comp_pull

theorem degree_eq_geometric_rank (x : scheme) : transfer.degree = cover.finrank x :=
  ramificationIndex_eq_geometric_rank x

def upstairsCycleClass : CoverChow →ₗ[ℚ] Betti :=
  model.cycleClass.comp sourceComparison.toLinearMap

/-- Both original maps still commute; pullback degree is now justified by local ramification. -/
theorem pull_comparison :
    upstairsCycleClass.comp actualPull = transfer.pull.comp model.cycleClass := by
  apply LinearMap.ext
  intro z
  change ProjectiveLineBettiCycleClass.cycleClass (sourceComparison (actualPull z)) =
    SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2
      (ProjectiveLineBettiCycleClass.cycleClass z)
  rw [ProjectiveLineSquareRamification.cohomologyPullback_square]
  change ProjectiveLineCycles.rationalChowDegree ℂ (sourceComparison (actualPull z)) •
      ProjectiveLineBettiCohomology.coverGenerator =
    (2 : ℚ) • (ProjectiveLineCycles.rationalChowDegree ℂ z •
      ProjectiveLineBettiCohomology.coverGenerator)
  rw [ProjectiveLineSquareChow.degree_pull, smul_smul]

theorem push_comparison :
    model.cycleClass.comp actualPush = transfer.push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  dsimp only [LinearMap.comp_apply, transfer, ProjectiveLineSquareRamification.degreeTransfer]
  rw [ProjectiveLineSquareGysin.push_eq_id, LinearMap.id_apply]
  change ProjectiveLineCycles.rationalChowDegree ℂ (actualPush z) •
      ProjectiveLineBettiCohomology.coverGenerator =
    ProjectiveLineCycles.rationalChowDegree ℂ (sourceComparison z) •
      ProjectiveLineBettiCohomology.coverGenerator
  rw [ProjectiveLineSquareChow.degree_push]

def upstairsCycles (_ : Unit) : CoverChow := actualPull zeroClass

theorem target_column (j : Unit) :
    (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [Module.Basis.equivFun_symm_apply]
  cases j
  simpa using ProjectiveLineCoverageCertificate.basis_vector ()

/-- The column proof consumes the actual weighted zero-cycle representative,
as well as the independently proved local-to-global native degree formula. -/
theorem upstairs_columns (j : Unit) :
    upstairsCycleClass (upstairsCycles j) =
      transfer.pull (basis.equivFun.symm (fun i ↦ (1 : Matrix Unit Unit ℚ) i j) : Betti) := by
  rw [target_column]
  change model.cycleClass (sourceComparison (actualPull zeroClass)) =
    SingularCochains.cohomologyPullback ProjectiveLineSquarePullback.pointMap 2
      ProjectiveLineBettiCohomology.coverGenerator
  rw [actual_zero_pull, map_smul, zeroClass_cycleClass,
    ramificationIndex_eq_two, ProjectiveLineSquareRamification.cohomologyPullback_square]
  norm_num

theorem geometric_chow_push_pull (z : BaseChow) :
    actualPush (actualPull z) = (ramificationIndex : ℚ) • z := by
  rw [ramificationIndex_eq_two]
  simpa only [Nat.cast_ofNat, two_smul] using ProjectiveLineSquareChow.push_pull ℂ z

def certificate : FiniteCoverageCertificate.Certificate model basis :=
  FiniteCoverageCertificate.of_degree_transfer model basis upstairsCycleClass transfer
    actualPush push_comparison upstairsCycles 1 ProjectiveLineCoverageCertificate.arithmetic
    upstairs_columns

theorem accepted : FiniteCoverageCertificate.check certificate = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ)
    ProjectiveLineCoverageCertificate.arithmetic = true
  decide +kernel

theorem normalized_cycles (j : Unit) : certificate.cycles j = zeroClass := by
  change (ramificationIndex : ℚ)⁻¹ • actualPush (actualPull zeroClass) = _
  rw [geometric_chow_push_pull, smul_smul, ramificationIndex_eq_two]
  norm_num

theorem model_satisfies_from_ramification : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

end HodgeConjecture.ProjectiveLineRamificationComparison

end
