module

public import HodgeConjecture.Realization.Betti.SplitDoubleCover
public import HodgeConjecture.Realization.Chow.SplitDoubleCover
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.Chow.FiniteFlatTransfer
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate

@[expose] public section

/-!
# The actual split double cover of P¹ in the exact aggregate

The source is the original scheme coproduct of two projective lines, with
the exact composite structure map through its finite étale fold. The Chow
maps are the original finite pushforward and flat pullback. Transfer on
native singular H² is the sum of restriction to the actual components.

The upstairs cycle map is uniquely specified by the two original P¹ cycle
maps through the independently proved native cohomology decomposition.
The downstairs Hodge model and its complete basis are unchanged. The cycle
used in the aggregate is the actual flat pullback of the infinity class.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineDoubleCoverCoverage

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

abbrev downstairs := projectiveLine ℂ
abbrev upstairs := downstairs ⨿ downstairs
abbrev cover := SplitDoubleCover.fold downstairs
abbrev baseStructure := downstairs ↘ Spec (.of ℂ)
abbrev sourceStructure := SplitDoubleCover.sourceStructure baseStructure

abbrev BaseChow := SplitDoubleCoverChow.BaseChow ℂ baseStructure 0
abbrev CoverChow := SplitDoubleCoverChow.CoverChow ℂ baseStructure 0
abbrev BaseBetti := ProjectiveLineBettiComplexification.Betti
abbrev CoverBetti := SplitDoubleCoverBetti.CoverBetti baseStructure 2

abbrev model := ProjectiveLineCoverageCertificate.model
abbrev basis := ProjectiveLineCoverageCertificate.basis
abbrev baseComparison := ProjectiveLineProductBetti.canonicalBettiEquiv
abbrev chowComparison := SplitDoubleCoverChow.chowEquiv ℂ baseStructure 0
abbrev bettiComparison := SplitDoubleCoverBetti.cohomologyEquiv baseStructure 2

abbrev actualPull := SplitDoubleCoverChow.actualPull ℂ baseStructure 0
abbrev actualPush := SplitDoubleCoverChow.actualPush ℂ baseStructure 0

/-- The original P¹ class map into canonical scheme-valued complex points. -/
def baseCycleClass : BaseChow →ₗ[ℚ] SplitDoubleCoverBetti.BaseBetti baseStructure 2 :=
  baseComparison.toLinearMap.comp model.cycleClass

/-- The unique upstairs class map agreeing with the original maps on both components. -/
def upstairsCycleClass : CoverChow →ₗ[ℚ] CoverBetti :=
  bettiComparison.symm.toLinearMap.comp
    ((baseCycleClass.prodMap baseCycleClass).comp chowComparison.toLinearMap)

theorem upstairsCycleClass_components (z : CoverChow) :
    bettiComparison (upstairsCycleClass z) =
      (baseCycleClass (chowComparison z).1, baseCycleClass (chowComparison z).2) :=
  bettiComparison.apply_symm_apply _

/-- The original component cycle maps determine the upstairs map uniquely. -/
theorem upstairsCycleClass_unique (L : CoverChow →ₗ[ℚ] CoverBetti)
    (h : ∀ z, bettiComparison (L z) =
      (baseCycleClass (chowComparison z).1, baseCycleClass (chowComparison z).2)) :
    L = upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  apply bettiComparison.injective
  exact (h z).trans (upstairsCycleClass_components z).symm

/-- Native singular transfer, transported only through the existing point-model comparison. -/
def transfer : RationalDegreeTransfer CoverBetti BaseBetti where
  pull := (SplitDoubleCoverBetti.actualPull baseStructure 2).comp baseComparison.toLinearMap
  push := baseComparison.symm.toLinearMap.comp
    (SplitDoubleCoverBetti.actualPush baseStructure 2)
  degree := 2
  degree_ne_zero := by decide
  push_comp_pull := by
    apply LinearMap.ext
    intro z
    have h := LinearMap.congr_fun
      (SplitDoubleCoverBetti.degreeTransfer baseStructure 2).push_comp_pull
      (baseComparison z)
    change SplitDoubleCoverBetti.actualPush baseStructure 2
      (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseComparison z)) =
        (2 : ℚ) • baseComparison z at h
    change baseComparison.symm
      (SplitDoubleCoverBetti.actualPush baseStructure 2
        (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseComparison z))) = (2 : ℚ) • z
    rw [h, map_smul, baseComparison.symm_apply_apply]

theorem pull_comparison :
    upstairsCycleClass.comp actualPull = transfer.pull.comp model.cycleClass := by
  apply LinearMap.ext
  intro z
  apply bettiComparison.injective
  change bettiComparison (upstairsCycleClass (actualPull z)) =
    bettiComparison (SplitDoubleCoverBetti.actualPull baseStructure 2 (baseCycleClass z))
  rw [upstairsCycleClass_components, SplitDoubleCoverChow.chowEquiv_pull,
    SplitDoubleCoverBetti.cohomologyEquiv_pull]

theorem push_comparison :
    model.cycleClass.comp actualPush = transfer.push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  apply baseComparison.injective
  change baseCycleClass (actualPush z) =
    baseComparison (baseComparison.symm
      (SplitDoubleCoverBetti.actualPush baseStructure 2 (upstairsCycleClass z)))
  rw [baseComparison.apply_symm_apply, SplitDoubleCoverBetti.actualPush_eq_sum,
    upstairsCycleClass_components, SplitDoubleCoverChow.actualPush_eq_sum, map_add]

theorem degree_eq_geometric_rank (x : downstairs) : transfer.degree = cover.finrank x :=
  (SplitDoubleCover.fold_finrank downstairs x).symm

def upstairsCycles (_ : Unit) : CoverChow :=
  actualPull ProjectiveLineBettiCycleClass.rationalInfinityClass

theorem target_column (j : Unit) :
    (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i j) : BaseBetti) =
      ProjectiveLineBettiCohomology.coverGenerator := by
  rw [Module.Basis.equivFun_symm_apply]
  cases j
  simpa using ProjectiveLineCoverageCertificate.basis_vector ()

theorem upstairs_columns (j : Unit) :
    upstairsCycleClass (upstairsCycles j) =
      transfer.pull (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i j) :
        BaseBetti) := by
  have h := LinearMap.congr_fun pull_comparison
    ProjectiveLineBettiCycleClass.rationalInfinityClass
  change upstairsCycleClass (upstairsCycles j) =
    transfer.pull (model.cycleClass ProjectiveLineBettiCycleClass.rationalInfinityClass) at h
  rw [ProjectiveLineHodgeCycleClass.model_cycleClass,
    ProjectiveLineBettiCycleClass.cycleClass_infinity] at h
  simpa only [target_column] using h

theorem geometric_chow_push_pull (z : BaseChow) :
    actualPush (actualPull z) = (2 : ℚ) • z := by
  simpa only [actualPush, actualPull, SplitDoubleCoverChow.actualPush,
    SplitDoubleCoverChow.actualPull, two_smul] using
    SchemeCycles.rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq
      ℂ baseStructure cover 0 2 (fun x => SplitDoubleCover.fold_finrank downstairs x) z

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

theorem model_satisfies_from_double_cover : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

end HodgeConjecture.ProjectiveLineDoubleCoverCoverage

end
