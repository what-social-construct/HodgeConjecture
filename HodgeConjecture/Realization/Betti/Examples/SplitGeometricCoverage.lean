module

public import HodgeConjecture.Realization.Betti.Examples.SplitCoverTransfer
public import HodgeConjecture.Realization.Chow.FiniteCoverCoverage
public import HodgeConjecture.Realization.Chow.FiniteFlatTransfer

@[expose] public section

/-!
# A degree-two geometric cover feeding the exact aggregate

The actual finite étale projection sends four reduced complex points to two.
The upstairs group is the original ordinary rational Chow group, graded by
the actual composite structure map. Pullback and pushforward below are the
original finite Chow maps, not replacements in point coordinates. Their
cycle classes commute with the native singular maps of the same scheme map.

Each upstairs cycle is the geometric flat pullback of an original point class.
The actual geometric rank and the native cohomological degree are both two.
Normalized pushforward recovers the original point classes, binding all
columns of the independently fixed Hodge basis. General-variety comparison
and upstairs generation are not supplied by this zero-dimensional example.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SplitGeometricCoverage

open AlgebraicGeometry CategoryTheory

abbrev BaseIndex := Fin 2
abbrev CoverIndex := Fin 2 × Fin 2
abbrev downstairs := SplitPointGeometry.scheme ℂ BaseIndex
abbrev upstairs := SplitPointGeometry.scheme ℂ CoverIndex
abbrev cover : upstairs ⟶ downstairs := SplitPointGeometry.twoSheetCover ℂ
abbrev baseStructure := SplitPointGeometry.toBase ℂ BaseIndex
abbrev sourceStructure : upstairs ⟶ Spec (.of ℂ) := cover ≫ baseStructure

abbrev BaseChow := SplitZeroCycles.OrdinaryChow ℂ BaseIndex
abbrev CoverChow := SchemeCycles.RationalChowGroup
  (SchemeCycles.DimensionFunction.ofLocallyOfFiniteType ℂ upstairs sourceStructure) 0
abbrev BaseBetti := SplitBetti.Cohomology BaseIndex
abbrev CoverBetti := SplitBetti.Cohomology CoverIndex

abbrev model := SplitOrdinaryBetti.hodgeModel BaseIndex
abbrev basis := SplitOrdinaryBetti.fullHodgeBasis BaseIndex
abbrev transfer := SplitBetti.twoSheetTransfer

/-- The original finite flat Chow pullback of the actual projection. -/
def actualPull : BaseChow →ₗ[ℚ] CoverChow :=
  SchemeCycles.rationalChowFiniteFlatPullback ℂ baseStructure cover 0

/-- The original finite Chow pushforward of the identical projection. -/
def actualPush : CoverChow →ₗ[ℚ] BaseChow :=
  SchemeCycles.rationalChowFinitePushforward ℂ baseStructure cover 0

/-- Ordinary upstairs Chow classes mapped to native singular cohomology. -/
def upstairsCycleClass : CoverChow →ₗ[ℚ] CoverBetti :=
  (SplitOrdinaryBetti.cycleClassOfStructure CoverIndex sourceStructure).toLinearMap

theorem pull_comparison :
    upstairsCycleClass.comp actualPull = transfer.pull.comp model.cycleClass := by
  apply LinearMap.ext
  intro z
  exact SplitOrdinaryBetti.cycleClassOfStructure_finiteFlatPullback baseStructure
    (Prod.fst : CoverIndex → BaseIndex) z

theorem push_comparison :
    model.cycleClass.comp actualPush = transfer.push.comp upstairsCycleClass := by
  apply LinearMap.ext
  intro z
  exact SplitOrdinaryBetti.cycleClassOfStructure_finitePushforward baseStructure
    (Prod.fst : CoverIndex → BaseIndex) z

/-- The degree in the native transfer is the rank of the actual scheme morphism. -/
theorem degree_eq_geometric_rank (x : downstairs) : transfer.degree = cover.finrank x :=
  SplitBetti.projectionTransfer_degree_eq_finrank BaseIndex (Fin 2) x

/-- Actual upstairs cycles are obtained by geometric pullback of reduced points. -/
def upstairsCycles (j : BaseIndex) : CoverChow :=
  actualPull (SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j)

theorem target_column (j : BaseIndex) :
    (basis.equivFun.symm (fun i => (1 : Matrix BaseIndex BaseIndex ℚ) i j) : BaseBetti) =
      (basis j : BaseBetti) := by
  apply congrArg Subtype.val
  apply basis.equivFun.injective
  ext i
  simp [Matrix.one_apply, eq_comm]

/-- The pulled-back point cycles supply every required upstairs basis column. -/
theorem upstairs_columns (j : BaseIndex) :
    upstairsCycleClass (upstairsCycles j) =
      transfer.pull (basis.equivFun.symm (fun i => (1 : Matrix BaseIndex BaseIndex ℚ) i j) :
        BaseBetti) := by
  have h := LinearMap.congr_fun pull_comparison
    (SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j)
  change upstairsCycleClass (upstairsCycles j) =
    transfer.pull (SplitOrdinaryBetti.cycleClass BaseIndex
      (SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j)) at h
  rw [SplitOrdinaryBetti.cycleClass_ordinaryPointClass] at h
  simpa only [target_column] using h

/-- The old geometric Chow degree law is instantiated by the actual rank-two map. -/
theorem geometric_chow_push_pull (z : BaseChow) :
    actualPush (actualPull z) = (2 : ℚ) • z := by
  simpa only [actualPush, actualPull, two_smul] using
    SchemeCycles.rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq
      ℂ baseStructure cover 0 2
      (fun x => SplitPointGeometry.twoSheetCover_finrank ℂ x) z

def arithmetic : ModularRankCertificate.Certificate BaseIndex where
  denominator := 1
  integerMatrix := 1
  modulus := 3
  modularInverse := 1

/-- The aggregate uses the proved geometric comparison and actual upstairs cycles. -/
def certificate : FiniteCoverageCertificate.Certificate model basis :=
  FiniteCoverageCertificate.of_degree_transfer model basis upstairsCycleClass transfer
    actualPush push_comparison upstairsCycles 1 arithmetic upstairs_columns

theorem accepted : FiniteCoverageCertificate.check certificate = true := by
  change ModularRankCertificate.check (1 : Matrix BaseIndex BaseIndex ℚ) arithmetic = true
  decide +kernel

/-- The certificate's cycles are the original ordinary downstairs point classes. -/
theorem normalized_cycles (j : BaseIndex) :
    certificate.cycles j = SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j := by
  change (transfer.degree : ℚ)⁻¹ • actualPush
    (actualPull (SplitZeroCycles.ordinaryPointClass ℂ BaseIndex j)) = _
  rw [SplitBetti.twoSheetTransfer_degree, geometric_chow_push_pull, smul_smul]
  norm_num

theorem model_satisfies_from_geometric_cover : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

end HodgeConjecture.SplitGeometricCoverage

end
