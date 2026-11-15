module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Realization.Betti.SingularHomotopy
public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeComparison
public import HodgeConjecture.Realization.HodgeTransport

@[expose] public section

/-!
# The verified P¹ comparison on canonical scheme complex points

The proved identity-on-scheme-sections homeomorphism induces the original
singular pullbacks in every degree. Its rational H² equivalence transports
the existing period comparison and pure Hodge structure to the canonical
scheme Betti target. The actual scheme filtration and 2πi Chern period are
retained. This is the existing computed P¹ case, not a general comparison
or purity theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.ProjectiveLineCanonicalComparison

open AlgebraicGeometry CategoryTheory TensorProduct

/-- Homeomorphism invariance uses the original continuous singular pullbacks. -/
def bettiEquiv (n : ℕ) :
    SingularCochains.Cohomology (TopCat.of ProjectiveLineComplexPoints.Point) n ≃ₗ[ℚ]
      SchemeBetti.Cohomology (projectiveLine ℂ ↘ Spec (.of ℂ)) n :=
  (SingularHomotopy.homeomorphIso ProjectiveLineComplexPoints.canonicalHomeomorph n).toLinearEquiv.symm

/-- The canonical target is the actual singular cohomology of the constructed point space. -/
abbrev Betti := SchemeBetti.Cohomology (projectiveLine ℂ ↘ Spec (.of ℂ)) 2

/-- Scalar extension of the original rational cohomology equivalence. -/
def complexificationEquiv : ProjectiveLineBettiComplexification.Complexification ≃ₗ[ℂ]
    RationalComplexification.Space Betti :=
  LinearEquiv.baseChange ℚ ℂ _ _ (bettiEquiv 2)

@[simp]
theorem complexificationEquiv_tmul (c : ℂ) (α : ProjectiveLineBettiComplexification.Betti) :
    complexificationEquiv (c ⊗ₜ[ℚ] α) = c ⊗ₜ[ℚ] bettiEquiv 2 α := rfl

/-- The same verified period map, now landing in the canonical scheme Betti group. -/
def comparison : ProjectiveLineDeRham.SchemeH2 ℂ ≃ₗ[ℂ] RationalComplexification.Space Betti :=
  ProjectiveLinePeriodComparison.comparison.trans complexificationEquiv

/-- The period-normalized comparison on that same target. -/
def normalizedComparison :
    ProjectiveLineDeRham.SchemeH2 ℂ ≃ₗ[ℂ] RationalComplexification.Space Betti :=
  ProjectiveLinePeriodComparison.normalizedComparison.trans complexificationEquiv

/-- The boundary period remains the original computed Laurent integral. -/
theorem boundaryPeriod_comparison (z : ProjectiveLineDeRham.SchemeH2 ℂ) :
    ProjectiveLineBettiComplexification.complexBoundaryPairing
        (complexificationEquiv.symm (comparison z)) = ProjectiveLinePeriods.schemeIntegral z := by
  rw [comparison, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact ProjectiveLinePeriodComparison.boundaryPeriod_comparison z

theorem comparison_chernCoordinate :
    comparison (ProjectiveLineDeRham.schemeChernCoordinate ℂ) =
      ProjectiveLinePeriodComparison.period ⊗ₜ[ℚ]
        bettiEquiv 2 ProjectiveLineBettiCohomology.coverGenerator := by
  change complexificationEquiv (ProjectiveLinePeriodComparison.comparison _) = _
  rw [ProjectiveLinePeriodComparison.comparison_chernCoordinate, complexificationEquiv_tmul]

/-- The actual scheme degree filtration transported by this constructed comparison. -/
abbrev geometricFiltration := SchemeDeRham.complexPointsHodgeFiltration
  (projectiveLine ℂ ↘ Spec (.of ℂ)) 2 comparison

theorem geometricFiltration_eq_map (p : ℤ) :
    geometricFiltration p =
      (ProjectiveLineHodgeComparison.geometricFiltration p).map complexificationEquiv.toLinearMap := by
  change (_ : Submodule ℂ (ProjectiveLineDeRham.SchemeH2 ℂ)).map
      (complexificationEquiv.toLinearMap.comp
        ProjectiveLinePeriodComparison.comparison.toLinearMap) = _
  exact Submodule.map_comp ProjectiveLinePeriodComparison.comparison.toLinearMap
    complexificationEquiv.toLinearMap _

/-- Purity is transported through the rational equivalence, with canonical conjugation. -/
def pureHodgeStructure : PureRationalHodgeStructure Betti 2 :=
  ProjectiveLineHodgeComparison.pureHodgeStructure.transport (bettiEquiv 2)

theorem pureHodgeStructure_filtration (p : ℤ) :
    pureHodgeStructure.filtration p = geometricFiltration p :=
  (geometricFiltration_eq_map p).symm

/-- The canonical rational target still comes from the actual scheme filtration, independently of cycles. -/
abbrev rationalHodgeClasses := SchemeDeRham.complexPointsRationalHodgeClasses
  (projectiveLine ℂ ↘ Spec (.of ℂ)) 2 comparison 1

theorem rationalHodgeClasses_eq_pureStructure :
    rationalHodgeClasses = PureRationalHodgeStructure.rationalHodgeClasses 1 pureHodgeStructure := by
  change HodgeFiltration.rationalHodgeClasses geometricFiltration 1 =
    HodgeFiltration.rationalHodgeClasses pureHodgeStructure.filtration 1
  congr 1
  funext p
  exact (pureHodgeStructure_filtration p).symm

/-- The scheme-point identification preserves the original independently defined rational target. -/
theorem mem_rationalHodgeClasses (α : Betti) :
    α ∈ rationalHodgeClasses ↔
      (bettiEquiv 2).symm α ∈ ProjectiveLineHodgeComparison.rationalHodgeClasses := by
  rw [rationalHodgeClasses_eq_pureStructure]
  exact PureRationalHodgeStructure.mem_rationalHodgeClasses_transport 1
    ProjectiveLineHodgeComparison.pureHodgeStructure (bettiEquiv 2) α

theorem rationalHodgeClasses_eq_top : rationalHodgeClasses = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro α
  exact (mem_rationalHodgeClasses α).mpr (ProjectiveLineHodgeComparison.all_rational_hodge _)

/-- The original ordinary Chow-to-singular map, followed by the actual homeomorphism pullback. -/
def cycleClass :
    SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0 →ₗ[ℚ] Betti :=
  (bettiEquiv 2).toLinearMap.comp ProjectiveLineBettiCycleClass.cycleClass

theorem normalizedComparison_cycleClass
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    normalizedComparison
      (RestrictScalars.addEquiv ℚ ℂ (ProjectiveLineDeRham.SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
      RationalComplexification.embedding Betti (cycleClass z) := by
  change complexificationEquiv (ProjectiveLinePeriodComparison.normalizedComparison _) = _
  rw [ProjectiveLinePeriodComparison.normalizedComparison_cycleClass]
  rfl

theorem comparison_cycleClass
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    comparison
      (RestrictScalars.addEquiv ℚ ℂ (ProjectiveLineDeRham.SchemeH2 ℂ)
        (ProjectiveLineSchemeCycleClass.cycleClass ℂ z)) =
      ProjectiveLinePeriodComparison.period • RationalComplexification.embedding Betti (cycleClass z) := by
  change complexificationEquiv (ProjectiveLinePeriodComparison.comparison _) = _
  rw [ProjectiveLinePeriodComparison.comparison_cycleClass, map_smul]
  rfl

end HodgeConjecture.ProjectiveLineCanonicalComparison
