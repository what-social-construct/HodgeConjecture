module

public import HodgeConjecture.Realization.Betti.ProjectiveLineCoverHarmonicComparison
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCanonicalComparison

@[expose] public section

/-!
# Actual P¹ Hodge filtration on the finite cover quotient

The rational cover quotient computes canonical scheme-point Betti H² through
the two original connecting maps. Its Hodge filtration is transported from
the existing actual scheme degree filtration and period comparison, using
the native rational complexification and conjugation. The finite Chow map
is the actual ordinary Chow degree followed by the component-step quotient;
its Betti comparison is proved to be the original ordinary cycle map.

This is a bounded P¹ comparison. It does not construct finite covers or
intrinsic analytic harmonic operators on arbitrary varieties.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineCoverHodgeComparison

open CircleCoverHarmonicComparison ProjectiveLineCoverHarmonicComparison

abbrev FiniteCoverCohomology := (Bool → ℚ) ⧸ LinearMap.range rationalCoboundary

/-- The actual geometric filtration transported through the proved cover comparison. -/
def pureHodgeStructure : PureRationalHodgeStructure FiniteCoverCohomology 2 :=
  ProjectiveLineCanonicalComparison.pureHodgeStructure.transport quotientBettiEquiv.symm

theorem filtration_eq_geometric_transport (p : ℤ) :
    pureHodgeStructure.filtration p =
      (ProjectiveLineCanonicalComparison.geometricFiltration p).map
        (LinearEquiv.baseChange ℚ ℂ _ _ quotientBettiEquiv.symm).toLinearMap := by
  change (ProjectiveLineCanonicalComparison.pureHodgeStructure.filtration p).map _ = _
  rw [ProjectiveLineCanonicalComparison.pureHodgeStructure_filtration]

/-- The rational Hodge target is the existing independently defined scheme target. -/
theorem mem_rationalHodgeClasses (x : FiniteCoverCohomology) :
    x ∈ PureRationalHodgeStructure.rationalHodgeClasses 1 pureHodgeStructure ↔
      quotientBettiEquiv x ∈ ProjectiveLineCanonicalComparison.rationalHodgeClasses := by
  rw [ProjectiveLineCanonicalComparison.rationalHodgeClasses_eq_pureStructure]
  exact PureRationalHodgeStructure.mem_rationalHodgeClasses_transport 1
    ProjectiveLineCanonicalComparison.pureHodgeStructure quotientBettiEquiv.symm x

/-- Ordinary Chow degree followed by the original component-step quotient. -/
def finiteCycleClass :
    SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0 →ₗ[ℚ]
      FiniteCoverCohomology :=
  (LinearMap.range rationalCoboundary).mkQ.comp
    (TwoComponentBoundary.step.comp (ProjectiveLineCycles.rationalChowDegree ℂ))

/-- The finite model retains the original ordinary Chow-to-canonical-Betti map. -/
theorem finiteCycleClass_commutes
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    quotientBettiEquiv (finiteCycleClass z) = ProjectiveLineCanonicalComparison.cycleClass z := by
  change quotientBettiEquiv (Submodule.Quotient.mk
    (TwoComponentBoundary.step (ProjectiveLineCycles.rationalChowDegree ℂ z))) = _
  rw [quotientBettiEquiv_step]
  change (ProjectiveLineCycles.rationalChowDegree ℂ z) •
      ProjectiveLineProductBetti.canonicalBettiEquiv ProjectiveLineBettiCohomology.coverGenerator =
    ProjectiveLineProductBetti.canonicalBettiEquiv
      ((ProjectiveLineCycles.rationalChowDegree ℂ z) • ProjectiveLineBettiCohomology.coverGenerator)
  exact (map_smul _ _ _).symm

theorem finiteCycleClass_has_hodge_type
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    finiteCycleClass z ∈ PureRationalHodgeStructure.rationalHodgeClasses 1 pureHodgeStructure := by
  rw [mem_rationalHodgeClasses, ProjectiveLineCanonicalComparison.rationalHodgeClasses_eq_top]
  exact Submodule.mem_top

end HodgeConjecture.ProjectiveLineCoverHodgeComparison

end
