module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeComparison
public import HodgeConjecture.Realization.FilteredHodgeTarget

@[expose] public section

/-!
# The fixed-codimension Hodge-cycle model of the computed projective line

The source is the original rational Chow group of zero-dimensional cycles
on P¹. The target is actual rational singular H². Rational Hodge classes
are defined from the actual derived de Rham filtration through the bounded
period comparison and canonical tensor conjugation. They are independent
of the ordinary cycle map. Its proved surjectivity then discharges the
existing fixed-codimension model's target condition, with an explicit
rational multiple of the original infinity class for every target class.

This specializes the existing model to this computed boundary-period
construction. It does not identify a separately constructed general Gysin
map, assert a new classical Hodge-conjecture case, or quantify over other
varieties or codimensions.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineHodgeCycleClass

open ProjectiveLineBettiComplexification

abbrev Source := SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0

/-- The fixed degree-two model with independently constructed geometric Hodge classes. -/
def model : RationalHodgeCycleClassModel Source Betti :=
  PureRationalHodgeStructure.cycleClassModel 1 ProjectiveLineHodgeComparison.pureHodgeStructure
    ProjectiveLineBettiCycleClass.cycleClass (by
    change LinearMap.range ProjectiveLineBettiCycleClass.cycleClass ≤
      ProjectiveLineHodgeComparison.rationalHodgeClasses
    rw [ProjectiveLineHodgeComparison.rationalHodgeClasses_eq_top]
    exact le_top)

theorem model_hodgeClasses :
    model.hodgeClasses = ProjectiveLineHodgeComparison.rationalHodgeClasses := rfl

theorem model_cycleClass : model.cycleClass = ProjectiveLineBettiCycleClass.cycleClass := rfl

/-- Every target class has its explicit ordinary Chow witness in the original source quotient. -/
theorem infinity_class_witness (z : Betti) :
    model.cycleClass (ProjectiveLineBettiCohomology.h2Equiv z •
      ProjectiveLineBettiCycleClass.rationalInfinityClass) = z := by
  change ProjectiveLineBettiCycleClass.cycleClass _ = z
  rw [map_smul, ProjectiveLineBettiCycleClass.cycleClass_infinity]
  exact (ProjectiveLineBettiCohomology.eq_smul_coverGenerator z).symm

/-- The existing target predicate holds for this constructed fixed-codimension model. -/
theorem model_satisfies_rationalHodgeTarget : RationalHodgeConjectureAt model := by
  intro z _
  exact ⟨ProjectiveLineBettiCohomology.h2Equiv z •
    ProjectiveLineBettiCycleClass.rationalInfinityClass, infinity_class_witness z⟩

theorem model_cycleClass_range_eq_hodgeClasses :
    LinearMap.range model.cycleClass = model.hodgeClasses :=
  (rationalHodgeConjectureAt_iff_range_eq model).mp model_satisfies_rationalHodgeTarget

/-- Ordinary classes have geometric type (1,1) under the original tensor embedding. -/
theorem cycleClass_has_geometric_type_one_one (z : Source) :
    rationalEmbedding (model.cycleClass z) ∈
      ProjectiveLineHodgeComparison.geometricHodgePiece 1 1 :=
  ProjectiveLineHodgeComparison.all_rational_hodge _

end HodgeConjecture.ProjectiveLineHodgeCycleClass
