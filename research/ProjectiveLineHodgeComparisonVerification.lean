module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
These tests use the actual derived degree filtration, original boundary-period
maps, actual rational singular H² and the original ordinary Chow quotient.
The fixed-codimension target is checked only for this computed P¹ model.
An imaginary complex class distinguishes geometric type (1,1) from the
embedded rational lattice; the explicit infinity witness retains the source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory TensorProduct HodgeConjecture
open ProjectiveLineBettiComplexification ProjectiveLineHodgeComparison
open ProjectiveLineHodgeCycleClass

namespace ProjectiveLineHodgeComparisonVerification

example (p : ℤ) :
    (ProjectiveLineDeRham.hodgeFiltration ℂ p).map
      ProjectiveLinePeriodComparison.comparison.toLinearMap =
        ProjectiveLineHodgeStructure.filtration p := comparison_map_hodgeFiltration p

example (p : ℤ) :
    (ProjectiveLineDeRham.hodgeFiltration ℂ p).map
      ProjectiveLinePeriodComparison.normalizedComparison.toLinearMap =
        ProjectiveLineHodgeStructure.filtration p := normalizedComparison_map_hodgeFiltration p

example (p : ℤ) (z : ProjectiveLineDeRham.SchemeH2 ℂ) :
    ProjectiveLinePeriodComparison.comparison z ∈ geometricFiltration p ↔
      z ∈ ProjectiveLineDeRham.hodgeFiltration ℂ p := comparison_mem_geometricFiltration p z

example (p q : ℤ) : geometricHodgePiece p q = ProjectiveLineHodgeStructure.bigrading p q :=
  geometricHodgePiece_eq_bigrading p q

example : geometricHodgePiece 0 2 = ⊥ := geometricHodgePiece_eq_bot 0 2 (by decide)

example : geometricHodgePiece 2 0 = ⊥ := geometricHodgePiece_eq_bot 2 0 (by decide)

example : geometricHodgePiece (-5) 7 = ⊥ := geometricHodgePiece_eq_bot (-5) 7 (by decide)

example (p : ℤ) : IsCompl (geometricFiltration p)
    (ProjectiveLineHodgeStructure.conjugateSubmodule (geometricFiltration (3 - p))) :=
  geometricFiltration_opposed p

example : rationalHodgeClasses = ProjectiveLineHodgeStructure.rationalHodgeClasses :=
  rationalHodgeClasses_eq_candidate

example (z : Betti) : z ∈ rationalHodgeClasses ↔
    rationalEmbedding z ∈ geometricHodgePiece 1 1 := mem_rationalHodgeClasses z

example : Function.Injective rationalEmbedding := rationalEmbedding_injective

/-- A genuine complex class of geometric type (1,1), outside the rational lattice below. -/
def imaginaryTensor : Complexification :=
  Complex.I ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator

theorem imaginaryTensor_has_geometric_type : imaginaryTensor ∈ geometricHodgePiece 1 1 := by
  rw [geometricHodgePiece_one_one]
  trivial

theorem imaginaryTensor_not_rational : imaginaryTensor ∉ Set.range rationalEmbedding := by
  rintro ⟨z, hz⟩
  have hc := congrArg coordinates hz
  simp only [coordinates_rationalEmbedding, imaginaryTensor, coordinates_tmul,
    ProjectiveLineBettiCohomology.h2Equiv_coverGenerator, Rat.cast_one, mul_one] at hc
  have hi := congrArg Complex.im hc
  norm_num at hi

/-- The actual normalized scheme Chern coordinate retains arbitrary complex coefficients. -/
theorem normalizedImaginaryChern :
    ProjectiveLinePeriodComparison.normalizedComparison
      (Complex.I • ProjectiveLineDeRham.schemeChernCoordinate ℂ) = imaginaryTensor := by
  apply coordinates.injective
  change coordinates _ = coordinates (Complex.I ⊗ₜ[ℚ] ProjectiveLineBettiCohomology.coverGenerator)
  rw [ProjectiveLinePeriodComparison.coordinates_normalizedComparison,
    ProjectiveLinePeriods.normalizedSchemeIntegral_eq_residue, map_smul,
    ProjectiveLineDeRham.schemeResidueEquiv_chernCoordinate, coordinates_tmul,
    ProjectiveLineBettiCohomology.h2Equiv_coverGenerator]
  simp

example : ProjectiveLinePeriodComparison.normalizedComparison
    (Complex.I • ProjectiveLineDeRham.schemeChernCoordinate ℂ) ∈ geometricHodgePiece 1 1 := by
  rw [normalizedImaginaryChern]
  exact imaginaryTensor_has_geometric_type

example (z : Betti) :
    model.cycleClass (ProjectiveLineBettiCohomology.h2Equiv z •
      ProjectiveLineBettiCycleClass.rationalInfinityClass) = z := infinity_class_witness z

example : model.cycleClass ProjectiveLineBettiCycleClass.rationalInfinityClass =
    ProjectiveLineBettiCohomology.coverGenerator :=
  ProjectiveLineBettiCycleClass.cycleClass_infinity

example : RationalHodgeConjectureAt model := model_satisfies_rationalHodgeTarget

example : LinearMap.range model.cycleClass = model.hodgeClasses :=
  model_cycleClass_range_eq_hodgeClasses

example (z : Betti) : IsRationalHodgeClass model z ↔
    rationalEmbedding z ∈ geometricHodgePiece 1 1 := Iff.rfl

example (z : Betti) : IsRationalHodgeClass model z →
    ∃ c : Source, model.cycleClass c = z := by
  intro _
  exact ⟨ProjectiveLineBettiCohomology.h2Equiv z •
    ProjectiveLineBettiCycleClass.rationalInfinityClass, infinity_class_witness z⟩

example (z : Source) : rationalEmbedding (model.cycleClass z) ∈ geometricHodgePiece 1 1 :=
  cycleClass_has_geometric_type_one_one z

end ProjectiveLineHodgeComparisonVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineHodgeComparison.comparison_map_hodgeFiltration,
      `HodgeConjecture.ProjectiveLineHodgeComparison.normalizedComparison_map_hodgeFiltration,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricFiltration,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricFiltration_eq,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricFiltration_antitone,
      `HodgeConjecture.ProjectiveLineHodgeComparison.comparison_mem_geometricFiltration,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricFiltration_opposed,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricHodgePiece,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricHodgePiece_eq_bigrading,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricHodgePiece_one_one,
      `HodgeConjecture.ProjectiveLineHodgeComparison.geometricHodgePiece_eq_bot,
      `HodgeConjecture.ProjectiveLineHodgeComparison.rationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineHodgeComparison.mem_rationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineHodgeComparison.rationalHodgeClasses_eq_candidate,
      `HodgeConjecture.ProjectiveLineHodgeComparison.all_rational_hodge,
      `HodgeConjecture.ProjectiveLineHodgeComparison.rationalHodgeClasses_eq_top,
      `HodgeConjecture.ProjectiveLineHodgeComparison.mem_rationalHodgeClasses_geometricFiltration,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.Source,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.model,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.model_hodgeClasses,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.model_cycleClass,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.infinity_class_witness,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.model_satisfies_rationalHodgeTarget,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.model_cycleClass_range_eq_hodgeClasses,
      `HodgeConjecture.ProjectiveLineHodgeCycleClass.cycleClass_has_geometric_type_one_one,
      `ProjectiveLineHodgeComparisonVerification.imaginaryTensor,
      `ProjectiveLineHodgeComparisonVerification.imaginaryTensor_has_geometric_type,
      `ProjectiveLineHodgeComparisonVerification.imaginaryTensor_not_rational,
      `ProjectiveLineHodgeComparisonVerification.normalizedImaginaryChern] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
