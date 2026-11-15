module

public import HodgeConjecture.Realization.Chow.FilteredTateGraphProjector
public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The tests use the original graph operator and genuine tensor products.
Controls distinguish the Tate cutoff, exclude a class outside a proper
filtration subspace, and instantiate the compatibility on the actual P¹
scheme-filtration target and ordinary Chow model. General Chow construction
and lower-left detection remain explicit in the equivalence theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open HodgeConjecture

namespace TateHodgeGraphVerification

theorem rationalOne_ne_zero : RationalComplexification.embedding ℚ 1 ≠ 0 := by
  intro h
  have h' : (1 : ℚ) = 0 := RationalComplexification.embedding_injective ℚ (by simpa using h)
  exact one_ne_zero h'

/-- Positive and negative Tate indices use the same cohomological convention. -/
theorem correctTateGraph_isHodge (p : ℤ) (α : ℚ) :
    PureRationalHodgeStructure.IsHodgeMorphism
      (PureRationalHodgeStructure.tateBlock p (PureRationalHodgeStructure.tate p))
      (PureRationalHodgeStructure.tateBlock p (PureRationalHodgeStructure.tate p))
      (ClassGraphProjector.operator α) := by
  apply (PureRationalHodgeStructure.graph_isHodge_iff p
    (PureRationalHodgeStructure.tate p) α).mpr
  rw [PureRationalHodgeStructure.rationalHodgeClasses,
    HodgeFiltration.mem_rationalHodgeClasses_iff]
  simp [PureRationalHodgeStructure.tate, HodgeFiltration.tate]

example : PureRationalHodgeStructure.IsHodgeMorphism
    (PureRationalHodgeStructure.tateBlock (-2) (PureRationalHodgeStructure.tate (-2)))
    (PureRationalHodgeStructure.tateBlock (-2) (PureRationalHodgeStructure.tate (-2)))
    (ClassGraphProjector.operator (3 : ℚ)) := correctTateGraph_isHodge (-2) 3

/-- Giving the source line the wrong cutoff changes the graph condition. -/
theorem wrongTateCutoff_notFiltered :
    ¬ HodgeFiltration.IsFilteredMap
      (HodgeFiltration.product (HodgeFiltration.tate 1) (HodgeFiltration.tate 0))
      (HodgeFiltration.product (HodgeFiltration.tate 1) (HodgeFiltration.tate 0))
      (ClassGraphProjector.operator (1 : ℚ)) := by
  rw [HodgeFiltration.graph_isFiltered_iff _ (HodgeFiltration.tate_antitone 0),
    HodgeFiltration.mem_rationalHodgeClasses_iff]
  simpa [HodgeFiltration.tate] using rationalOne_ne_zero

/-- A proper-subspace control; this constant filtration is not claimed to be pure. -/
def properFiltration (_ : ℤ) :
    Submodule ℂ (RationalComplexification.Space (ℚ × ℚ)) :=
  LinearMap.ker (RationalComplexification.map (LinearMap.snd ℚ ℚ ℚ))

theorem properFiltration_antitone : Antitone properFiltration := fun _ _ _ ↦ le_rfl

theorem nonHodgeGraph_notFiltered :
    ¬ HodgeFiltration.IsFilteredMap
      (HodgeFiltration.product (HodgeFiltration.tate 1) properFiltration)
      (HodgeFiltration.product (HodgeFiltration.tate 1) properFiltration)
      (ClassGraphProjector.operator ((0, 1) : ℚ × ℚ)) := by
  rw [HodgeFiltration.graph_isFiltered_iff _ properFiltration_antitone,
    HodgeFiltration.mem_rationalHodgeClasses_iff]
  change ¬ RationalComplexification.map (LinearMap.snd ℚ ℚ ℚ)
    (RationalComplexification.embedding (ℚ × ℚ) (0, 1)) = 0
  rw [RationalComplexification.map_embedding]
  exact rationalOne_ne_zero

/-- Instantiate the proved compatibility on the original geometric P¹ model. -/
theorem projectiveLineCompatibility :
    ClassGraphProjectorHodgeCompatibility ProjectiveLineHodgeCycleClass.model
      (PureRationalHodgeStructure.IsHodgeMorphism
        (PureRationalHodgeStructure.tateBlock 1 ProjectiveLineHodgeComparison.pureHodgeStructure)
        (PureRationalHodgeStructure.tateBlock 1 ProjectiveLineHodgeComparison.pureHodgeStructure)) :=
  PureRationalHodgeStructure.classGraphHodgeCompatibility 1
    ProjectiveLineHodgeComparison.pureHodgeStructure
    ProjectiveLineHodgeCycleClass.model.cycleClass
    ProjectiveLineHodgeCycleClass.model.cycleClass_lands

theorem projectiveLineGraph_isHodge (α : ProjectiveLineBettiComplexification.Betti) :
    PureRationalHodgeStructure.IsHodgeMorphism
      (PureRationalHodgeStructure.tateBlock 1 ProjectiveLineHodgeComparison.pureHodgeStructure)
      (PureRationalHodgeStructure.tateBlock 1 ProjectiveLineHodgeComparison.pureHodgeStructure)
      (ClassGraphProjector.operator α) :=
  (projectiveLineCompatibility.graph_isHodge_iff α).mpr
    (ProjectiveLineHodgeComparison.all_rational_hodge α)

/-- The Hodge predicate also preserves the actual recovered Hodge pieces. -/
example (α : ProjectiveLineBettiComplexification.Betti) (r s : ℤ)
    (z : RationalComplexification.Space (ℚ × ProjectiveLineBettiComplexification.Betti))
    (hz : z ∈ (PureRationalHodgeStructure.tateBlock 1
      ProjectiveLineHodgeComparison.pureHodgeStructure).piece r s) :
    RationalComplexification.map (ClassGraphProjector.operator α) z ∈
      (PureRationalHodgeStructure.tateBlock 1
        ProjectiveLineHodgeComparison.pureHodgeStructure).piece r s :=
  PureRationalHodgeStructure.map_mem_piece (projectiveLineGraph_isHodge α) r s hz

end TateHodgeGraphVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.RationalComplexification.prodEquiv_conjugation,
      `HodgeConjecture.RationalComplexification.conjugate_productSubmodule,
      `HodgeConjecture.RationalComplexification.isCompl_productSubmodule,
      `HodgeConjecture.HodgeFiltration.product,
      `HodgeConjecture.HodgeFiltration.tate,
      `HodgeConjecture.PureRationalHodgeStructure.IsHodgeMorphism,
      `HodgeConjecture.PureRationalHodgeStructure.map_mem_piece,
      `HodgeConjecture.PureRationalHodgeStructure.product,
      `HodgeConjecture.PureRationalHodgeStructure.tate,
      `HodgeConjecture.PureRationalHodgeStructure.tateBlock,
      `HodgeConjecture.HodgeFiltration.prodEquiv_graph_operator,
      `HodgeConjecture.HodgeFiltration.lineMap_isFiltered_iff,
      `HodgeConjecture.HodgeFiltration.graph_isFiltered_iff_lineMap,
      `HodgeConjecture.HodgeFiltration.graph_isFiltered_iff,
      `HodgeConjecture.PureRationalHodgeStructure.lineMap_isHodge_iff,
      `HodgeConjecture.PureRationalHodgeStructure.graph_isHodge_iff,
      `HodgeConjecture.PureRationalHodgeStructure.classGraphHodgeCompatibility,
      `HodgeConjecture.PureRationalHodgeStructure.rationalHodgeConjectureAt_iff_hodgeGraphLifts,
      `TateHodgeGraphVerification.correctTateGraph_isHodge,
      `TateHodgeGraphVerification.wrongTateCutoff_notFiltered,
      `TateHodgeGraphVerification.nonHodgeGraph_notFiltered,
      `TateHodgeGraphVerification.projectiveLineCompatibility,
      `TateHodgeGraphVerification.projectiveLineGraph_isHodge] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
