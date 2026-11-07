module

public import HodgeConjecture.Realization.Betti.Examples.CircleOrientedCycle
public import Lean.Util.CollectAxioms

@[expose] public section

/-! Literal increasing-angle semicircles and native full/small cycle boundaries. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial HodgeConjecture
open CircleTopology CircleOrientedCycle

namespace CircleOrientedCycleVerification

example (t : unitInterval) : firstPath t = Circle.exp (-Real.pi / 2 + Real.pi * t.val) := rfl

example (t : unitInterval) : secondPath t = Circle.exp (Real.pi / 2 + Real.pi * t.val) :=
  secondPath_angle t

example (t : unitInterval) : firstPath t ∈ firstOpen ∧ secondPath t ∈ secondOpen :=
  ⟨firstPath_mem_first t, secondPath_mem_second t⟩

example : firstPath 0 = (overlapPoint false : Circle) := firstPath.source

example : firstPath 1 = (overlapPoint true : Circle) := firstPath.target

example : secondPath 0 = (overlapPoint true : Circle) := secondPath.source

example : secondPath 1 = (overlapPoint false : Circle) := secondPath.target

example : firstPath ⟨1/2, by norm_num⟩ = 1 := by
  change Circle.exp (-Real.pi / 2 + Real.pi * (1/2)) = 1
  have h : -Real.pi / 2 + Real.pi * (1/2) = 0 := by ring
  rw [h, Circle.exp_zero]

example : secondPath ⟨1/2, by norm_num⟩ = -1 := by
  change -Circle.exp (-Real.pi / 2 + Real.pi * (1/2)) = -1
  have h : -Real.pi / 2 + Real.pi * (1/2) = 0 := by ring
  rw [h, Circle.exp_zero]

example : singular.δ (0 : Fin 2) firstSimplex = endpoint true ∧
    singular.δ (1 : Fin 2) firstSimplex = endpoint false :=
  ⟨firstSimplex_face_zero, firstSimplex_face_one⟩

example : singular.δ (0 : Fin 2) secondSimplex = endpoint false ∧
    singular.δ (1 : Fin 2) secondSimplex = endpoint true :=
  ⟨secondSimplex_face_zero, secondSimplex_face_one⟩

example : SingularChainCoordinates.boundary singular 0 cycleCoordinates = 0 :=
  cycleCoordinates_boundary

example : (SingularChainCoordinates.complex singular).d 1 0 cycle = 0 := cycle_boundary

example : SingularChainCoordinates.boundary small.toSSet 0 smallCycleCoordinates = 0 :=
  smallCycleCoordinates_boundary

example : (SingularChainCoordinates.complex small.toSSet).d 1 0 smallCycle = 0 :=
  smallCycle_boundary

example : (SubcomplexChainCoordinates.inclusion small).f 1 smallCycle = cycle :=
  inclusion_smallCycle

end CircleOrientedCycleVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CircleOrientedCycle.firstAngle,
      `HodgeConjecture.CircleOrientedCycle.firstAngle_mem_arc,
      `HodgeConjecture.CircleOrientedCycle.exp_add_pi,
      `HodgeConjecture.CircleOrientedCycle.neg_exp_negative_half,
      `HodgeConjecture.CircleOrientedCycle.neg_exp_positive_half,
      `HodgeConjecture.CircleOrientedCycle.firstPath,
      `HodgeConjecture.CircleOrientedCycle.secondPath,
      `HodgeConjecture.CircleOrientedCycle.firstPath_mem_first,
      `HodgeConjecture.CircleOrientedCycle.secondPath_mem_second,
      `HodgeConjecture.CircleOrientedCycle.secondPath_angle,
      `HodgeConjecture.CircleOrientedCycle.firstContinuousSimplex,
      `HodgeConjecture.CircleOrientedCycle.secondContinuousSimplex,
      `HodgeConjecture.CircleOrientedCycle.firstSimplex,
      `HodgeConjecture.CircleOrientedCycle.secondSimplex,
      `HodgeConjecture.CircleOrientedCycle.endpoint,
      `HodgeConjecture.CircleOrientedCycle.firstSimplex_face_zero,
      `HodgeConjecture.CircleOrientedCycle.firstSimplex_face_one,
      `HodgeConjecture.CircleOrientedCycle.secondSimplex_face_zero,
      `HodgeConjecture.CircleOrientedCycle.secondSimplex_face_one,
      `HodgeConjecture.CircleOrientedCycle.firstSimplex_mem_first,
      `HodgeConjecture.CircleOrientedCycle.secondSimplex_mem_second,
      `HodgeConjecture.CircleOrientedCycle.cycleCoordinates,
      `HodgeConjecture.CircleOrientedCycle.cycleCoordinates_boundary,
      `HodgeConjecture.CircleOrientedCycle.cycle,
      `HodgeConjecture.CircleOrientedCycle.cycle_boundary,
      `HodgeConjecture.CircleOrientedCycle.firstContainedSimplex,
      `HodgeConjecture.CircleOrientedCycle.secondContainedSimplex,
      `HodgeConjecture.CircleOrientedCycle.intersectionEndpoint,
      `HodgeConjecture.CircleOrientedCycle.smallEndpoint,
      `HodgeConjecture.CircleOrientedCycle.firstSmallSimplex,
      `HodgeConjecture.CircleOrientedCycle.secondSmallSimplex,
      `HodgeConjecture.CircleOrientedCycle.firstSmallSimplex_face_zero,
      `HodgeConjecture.CircleOrientedCycle.firstSmallSimplex_face_one,
      `HodgeConjecture.CircleOrientedCycle.secondSmallSimplex_face_zero,
      `HodgeConjecture.CircleOrientedCycle.secondSmallSimplex_face_one,
      `HodgeConjecture.CircleOrientedCycle.smallCycleCoordinates,
      `HodgeConjecture.CircleOrientedCycle.smallCycle,
      `HodgeConjecture.CircleOrientedCycle.inclusion_smallCycle,
      `HodgeConjecture.CircleOrientedCycle.smallCycle_boundary,
      `HodgeConjecture.CircleOrientedCycle.smallCycleCoordinates_boundary,
      `HodgeConjecture.CircleOrientedCycle.cycle_eq_injections,
      `HodgeConjecture.CircleOrientedCycle.smallCycle_eq_injections] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
