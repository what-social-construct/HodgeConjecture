module

import Solution
import Lean.Util.CollectAxioms

/-! Local checks of the existing fixed-ring submission candidate.

Challenge is loaded into a separate environment: its deliberate statement
holes never enter the Solution environment. This diagnostic checks theorem
types and Solution axioms. It does not replace Comparator or NanoDa replay.
-/

open Lean Elab Command

run_cmd do
  let challenge ← liftIO <| importModules #[{ module := `Challenge }] {}
  let solution ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.Palomar.fixedPoints_heightOne_contraction,
      `HodgeConjecture.Palomar.heightOne_fixedRing_unramified_descent] do
    let some expected := challenge.find? declaration
      | throwError "Missing Challenge declaration {declaration}"
    let some actual := solution.find? declaration
      | throwError "Missing Solution declaration {declaration}"
    unless expected.levelParams == actual.levelParams do
      throwError "Universe parameters differ for {declaration}"
    let sameType ← liftTermElabM <| Meta.isDefEq expected.type actual.type
    unless sameType do
      throwError "Challenge/Solution types differ for {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected Solution axiom {name} in {declaration}"
    logInfo m!"PASS local Challenge/Solution type and axiom check: {declaration}; {axioms.toList}"
