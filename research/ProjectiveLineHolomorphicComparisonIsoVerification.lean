module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineHolomorphicComparisonIso
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

/-!
Focused verification of invertibility for the original canonical projective-line
holomorphic Betti comparison in degree two.
-/

open AlgebraicGeometry CategoryTheory HodgeConjecture

example : IsIso (ModuleCat.ofHom
    (Scheme.ComplexPoints.holomorphicBettiComparison
      (x := projectiveLine ℂ ↘ Spec (.of ℂ)) 1 2)) :=
  ProjectiveLineHolomorphicComparisonIso.holomorphicBettiComparison_isIso

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.generator_ne_zero,
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.comparison_embedded_generator_ne_zero,
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.targetCoordinates,
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.scalarComparison_one_ne_zero,
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.comparison_bijective,
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.holomorphicBettiComparison_isIso,
      `HodgeConjecture.ProjectiveLineHolomorphicComparisonIso.comparisonEquiv] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
