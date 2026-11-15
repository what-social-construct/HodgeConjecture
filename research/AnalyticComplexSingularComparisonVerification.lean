module

public import HodgeConjecture.Realization.DeRham.AnalyticComplexSingularComparison
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

/-!
The actual unrestricted complex singular group maps to intrinsic
holomorphic hypercohomology through its native constant-sheaf comparison.
-/

set_option autoImplicit false

open CategoryTheory HodgeConjecture
open scoped Manifold ContDiff

example (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [StronglyLocallyContractibleSpace M] [T2Space M]
    [LocallyCompactSpace M] [SecondCountableTopology M] (n : ℕ) :
    IsIso (AnalyticBettiComparison.complexSingularToHolomorphic E M n) :=
  AnalyticBettiComparison.complexSingularToHolomorphic_isIso E M n

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.AnalyticBettiComparison.complexSingularToHolomorphic,
      `HodgeConjecture.AnalyticBettiComparison.complexSingularToHolomorphic_isIso,
      `HodgeConjecture.AnalyticBettiComparison.complexSingularHolomorphicIso,
      `HodgeConjecture.AnalyticBettiComparison.complexSingularHolomorphicIso_hom,
      `HodgeConjecture.AnalyticBettiComparison.cochainHolomorphicComparison,
      `HodgeConjecture.AnalyticBettiComparison.cochainHolomorphicComparison_isIso] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
