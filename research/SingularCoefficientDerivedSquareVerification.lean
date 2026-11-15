module

public import HodgeConjecture.Realization.Betti.SingularCoefficientDerivedSquare
public import Mathlib.Analysis.Complex.Basic
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory HomologicalComplex HodgeConjecture

namespace SingularCoefficientDerivedSquareVerification

/-- On the complex plane the actual complex singular sheaf complex computes
compatible rational and complex hypercohomology after scalar restriction. -/
def complexPlaneRestrictedHypercohomologyIso (n : ℕ) :=
  SingularCoefficientChange.restrictedHypercohomologyIso (TopCat.of ℂ)
    (SingularCoefficientChange.sheafComplex (TopCat.of ℂ))
    (SingularCoefficientChange.cochainSheaf_isFlasque_of_locallyCompact_secondCountable
      (TopCat.of ℂ)) n

/-- The coefficient square already commutes at original termwise sections. -/
example (X : TopCat.{0}) (n : ℕ) :=
  SingularCoefficientChange.coefficientCohomologyMap_sections X n

end SingularCoefficientDerivedSquareVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularCoefficientChange.injectiveSheaf_isFlasque,
      `HodgeConjecture.SingularCoefficientChange.restrictedSectionsHomologyIso,
      `HodgeConjecture.SingularCoefficientChange.restrictedSectionsHomologyIso_hom_naturality,
      `HodgeConjecture.SingularCoefficientChange.coefficientCohomologyMap_sections,
      `HodgeConjecture.SingularCoefficientChange.restrictedHypercohomologyIso,
      `HodgeConjecture.SingularCoefficientChange.restrictedCohomologyViaInjectiveIso,
      `SingularCoefficientDerivedSquareVerification.complexPlaneRestrictedHypercohomologyIso] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
