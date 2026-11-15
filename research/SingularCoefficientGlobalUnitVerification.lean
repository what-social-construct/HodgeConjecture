module

public import HodgeConjecture.Realization.Betti.SingularCoefficientTensorBridge
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The original ℚ-to-ℂ coefficient map commutes with the actual global
sheafification units, including their original pullbacks to the top open.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HodgeConjecture

example (X : TopCat.{0}) (n : ℕ) :
    (SingularCochains.globalCochainsToSheaf X).f n ≫
        (SheafHypercohomology.globalSections ℚ X).map
          ((SingularCoefficientChange.sheafCoefficientMap X).f n) =
      (SingularCoefficientChange.coefficientMap X).f n ≫
        (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).map
          ((SingularCoefficientChange.globalCochainsToSheaf X).f n) :=
  SingularCoefficientChange.globalUnit_coefficient X n

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularCoefficientChange.coefficientMap,
      `HodgeConjecture.SingularCoefficientChange.coefficientMap_eq_one_tmul,
      `HodgeConjecture.SingularCoefficientChange.coefficientMap_naturality,
      `HodgeConjecture.SingularCoefficientChange.presheafCoefficientMap,
      `HodgeConjecture.SingularCoefficientChange.presheafComplexCoefficientMap,
      `HodgeConjecture.SingularCoefficientChange.constantPresheafMap_coefficient,
      `HodgeConjecture.SingularCoefficientChange.sheafCoefficientMap,
      `HodgeConjecture.SingularCoefficientChange.augmentation_coefficient,
      `HodgeConjecture.SingularCoefficientChange.comparison_coefficient,
      `HodgeConjecture.SingularCoefficientChange.globalUnit_coefficient,
      `HodgeConjecture.SingularCoefficientChange.globalUnit_coefficient_complex,
      `HodgeConjecture.SingularCoefficientChange.globalUnit_coefficient_homology,
      `HodgeConjecture.SingularCoefficientChange.restrictedComplexHomologyIso,
      `HodgeConjecture.SingularCoefficientChange.coefficientCohomologyMap,
      `HodgeConjecture.SingularCoefficientChange.tensorUnit,
      `HodgeConjecture.SingularCoefficientChange.tensorUnitComplexMap,
      `HodgeConjecture.SingularCoefficientChange.coefficientMap_factor] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
