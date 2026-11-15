module

public import HodgeConjecture.SheafCohomology.DerivedScalarRestrictionNaturality
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Naturality checks for the actual derived postcomposition and flasque
hypercohomology maps used by scalar restriction.
-/

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.BoundedBelowDerived.mapExtendXIso_hom_naturality,
      `HodgeConjecture.BoundedBelowDerived.mapExtendIso_hom_naturality,
      `HodgeConjecture.BoundedBelowDerived.mapExtendIso_inv_naturality,
      `HodgeConjecture.BoundedBelowDerived.rightDerivedPostcomposeIso_hom_naturality,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.globalSections_rightDerivedPostcomposeIso_hom_naturality,
      `HodgeConjecture.SheafHypercohomology.nonnegativeMap_comp,
      `HodgeConjecture.SheafHypercohomology.hypercohomologyMap_comp,
      `HodgeConjecture.SheafHypercohomology.injectiveResolution_nonnegativeMap_naturality,
      `HodgeConjecture.SheafHypercohomology.injectiveResolutionDerivedIso_hom_naturality,
      `HodgeConjecture.SheafHypercohomology.nonnegativeSectionsHomologyIso_hom_naturality,
      `HodgeConjecture.SheafHypercohomology.comparisonFromComplexHomology_naturality,
      `HodgeConjecture.SheafHypercohomology.complexHomologyIsoHypercohomology_hom_naturality,
      `HodgeConjecture.SheafHypercohomology.complexHomologyIsoHypercohomology_inv_naturality,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.restrictedResolutionMap,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.restrictedResolutionMap_naturality,
      `HodgeConjecture.SheafCohomology.ScalarRestriction.restrictedResolutionHypercohomology_naturality] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
