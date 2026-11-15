module

public import HodgeConjecture.Realization.Betti.ComplexSingularConstantSheafCohomology
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

/-!
The derived comparison below uses unrestricted complex-valued functionals on
the original rational singular chains. The flasque and global-unit proofs
are checked on their original maps, with no assumed comparison isomorphism.
-/

set_option autoImplicit false

open CategoryTheory HodgeConjecture

example (X : TopCat.{0}) [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [StronglyLocallyContractibleSpace X] (n : ℕ) :
    IsIso (SingularCoefficientChange.cohomologyToConstantSheafDerived X n) :=
  SingularCoefficientChange.cohomologyToConstantSheafDerived_isIso X n

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ComplexCoverSmallCochains.restriction_coordinates,
      `HodgeConjecture.ComplexCoverSmallCochains.restriction_quasiIso,
      `HodgeConjecture.ComplexCoverSmallCochains.restriction_surjective,
      `HodgeConjecture.ComplexCoverSmallCochains.vanishingComplex_acyclic,
      `HodgeConjecture.SingularCoefficientChange.globalCochainsToSheaf_eq_zero_iff,
      `HodgeConjecture.SingularCoefficientChange.exists_locallyZero_primitive,
      `HodgeConjecture.SingularCoefficientChange.sheafificationKernel_acyclic,
      `HodgeConjecture.SingularCoefficientChange.exists_cochain_locally_eq_of_closed_cover,
      `HodgeConjecture.SingularCoefficientChange.globalCochainsToSheaf_surjective,
      `HodgeConjecture.SingularCoefficientChange.globalCochainsToSheaf_quasiIso,
      `HodgeConjecture.SingularCoefficientChange.cohomologyToHypercohomology,
      `HodgeConjecture.SingularCoefficientChange.cohomologyToHypercohomology_isIso,
      `HodgeConjecture.SingularCoefficientChange.constantResolutionHypercohomologyIso,
      `HodgeConjecture.SingularCoefficientChange.cohomologyToConstantSheafDerived,
      `HodgeConjecture.SingularCoefficientChange.cohomologyToConstantSheafDerived_isIso,
      `HodgeConjecture.SingularCoefficientChange.cohomologyToConstantSheafDerived_resolution] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
