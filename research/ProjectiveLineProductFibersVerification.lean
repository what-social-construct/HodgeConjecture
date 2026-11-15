module

public import HodgeConjecture.Cycles.ProjectiveLineProductChowClasses
public import HodgeConjecture.Cycles.ProjectiveLineProductFiberCodimension
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberClassInputs
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberSupportedClass
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberChowBettiData
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberPairedWitness
public import Lean.Util.CollectAxioms

/-!
Focused axiom audit for the actual codimension-one coordinate-fiber Chow
classes and their supported Betti classes on P¹ × P¹. This checks the
specific geometric construction; it does not assert a general product Chow
cycle-class map or its compatibility with rational equivalence.
-/

@[expose] public section

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineProductChow.dimensionFunction,
      `HodgeConjecture.ProjectiveLineProductChow.firstCarrier_supportDegree_one,
      `HodgeConjecture.ProjectiveLineProductChow.secondCarrier_supportDegree_one,
      `HodgeConjecture.ProjectiveLineProductChow.firstZeroCycle,
      `HodgeConjecture.ProjectiveLineProductChow.secondZeroCycle,
      `HodgeConjecture.ProjectiveLineProductChow.firstZeroChowClass,
      `HodgeConjecture.ProjectiveLineProductChow.secondZeroChowClass,
      `HodgeConjecture.ProjectiveLineProductChow.firstZeroRationalChowClass,
      `HodgeConjecture.ProjectiveLineProductChow.secondZeroRationalChowClass,
      `HodgeConjecture.ProjectiveLineProductFiberCodimension.firstAffineGenericPoint_map,
      `HodgeConjecture.ProjectiveLineProductFiberCodimension.secondAffineGenericPoint_map,
      `HodgeConjecture.ProjectiveLineProductFiberCodimension.firstAffineGenericPoint_height_one,
      `HodgeConjecture.ProjectiveLineProductFiberCodimension.secondAffineGenericPoint_height_one,
      `HodgeConjecture.ProjectiveLineProductFiberCodimension.firstZeroCarrier_codimension_one,
      `HodgeConjecture.ProjectiveLineProductFiberCodimension.secondZeroCarrier_codimension_one,
      `HodgeConjecture.ProjectiveLineProductFiberClassInputs.lineGenerator_eq_zeroCycleClass,
      `HodgeConjecture.ProjectiveLineProductFiberClassInputs.firstClass_eq_pullback_zeroCycleClass,
      `HodgeConjecture.ProjectiveLineProductFiberClassInputs.secondClass_eq_pullback_zeroCycleClass,
      `HodgeConjecture.ProjectiveLineProductFiberClassInputs.firstCarrier_ideal_eq_comap_zeroPoint,
      `HodgeConjecture.ProjectiveLineProductFiberClassInputs.secondCarrier_ideal_eq_comap_zeroPoint,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.firstPunctured_eq_outside_fiber,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.secondPunctured_eq_outside_fiber,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.firstComplement_eq_outside_fiber,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.secondComplement_eq_outside_fiber,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.firstSupportedClass,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.secondSupportedClass,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.forget_firstSupportedClass,
      `HodgeConjecture.ProjectiveLineProductFiberSupportedClass.forget_secondSupportedClass,
      `HodgeConjecture.ProjectiveLineProductFiberChowBettiData.pulledThom,
      `HodgeConjecture.ProjectiveLineProductFiberChowBettiData.firstFiberData,
      `HodgeConjecture.ProjectiveLineProductFiberChowBettiData.secondFiberData,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.firstFiberGysinClass,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.secondFiberGysinClass,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.firstFiberGysinClass_eq_firstClass,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.secondFiberGysinClass_eq_secondClass,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.fiberCycle,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.fiberChowClass,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.fiberChowClass_eq,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.supportedBettiCombination_eq,
      `HodgeConjecture.ProjectiveLineProductFiberPairedWitness.exists_paired_witness] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end
