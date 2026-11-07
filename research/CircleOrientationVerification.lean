module

public import HodgeConjecture.Realization.Betti.Examples.CircleOrientedPairing
public import Lean.Util.CollectAxioms

@[expose] public section

/-! The original positive circle cycle fixes the computed H¹ generator and sign. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex HodgeConjecture
open CircleOrientedPairing CircleOrientedCycle

namespace CircleOrientationVerification

example : loopPairing CircleCohomology.coverGenerator = 1 := loopPairing_coverGenerator

example : loopPairing (-CircleCohomology.coverGenerator) = -1 := by
  rw [map_neg, loopPairing_coverGenerator]

example (q : ℚ) : loopPairing (q • CircleCohomology.coverGenerator) = q := by
  rw [map_smul, loopPairing_coverGenerator, smul_eq_mul, mul_one]

example (z : SingularCochains.Cohomology space 1) :
    loopPairing z = CircleCohomology.h1Equiv z := loopPairing_eq_coordinate z

example (z : SingularCochains.Cohomology space 1) :
    z = loopPairing z • CircleCohomology.coverGenerator := by
  apply CircleCohomology.h1Equiv.injective
  rw [map_smul, CircleCohomology.h1Equiv_coverGenerator, ← loopPairing_eq_coordinate,
    smul_eq_mul, mul_one]

example : Function.Bijective loopPairing := by
  have he : (loopPairing : SingularCochains.Cohomology space 1 → ℚ) =
      CircleCohomology.h1Equiv := funext loopPairing_eq_coordinate
  rw [he]
  exact CircleCohomology.h1Equiv.bijective

example (z : SingularCochains.Cohomology (TopCat.of CircleTopology.overlap) 0) :
    loopPairing (CircleCohomology.connecting z) =
      CircleCohomology.overlapZeroEquiv z true -
        CircleCohomology.overlapZeroEquiv z false := loopPairing_connecting z

example (φ : SubcomplexCochains.Cochain small.toSSet 1) :
    SingularCyclePairing.evaluation small.toSSet 1 smallCycle φ =
      φ firstSmallSimplex + φ secondSmallSimplex := evaluation_smallCycle φ

example (u : SubcomplexConnectingRepresentative.Cocycle intersection 0) :
    smallLoopPairing
      (SubcomplexCochains.connecting first second 0
        (SubcomplexConnectingRepresentative.cocycleClass intersection 0 u)) =
      u.val (intersectionEndpoint true) - u.val (intersectionEndpoint false) :=
  smallLoopPairing_connecting u

/-- Pairing one rules out an actual native filling chain for the positive loop. -/
theorem positive_cycle_not_boundary :
    ¬ ∃ b : (SingularChainCoordinates.complex singular).X 2,
      (SingularChainCoordinates.complex singular).d 2 1 b = cycle := by
  rintro ⟨b, hb⟩
  obtain ⟨φ, hφ⟩ := SubcomplexConnectingRepresentative.cocycleClass_surjective singular 1
    CircleCohomology.coverGenerator
  have he := SingularCyclePairing.pairing_cocycleClass singular 0 cycle cycle_boundary
    φ.val φ.property
  change loopPairing (SubcomplexConnectingRepresentative.cocycleClass singular 1 φ) =
    SingularCyclePairing.evaluation singular 1 cycle φ.val at he
  rw [hφ, loopPairing_coverGenerator] at he
  have hz := SingularCyclePairing.evaluation_boundary_eq_zero singular 1 b φ.val φ.property
  rw [hb] at hz
  exact zero_ne_one (hz.symm.trans he.symm)

end CircleOrientationVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CircleOrientedPairing.loopPairing,
      `HodgeConjecture.CircleOrientedPairing.smallLoopPairing,
      `HodgeConjecture.CircleOrientedPairing.firstEndpoint,
      `HodgeConjecture.CircleOrientedPairing.secondEndpoint,
      `HodgeConjecture.CircleOrientedPairing.firstContained_face_zero,
      `HodgeConjecture.CircleOrientedPairing.firstContained_face_one,
      `HodgeConjecture.CircleOrientedPairing.secondContained_face_zero,
      `HodgeConjecture.CircleOrientedPairing.secondContained_face_one,
      `HodgeConjecture.CircleOrientedPairing.evaluation_smallCycle,
      `HodgeConjecture.CircleOrientedPairing.smallLoopPairing_connecting,
      `HodgeConjecture.CircleOrientedPairing.overlapToIntersection,
      `HodgeConjecture.CircleOrientedPairing.intersectionIso_hom,
      `HodgeConjecture.CircleOrientedPairing.overlapCoordinate_cocycleClass,
      `HodgeConjecture.CircleOrientedPairing.smallLoopPairing_restriction,
      `HodgeConjecture.CircleOrientedPairing.restriction_connecting,
      `HodgeConjecture.CircleOrientedPairing.loopPairing_connecting,
      `HodgeConjecture.CircleOrientedPairing.loopPairing_eq_coordinate,
      `HodgeConjecture.CircleOrientedPairing.loopPairing_coverGenerator,
      `CircleOrientationVerification.positive_cycle_not_boundary] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
