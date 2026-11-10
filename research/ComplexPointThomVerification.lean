module

public import HodgeConjecture.Realization.Betti.Examples.ComplexPointThom
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The actual punctured-plane boundary gives a nonzero local class whose
absolute image in the contractible plane is zero. The original point unit
has that relative image and positive loop pairing one.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HodgeConjecture HodgeConjecture.ComplexPointThom

namespace ComplexPointThomVerification

example : (point : ℂ) = 0 := rfl

example : Subsingleton Point := inferInstance

example : pointCoordinates pointUnit = 1 := pointCoordinates_pointUnit

example : thomClass = connecting
    (SingularCochains.cohomologyPullback (TopCat.ofHom PuncturedComplexCircle.radial) 1
      CircleCohomology.coverGenerator) := thomClass_eq_connecting

example : thomClass = RelativeCochains.connecting puncturedSubcomplex 1
    ((puncturedCohomologyIso 1).inv
      (SingularCochains.cohomologyPullback (TopCat.ofHom PuncturedComplexCircle.radial) 1
        CircleCohomology.coverGenerator)) := thomClass_eq_nativeConnecting

example : IsIso connecting := inferInstance

example : coordinates thomClass = 1 := coordinates_thomClass

example : thomClass ≠ 0 := thomClass_ne_zero

example : boundaryPairing thomClass = 1 := boundaryPairing_thomClass

example : boundaryPairing (-thomClass) = -1 := by
  rw [map_neg, boundaryPairing_thomClass]

example : RelativeCochains.forget puncturedSubcomplex 2 thomClass = 0 := forget_thomClass

example : localGysin pointUnit = thomClass := localGysin_pointUnit

example : Function.Bijective localGysin := localGysin_bijective

example (q : ℚ) : localGysin (q • pointUnit) = q • thomClass := by
  rw [map_smul, localGysin_pointUnit]

example (q : ℚ) : coordinates (rationalGysin q) = q := coordinates_rationalGysin q

example (z : LocalH2) : z = coordinates z • thomClass := eq_smul_thomClass z

example (z : LocalH2) (hz : boundaryPairing z = 1) : z = thomClass := thomClass_unique z hz

example (z : SingularCochains.Cohomology (TopCat.of Point) 0) :
    thomIso z = localGysin z := thomIso_apply z

theorem absolute_forget_eq_zero : RelativeCochains.forget puncturedSubcomplex 2 = 0 :=
  (SingularContractible.isZero_cohomology ℂ 2 (by decide)).eq_of_tgt _ _

end ComplexPointThomVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ComplexPointThom.punctured,
      `HodgeConjecture.ComplexPointThom.puncturedCohomologyIso,
      `HodgeConjecture.ComplexPointThom.nativeConnecting_mono,
      `HodgeConjecture.ComplexPointThom.nativeConnecting_epi,
      `HodgeConjecture.ComplexPointThom.nativeConnecting_isIso,
      `HodgeConjecture.ComplexPointThom.connecting,
      `HodgeConjecture.ComplexPointThom.connecting_isIso,
      `HodgeConjecture.ComplexPointThom.connectingIso,
      `HodgeConjecture.ComplexPointThom.connectingIso_hom,
      `HodgeConjecture.ComplexPointThom.circleIso,
      `HodgeConjecture.ComplexPointThom.circleIso_hom,
      `HodgeConjecture.ComplexPointThom.thomClass,
      `HodgeConjecture.ComplexPointThom.thomClass_eq_connecting,
      `HodgeConjecture.ComplexPointThom.thomClass_eq_nativeConnecting,
      `HodgeConjecture.ComplexPointThom.coordinates,
      `HodgeConjecture.ComplexPointThom.coordinates_circleIso,
      `HodgeConjecture.ComplexPointThom.coordinates_thomClass,
      `HodgeConjecture.ComplexPointThom.thomClass_ne_zero,
      `HodgeConjecture.ComplexPointThom.boundaryPairing,
      `HodgeConjecture.ComplexPointThom.boundaryPairing_eq_coordinates,
      `HodgeConjecture.ComplexPointThom.boundaryPairing_thomClass,
      `HodgeConjecture.ComplexPointThom.thomClass_unique,
      `HodgeConjecture.ComplexPointThom.eq_smul_thomClass,
      `HodgeConjecture.ComplexPointThom.forget_thomClass,
      `HodgeConjecture.ComplexPointThom.rationalGysin,
      `HodgeConjecture.ComplexPointThom.rationalGysin_one,
      `HodgeConjecture.ComplexPointThom.coordinates_rationalGysin,
      `HodgeConjecture.ComplexPointThom.point,
      `HodgeConjecture.ComplexPointThom.point_nonempty,
      `HodgeConjecture.ComplexPointThom.point_subsingleton,
      `HodgeConjecture.ComplexPointThom.pointCoordinates,
      `HodgeConjecture.ComplexPointThom.pointUnit,
      `HodgeConjecture.ComplexPointThom.pointCoordinates_pointUnit,
      `HodgeConjecture.ComplexPointThom.localGysin,
      `HodgeConjecture.ComplexPointThom.localGysin_pointUnit,
      `HodgeConjecture.ComplexPointThom.localGysin_eq_smul,
      `HodgeConjecture.ComplexPointThom.thomIso,
      `HodgeConjecture.ComplexPointThom.thomIso_apply,
      `HodgeConjecture.ComplexPointThom.localGysin_bijective,
      `ComplexPointThomVerification.absolute_forget_eq_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
