module

public import HodgeConjecture.Realization.Betti.RelativeMayerVietoris
public import HodgeConjecture.Realization.Betti.Circle
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Strict gluing is checked on original relative cochains. An actual relative
circle class, obtained from the original overlap indicator by local boundary
and inverse excision, forgets to the positive nonzero circle cover generator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory HomologicalComplex HodgeConjecture

namespace RelativeExcisionVerification

example (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (φ : RelativeCochains.Cochain (RelativeUnion.localBoundary A B) n) :
    (RelativeUnion.restriction A B).f n (RelativeUnion.extensionLinear A B n φ) = φ :=
  RelativeUnion.restriction_extension A B n φ

example (S : SSet.{0}) (A B : S.Subcomplex) (n : ℕ)
    (φ : RelativeCochains.Cochain (RelativeUnion.unionBoundary A B) n) :
    RelativeUnion.extensionLinear A B n ((RelativeUnion.restriction A B).f n φ) = φ :=
  RelativeUnion.extension_restriction A B n φ

open CircleTopology

abbrev space : TopCat := TopCat.of Circle
abbrev first : (TopCat.toSSet.obj space).Subcomplex :=
  SingularSubcomplexes.subsetSingular space firstOpen
abbrev second : (TopCat.toSSet.obj space).Subcomplex :=
  SingularSubcomplexes.subsetSingular space secondOpen

def overlapIndicator : SingularCochains.Cohomology (TopCat.of overlap) 0 :=
  CircleCohomology.overlapZeroEquiv.symm (TwoComponentBoundary.step 1)

/-- The class is built from actual local relative boundary and actual inverse excision. -/
def circleRelativeClass : RelativeCochains.Cohomology second 1 :=
  (RelativeExcision.excisionIso space firstOpen secondOpen firstOpen_isOpen
    secondOpen_isOpen opens_cover 1).inv
    (RelativeMayerVietoris.localConnectingActual space firstOpen secondOpen 0 overlapIndicator)

/-- The original positive sign is detected by the existing circle generator. -/
theorem circleRelativeClass_forget :
    RelativeCochains.forget second 1 circleRelativeClass = CircleCohomology.coverGenerator := by
  have h := RelativeMayerVietoris.connecting_excision_forget space firstOpen secondOpen
    firstOpen_isOpen secondOpen_isOpen opens_cover 0
  exact congrArg (fun f => f overlapIndicator) h

theorem circleRelativeClass_ne_zero : circleRelativeClass ≠ 0 := by
  intro h
  have h' := circleRelativeClass_forget
  rw [h, map_zero] at h'
  exact CircleCohomology.coverGenerator_ne_zero h'.symm

end RelativeExcisionVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ShortExactQuasiIso.left,
      `HodgeConjecture.RelativeUnion.restriction,
      `HodgeConjecture.RelativeUnion.difference_pair_zero,
      `HodgeConjecture.RelativeUnion.extensionFunction,
      `HodgeConjecture.RelativeUnion.extensionFunction_restrictions,
      `HodgeConjecture.RelativeUnion.extensionLinear,
      `HodgeConjecture.RelativeUnion.extension_restriction,
      `HodgeConjecture.RelativeUnion.restriction_extension,
      `HodgeConjecture.RelativeUnion.cochainEquiv,
      `HodgeConjecture.RelativeUnion.excisionIso,
      `HodgeConjecture.RelativeUnion.intersectionIso,
      `HodgeConjecture.RelativeUnion.boundaryIso,
      `HodgeConjecture.RelativeExcision.toUnion,
      `HodgeConjecture.RelativeExcision.restriction,
      `HodgeConjecture.RelativeExcision.toUnion_excisionIso,
      `HodgeConjecture.RelativeExcision.quotient_quasiIso,
      `HodgeConjecture.RelativeExcision.toUnion_quasiIso,
      `HodgeConjecture.RelativeExcision.restriction_quasiIso,
      `HodgeConjecture.RelativeExcision.toUnion_forget,
      `HodgeConjecture.RelativeExcision.smallRestriction_quasiIso,
      `HodgeConjecture.RelativeExcision.relativeRestriction_quasiIso,
      `HodgeConjecture.RelativeExcision.smallCohomologyIso,
      `HodgeConjecture.RelativeExcision.excisionIso,
      `HodgeConjecture.RelativeExcision.excisionIso_hom,
      `HodgeConjecture.RelativeExcision.smallCohomologyIso_forget,
      `HodgeConjecture.RelativeMayerVietoris.intersectionCohomologyIso,
      `HodgeConjecture.RelativeMayerVietoris.localConnecting,
      `HodgeConjecture.RelativeMayerVietoris.localToAbsolute,
      `HodgeConjecture.RelativeMayerVietoris.shortComplexMap,
      `HodgeConjecture.RelativeMayerVietoris.connecting_naturality,
      `HodgeConjecture.RelativeMayerVietoris.localConnecting_forget,
      `HodgeConjecture.RelativeMayerVietoris.localConnectingActual,
      `HodgeConjecture.RelativeMayerVietoris.excisionIso_inv_forget_small,
      `HodgeConjecture.RelativeMayerVietoris.connecting_excision_forget,
      `HodgeConjecture.RelativeMayerVietoris.localConnecting_excision_forget,
      `RelativeExcisionVerification.circleRelativeClass,
      `RelativeExcisionVerification.circleRelativeClass_forget,
      `RelativeExcisionVerification.circleRelativeClass_ne_zero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
