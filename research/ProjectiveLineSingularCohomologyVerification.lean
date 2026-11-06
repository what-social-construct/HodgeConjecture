module

import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineSingularCohomology
import Lean.Util.CollectAxioms

/-!
The actual original Mayer–Vietoris connecting map is invertible, with no
dimension premise. The circle comparison is the original radial pullback
followed by this exact connecting map. All dependencies are audited.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HodgeConjecture HodgeConjecture.ProjectiveLineComplexPoints
open HodgeConjecture.ProjectiveLineAnalyticCover
open HodgeConjecture.ProjectiveLineSingularCohomology

example : IsZero (ModuleCat.of ℚ
    (SingularCochains.Cohomology (TopCat.of finiteOpen) 1 ×
      SingularCochains.Cohomology (TopCat.of reciprocalOpen) 1)) :=
  isZero_pairCohomology 1 (by decide)

example : SingularMayerVietoris.difference
    (TopCat.of Point) finiteOpen reciprocalOpen 1 = 0 := difference_eq_zero 1 (by decide)

example : SingularMayerVietoris.restriction
    (TopCat.of Point) finiteOpen reciprocalOpen 2 = 0 := restriction_eq_zero 2 (by decide)

example : Mono (SingularMayerVietoris.connecting (TopCat.of Point)
    finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1) :=
  connecting_mono

example : Epi (SingularMayerVietoris.connecting (TopCat.of Point)
    finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1) :=
  connecting_epi

example : IsIso (SingularMayerVietoris.connecting (TopCat.of Point)
    finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1) :=
  connecting_isIso

example : connectingIso.hom = SingularMayerVietoris.connecting (TopCat.of Point)
    finiteOpen reciprocalOpen isOpen_finiteOpen isOpen_reciprocalOpen cover 1 :=
  connectingIso_hom_eq_mayerVietoris

example : circleIso.hom = SingularCochains.cohomologyPullback
    (TopCat.ofHom overlapCircleHomotopyEquiv.toFun) 1 ≫ connecting := circleIso_hom

example : connecting ≫ connectingIso.inv = 𝟙 _ := connectingIso.hom_inv_id

example : circleIso.inv ≫ circleIso.hom = 𝟙 _ := circleIso.inv_hom_id

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.ProjectiveLineSingularCohomology.isZero_pairCohomology,
    `HodgeConjecture.ProjectiveLineSingularCohomology.difference_eq_zero,
    `HodgeConjecture.ProjectiveLineSingularCohomology.restriction_eq_zero,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connecting,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connecting_mono,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connecting_epi,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connecting_isIso,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connectingIso,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connectingIso_hom,
    `HodgeConjecture.ProjectiveLineSingularCohomology.connectingIso_hom_eq_mayerVietoris,
    `HodgeConjecture.ProjectiveLineSingularCohomology.circleIso,
    `HodgeConjecture.ProjectiveLineSingularCohomology.circleIso_hom]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
