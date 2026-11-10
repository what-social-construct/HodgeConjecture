module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineNormalChartBoundary
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The original finite chart identifies the actual punctured pairs, and its
native relative boundary carries the positively oriented local Thom class.
These checks retain the simplex map and the actual singleton source.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex HodgeConjecture
open HodgeConjecture.ProjectiveLineNormalChart
open HodgeConjecture.ProjectiveLineAnalyticCover

namespace ProjectiveLineNormalChartVerification

example : ComplexPointThom.puncturedSubcomplex =
    localBoundary.preimage finiteSSetIso.hom := punctured_preimage

example (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj (TopCat.of ℂ)).obj n)
    (t : SimplexCategory.toTop.obj n.unop) :
    SingularSubcomplexes.simplexMap space n (finiteSSetIso.hom.app n σ).val t =
      ProjectiveLineComplexPoints.finite
        (SingularSubcomplexes.simplexMap (TopCat.of ℂ) n σ t) :=
  finiteSSetIso_simplexMap n σ t

example (n : ℕ) : (normalClassIso n).inv =
    homologyMap (RelativeCochains.pullback finiteSSetIso.hom punctured_preimage.le) n :=
  normalClassIso_inv n

example : (normalClassIso 2).hom ComplexPointThom.thomClass =
    RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
      overlapOrientationClass := normalClassIso_thomClass

example : SingularCochains.cohomologyPullback
    (TopCat.ofHom puncturedChart) 1 overlapOrientationClass =
      SingularCochains.cohomologyPullback (TopCat.ofHom PuncturedComplexCircle.radial) 1
        CircleCohomology.coverGenerator := overlapOrientationClass_pullback

theorem transported_thomClass_ne_zero :
    (normalClassIso 2).hom ComplexPointThom.thomClass ≠ 0 := by
  intro h
  apply ComplexPointThom.thomClass_ne_zero
  apply (normalClassIso 2).toLinearEquiv.injective
  change (normalClassIso 2).hom ComplexPointThom.thomClass = (normalClassIso 2).hom 0
  simpa only [map_zero] using h

theorem native_localConnecting_ne_zero :
    RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
      overlapOrientationClass ≠ 0 := by
  unfold overlapOrientationClass
  rw [← normalClassIso_thomClass]
  exact transported_thomClass_ne_zero

theorem singleton_unit_transport :
    (normalClassIso 2).hom
        (ComplexPointThom.localGysin ComplexPointThom.pointUnit) =
      RelativeMayerVietoris.localConnectingActual space finiteOpen reciprocalOpen 1
        overlapOrientationClass := by
  rw [ComplexPointThom.localGysin_pointUnit]
  exact normalClassIso_thomClass

theorem transported_orientation_positive :
    ComplexPointThom.boundaryPairing
        ((normalClassIso 2).inv ((normalClassIso 2).hom ComplexPointThom.thomClass)) = 1 := by
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id]
  exact ComplexPointThom.boundaryPairing_thomClass

end ProjectiveLineNormalChartVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineNormalChart.puncturedChart,
      `HodgeConjecture.ProjectiveLineNormalChart.finiteSSetIso,
      `HodgeConjecture.ProjectiveLineNormalChart.finiteSSetIso_simplexMap,
      `HodgeConjecture.ProjectiveLineNormalChart.punctured_preimage,
      `HodgeConjecture.ProjectiveLineNormalChart.puncturedSSetMap,
      `HodgeConjecture.ProjectiveLineNormalChart.normalPullbackIso,
      `HodgeConjecture.ProjectiveLineNormalChart.normalClassIso,
      `HodgeConjecture.ProjectiveLineNormalChart.normalClassIso_inv,
      `HodgeConjecture.ProjectiveLineNormalChart.normalClassIso_hom,
      `HodgeConjecture.ProjectiveLineNormalChart.punctured_map_intersection,
      `HodgeConjecture.ProjectiveLineNormalChart.punctured_cohomology_comparison,
      `HodgeConjecture.ProjectiveLineNormalChart.punctured_cohomology_comparison_inv,
      `HodgeConjecture.ProjectiveLineNormalChart.localConnectingActual_normalClassIso_inv,
      `HodgeConjecture.ProjectiveLineNormalChart.overlap_radial_comp,
      `HodgeConjecture.ProjectiveLineNormalChart.overlapOrientationClass,
      `HodgeConjecture.ProjectiveLineNormalChart.overlapOrientationClass_pullback,
      `HodgeConjecture.ProjectiveLineNormalChart.normalClassIso_thomClass,
      `ProjectiveLineNormalChartVerification.transported_thomClass_ne_zero,
      `ProjectiveLineNormalChartVerification.native_localConnecting_ne_zero,
      `ProjectiveLineNormalChartVerification.singleton_unit_transport,
      `ProjectiveLineNormalChartVerification.transported_orientation_positive] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
