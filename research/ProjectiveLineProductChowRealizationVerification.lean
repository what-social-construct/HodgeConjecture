module

public import HodgeConjecture.Cycles.ProjectiveLineProductZeroFiberRestriction
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroChartComplex
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriersDistinct
public import HodgeConjecture.Cycles.ProjectiveLineProductGenericDegree
public import HodgeConjecture.Cycles.TopDegreePrincipalRelations
public import HodgeConjecture.Cycles.ProjectiveLineProductFiberChowIndependence
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductChowFiberRealization
public import Lean.Util.CollectAxioms

/-!
Focused axiom audit for the actual rational degree-one Chow group on
`P¹_ℂ × P¹_ℂ` and its ordinary cycle-class realization in rational
singular H². The two zero-fiber classes generate the ordinary Chow
quotient and are independent. The unconditional map sends them to the
proved supported fiber Gysin classes and realizes every product H² class.
-/

@[expose] public section

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SchemeCycles.principalDivisor_mem_principalRelations_of_genericDegree,
      `HodgeConjecture.SchemeCycles.mem_principalRelations_iff_exists_ambientPrincipalDivisor,
      `HodgeConjecture.SchemeCycles.exists_nonzero_multiple_rational_cycle_integral,
      `HodgeConjecture.SchemeCycles.exists_nonzero_multiple_integral_relation,
      `HodgeConjecture.SchemeCycles.rationalRelation_has_ambientPrincipalDivisor_multiple,
      `HodgeConjecture.SchemeCycles.localOrder_atPrime_generator_self,
      `HodgeConjecture.SchemeCycles.localOrder_atPrime_generator_other,
      `HodgeConjecture.SchemeCycles.spec_principalDivisor_primeGenerator,
      `HodgeConjecture.SchemeCycles.spec_fundamentalCycle_eq_principalDivisor,
      `HodgeConjecture.SchemeCycles.spec_principalRelations_one_eq_top,
      `HodgeConjecture.SchemeCycles.spec_rationalChowGroup_one_eq_zero,
      `HodgeConjecture.SchemeCycles.exists_unit_of_all_heightOneOrder_zero,
      `HodgeConjecture.SchemeCycles.spec_exists_unit_of_all_divisorOrder_zero,
      `HodgeConjecture.SchemeCycles.principalDivisor_globalUnit_zero,
      `HodgeConjecture.SchemeCycles.principalDivisor_baseFieldScalar_zero,
      `HodgeConjecture.SchemeCycles.baseFieldScalar_openImmersion,
      `HodgeConjecture.SchemeCycles.exists_scalar_of_affineProduct_unit,
      `HodgeConjecture.SchemeCycles.exists_baseScalar_of_affineProduct_specUnit,
      `HodgeConjecture.ProjectiveLineProductAffineChowVanishing.chart_restricted_rationalChowGroup_one_eq_zero,
      `HodgeConjecture.ProjectiveLineProductAffineChowLocalization.boundary_support_eq_infinity_fibers,
      `HodgeConjecture.ProjectiveLineProductAffineChowLocalization.range_boundaryPushforward_eq_ker_restrict,
      `HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization.boundary_support_eq_zero_fibers,
      `HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization.range_boundaryPushforward_eq_ker_restrict,
      `HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization.boundaryPushforward_surjective_of_affine_zero,
      `HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators.degree_one_boundary_carrier_eq_zero_fiber,
      `HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators.cycle_supported_on_boundary_mem_span,
      `HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators.rationalChowGroup_span_zero_fibers,
      `AlgebraicGeometry.projectiveLineProduct_isReduced,
      `AlgebraicGeometry.denseRange_projectiveLineProductAffineChart,
      `AlgebraicGeometry.projectiveLineProduct_isIntegral,
      `HodgeConjecture.ProjectiveLineProductChow.generic_degree_two,
      `HodgeConjecture.ProjectiveLineProductChow.generic_degree_sub_one_eq_one,
      `HodgeConjecture.ProjectiveLineProductZeroFiberRestriction.firstZeroCycle_restrict_zero,
      `HodgeConjecture.ProjectiveLineProductZeroFiberRestriction.secondZeroCycle_restrict_zero,
      `HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization.chart_complex_eq_productTensorChart_true_true,
      `HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators.firstZeroCarrier_ne_secondZeroCarrier,
      `HodgeConjecture.ProjectiveLineProductFiberChowIndependence.rational_zero_fiber_classes_independent,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberChowSection,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberChowSection_surjective,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberChowSection_injective,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberChowEquiv,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberBettiRealization,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberBettiRealization_first,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberBettiRealization_second,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberBettiRealization_fiberChowClass,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.fiberBettiRealization_surjective,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass_first,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass_second,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass_fiberChowClass,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass_surjective,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowCycleClass_injective,
      `HodgeConjecture.ProjectiveLineProductChowFiberRealization.ordinaryChowBettiEquiv] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"

end
