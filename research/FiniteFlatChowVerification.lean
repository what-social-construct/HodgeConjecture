module

import HodgeConjecture.Realization.Chow.FiniteFlatTransfer
import Mathlib.Algebra.DualNumber
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Enforced kernel-axiom boundary for the actual finite flat Chow transfer,
including the full principal-relation and local multiplicity proof chain. -/

open AlgebraicGeometry CategoryTheory HodgeConjecture.SchemeCycles

noncomputable section

universe u

section NonreducedFiber

variable (k : Type u) [Field k]

local instance : Module.Finite k (DualNumber k) :=
  inferInstanceAs (Module.Finite k (k × k))

local instance : IsScalarTower k (DualNumber k) (DualNumber k) where
  smul_assoc a b c := by
    ext <;> simp [smul_eq_mul, mul_add, mul_assoc]

local instance : IsNoetherianRing (DualNumber k) := IsNoetherianRing.of_finite k _

local instance : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) := by
  rw [IsFinite.SpecMap_iff]
  exact (RingHom.finite_algebraMap).mpr inferInstance

local instance : Flat (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) := by
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff).mpr inferInstance

/-- A square-zero thickening pulls and pushes on the actual rational Chow quotient
with degree two, so the multiplicity has not been reduced to the support's degree one. -/
example (c : RationalChowGroup
    (DimensionFunction.ofLocallyOfFiniteType k (Spec (CommRingCat.of k)) (𝟙 _)) 0) :
    rationalChowFinitePushforward k (𝟙 _)
        (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) 0
      (rationalChowFiniteFlatPullback k (𝟙 _)
        (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))) 0 c) = 2 • c := by
  apply rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq
    k (𝟙 _) _ 0 2 _ c
  intro y
  rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank k (k × k) = 2
  simp

end NonreducedFiber

end

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SchemeCycles.finiteFiberDegree_eq_finrank,
      `HodgeConjecture.SchemeCycles.finitePushforward_finiteFiberPullback_of_finrank_eq,
      `HodgeConjecture.CommutativeAlgebra.length_quotient_map_of_flat,
      `AlgebraicGeometry.natCast_length_quotient_span_eq_sum_minimalPrimes,
      `HodgeConjecture.CommutativeAlgebra.flatLocal_length_difference_eq_sum_minimalPrimes,
      `AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization,
      `HodgeConjecture.SchemeCycles.fiber_stalkMap_ker,
      `HodgeConjecture.SchemeCycles.finiteFiberMultiplicity_eq_length_quotient,
      `HodgeConjecture.SchemeCycles.component_localized_length,
      `HodgeConjecture.SchemeCycles.componentPoint_principal_quotient_length,
      `HodgeConjecture.SchemeCycles.stalkDim_eq_one_of_degree_eq_component_sub_one,
      `HodgeConjecture.SchemeCycles.finiteFlat_localOrder_fraction_eq_minimalPrime_sum,
      `HodgeConjecture.SchemeCycles.finiteFiberMultiplicity_pullback_closed,
      `HodgeConjecture.SchemeCycles.finiteFiberPullback_closedImmersionPushforward,
      `HodgeConjecture.SchemeCycles.flatComponent_principalDivisor_apply_fraction,
      `HodgeConjecture.SchemeCycles.finiteFlat_pullback_principalDivisor_eq_sum_components,
      `HodgeConjecture.SchemeCycles.gradedFiniteFiberPullback_principalRelation_mem,
      `HodgeConjecture.SchemeCycles.principalRelations_le_comap_finiteFlatPullback,
      `HodgeConjecture.SchemeCycles.chowFiniteFlatPullback,
      `HodgeConjecture.SchemeCycles.rationalPrincipalRelations_le_comap_finiteFlatPullback,
      `HodgeConjecture.SchemeCycles.rationalChowFiniteFlatPullback,
      `HodgeConjecture.SchemeCycles.chowFinitePushforward_finiteFlatPullback_of_finrank_eq,
      `HodgeConjecture.SchemeCycles.rationalChowFinitePushforward_finiteFlatPullback_of_finrank_eq,
      `HodgeConjecture.finiteFlatChowTransfer,
      `HodgeConjecture.rationalChowFiniteFlatPullback_injective,
      `HodgeConjecture.finiteFlatChow_normalizedProjector_isIdempotent] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
