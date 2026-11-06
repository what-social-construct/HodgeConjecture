module

import HodgeConjecture.Cycles.RationalFiniteChowPushforward
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP107: actual scheme norm/divisor compatibility and finite Chow descent.
Run with `lake env lean research/FiniteNormChowVerification.lean`.

The checks exercise signed orders and preservation of the existing
rational-equivalence relation. The quotient checks deliberately require
neither integral ambient schemes nor dominance, and supply no grading
or principal-relation compatibility hypothesis. The declaration audit
rejects every axiom outside the standard three.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory HodgeConjecture.SchemeCycles

universe u

section SignedDivisor

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
  (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
  (f : X ⟶ Y) [IsFinite f] [IsDominant f]

-- The geometric identity covers denominator contributions, including negative cycles.
example (g : X.functionFieldˣ) :
    finitePushforward ℤ f (principalDivisor X g⁻¹) =
      -principalDivisor Y (functionFieldNorm f g) := by
  rw [finitePushforward_principalDivisor k pY, map_inv, principalDivisor_inv]

end SignedDivisor

section QuotientConsumers

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian Y]
  (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
  (f : X ⟶ Y) [IsFinite f] (n : ℤ)

-- Existing rational equivalence is preserved on actual cycle representatives.
example
    (c d : cyclesOfDegree ℤ (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n)
    (h : RationallyEquivalent (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n c d) :
    RationallyEquivalent (DimensionFunction.ofLocallyOfFiniteType k Y pY) n
      (gradedFinitePushforward ℤ _ _ f
        (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n c)
      (gradedFinitePushforward ℤ _ _ f
        (supportDegree_imageSubscheme_ofLocallyOfFiniteType k pY f) n d) := by
  apply (classMap_eq_iff _ n _ _).mp
  rw [← chowFinitePushforward_classMap, ← chowFinitePushforward_classMap]
  exact congrArg (chowFinitePushforward k pY f n) ((classMap_eq_iff _ n c d).mpr h)

-- The final maps are available for arbitrary Noetherian ambient schemes,
-- including finite maps that are not dominant; every carrier uses its own image.
example :
    ChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n →ₗ[ℤ]
      ChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n :=
  chowFinitePushforward k pY f n

example :
    RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k X (f ≫ pY)) n →ₗ[ℚ]
      RationalChowGroup (DimensionFunction.ofLocallyOfFiniteType k Y pY) n :=
  rationalChowFinitePushforward k pY f n

end QuotientConsumers

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_finite,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_maximalEquiv,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_maximalEquiv_val,
    `HodgeConjecture.CommutativeAlgebra.finite_primesOver,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_localRingEquiv,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_denominators,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_isDomain,
    `HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField.algebra,
    `HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField.scalarTower,
    `HodgeConjecture.CommutativeAlgebra.FiniteLocalizationFractionField.isFractionRing,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_baseAlgebra,
    `HodgeConjecture.CommutativeAlgebra.finiteLocalization_baseScalarTower,
    `HodgeConjecture.CommutativeAlgebra.maximalQuotientResidueEquiv,
    `HodgeConjecture.CommutativeAlgebra.maximalQuotientResidueEquiv_mk,
    `HodgeConjecture.CommutativeAlgebra.residueDegree_eq_quotientDegree,
    `HodgeConjecture.SchemeCycles.finiteAffine_primeIdealOf_comap,
    `HodgeConjecture.SchemeCycles.finiteAffine_primesOverEquivFiber,
    `HodgeConjecture.SchemeCycles.finiteAffineFiberEquiv,
    `HodgeConjecture.SchemeCycles.finiteAffine_fiber_finite,
    `HodgeConjecture.SchemeCycles.finiteAffineFiber_stalkEquiv,
    `HodgeConjecture.SchemeCycles.finiteAffineFiber_stalkKrullDimLE,
    `HodgeConjecture.SchemeCycles.finiteAffineFiber_stalkIsNoetherianRing,
    `HodgeConjecture.SchemeCycles.finiteAffineFiber_localOrder,
    `HodgeConjecture.SchemeCycles.finiteAffineFiber_stalkEquiv_stalkMap,
    `HodgeConjecture.SchemeCycles.finiteAffineFiber_residueDegree,
    `HodgeConjecture.SchemeCycles.divisorOrder_norm_eq_sum_finiteAffine,
    `HodgeConjecture.SchemeCycles.divisorOrder_norm_eq_sum_fiber,
    `HodgeConjecture.SchemeCycles.point_coheight_eq_of_finite_dominant,
    `HodgeConjecture.SchemeCycles.stalkDimension_finite_dominant,
    `HodgeConjecture.SchemeCycles.supportCodimension_finite_dominant,
    `HodgeConjecture.SchemeCycles.divisorPointOfFiniteFiber,
    `HodgeConjecture.SchemeCycles.divisorPointOfFiniteFiber_val,
    `HodgeConjecture.SchemeCycles.finiteLocalization_fractionScalarTower,
    `HodgeConjecture.SchemeCycles.localOrder_norm_eq_sum_finiteLocalization,
    `HodgeConjecture.SchemeCycles.functionFieldNorm,
    `HodgeConjecture.SchemeCycles.functionFieldNorm_eq,
    `HodgeConjecture.SchemeCycles.residueFieldMap_bijective_of_surjectiveOnStalks,
    `HodgeConjecture.SchemeCycles.residueFieldEquivOfSurjectiveOnStalks,
    `HodgeConjecture.SchemeCycles.functionFieldResidueEquiv,
    `HodgeConjecture.SchemeCycles.supportFunctionFieldResidueEquiv,
    `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_residue,
    `HodgeConjecture.SchemeCycles.residueFieldDegree,
    `HodgeConjecture.SchemeCycles.functionField_finrank_eq_residueFieldDegree,
    `HodgeConjecture.SchemeCycles.residueFieldDegree_comp_of_source_surjectiveOnStalks,
    `HodgeConjecture.SchemeCycles.residueFieldDegree_comp_of_target_surjectiveOnStalks,
    `HodgeConjecture.SchemeCycles.finitePushforwardDegree_eq_residueFieldDegree,
    `HodgeConjecture.SchemeCycles.imageSubscheme_eq_pointSupport,
    `HodgeConjecture.SchemeCycles.finiteFiber_finite,
    `HodgeConjecture.SchemeCycles.finitePushforward_apply_pointSupport,
    `HodgeConjecture.SchemeCycles.principalDivisor_apply_point,
    `HodgeConjecture.SchemeCycles.finitePushforward_principalDivisor,
    `HodgeConjecture.SchemeCycles.finitePushforward_closedImmersion_square,
    `HodgeConjecture.SchemeCycles.finiteImageNorm,
    `HodgeConjecture.SchemeCycles.finitePushforward_ambientPrincipalDivisor,
    `HodgeConjecture.SchemeCycles.PrincipalRelationData.finiteImage,
    `HodgeConjecture.SchemeCycles.gradedFinitePushforward_principalRelation,
    `HodgeConjecture.SchemeCycles.principalRelations_le_comap_finitePushforward,
    `HodgeConjecture.SchemeCycles.chowFinitePushforward,
    `HodgeConjecture.SchemeCycles.chowFinitePushforward_classMap,
    `HodgeConjecture.SchemeCycles.rationalPrincipalRelations_le_comap_finitePushforward,
    `HodgeConjecture.SchemeCycles.rationalChowFinitePushforward,
    `HodgeConjecture.SchemeCycles.rationalChowFinitePushforward_classMap,
    `HodgeConjecture.SchemeCycles.rationalChowFinitePushforward_rationalize,
    `HodgeConjecture.SchemeCycles.localOrder_ringEquiv,
    `HodgeConjecture.SchemeCycles.localOrder_algEquiv_of_isLocalization,
    `HodgeConjecture.SchemeCycles.chowFinitePushforward_eq_closedImmersionPushforward]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
