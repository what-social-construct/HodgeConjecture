import HodgeConjecture
import Solution
import HodgeConjecture.CommutativeAlgebra.SplitFieldQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Release-candidate declaration checks

This file makes the theorem-name inventory in `CLAIM_LEDGER.md` executable.
Run it with:

`lake env lean research/Verification.lean`

It is intentionally outside the library's default import tree.
-/

#check HodgeConjecture.SchemeCorrespondence.identityCompIsom
#check HodgeConjecture.SchemeCorrespondence.compIdentityIsom
#check HodgeConjecture.SchemeCorrespondence.assocIsom
#check HodgeConjecture.SchemeCorrespondence.classMonoid
#check HodgeConjecture.SchemeCorrespondence.finiteEtaleClassSubmonoid
#check HodgeConjecture.SchemeCorrespondence.HasFiniteEtaleLegs.identity
#check HodgeConjecture.SchemeCorrespondence.HasFiniteEtaleLegs.transpose
#check HodgeConjecture.SchemeCorrespondence.HasFiniteEtaleLegs.comp
#check HodgeConjecture.SchemeCorrespondence.freeTransposeRingInvo
#check HodgeConjecture.SchemeCorrespondence.finiteEtaleFreeTransposeRingInvo
#check HodgeConjecture.projectorIdempotenceDefect
#check HodgeConjecture.map_projectorIdempotenceDefect
#check HodgeConjecture.projectorIdempotenceDefect_eq_zero_iff
#check HodgeConjecture.collisionMultiplication_surjective
#check HodgeConjecture.SchemeCorrespondence.FiniteDeckAction.toFiniteEtaleAlgebra
#check HodgeConjecture.SchemeCorrespondence.groupAlgebraCorrespondence_isIdempotent
#check HodgeConjecture.SchemeCorrespondence.CompactifiedDeckGraphComparison
#check HodgeConjecture.SchemeCorrespondence.CompactifiedDeckGraphComparison.compactifiedGroupAlgebraProjector_restricts
#check HodgeConjecture.SchemeCorrespondence.CompactifiedDeckGraphComparison.compactifiedGroupAlgebraProjector_isIdempotent
#check HodgeConjecture.SchemeCorrespondence.CompactifiedDeckGraphComparison.compactifiedGroupAlgebraProjector_defect_eq_zero
#check HodgeConjecture.SchemeCorrespondence.CompactifiedDeckGraphComparison.groupAlgebraProjectorExtension
#check HodgeConjecture.SchemeCorrespondence.CompactifiedDeckGraphComparison.subgroupAveragingProjectorExtension
#check HodgeConjecture.SchemeCorrespondence.GroupAlgebraDiagonalDecomposition.toDiagonalDecompositionLift
#check HodgeConjecture.SchemeCorrespondence.averagingProjector_isIdempotent
#check HodgeConjecture.SchemeCorrespondence.complementaryAveragingProjector_isIdempotent
#check HodgeConjecture.SchemeCorrespondence.heckeElement_eq_of_rel
#check HodgeConjecture.SchemeCorrespondence.doubleCosetOperator
#check HodgeConjecture.SchemeCorrespondence.heckeCorrespondence_isIdempotent
#check HodgeConjecture.SchemeCorrespondence.BoundarySubgroupProjectorExtension.toCompactifiedPUnit
#check HodgeConjecture.SchemeCorrespondence.CompactifiedSubgroupProjectorExtension.toBoundary
#check HodgeConjecture.SchemeCorrespondence.BoundarySubgroupProjectorExtension.toCompactifiedPUnit_toBoundary
#check HodgeConjecture.SchemeCorrespondence.CompactifiedSubgroupProjectorExtension.toBoundary_toCompactifiedPUnit
#check HodgeConjecture.GaloisCollisionDecomposition.classOf_collision_eq_sum_graph
#check HodgeConjecture.GaloisCollisionDecomposition.averagingProjector_realizes_normalizedCollisionClass
#check HodgeConjecture.GaloisCollisionDecomposition.normalizedCollisionClass_isIdempotent
#check HodgeConjecture.separatedEtaleCollisionSchemeDecomposition
#check HodgeConjecture.finiteEtaleCollisionSchemeDecomposition
#check HodgeConjecture.genericSheetSelector_invariant_iff_saturated
#check HodgeConjecture.MarkedSheetProjector.decomposition_conj_multiplication
#check HodgeConjecture.MarkedSheetProjector.selectorDecomposition_conj_multiplication
#check HodgeConjecture.MarkedSheetProjector.selectorToMarked_eq_shear
#check HodgeConjecture.MarkedSheetProjector.shear_conj_diagonalOperator
#check HodgeConjecture.BlockGraphProjector.operator
#check HodgeConjecture.BlockGraphProjector.operator_isIdempotent
#check HodgeConjecture.BlockGraphProjector.operator_eq_shear_diagonal_shear_symm
#check HodgeConjecture.NormalizationInertia.normalClosureFiniteDeckAction
#check HodgeConjecture.CollisionFoundations.NormalClosureData.isGalois
#check HodgeConjecture.NormalizationInertia.normalClosureNormalizationSchemeIso_hom_comp_toBase
#check HodgeConjecture.NormalizationInertia.conjugateNormalClosureEmbeddingOverBase_right_mul
#check HodgeConjecture.NormalizationInertia.conjugateNormalClosureToIntermediateNormalization_right_mul
#check HodgeConjecture.NormalizationInertia.conjugateNormalClosureToIntermediateNormalization_comp_toBase
#check HodgeConjecture.NormalizationInertia.Diagram.ConjugateCenterRealization
#check HodgeConjecture.NormalizationInertia.pulledBackConjugateBoundaryIdeal
#check HodgeConjecture.NormalizationInertia.fixedMovingBoundaryIdeal
#check HodgeConjecture.NormalizationInertia.ConjugateBoundarySeparation
#check HodgeConjecture.NormalizationInertia.Diagram.ConjugateBoundaryData
#check HodgeConjecture.NormalizationInertia.noCodimensionOneRamification_iff_isEmpty
#check HodgeConjecture.NormalizationInertia.Diagram.noCodimensionOneRamification_of_conjugateBoundarySeparation
#check HodgeConjecture.NormalizationInertia.Diagram.forall_inertiaSaturated_of_conjugateBoundarySeparation
#check HodgeConjecture.NormalizationInertia.Diagram.globalSheetSelectorExtension_of_conjugateBoundarySeparation
#check HodgeConjecture.NormalizationInertia.Diagram.compactifiedSubgroupProjectorExtension_nonempty_of_conjugateBoundarySeparation
#check HodgeConjecture.NormalizationInertia.fixedFieldNormalizationEquivFixedRing
#check HodgeConjecture.NormalizationInertia.intermediateNormalizationEquivFixedRing
#check HodgeConjecture.NormalizationInertia.InertiaFixedRingUnramifiedAt
#check HodgeConjecture.NormalizationInertia.fixedRing_isUnramifiedAt_of_inertia_le_localized
#check HodgeConjecture.NormalizationInertia.fixedRing_isUnramifiedAt_of_inertia_le
#check HodgeConjecture.NormalizationInertia.fixedPointsLocalRingHom
#check HodgeConjecture.NormalizationInertia.fixedPointsLocalRingHom_isLocalHom
#check HodgeConjecture.NormalizationInertia.fixedPointsLocalRingHom_injective
#check HodgeConjecture.NormalizationInertia.fixedPoints_hasGoingDown
#check HodgeConjecture.NormalizationInertia.fixedPoints_primeHeight_under_eq_one
#check HodgeConjecture.NormalizationInertia.localizationAtPrime_isDiscreteValuationRing_of_primeHeight_eq_one
#check HodgeConjecture.NormalizationInertia.fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one
#check HodgeConjecture.NormalizationInertia.fixedSubgroupNormalizationRing_localization_isDiscreteValuationRing
#check HodgeConjecture.NormalizationInertia.fixedSubgroupNormalizationRing_isUnramifiedAt_of_inertia_le
#check HodgeConjecture.NormalizationInertia.primeInertiaSubgroup
#check HodgeConjecture.NormalizationInertia.eq_of_under_primeInertiaSubgroup_eq
#check HodgeConjecture.NormalizationInertia.mem_primeInertiaSubgroup_iff
#check HodgeConjecture.NormalizationInertia.mem_primeInertiaSubgroup_of_smul_sub_mem
#check HodgeConjecture.NormalizationInertia.FullInvariantNormalizationRing
#check HodgeConjecture.NormalizationInertia.normalizationPrimeInertiaGroup
#check HodgeConjecture.NormalizationInertia.NormalizationPrimeInertiaFixedRingUnramifiedAt
#check HodgeConjecture.NormalizationInertia.baseEquivFullInvariantNormalizationRing
#check HodgeConjecture.NormalizationInertia.Diagram.valuationInertia_sub_centerPrime
#check HodgeConjecture.NormalizationInertia.Diagram.valuationInertia_le_normalizationPrimeInertiaGroup
#check HodgeConjecture.NormalizationInertia.Diagram.PrimeInertiaComparisonAt
#check HodgeConjecture.NormalizationInertia.Diagram.valuationInertia_eq_normalizationPrimeInertiaGroup
#check HodgeConjecture.NormalizationInertia.Diagram.normalizationPrimeInertia_le_of_valuationInertia_le
#check HodgeConjecture.NormalizationInertia.ValuationLocalizationAt
#check HodgeConjecture.NormalizationInertia.HasValuationLocalizationAt
#check HodgeConjecture.NormalizationInertia.ValuationLocalizationAt.toValuationCenteredAt
#check HodgeConjecture.NormalizationInertia.ValuationLocalizationAt.primeInertia_le_valuationInertia
#check HodgeConjecture.NormalizationInertia.Diagram.hasValuationLocalizationAt_of_isNoetherianRing
#check HodgeConjecture.NormalizationInertia.Diagram.primeInertiaComparisonAt_of_localization
#check HodgeConjecture.NormalizationInertia.Diagram.primeInertiaComparisonAt_of_isNoetherianRing
#check HodgeConjecture.NormalizationInertia.Diagram.valuationInertia_eq_normalizationPrimeInertiaGroup_of_isNoetherianRing
#check HodgeConjecture.NormalizationInertia.Diagram.normalizationPrimeInertia_le_of_valuationInertia_le_of_isNoetherianRing
#check HodgeConjecture.NormalizationInertia.normalizationFixedRing_isUnramifiedAt_of_primeInertia_le
#check HodgeConjecture.NormalizationInertia.Diagram.fixedRing_isUnramifiedAt_of_valuationInertia_le
#check HodgeConjecture.CollisionFoundations.NormalClosureData.collisionToGenericSheets
#check HodgeConjecture.CollisionFoundations.NormalClosureData.collisionToGenericSheets_elem_eq_baseSheetSelector
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorToGenericSheets
#check HodgeConjecture.CollisionFoundations.NormalClosureData.sheetEmbeddingEquiv
#check HodgeConjecture.CollisionFoundations.NormalClosureData.sheetDeltaTensor
#check HodgeConjecture.CollisionFoundations.NormalClosureData.sheetDeltaTensor_maps_to_selector
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorToGenericSheets_surjective
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorToGenericSheets_bijective
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorGenericSheetsEquiv
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureBaseSheetAugmentation
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorDiagonal
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureBaseSheetAugmentation_comp_tensorToGenericSheets
#check HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureBaseSheetAugmentation_comp_tensorGenericSheetsEquiv
#check HodgeConjecture.CollisionFoundations.NormalClosureData.rationalMarkedSheetAlgebra
#check HodgeConjecture.CollisionFoundations.formallyUnramifiedElem_isIdempotent
#check HodgeConjecture.CollisionFoundations.formallyUnramifiedMarkedAugmentedAlgebra
#check HodgeConjecture.MarkedAugmentedAlgebra
#check HodgeConjecture.MarkedAugmentedAlgebra.augmentationIdeal
#check HodgeConjecture.MarkedAugmentedAlgebra.augmentationIdeal_eq_span_one_sub_selector
#check HodgeConjecture.MarkedAugmentedAlgebra.regularAction
#check HodgeConjecture.MarkedAugmentedAlgebra.selectorAlgebraDecomposition
#check HodgeConjecture.MarkedSheetProjector.baseAugmentation
#check HodgeConjecture.MarkedSheetProjector.selectorAlgebraDecomposition
#check HodgeConjecture.normalizedPullPush_isIdempotent
#check HodgeConjecture.RationalDegreeTransfer.normalizedProjector_isIdempotent
#check HodgeConjecture.RationalHodgeCycleClassModel
#check HodgeConjecture.IsRationalHodgeClass
#check HodgeConjecture.IsAlgebraicHodgeClass
#check HodgeConjecture.RationalHodgeConjectureAt
#check HodgeConjecture.rationalHodgeConjectureAt_iff
#check HodgeConjecture.rationalHodgeConjectureAt_iff_range_eq
#check HodgeConjecture.RationalHodgeConjectureForModel
#check HodgeConjecture.RationalHodgeConjecture
#check HodgeConjecture.RationalHodgeConjectureForFamily
#check HodgeConjecture.ClassGraphProjector.operator
#check HodgeConjecture.ClassGraphProjector.operator_isIdempotent
#check HodgeConjecture.ClassGraphProjector.lowerLeftClass_operator
#check HodgeConjecture.ClassGraphProjector.operator_injective
#check HodgeConjecture.ClassGraphProjector.operator_mul_operator
#check HodgeConjecture.ClassGraphProjector.operator_mul_comm_iff
#check HodgeConjecture.ClassGraphProjector.operator_eq_shear_diagonal_shear_symm
#check HodgeConjecture.ClassGraphProjector.reflection_isInvolution
#check HodgeConjecture.ClassGraphProjector.operator_eq_average_reflection
#check HodgeConjecture.MarkedSheetProjector.graphOperator_eq_classGraphProjector
#check HodgeConjecture.MarkedSheetProjector.productRealization_surjective
#check HodgeConjecture.MarkedSheetProjector.productRealization_intertwines_graphOperator
#check HodgeConjecture.MarkedSheetProjector.productRealization_intertwines_selectorMultiplication
#check HodgeConjecture.UniversalIdempotentAlgebra
#check HodgeConjecture.UniversalIdempotentAlgebra.mapOfIdempotent
#check HodgeConjecture.UniversalIdempotentAlgebra.comp_mapOfIdempotent
#check HodgeConjecture.UniversalIdempotentAlgebra.RepresentationMorphism
#check HodgeConjecture.UniversalIdempotentAlgebra.RepresentationMorphism.intertwines_iff_selector
#check HodgeConjecture.AlgebraProjectorExtension.restriction_comp_compactifiedIdempotentMap
#check HodgeConjecture.AlgebraicProjectorLift.realization_idempotentMap_square
#check HodgeConjecture.AlgebraicProjectorLift.ofIdempotentMapSquare
#check HodgeConjecture.AlgebraicProjectorLift.nonempty_iff_exists_idempotentMap_square
#check HodgeConjecture.MarkedSelectorActionComparison.toIdempotentRepresentationMorphism
#check HodgeConjecture.MarkedSelectorActionComparison.action_comp_compactifiedIdempotentMap_eq_classGraph
#check HodgeConjecture.MarkedGaloisSelectorComparison
#check HodgeConjecture.MarkedGaloisSelectorComparison.toIdempotentRepresentationMorphism
#check HodgeConjecture.MarkedGaloisSelectorComparison.palomarTargetSquare
#check HodgeConjecture.MarkedGaloisSelectorComparison.lowerLeftClass_action_eq
#check HodgeConjecture.MarkedGaloisSelectorComparison.realizes
#check HodgeConjecture.MarkedGaloisSelectorComparison.toAlgebraicProjectorLift
#check HodgeConjecture.MarkedGaloisSelectorComparison.isAlgebraicHodgeClass_of_comparison
#check HodgeConjecture.ClassDependentMarkedGaloisSelectorWitness
#check HodgeConjecture.ClassDependentMarkedGaloisSelectorWitness.toAlgebraicProjectorLift
#check HodgeConjecture.ClassDependentMarkedGaloisSelectorCoverage
#check HodgeConjecture.everyHodgeClassHasGraphProjectorLift_of_classDependentMarkedGaloisSelectorCoverage
#check HodgeConjecture.rationalHodgeConjectureAt_of_classDependentMarkedGaloisSelectorCoverage
#check HodgeConjecture.StrongGraphProjectorLiftReplacementByClassDependentMarkedGaloisSelector
#check HodgeConjecture.classDependentMarkedGaloisSelectorCoverage_of_everyHodgeClassHasGraphProjectorLift
#check HodgeConjecture.rationalHodgeConjectureAt_iff_classDependentMarkedGaloisSelectorCoverage
#check HodgeConjecture.ClassGraphProjectorConstruction
#check HodgeConjecture.ClassGraphProjectorDetection
#check HodgeConjecture.ClassGraphProjectorHodgeCompatibility
#check HodgeConjecture.isAlgebraicHodgeClass_iff_graphProjectorLift
#check HodgeConjecture.EveryHodgeClassHasGraphProjectorLift
#check HodgeConjecture.EveryHodgeClassHasPalomarTargetSquare
#check HodgeConjecture.everyHodgeClassHasGraphProjectorLift_iff_palomarTargetSquare
#check HodgeConjecture.rationalHodgeConjectureAt_iff_everyHodgeClassHasPalomarTargetSquare
#check HodgeConjecture.EveryClassGraphHodgeMorphismHasAlgebraicLift
#check HodgeConjecture.rationalHodgeConjectureAt_iff_everyHodgeClassHasGraphProjectorLift
#check HodgeConjecture.rationalHodgeConjectureAt_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
#check HodgeConjecture.rationalHodgeConjectureForModel_iff_everyHodgeClassHasGraphProjectorLift
#check HodgeConjecture.rationalHodgeConjectureForModel_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
#check HodgeConjecture.rationalHodgeConjectureForFamily_iff_everyHodgeClassHasGraphProjectorLift
#check HodgeConjecture.rationalHodgeConjectureForFamily_iff_everyClassGraphHodgeMorphismHasAlgebraicLift
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.isAlgebraicHodgeClass_of_classGraphProjector
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.ClassIndexedFiniteCoverGraphCoverage
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.GraphProjectorLiftFactorizationThroughFixedDeckData
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.everyHodgeClassHasGraphProjectorLift_of_classIndexedFiniteCoverCoverage
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.classIndexedFiniteCoverGraphCoverage_of_everyHodgeClassHasGraphProjectorLift
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.rationalHodgeConjectureAt_iff_classIndexedFiniteCoverGraphCoverage
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.rationalHodgeConjectureAt_of_every_classGraphProjector_for_fixed_extensionData
#check HodgeConjecture.NormalizationInertia.Diagram.baseClass_inertiaSaturated_of_different_not_le
#check HodgeConjecture.baseSheet_projector_extends_iff_different_not_le
#check HodgeConjecture.SchemeCorrespondence.PrescribedChowProjectorLift.nonempty_iff_forall_different_not_le
#check HodgeConjecture.SchemeCorrespondence.exists_prescribed_subgroupAverage_chowProjector_of_different_away
#check HodgeConjecture.AlgebraProjectorClosure
#check HodgeConjecture.AlgebraProjectorClosure.convolutionDefect
#check HodgeConjecture.AlgebraProjectorClosure.restriction_convolutionDefect
#check HodgeConjecture.AlgebraProjectorClosure.convolutionDefect_eq_zero_iff
#check HodgeConjecture.AlgebraProjectorClosure.ZeroDefectWitness
#check HodgeConjecture.AlgebraProjectorClosure.ZeroDefectWitness.closureClass_isIdempotent
#check HodgeConjecture.AlgebraProjectorClosure.toAlgebraProjectorExtension

-- Restriction-free core and the concrete split-point checkpoint.
#check HodgeConjecture.MarkedProjectorActionComparison
#check HodgeConjecture.MarkedProjectorActionComparison.lowerLeftClass_action_eq_generatedClass
#check HodgeConjecture.MarkedProjectorActionComparison.toIdempotentRepresentationMorphism
#check HodgeConjecture.MarkedProjectorActionComparison.action_comp_idempotentMap_eq_classGraph
#check HodgeConjecture.SplitPointGeometry.toBase
#check HodgeConjecture.SplitPointGeometry.pointSpan_comp_self_iso
#check HodgeConjecture.SplitPointGeometry.pointProjector_isIdempotent
#check HodgeConjecture.SplitPointCorrespondence.constantCoordinates_eq_markedDecomposition
#check HodgeConjecture.SplitPointCorrespondence.realization_firstPointProjector
#check HodgeConjecture.SplitPointCorrespondence.markedComparison
#check HodgeConjecture.SplitPointCorrespondence.projectorLift
#check HodgeConjecture.SplitPointCorrespondence.palomarTargetSquare

#print axioms HodgeConjecture.SplitPointGeometry.pointProjector_isIdempotent
#print axioms HodgeConjecture.SplitPointCorrespondence.palomarTargetSquare

-- Actual finite split-span coefficient realization.
#check HodgeConjecture.FiniteSpanMatrix.matrix_pullback
#check HodgeConjecture.FiniteSpanMatrix.matrix_sigma
#check HodgeConjecture.SplitPointGeometry.labelEquivOfIso_respects_map
#check HodgeConjecture.SplitPointGeometry.fiberIso
#check HodgeConjecture.SplitPointGeometry.span_comp_iso
#check HodgeConjecture.SplitPointGeometry.span_sum_iso
#check HodgeConjecture.SplitSpanRealization.matrix_eq_of_isom
#check HodgeConjecture.SplitSpanRealization.classSubmonoid
#check HodgeConjecture.SplitSpanRealization.realization
#check HodgeConjecture.SplitSpanRealization.realization_surjective
#check HodgeConjecture.SplitSpanRealization.realization_empty
#check HodgeConjecture.SplitSpanRealization.realization_sum
#check HodgeConjecture.SplitSpanRealization.toFiniteEtaleFreeAlgebra_sum
#check HodgeConjecture.SplitSpanRealization.toFiniteEtaleFreeAlgebra_injective
#check HodgeConjecture.GeometricSplitPoints.projector_toFiniteEtaleFreeAlgebra
#check HodgeConjecture.GeometricSplitPoints.matrixRealization_projector
#check HodgeConjecture.GeometricSplitPoints.coefficientRealization_projector
#check HodgeConjecture.GeometricSplitPoints.markedComparison
#check HodgeConjecture.GeometricSplitPoints.projectorLift
#check HodgeConjecture.GeometricSplitPoints.palomarTargetSquare

#print axioms HodgeConjecture.SplitPointGeometry.span_comp_iso
#print axioms HodgeConjecture.SplitSpanRealization.realization
#print axioms HodgeConjecture.SplitSpanRealization.realization_surjective
#print axioms HodgeConjecture.GeometricSplitPoints.palomarTargetSquare

-- Exact finite-additivity quotient, with actual scheme point decomposition.
#check HodgeConjecture.SplitPointGeometry.span_pointDecomposition_iso
#check HodgeConjecture.SplitPointGeometry.pointDecomposition_hasFiniteEtaleLegs
#check HodgeConjecture.SplitSpanRealization.decompositionDefect_mem
#check HodgeConjecture.SplitSpanRealization.additiveRelations_eq_ker
#check HodgeConjecture.SplitSpanRealization.quotientRealization_bijective
#check HodgeConjecture.SplitSpanRealization.quotientRealizationEquiv
#check HodgeConjecture.SplitSpanRealization.realization_not_injective
#check HodgeConjecture.SplitSpanRealization.additiveRelations_ne_bot
#check HodgeConjecture.GeometricSplitPoints.additiveCoefficientRealization_comp_classMap
#check HodgeConjecture.GeometricSplitPoints.additivePalomarTargetSquare

#print axioms HodgeConjecture.SplitPointGeometry.span_pointDecomposition_iso
#print axioms HodgeConjecture.SplitSpanRealization.additiveRelations_eq_ker
#print axioms HodgeConjecture.SplitSpanRealization.quotientRealizationEquiv
#print axioms HodgeConjecture.SplitSpanRealization.realization_not_injective
#print axioms HodgeConjecture.GeometricSplitPoints.additivePalomarTargetSquare

-- Degenerate endpoint: the empty identity span becomes zero, as it should.
example (K : Type) [Field K] :
    (1 : HodgeConjecture.SplitSpanRealization.AdditiveQuotient K (Fin 0)) = 0 := by
  apply (HodgeConjecture.SplitSpanRealization.quotientRealizationEquiv K (Fin 0)).injective
  simp only [map_one, map_zero]
  ext i
  exact Fin.elim0 i

-- Actual integral closed-subscheme classification and the no-curves input.
#check HodgeConjecture.SplitPointGeometry.existsUnique_pointIso_of_isIntegral
#check HodgeConjecture.SplitPointGeometry.labelEquivIntegralClosedSubscheme
#check HodgeConjecture.SplitPointGeometry.integralClosedSubscheme_dimension
#check HodgeConjecture.SplitPointGeometry.topologicalKrullDim_eq_zero_of_isClosedImmersion
#check HodgeConjecture.SplitPointGeometry.not_one_le_topologicalKrullDim_of_isClosedImmersion
#check HodgeConjecture.SplitFieldQuotient.existsUnique_prime_eq_ker_eval
#check HodgeConjecture.SplitFieldQuotient.evalQuotientEquiv
#check HodgeConjecture.SplitFieldQuotient.exists_prime_quotient_equiv

#print axioms HodgeConjecture.SplitPointGeometry.existsUnique_pointIso_of_isIntegral
#print axioms HodgeConjecture.SplitPointGeometry.labelEquivIntegralClosedSubscheme
#print axioms HodgeConjecture.SplitPointGeometry.not_one_le_topologicalKrullDim_of_isClosedImmersion
#print axioms HodgeConjecture.SplitFieldQuotient.exists_prime_quotient_equiv

-- No integral closed subscheme exists when the ambient label set is empty.
example (K : Type) [Field K] :
    IsEmpty (HodgeConjecture.SplitPointGeometry.IntegralClosedSubscheme K (Fin 0)) :=
  ⟨fun J ↦ Fin.elim0
    ((HodgeConjecture.SplitPointGeometry.labelEquivIntegralClosedSubscheme K (Fin 0)).symm J)⟩

-- In particular the actual integral-curve indexing type is empty.
example (K : Type) [Field K] (I : Type) [Finite I] :
    IsEmpty {J : HodgeConjecture.SplitPointGeometry.IntegralClosedSubscheme K I //
      topologicalKrullDim J.val.subscheme = 1} := by
  refine ⟨fun J ↦ ?_⟩
  have h := J.property
  rw [HodgeConjecture.SplitPointGeometry.integralClosedSubscheme_dimension] at h
  exact zero_ne_one h

-- Actual zero-cycles, principal-divisor relations, and the Chow quotient.
#check HodgeConjecture.SplitZeroCycles.coordinates
#check HodgeConjecture.SplitZeroCycles.coordinates_pointCycle
#check HodgeConjecture.SplitZeroCycles.rationalize_injective
#check HodgeConjecture.SplitZeroCycles.rationalizationEquiv_tmul
#check HodgeConjecture.SplitZeroCycles.integralCurve_isEmpty
#check HodgeConjecture.SplitZeroCycles.PrincipalDivisorData
#check HodgeConjecture.SplitZeroCycles.principalDivisor_unique
#check HodgeConjecture.SplitZeroCycles.relations_eq_bot
#check HodgeConjecture.SplitZeroCycles.rationallyEquivalent_iff_eq
#check HodgeConjecture.SplitZeroCycles.classMap_bijective
#check HodgeConjecture.SplitZeroCycles.chowCoordinates
#check HodgeConjecture.SplitZeroCycles.chowCoordinates_pointCycle
#check HodgeConjecture.SplitZeroCycles.chowRationalize_injective
#check HodgeConjecture.SplitZeroCycles.chowRationalizationEquiv
#check HodgeConjecture.SplitZeroCycles.chowRationalizationEquiv_tmul_pointCycle

#print axioms HodgeConjecture.SplitZeroCycles.coordinates
#print axioms HodgeConjecture.SplitZeroCycles.principalDivisor_unique
#print axioms HodgeConjecture.SplitZeroCycles.relations_eq_bot
#print axioms HodgeConjecture.SplitZeroCycles.chowCoordinates
#print axioms HodgeConjecture.SplitZeroCycles.chowRationalizationEquiv
#print axioms HodgeConjecture.SplitZeroCycles.chowRationalizationEquiv_tmul_pointCycle

-- The empty split scheme has zero Chow group, including over the integers.
example (K : Type) [Field K] (R : Type) [CommRing R]
    (z : HodgeConjecture.SplitZeroCycles.Chow K (Fin 0) R) : z = 0 := by
  apply (HodgeConjecture.SplitZeroCycles.chowCoordinates K (Fin 0) R).injective
  ext i
  exact Fin.elim0 i

-- An actual reduced point remains a nonzero class; rational equivalence has
-- not collapsed it in the passage from cycles to the Chow quotient.
example (K : Type) [Field K] (I : Type) [Finite I] (i : I) :
    HodgeConjecture.SplitZeroCycles.classMap K I ℤ
      (HodgeConjecture.SplitZeroCycles.pointCycle K I ℤ i) ≠ 0 := by
  classical
  intro h
  have hi := congrArg (fun z ↦ HodgeConjecture.SplitZeroCycles.chowCoordinates K I ℤ z i) h
  simp [HodgeConjecture.SplitZeroCycles.pointCycle] at hi

-- Actual products, scheme-theoretic images/fibers, and conventional multiplicities.
#check HodgeConjecture.SplitPointGeometry.productIso
#check HodgeConjecture.SplitPointGeometry.pointInclusion_productIso
#check HodgeConjecture.SplitPointGeometry.diagonal_productIso
#check HodgeConjecture.SplitPointGeometry.diagonalMap_isOpenImmersion
#check HodgeConjecture.SplitPointGeometry.diagonalMap_isClosedImmersion
#check HodgeConjecture.SplitPointGeometry.pointFiberIso
#check HodgeConjecture.SplitPointGeometry.pointIdealSheaf_comap_mapOfFunction
#check HodgeConjecture.SplitPointGeometry.imageIntegralSubschemeIso
#check HodgeConjecture.SplitPointGeometry.stalkMap_length_of_isOpenImmersion
#check HodgeConjecture.SplitPointGeometry.residueFieldMap_finrank_of_isIso
#check HodgeConjecture.SplitZeroCycles.pullback_pointCycle_eq_fiberCycle
#check HodgeConjecture.SplitZeroCycles.pushforward_single_eq_imageDegree
#check HodgeConjecture.SplitZeroCycles.externalProduct_pointCycle
#check HodgeConjecture.SplitZeroCycles.coordinates_intersection

-- Geometric convolution, its exact additive-span presentation, and Chow action.
#check HodgeConjecture.SplitChowCorrespondence.matrixCoordinates_comp
#check HodgeConjecture.SplitChowCorrespondence.matrixCoordinates_diagonal
#check HodgeConjecture.SplitChowCorrespondence.comp_assoc
#check HodgeConjecture.SplitChowCorrespondence.matrixAlgEquiv
#check HodgeConjecture.SplitChowCorrespondence.mul_eq_comp
#check HodgeConjecture.SplitChowCorrespondence.spanQuotientEquiv
#check HodgeConjecture.SplitChowCorrespondence.spanQuotientEquiv_pointSpanClass
#check HodgeConjecture.SplitChowCorrespondence.spanQuotientEquiv_ofSchemeSpan
#check HodgeConjecture.SplitChowCorrespondence.chowCoordinates_action
#check HodgeConjecture.SplitChowCorrespondence.action_comp
#check HodgeConjecture.SplitChowCorrespondence.diagonal_action

#print axioms HodgeConjecture.SplitPointGeometry.productIso
#print axioms HodgeConjecture.SplitPointGeometry.pointIdealSheaf_comap_mapOfFunction
#print axioms HodgeConjecture.SplitZeroCycles.pullback_pointCycle_eq_fiberCycle
#print axioms HodgeConjecture.SplitZeroCycles.pushforward_single_eq_imageDegree
#print axioms HodgeConjecture.SplitChowCorrespondence.matrixCoordinates_comp
#print axioms HodgeConjecture.SplitChowCorrespondence.matrixAlgEquiv
#print axioms HodgeConjecture.SplitChowCorrespondence.spanQuotientEquiv_ofSchemeSpan
#print axioms HodgeConjecture.SplitChowCorrespondence.chowCoordinates_action

-- The diagonal really is flat, and the composition pushforward really proper.
example (K : Type) [Field K] (I : Type) [Finite I] :
    AlgebraicGeometry.Flat
      (HodgeConjecture.SplitPointGeometry.mapOfFunction K (fun i : I ↦ (i, i))) :=
  inferInstance

example (K : Type) [Field K] (I J L : Type) [Finite I] [Finite J] [Finite L] :
    AlgebraicGeometry.IsProper
      (HodgeConjecture.SplitPointGeometry.mapOfFunction K
        (fun t : I × J × L ↦ (t.1, t.2.2))) := inferInstance

-- Proper cycle degree is evaluated at the generic point of the actual subscheme.
example (K : Type) [Field K] (S I : Type) [Finite S] [Finite I] (f : S → I)
    (W : HodgeConjecture.SplitPointGeometry.IntegralClosedSubscheme K S) :
    letI := W.property
    HodgeConjecture.SplitZeroCycles.imageDegree K f W (genericPoint W.val.subscheme) = 1 := by
  letI := W.property
  exact HodgeConjecture.SplitZeroCycles.imageDegree_eq_one K f W _

-- The empty scheme's convolution algebra has zero diagonal identity.
example (K : Type) [Field K] :
    (1 : HodgeConjecture.SplitChowCorrespondence.EndAlgebra K (Fin 0)) = 0 := by
  apply (HodgeConjecture.SplitChowCorrespondence.matrixAlgEquiv K (Fin 0)).injective
  simp only [map_one, map_zero]
  ext i
  exact Fin.elim0 i

-- Matrix-unit orientation: (0 → 1) after (1 → 0) is the point at 1.
example (K : Type) [Field K] :
    HodgeConjecture.SplitChowCorrespondence.comp K
      (HodgeConjecture.SplitChowCorrespondence.pointCorrespondence K (0 : Fin 2) (1 : Fin 2))
      (HodgeConjecture.SplitChowCorrespondence.pointCorrespondence K (1 : Fin 2) (0 : Fin 2)) =
      HodgeConjecture.SplitChowCorrespondence.pointCorrespondence K (1 : Fin 2) (1 : Fin 2) := by
  apply (HodgeConjecture.SplitChowCorrespondence.matrixCoordinates K (Fin 2) (Fin 2)).injective
  simp [HodgeConjecture.SplitChowCorrespondence.matrixCoordinates_comp]

-- Actual complex points, their topology, and the actual singular zero-kernel.
#check HodgeConjecture.SplitComplexPoints.existsUnique_eq_evalPoint
#check HodgeConjecture.SplitComplexPoints.isEmbedding_evaluation
#check HodgeConjecture.SplitComplexPoints.pointDiscreteTopology
#check HodgeConjecture.SplitComplexPoints.schemeMorphism_toBase
#check HodgeConjecture.SplitComplexPoints.schemeMorphism_map
#check HodgeConjecture.SplitComplexPoints.productHomeomorph_fst
#check HodgeConjecture.SingularDegreeZero.simplexEquivSingularSet_face
#check HodgeConjecture.SingularDegreeZero.cocycles_toSubmodule
#check HodgeConjecture.SingularDegreeZero.equivFunctions
#check HodgeConjecture.SingularDegreeZero.pullback_comp
#check HodgeConjecture.SingularDegreeZero.transfer_projectionFormula
#check HodgeConjecture.SingularDegreeZero.zeroSimplexLiftEquiv
#check HodgeConjecture.SingularDegreeZero.transfer_simplex_eq_sum_lifts

-- The cycle-class map and the geometric cohomological algebra action.
#check HodgeConjecture.SplitBetti.cycleClass
#check HodgeConjecture.SplitBetti.cycleClass_pointCycle
#check HodgeConjecture.SplitBetti.cycleClass_pullback
#check HodgeConjecture.SplitBetti.cycleClass_pushforward
#check HodgeConjecture.SplitBetti.cycleClass_intersection
#check HodgeConjecture.SplitBetti.cycleClass_action
#check HodgeConjecture.SplitBetti.coordinates_action
#check HodgeConjecture.SplitBetti.action_comp
#check HodgeConjecture.SplitBetti.realization
#check HodgeConjecture.SplitBetti.realization_cycleClass
#check HodgeConjecture.SplitBetti.correspondenceAction

#print axioms HodgeConjecture.SplitComplexPoints.existsUnique_eq_evalPoint
#print axioms HodgeConjecture.SplitComplexPoints.pointDiscreteTopology
#print axioms HodgeConjecture.SingularDegreeZero.simplexEquivSingularSet_face
#print axioms HodgeConjecture.SingularDegreeZero.equivFunctions
#print axioms HodgeConjecture.SingularDegreeZero.transfer_simplex_eq_sum_lifts
#print axioms HodgeConjecture.SplitBetti.cycleClass
#print axioms HodgeConjecture.SplitBetti.cycleClass_action
#print axioms HodgeConjecture.SplitBetti.realization
#print axioms HodgeConjecture.SplitBetti.realization_cycleClass

-- The empty affine scheme has no actual complex-algebra points.
example : IsEmpty (HodgeConjecture.SplitComplexPoints.Point (Fin 0)) :=
  ⟨fun p ↦ Fin.elim0 ((HodgeConjecture.SplitComplexPoints.labelEquiv (Fin 0)).symm p)⟩

-- Its unreduced degree-zero singular cohomology is zero.
example (h : HodgeConjecture.SplitBetti.Cohomology (Fin 0)) : h = 0 := by
  apply (HodgeConjecture.SplitBetti.coordinates (Fin 0)).injective
  ext i
  exact Fin.elim0 i

-- Every constructed point class satisfies the actual singular cocycle equation.
example (I : Type) [Finite I] (i : I) :
    HodgeConjecture.SingularDegreeZero.coboundary
      (HodgeConjecture.SplitComplexPoints.Point I)
      (HodgeConjecture.SplitBetti.cycleClass I
        (HodgeConjecture.SplitZeroCycles.classMap ℂ I ℚ
          (HodgeConjecture.SplitZeroCycles.pointCycle ℂ I ℚ i))).val = 0 :=
  (HodgeConjecture.SplitBetti.cycleClass I
    (HodgeConjecture.SplitZeroCycles.classMap ℂ I ℚ
      (HodgeConjecture.SplitZeroCycles.pointCycle ℂ I ℚ i))).property

-- Empty fibers contribute zero to the actual cohomological transfer.
example :
    HodgeConjecture.SplitBetti.coordinates (Fin 2)
      (HodgeConjecture.SplitBetti.pushforward (fun _ : Fin 1 ↦ (0 : Fin 2))
        (1 : HodgeConjecture.SplitBetti.Cohomology (Fin 1))) 1 = 0 := by
  rw [HodgeConjecture.SplitBetti.coordinates_pushforward]
  simp

-- Fiber sizes may vary: the fiber over 1 here has exactly two points.
example :
    HodgeConjecture.SplitBetti.coordinates (Fin 2)
      (HodgeConjecture.SplitBetti.pushforward
        (fun i : Fin 3 ↦ if i = 0 then (0 : Fin 2) else 1)
        (1 : HodgeConjecture.SplitBetti.Cohomology (Fin 3))) 1 = 2 := by
  rw [HodgeConjecture.SplitBetti.coordinates_pushforward]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  norm_num [Fin.sum_univ_three, HodgeConjecture.SplitBetti.coordinates_apply, h20]

-- The point-pair correspondence 1 → 0 carries the class of point 1 to point 0.
example :
    HodgeConjecture.SplitBetti.action
      (HodgeConjecture.SplitChowCorrespondence.pointCorrespondence ℂ (1 : Fin 2) (0 : Fin 2))
      (HodgeConjecture.SplitBetti.cycleClass (Fin 2)
        (HodgeConjecture.SplitZeroCycles.classMap ℂ (Fin 2) ℚ
          (HodgeConjecture.SplitZeroCycles.pointCycle ℂ (Fin 2) ℚ 1))) =
      HodgeConjecture.SplitBetti.cycleClass (Fin 2)
        (HodgeConjecture.SplitZeroCycles.classMap ℂ (Fin 2) ℚ
          (HodgeConjecture.SplitZeroCycles.pointCycle ℂ (Fin 2) ℚ 0)) := by
  apply (HodgeConjecture.SplitBetti.coordinates (Fin 2)).injective
  rw [HodgeConjecture.SplitBetti.coordinates_action,
    HodgeConjecture.SplitBetti.coordinates_cycleClass,
    HodgeConjecture.SplitBetti.coordinates_cycleClass,
    HodgeConjecture.SplitChowCorrespondence.matrixCoordinates_pointCorrespondence]
  ext j
  simp [-HodgeConjecture.SplitZeroCycles.coordinates_apply, Matrix.mulVec,
    dotProduct, Matrix.single, Pi.single_apply, eq_comm]

-- Actual Chow graph blocks and the independent tensor Hodge structure.
#check HodgeConjecture.SplitChowTateBlock.optionSchemeIso
#check HodgeConjecture.SplitChowTateBlock.pointInclusion_optionSchemeIso
#check HodgeConjecture.SplitChowTateBlock.mapSome_optionSchemeIso
#check HodgeConjecture.SplitChowTateBlock.matrix_encode
#check HodgeConjecture.SplitChowTateBlock.decode_encode
#check HodgeConjecture.SplitChowTateBlock.encode_isIdempotent
#check HodgeConjecture.SplitHodgeStructure.complexCoordinates_tmul
#check HodgeConjecture.SplitHodgeStructure.rationalEmbedding_injective
#check HodgeConjecture.SplitHodgeStructure.conjugation_tmul
#check HodgeConjecture.SplitHodgeStructure.bigrading_direct
#check HodgeConjecture.SplitHodgeStructure.conjugation_bigrading
#check HodgeConjecture.SplitHodgeStructure.mem_rationalHodgeClasses
#check HodgeConjecture.SplitHodgeStructure.all_isHodgeMorphism

-- All three generic interfaces now have actual finite split inputs.
#check HodgeConjecture.SplitBettiTateBlock.blockCoordinates_snd
#check HodgeConjecture.SplitBettiTateBlock.realization_encode
#check HodgeConjecture.SplitBettiTateBlock.cycleClass_decode
#check HodgeConjecture.SplitBettiTateBlock.hodgeModel
#check HodgeConjecture.SplitBettiTateBlock.construction
#check HodgeConjecture.SplitBettiTateBlock.detection
#check HodgeConjecture.SplitBettiTateBlock.hodgeCompatibility
#check HodgeConjecture.SplitBettiTateBlock.graphProjectorLift
#check HodgeConjecture.SplitBettiTateBlock.hodgeConjectureAt_iff_hodgeMorphismLift
#check HodgeConjecture.SplitBettiTateBlock.hodgeConjectureAt_iff_palomarTargetSquare
#check HodgeConjecture.SplitBettiTateBlock.everyHodgeClassHasPalomarTargetSquare

#print axioms HodgeConjecture.SplitChowTateBlock.optionSchemeIso
#print axioms HodgeConjecture.SplitChowTateBlock.matrix_encode
#print axioms HodgeConjecture.SplitChowTateBlock.decode_encode
#print axioms HodgeConjecture.SplitChowTateBlock.encode_isIdempotent
#print axioms HodgeConjecture.SplitHodgeStructure.complexCoordinates_tmul
#print axioms HodgeConjecture.SplitHodgeStructure.conjugation_tmul
#print axioms HodgeConjecture.SplitHodgeStructure.bigrading_direct
#print axioms HodgeConjecture.SplitHodgeStructure.all_isHodgeMorphism
#print axioms HodgeConjecture.SplitBettiTateBlock.realization_encode
#print axioms HodgeConjecture.SplitBettiTateBlock.cycleClass_decode
#print axioms HodgeConjecture.SplitBettiTateBlock.hodgeCompatibility
#print axioms HodgeConjecture.SplitBettiTateBlock.graphProjectorLift
#print axioms HodgeConjecture.SplitBettiTateBlock.hodgeConjectureAt_iff_hodgeMorphismLift
#print axioms HodgeConjecture.SplitBettiTateBlock.everyHodgeClassHasPalomarTargetSquare

section SplitTateBlockRegressions

open HodgeConjecture

-- Empty complement: the graph of its zero class is the Tate identity.
example :
    SplitChowTateBlock.encode (Fin 0) 0 =
      (1 : SplitChowCorrespondence.EndAlgebra ℂ (Option (Fin 0))) := by
  apply (SplitChowCorrespondence.matrixAlgEquiv ℂ (Option (Fin 0))).injective
  rw [SplitChowTateBlock.matrix_encode, map_one]
  ext output input
  cases output with
  | none =>
    cases input with
    | none => simp
    | some i => exact Fin.elim0 i
  | some i => exact Fin.elim0 i

-- The source-first point pair (none, some i) is the lower-left Chow block.
example (I : Type) [Fintype I] [DecidableEq I] (i : I) :
    SplitChowTateBlock.decode I
      (SplitChowCorrespondence.pointCorrespondence ℂ (none : Option I) (some i)) =
        SplitZeroCycles.classMap ℂ I ℚ (SplitZeroCycles.pointCycle ℂ I ℚ i) := by
  apply (SplitZeroCycles.chowCoordinates ℂ I ℚ).injective
  ext j
  rw [SplitChowTateBlock.coordinates_decode,
    SplitChowCorrespondence.matrixAlgEquiv_apply,
    SplitChowCorrespondence.matrixCoordinates_pointCorrespondence]
  simp [-SplitZeroCycles.coordinates_apply, Matrix.single, Pi.single_apply, eq_comm]

-- Its transpose is upper-right, and must not decode to the original class.
example (I : Type) [Fintype I] [DecidableEq I] (i : I) :
    SplitChowTateBlock.decode I
      (SplitChowCorrespondence.pointCorrespondence ℂ (some i) (none : Option I)) = 0 := by
  apply (SplitZeroCycles.chowCoordinates ℂ I ℚ).injective
  ext j
  rw [SplitChowTateBlock.coordinates_decode,
    SplitChowCorrespondence.matrixAlgEquiv_apply,
    SplitChowCorrespondence.matrixCoordinates_pointCorrespondence]
  simp [Matrix.single]

-- The explicit actual Chow lift satisfies the universal algebra-hom square.
set_option synthInstance.maxHeartbeats 60000 in
example (I : Type) [Fintype I] [DecidableEq I] (α : SplitBetti.Cohomology I) :
    (SplitBettiTateBlock.correspondenceAction I).action.comp
      (SplitBettiTateBlock.graphProjectorLift I α).algebraIdempotentMap =
        (SplitBettiTateBlock.graphProjectorLift I α).cohomologicalIdempotentMap :=
  (SplitBettiTateBlock.graphProjectorLift I α).realization_idempotentMap_square

end SplitTateBlockRegressions

-- Genuine split G-torsor geometry and its homogeneous quotient, without normality.
#check HodgeConjecture.SplitGaloisSheets.regularAction
#check HodgeConjecture.SplitGaloisSheets.sheetAction
#check HodgeConjecture.SplitGaloisSheets.quotientMap_equivariant
#check HodgeConjecture.SplitGaloisSheets.quotientMap_isFinite
#check HodgeConjecture.SplitGaloisSheets.quotientMap_isEtale
#check HodgeConjecture.SplitGaloisSheets.quotientMap_isProper
#check HodgeConjecture.SplitGaloisSheets.quotientMap_surjective
#check HodgeConjecture.SplitGaloisSheets.regularToBase_surjective
#check HodgeConjecture.SplitGaloisSheets.regularAction_existsUnique
#check HodgeConjecture.SplitGaloisSheets.regularTorsorIso_hom_fst
#check HodgeConjecture.SplitGaloisSheets.regularTorsorIso_hom_snd
#check HodgeConjecture.SplitGaloisSheets.regularCollisionDecomposition

-- The source ideal is realized by actual point cycles and geometric intersection.
#check HodgeConjecture.SplitGaloisResidual.sheetEquiv
#check HodgeConjecture.SplitGaloisResidual.residualCoordinates_mul
#check HodgeConjecture.SplitGaloisResidual.residualChowEquiv
#check HodgeConjecture.SplitGaloisResidual.residualChow_residualClass
#check HodgeConjecture.SplitGaloisResidual.residualChow_mul
#check HodgeConjecture.SplitChowDiagonal.matrix_diagonalAlgHom
#check HodgeConjecture.SplitChowDiagonal.diagonalAlgHom_injective
#check HodgeConjecture.SplitChowDiagonal.diagonalAlgHom_single

-- Action comparisons need no reverse ambient-algebra restriction homomorphism.
#check HodgeConjecture.MarkedProjectorActionComparison
#check HodgeConjecture.MarkedProjectorActionComparison.lowerLeftClass_action_eq_generatedClass
#check HodgeConjecture.MarkedProjectorActionComparison.realizes
#check HodgeConjecture.MarkedProjectorActionComparison.action_comp_idempotentMap_eq_classGraph

-- Multiplicativity rigidifies q - 1 without a unit-preservation hypothesis.
#check HodgeConjecture.MarkedAugmentedAlgebra.residualClass_mul_eq_neg
#check HodgeConjecture.MarkedAugmentedAlgebra.generatedClass_mul_image
#check HodgeConjecture.MarkedAugmentedAlgebra.generatedClass_sq_eq_neg
#check HodgeConjecture.MarkedAugmentedAlgebra.generatedClass_eq_neg_one_of_one_mem_range
#check HodgeConjecture.MarkedAugmentedAlgebra.generatedClass_eq_neg_one_of_surjective

#print axioms HodgeConjecture.SplitGaloisSheets.quotientMap_equivariant
#print axioms HodgeConjecture.SplitGaloisSheets.regularAction_existsUnique
#print axioms HodgeConjecture.SplitGaloisSheets.regularCollisionDecomposition
#print axioms HodgeConjecture.SplitGaloisResidual.residualChowEquiv
#print axioms HodgeConjecture.SplitGaloisResidual.residualChow_residualClass
#print axioms HodgeConjecture.SplitGaloisResidual.residualChow_mul
#print axioms HodgeConjecture.SplitChowDiagonal.diagonalAlgHom
#print axioms HodgeConjecture.SplitChowDiagonal.diagonalAlgHom_single
#print axioms HodgeConjecture.MarkedProjectorActionComparison.lowerLeftClass_action_eq_generatedClass
#print axioms HodgeConjecture.MarkedProjectorActionComparison.action_comp_idempotentMap_eq_classGraph
#print axioms HodgeConjecture.MarkedAugmentedAlgebra.generatedClass_sq_eq_neg
#print axioms HodgeConjecture.MarkedAugmentedAlgebra.generatedClass_eq_neg_one_of_surjective

noncomputable section SplitGaloisRegressions

open HodgeConjecture

-- The regular torsor genuinely accepts a noncommutative finite group.
example :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠
      Equiv.swap 1 2 * Equiv.swap (0 : Fin 3) 1 := by decide

example :
    GaloisCollisionDecomposition (Equiv.Perm (Fin 3))
      (SplitPointGeometry.toBase ℂ (Equiv.Perm (Fin 3))) :=
  SplitGaloisSheets.regularCollisionDecomposition (Equiv.Perm (Fin 3))

-- A concrete nonnormal point stabilizer still gives a finite étale quotient cover.
example :
    let D := MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)
    ¬D.Normal ∧
      AlgebraicGeometry.IsEtale (SplitGaloisSheets.quotientMap (Equiv.Perm (Fin 3)) D) ∧
      AlgebraicGeometry.Surjective
        (SplitGaloisSheets.quotientMap (Equiv.Perm (Fin 3)) D) := by
  dsimp only
  refine ⟨?_, inferInstance, inferInstance⟩
  intro h
  have hc := h.conj_mem (Equiv.swap (1 : Fin 3) 2) (by decide)
    (Equiv.swap (0 : Fin 3) 1)
  exact (by decide :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 * (Equiv.swap (0 : Fin 3) 1)⁻¹ ∉
      MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)) hc

-- The maximal subgroup leaves exactly the marked sheet and no complement.
example (G : Type) [Group G] :
    IsEmpty (SplitGaloisResidual.Complement (⊤ : Subgroup G)) := by
  letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  exact ⟨fun s ↦ s.property (Subsingleton.elim _ _)⟩

example (G : Type) [Group G] [Finite G] :
    SplitGaloisResidual.fundamentalClass (⊤ : Subgroup G) = 0 := by
  letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  apply (SplitZeroCycles.chowCoordinates ℂ
    (SplitGaloisResidual.Complement (⊤ : Subgroup G)) ℚ).injective
  ext s
  exact (s.property (Subsingleton.elim _ _)).elim

-- The geometric residual class has the negative, not positive, fundamental sign.
example (G : Type) [Group G] [Finite G] (D : Subgroup G) :
    SplitGaloisResidual.residualChow D (MarkedSheetProjector.residualClass D) +
      SplitGaloisResidual.fundamentalClass D = 0 := by
  rw [SplitGaloisResidual.residualChow_residualClass]
  exact neg_add_cancel _

-- A singleton point function lands on its actual diagonal point pair.
example :
    SplitChowDiagonal.diagonalAlgHom ℂ (Fin 2) (Pi.single 1 1) =
      SplitChowCorrespondence.pointCorrespondence ℂ (1 : Fin 2) 1 :=
  SplitChowDiagonal.diagonalAlgHom_single ℂ (Fin 2) 1

-- Surjective multiplicative linear maps force the sign, with no map_one assumption.
example {A B : Type} [CommRing A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]
    (M : MarkedAugmentedAlgebra ℚ A) (θ : M.Residual →ₗ[ℚ] B)
    (hMul : ∀ x y, θ (x * y) = θ x * θ y) (hSurj : Function.Surjective θ) :
    M.generatedClass θ + 1 = 0 := by
  rw [M.generatedClass_eq_neg_one_of_surjective θ hMul hSurj]
  exact neg_add_cancel _

end SplitGaloisRegressions

-- The change of splitting is an invertible actual Chow correspondence.
#check HodgeConjecture.SplitChowShear.column_mul_column
#check HodgeConjecture.SplitChowShear.shear_mul_shear_neg
#check HodgeConjecture.SplitChowShear.conjugation_pointProjector
#check HodgeConjecture.SplitBettiTateBlock.realization_shear

-- Actual marked-sheet data supply the alpha-free comparison and its target square.
#check HodgeConjecture.SplitGaloisMarkedComparison.sheetSchemeIso
#check HodgeConjecture.SplitGaloisMarkedComparison.residualRealization_mul
#check HodgeConjecture.SplitGaloisMarkedComparison.residualRealization_surjective
#check HodgeConjecture.SplitGaloisMarkedComparison.generatedChowClass_eq_neg_fundamental
#check HodgeConjecture.SplitGaloisMarkedComparison.generatedClass_eq_neg_one
#check HodgeConjecture.SplitGaloisMarkedComparison.sourceToBlock_eq_realization_shear
#check HodgeConjecture.SplitGaloisMarkedComparison.markedEmbedding_injective
#check HodgeConjecture.SplitGaloisMarkedComparison.markedEmbedding_action
#check HodgeConjecture.SplitGaloisMarkedComparison.markedProjector_eq_encode
#check HodgeConjecture.SplitGaloisMarkedComparison.markedProjector_isIdempotent
#check HodgeConjecture.SplitGaloisMarkedComparison.markedProjector_realizes
#check HodgeConjecture.SplitGaloisMarkedComparison.comparison
#check HodgeConjecture.SplitGaloisMarkedComparison.detectedClass
#check HodgeConjecture.SplitGaloisMarkedComparison.projectorLift
#check HodgeConjecture.SplitGaloisMarkedComparison.palomarTargetSquare

#print axioms HodgeConjecture.SplitChowShear.shear_mul_shear_neg
#print axioms HodgeConjecture.SplitChowShear.conjugation_pointProjector
#print axioms HodgeConjecture.SplitBettiTateBlock.realization_shear
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.residualRealization_mul
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.generatedClass_eq_neg_one
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.sourceToBlock_eq_realization_shear
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.markedEmbedding_injective
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.markedEmbedding_action
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.markedProjector_realizes
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.comparison
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.detectedClass
#print axioms HodgeConjecture.SplitGaloisMarkedComparison.palomarTargetSquare

noncomputable section SplitGaloisMarkedRegressions

open HodgeConjecture Classical
open HodgeConjecture.SplitGaloisMarkedComparison HodgeConjecture.SplitGaloisResidual

variable {G : Type} [Group G] [Finite G] (D : Subgroup G)

local instance : Fintype (SplitGaloisResidual.Complement D) :=
  Fintype.ofFinite (SplitGaloisResidual.Complement D)

-- Constant-marked coordinates mark the constant unit, not the selector.
example : sourceToBlock D 1 = (1, 0) := by
  apply Prod.ext
  · simp
  · apply (SplitBetti.coordinates (SplitGaloisResidual.Complement D)).injective
    ext s
    rw [coordinates_sourceToBlock_snd]
    simp

-- Decode the geometrically constructed projector, retaining the fundamental sign.
example :
    SplitChowTateBlock.decode (SplitGaloisResidual.Complement D) (markedProjector D) =
      -fundamentalClass D := by
  rw [detectedClass, generatedChowClass_eq_neg_fundamental]

-- The full action works beyond the marked selector: a complementary point
-- function multiplying the constant two gives twice that point function.
set_option synthInstance.maxHeartbeats 60000 in
example (s : SplitGaloisResidual.Complement D) :
    SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)
      (markedEmbedding D (Pi.single s.val 1)) (sourceToBlock D 2) =
        sourceToBlock D (Pi.single s.val 2) := by
  rw [markedEmbedding_action]
  congr 1
  funext t
  by_cases h : t = s.val
  · subst t
    simp
  · simp [h]

-- The constructed marked projector satisfies the full universal algebra-hom square.
set_option synthInstance.maxHeartbeats 60000 in
example :
    (SplitBettiTateBlock.correspondenceAction (SplitGaloisResidual.Complement D)).action.comp
      (UniversalIdempotentAlgebra.mapOfIdempotent
        (markedProjector D) (markedProjector_isIdempotent D)) =
      UniversalIdempotentAlgebra.mapOfIdempotent
        (ClassGraphProjector.operator (generatedClass D))
        (ClassGraphProjector.operator_isIdempotent (generatedClass D)) :=
  palomarTargetSquare D

end SplitGaloisMarkedRegressions

-- Selected literature conclusions are explicit hypotheses, not project axioms.
#check HodgeConjecture.NormalizationInertia.inertiaFixedRingUnramifiedAt_iff
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtensionHypothesis
#check HodgeConjecture.LiteratureInputs.DeckExtensionHypothesis
#check HodgeConjecture.LiteratureInputs.chosenExtension
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.original_isFinite
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.original_isEtale
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.inclusion_toBase
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.restriction_inclusion
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.liftDeckAction
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.liftDeckAction_unique
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.liftDeckAction_inclusion
#check HodgeConjecture.ChowLocalizationHypotheses
#check HodgeConjecture.ChowLocalization.exists_lift
#check HodgeConjecture.ChowLocalization.two_lifts_differ_by_boundary
#check HodgeConjecture.ChowLocalization.projectorClosure_nonempty
#check HodgeConjecture.ChowLocalization.convolutionDefect_mem_range
#check HodgeConjecture.ChowLocalization.exists_boundary_of_convolutionDefect

#print axioms HodgeConjecture.NormalizationInertia.inertiaFixedRingUnramifiedAt_iff
#print axioms HodgeConjecture.LiteratureInputs.chosenExtension
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.original_isFinite
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.original_isEtale
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.inclusion_toBase
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.inclusion_isOpenImmersion
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.toBase_isProper
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.restriction_inclusion
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.deckEquiv
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.liftDeckAction
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.restriction_comp_liftDeckAction
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.liftDeckAction_unique
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.liftDeckAction_inclusion
#print axioms HodgeConjecture.ChowLocalization.exists_lift
#print axioms HodgeConjecture.ChowLocalization.two_lifts_differ_by_boundary
#print axioms HodgeConjecture.ChowLocalization.projectorClosure
#print axioms HodgeConjecture.ChowLocalization.projectorClosure_nonempty
#print axioms HodgeConjecture.ChowLocalization.convolutionDefect_mem_range
#print axioms HodgeConjecture.ChowLocalization.exists_boundary_of_convolutionDefect
#print axioms HodgeConjecture.Palomar.fixedPoints_heightOne_contraction
#print axioms HodgeConjecture.Palomar.heightOne_fixedRing_unramified_descent

noncomputable section SourceInputRegressions

open HodgeConjecture HodgeConjecture.LiteratureInputs
open AlgebraicGeometry CategoryTheory HodgeConjecture.SchemeCorrespondence

-- Importing the input surface installs no selected geometric hypotheses.
example {X U Y : Scheme} (_j : U ⟶ X) (_p : Y ⟶ U) : True := by
  fail_if_success
    have : FiniteEtaleExtensionHypothesis _j _p := inferInstance
  trivial

example {X U Y : Scheme} {j : U ⟶ X} {p : Y ⟶ U}
    (_E : FiniteEtaleExtension j p) : True := by
  fail_if_success
    have : DeckExtensionHypothesis _E := inferInstance
  trivial

-- An explicitly supplied deck-extension input lifts the whole actual action.
example {X U Y : Scheme} {j : U ⟶ X} {p : Y ⟶ U}
    (E : FiniteEtaleExtension j p) [DeckExtensionHypothesis E]
    {G : Type} [Group G] (α : FiniteDeckAction p G) :
    ∃! β : FiniteDeckAction E.toBase G, E.restriction.comp β = α := by
  exact ⟨E.liftDeckAction α, E.restriction_comp_liftDeckAction α,
    fun β hβ ↦ E.liftDeckAction_unique α β hβ⟩

-- Even a true exact sequence is not silently registered as a literature input.
example : True := by
  fail_if_success
    have : ChowLocalizationHypotheses (LinearMap.inr ℚ ℚ ℚ)
        (AlgHom.fst ℚ ℚ ℚ).toLinearMap := inferInstance
  trivial

-- This concrete exact sequence supplies its own proved local package.
example : ∃ c : ℚ × ℚ, (AlgHom.fst ℚ ℚ ℚ) c = 1 := by
  letI : ChowLocalizationHypotheses (LinearMap.inr ℚ ℚ ℚ)
      (AlgHom.fst ℚ ℚ ℚ).toLinearMap :=
    ⟨LinearMap.range_inr ℚ ℚ ℚ, fun a ↦ ⟨(a, 0), rfl⟩⟩
  exact ChowLocalization.exists_lift (LinearMap.inr ℚ ℚ ℚ)
    (AlgHom.fst ℚ ℚ ℚ).toLinearMap 1

-- Boundary support does not imply zero defect: the raw lift (1,2) of 1
-- under the first projection has defect (0,2), in the second-factor image.
theorem sourceInput_boundary_defect_can_be_nonzero :
    let P := ChowLocalization.projectorClosure (AlgHom.fst ℚ ℚ ℚ)
      (1 : ℚ) (by simp [IsIdempotentElem])
    ∃ x : P.Closure,
      P.convolutionDefect x ∈ LinearMap.range (LinearMap.inr ℚ ℚ ℚ) ∧
      P.convolutionDefect x ≠ 0 := by
  let hLoc : ChowLocalizationHypotheses (LinearMap.inr ℚ ℚ ℚ)
      (AlgHom.fst ℚ ℚ ℚ).toLinearMap :=
    ⟨LinearMap.range_inr ℚ ℚ ℚ, fun a ↦ ⟨(a, 0), rfl⟩⟩
  let P := ChowLocalization.projectorClosure (AlgHom.fst ℚ ℚ ℚ)
    (1 : ℚ) (by simp [IsIdempotentElem])
  letI : ChowLocalizationHypotheses (LinearMap.inr ℚ ℚ ℚ)
      P.restriction.toLinearMap := hLoc
  let x : P.Closure := ⟨(1, 2), rfl⟩
  refine ⟨x, ChowLocalization.convolutionDefect_mem_range
    (LinearMap.inr ℚ ℚ ℚ) P x, ?_⟩
  change ((1, 2) : ℚ × ℚ) * (1, 2) - (1, 2) ≠ 0
  norm_num [Prod.mk_mul_mk, Prod.mk_sub_mk, Prod.ext_iff]

#print axioms sourceInput_boundary_defect_can_be_nonzero

end SourceInputRegressions

-- Core Chow detection does not require residual surjectivity.
#check HodgeConjecture.MarkedProjectorActionComparison.cycleClass_decode_eq_generatedClass
#print axioms HodgeConjecture.MarkedProjectorActionComparison.cycleClass_decode_eq_generatedClass
#print axioms HodgeConjecture.MarkedGaloisSelectorComparison.isAlgebraicHodgeClass_of_comparison

noncomputable section ChosenProjectorRegressions

open HodgeConjecture

variable {A Gamma H : Type*}
variable [CommRing A] [Algebra ℚ A] [Ring Gamma] [Algebra ℚ Gamma]
variable [AddCommGroup H] [Module ℚ H]
variable {M : MarkedAugmentedAlgebra ℚ A}
variable {rho : RationalCorrespondenceAction Gamma (ℚ × H)} {projector : Gamma}
variable (B : MarkedProjectorActionComparison M rho projector)

-- The lift retains the chosen correspondence.
example (hProjector : IsIdempotentElem projector)
    (hSurjective : Function.Surjective B.residualRealization) :
    (B.toAlgebraicProjectorLift hProjector hSurjective).projector = projector :=
  rfl

-- Keeping the supplied extension package retains its original restriction law.
example {E : AlgebraProjectorExtension A Gamma M.selector} {x : E.Extension}
    (Bext : MarkedSelectorActionComparison M rho E x)
    (hSurjective : Function.Surjective Bext.residualRealization) :
    E.restriction (Bext.toAlgebraicProjectorLift hSurjective).projector =
      M.selector :=
  E.projector_restricts x

end ChosenProjectorRegressions

-- Actual closed deck graphs and their scheme-theoretic restriction.
#check HodgeConjecture.SchemeCorrespondence.graphMorphism
#check HodgeConjecture.SchemeCorrespondence.graphMorphism_fst
#check HodgeConjecture.SchemeCorrespondence.graphMorphism_snd
#check HodgeConjecture.SchemeCorrespondence.graphMorphism_isClosedImmersion
#check HodgeConjecture.SchemeCorrespondence.graphIdeal
#check HodgeConjecture.SchemeCorrespondence.graphSubschemeIso
#check HodgeConjecture.SchemeCorrespondence.graphSubschemeIso_hom_subschemeι
#check HodgeConjecture.SchemeCorrespondence.graphMorphism_isProper
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.pairInclusion
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.pairInclusion_isOpenImmersion
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graph_restriction_commutes
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphRestriction_isPullback
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphIdeal_restriction
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphIdeal_liftDeckAction

#print axioms HodgeConjecture.SchemeCorrespondence.graphMorphism
#print axioms HodgeConjecture.SchemeCorrespondence.graphMorphism_fst
#print axioms HodgeConjecture.SchemeCorrespondence.graphMorphism_snd
#print axioms HodgeConjecture.SchemeCorrespondence.graphMorphism_isClosedImmersion
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal
#print axioms HodgeConjecture.SchemeCorrespondence.graphSubschemeIso
#print axioms HodgeConjecture.SchemeCorrespondence.graphSubschemeIso_hom_subschemeι
#print axioms HodgeConjecture.SchemeCorrespondence.graphMorphism_isProper
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.pairInclusion
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.pairInclusion_isOpenImmersion
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graph_restriction_commutes
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphRestriction_isPullback
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphIdeal_restriction
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphIdeal_liftDeckAction

noncomputable section ClosedGraphRegressions

open HodgeConjecture HodgeConjecture.LiteratureInputs
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence

-- The identity graph is the actual relative diagonal.
example {S X : Scheme} (pX : X ⟶ S) :
    graphMorphism pX (1 : DeckTransformation pX) = pullback.diagonal pX := by
  apply pullback.hom_ext
  · simp
  · simp only [graphMorphism_snd, pullback.diagonal_snd]
    change (1 : DeckTransformation pX).hom.left = 𝟙 X
    simp only [show (1 : DeckTransformation pX).hom = 𝟙 (Over.mk pX) from rfl,
      Over.id_left]
    rfl

-- Both projections agree with the previously constructed graph span.
example {S X : Scheme} (pX : X ⟶ S) (σ : DeckTransformation pX) :
    graphMorphism pX σ ≫ pullback.fst pX pX = (graph pX σ).left ∧
      graphMorphism pX σ ≫ pullback.snd pX pX = (graph pX σ).right := by
  constructor <;> simp

-- Separatedness supplies the closed graph and its exact subscheme inclusion.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX]
    (σ : DeckTransformation pX) :
    IsClosedImmersion (graphMorphism pX σ) ∧
      (graphSubschemeIso pX σ).hom ≫ (graphIdeal pX σ).subschemeι =
        graphMorphism pX σ :=
  ⟨inferInstance, graphSubschemeIso_hom_subschemeι pX σ⟩

-- Restricting an already extended automorphism needs no deck-extension input.
example {X U Y : Scheme} {j : U ⟶ X} {p : Y ⟶ U}
    (E : FiniteEtaleExtension j p) [IsOpenImmersion j]
    (σ : DeckTransformation E.toBase) :
    graphIdeal p (E.restriction σ) =
      (graphIdeal E.toBase σ).comap E.pairInclusion := by
  fail_if_success
    have : DeckExtensionHypothesis E := inferInstance
  exact E.graphIdeal_restriction σ

-- A prescribed original action uses precisely the explicit lifting input.
example {X U Y : Scheme} {j : U ⟶ X} {p : Y ⟶ U}
    (E : FiniteEtaleExtension j p) [IsOpenImmersion j] [DeckExtensionHypothesis E]
    {G : Type} [Group G] (α : FiniteDeckAction p G) (g : G) :
    graphIdeal p (α g) =
      (graphIdeal E.toBase (E.liftDeckAction α g)).comap E.pairInclusion :=
  E.graphIdeal_liftDeckAction α g

end ClosedGraphRegressions

-- General finite cycles reuse the split generators and restrict actual graph cycles.
#check HodgeConjecture.SchemeCycles.IntegralClosedSubscheme
#check HodgeConjecture.SchemeCycles.Cycles
#check HodgeConjecture.SchemeCycles.openRestriction
#check HodgeConjecture.SchemeCorrespondence.graphCycleLinearMap
#check HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphCycleLinearMap_restriction

#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle
#print axioms HodgeConjecture.SchemeCycles.isIntegral_of_iso
#print axioms HodgeConjecture.SchemeCycles.openRestrictionSubscheme_isIntegral
#print axioms HodgeConjecture.SchemeCycles.openRestriction
#print axioms HodgeConjecture.SchemeCycles.openRestriction_fundamentalCycle_of_nonempty
#print axioms HodgeConjecture.SchemeCycles.openRestriction_fundamentalCycle_of_isEmpty
#print axioms HodgeConjecture.SchemeCycles.openRestriction_id
#print axioms HodgeConjecture.SchemeCycles.openRestriction_comp
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal_isIntegral
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal_topologicalKrullDim
#print axioms HodgeConjecture.SchemeCorrespondence.graphCycle
#print axioms HodgeConjecture.SchemeCorrespondence.graphCycleLinearMap_single
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.original_isIntegral
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphCycle_restriction
#print axioms HodgeConjecture.LiteratureInputs.FiniteEtaleExtension.graphCycleLinearMap_restriction

noncomputable section IntegralGraphCycleRegressions

open HodgeConjecture HodgeConjecture.LiteratureInputs
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCycles HodgeConjecture.SchemeCorrespondence

-- The split cycle type is the canonical scheme-cycle type, without a conversion.
example (K : Type) [Field K] (I : Type) [Finite I] :
    SplitZeroCycles.Cycles K I ℚ =
      SchemeCycles.Cycles (SplitPointGeometry.scheme K I) ℚ := rfl

-- The existing point generator is exactly the canonical integral generator.
example (K : Type) [Field K] (I : Type) [Finite I] (i : I) :
    SplitZeroCycles.pointCycle K I ℚ i =
      fundamentalCycle ℚ (SplitPointGeometry.pointIntegralSubscheme K I i) := rfl

-- Restriction to an empty open really kills each actual integral support.
example {X U : Scheme} [IsEmpty U] (j : U ⟶ X) [IsOpenImmersion j]
    (Z : SchemeCycles.IntegralClosedSubscheme X) :
    openRestriction ℚ j (fundamentalCycle ℚ Z) = 0 := by
  letI : IsEmpty (Z.val.comap j).subscheme :=
    Function.isEmpty (Z.val.comap j).subschemeι.base
  exact openRestriction_fundamentalCycle_of_isEmpty j ℚ Z

-- Iterated open restriction has the geometric contravariant order.
example {X U V : Scheme} (j : U ⟶ X) (k : V ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion k] (z : SchemeCycles.Cycles X ℚ) :
    openRestriction ℚ (k ≫ j) z =
      openRestriction ℚ k (openRestriction ℚ j z) :=
  (LinearMap.congr_fun (openRestriction_comp j ℚ k) z).symm

-- Rational graph assembly retains a genuinely signed coefficient.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ : DeckTransformation pX) :
    graphCycleLinearMap pX (MonoidAlgebra.single σ (-3 / 2 : ℚ)) =
      (-3 / 2 : ℚ) • graphCycle pX ℚ σ :=
  graphCycleLinearMap_single pX σ (-3 / 2)

-- Restricting a supplied graph still does not install a deck-extension input.
example {X U Y : Scheme} {j : U ⟶ X} {p : Y ⟶ U}
    (E : FiniteEtaleExtension j p) [IsOpenImmersion j]
    [IsIntegral E.carrier] [Nonempty Y] (σ : DeckTransformation E.toBase) :
    letI := E.finite
    letI := E.original_isFinite
    letI := E.original_isIntegral
    letI := E.pairInclusion_isOpenImmersion
    openRestriction ℚ E.pairInclusion (graphCycle E.toBase ℚ σ) =
      graphCycle p ℚ (E.restriction σ) := by
  fail_if_success
    have : DeckExtensionHypothesis E := inferInstance
  exact E.graphCycle_restriction ℚ σ

end IntegralGraphCycleRegressions

-- Actual scheme-theoretic graph composition and ambient integral multiplicity.
#check HodgeConjecture.SchemeCorrespondence.tripleProduct
#check HodgeConjecture.SchemeCorrespondence.graphIntersectionIdeal
#check HodgeConjecture.SchemeCorrespondence.graphCompositionIso_hom_subschemeι
#check HodgeConjecture.SchemeCycles.integralSubscheme_genericStalk_length

#print axioms HodgeConjecture.SchemeCorrespondence.graphCompositionMorphism
#print axioms HodgeConjecture.SchemeCorrespondence.graphCompositionMorphism_p13
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionIdeal_eq_ker
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionIso
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionIso_hom_subschemeι
#print axioms HodgeConjecture.SchemeCorrespondence.graphCompositionIso
#print axioms HodgeConjecture.SchemeCorrespondence.graphCompositionIso_hom_subschemeι
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionIdeal_map_p13
#print axioms HodgeConjecture.SchemeCycles.genericStalk_length_of_isClosedImmersion
#print axioms HodgeConjecture.SchemeCycles.integralSubscheme_genericStalk_length

noncomputable section GraphCompositionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence HodgeConjecture.SchemeCycles

-- The two equations have the noncommutative order: τ first, then σ.
example {S X : Scheme} (pX : X ⟶ S) (σ τ : DeckTransformation pX) :
    graphCompositionMorphism pX σ τ ≫ tripleProductP12 pX = graphMorphism pX τ ∧
      graphCompositionMorphism pX σ τ ≫ tripleProductP23 pX ≫
        pullback.snd pX pX = τ.toSchemeHom ≫ σ.toSchemeHom := by
  constructor <;> simp

-- Identity graphs work in both multiplication positions.
example {S X : Scheme} (pX : X ⟶ S) (σ : DeckTransformation pX) :
    graphCompositionMorphism pX 1 σ ≫ tripleProductP13 pX = graphMorphism pX σ ∧
      graphCompositionMorphism pX σ 1 ≫ tripleProductP13 pX = graphMorphism pX σ := by
  constructor <;> simp

-- Exact ideal-image equality requires separatedness, not finiteness or integrality.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphIntersectionIdeal pX σ τ).map (tripleProductP13 pX) =
      graphIdeal pX (σ * τ) := by
  fail_if_success
    have : IsFinite pX := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  exact graphIntersectionIdeal_map_p13 pX σ τ

-- The restricted projection is proper on this support, not asserted on all T.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    IsProper ((graphIntersectionIdeal pX σ τ).subschemeι ≫ tripleProductP13 pX) := by
  rw [← graphCompositionIso_hom_subschemeι]
  infer_instance

-- An integral source gives an actual integral intersection of the same dimension.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    IsIntegral (graphIntersectionIdeal pX σ τ).subscheme ∧
      topologicalKrullDim (graphIntersectionIdeal pX σ τ).subscheme =
        topologicalKrullDim X := by
  refine ⟨SchemeCycles.isIntegral_of_iso (graphIntersectionIso pX σ τ), ?_⟩
  let e := Scheme.homeoOfIso (graphIntersectionIso pX σ τ)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

-- The integral graph's coefficient uses the actual AMBIENT scalar structure.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ : DeckTransformation pX) :
    let Z := graphIntegralSubscheme pX σ
    letI := Z.property
    letI : Algebra
        ((pullback pX pX).presheaf.stalk
          (Z.val.subschemeι.base (genericPoint Z.val.subscheme)))
        Z.val.subscheme.functionField :=
      (Z.val.subschemeι.stalkMap (genericPoint Z.val.subscheme)).hom.toAlgebra
    Module.length
      ((pullback pX pX).presheaf.stalk
        (Z.val.subschemeι.base (genericPoint Z.val.subscheme)))
      Z.val.subscheme.functionField = 1 :=
  integralSubscheme_genericStalk_length (graphIntegralSubscheme pX σ)

-- Reuse the existing generic degree-one calculation for the actual isomorphism.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX]
    (σ τ : DeckTransformation pX) (z : (graphIntersectionIdeal pX σ τ).subscheme) :
    let f := (graphCompositionIso pX σ τ).hom
    letI : Algebra ((graphIdeal pX (σ * τ)).subscheme.residueField (f.base z))
        ((graphIntersectionIdeal pX σ τ).subscheme.residueField z) :=
      (f.residueFieldMap z).hom.toAlgebra
    Module.finrank ((graphIdeal pX (σ * τ)).subscheme.residueField (f.base z))
      ((graphIntersectionIdeal pX σ τ).subscheme.residueField z) = 1 :=
  SplitPointGeometry.residueFieldMap_finrank_of_isIso (graphCompositionIso pX σ τ).hom z

end GraphCompositionRegressions

-- Actual degree-one image cycles and graph-slice pull–push.
#print axioms HodgeConjecture.SchemeCycles.residueFieldMap_finrank_of_isIso
#print axioms HodgeConjecture.SchemeCycles.closedImageSubschemeIso
#print axioms HodgeConjecture.SchemeCycles.closedImageSubschemeIso_genericPoint
#print axioms HodgeConjecture.SchemeCycles.closedImageCycle_eq_residueDegree_smul
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_id
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_comp
#print axioms HodgeConjecture.SchemeCorrespondence.graphMorphism_isOpenImmersion
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionIdeal_subschemeι_isOpenImmersion
#print axioms HodgeConjecture.SchemeCorrespondence.graphSlicePairMap_isIso
#print axioms HodgeConjecture.SchemeCorrespondence.graphSliceMorphism_isOpenImmersion
#print axioms HodgeConjecture.SchemeCorrespondence.graphSlice_isPullback
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal_comap_p12_eq_graphSlice_ker
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal_comap_graphSlicePairMap
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal_map_graphSliceMorphism
#print axioms HodgeConjecture.SchemeCorrespondence.graphRightPullback_graphCycle
#print axioms HodgeConjecture.SchemeCorrespondence.graphSlicePullPush_graphCycle
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionCycle_image_p13
#print axioms HodgeConjecture.SchemeCorrespondence.graphSlicePullPush_graphCycleLinearMap_single

noncomputable section GraphSliceCycleRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence HodgeConjecture.SchemeCycles

-- The generic closed pushforward has the actual identity law.
example {X : Scheme} (z : Cycles X ℚ) :
    closedImmersionPushforward ℚ (𝟙 X) z = z := by
  rw [closedImmersionPushforward_id]
  rfl

-- Its composition follows the geometric covariant order.
example {X Y T : Scheme} (f : X ⟶ Y) (g : Y ⟶ T)
    [IsClosedImmersion f] [IsClosedImmersion g] (z : Cycles X ℚ) :
    closedImmersionPushforward ℚ (f ≫ g) z =
      closedImmersionPushforward ℚ g (closedImmersionPushforward ℚ f z) :=
  (LinearMap.congr_fun (closedImmersionPushforward_comp f ℚ g) z).symm

-- Genuine closed image cycles retain negative coefficients.
example {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f]
    (Z : IntegralClosedSubscheme X) :
    closedImmersionPushforward ℚ f (Finsupp.single Z (-3 / 2 : ℚ)) =
      (-3 / 2 : ℚ) • closedImageCycle f ℚ Z :=
  closedImmersionPushforward_single f ℚ Z (-3 / 2)

-- The slice is the actual graph inverse image, before any integrality assumption.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] (τ : DeckTransformation pX) :
    (graphIdeal pX τ).comap (tripleProductP12 pX) = (graphSliceMorphism pX τ).ker :=
  graphIdeal_comap_p12_eq_graphSlice_ker pX τ

-- Openness is an étale conclusion; no finite-cover premise is installed.
example {S X : Scheme} (pX : X ⟶ S) [IsEtale pX] [IsSeparated pX]
    (τ : DeckTransformation pX) :
    IsOpenImmersion (graphSliceMorphism pX τ) ∧ IsClosedImmersion (graphSliceMorphism pX τ) := by
  fail_if_success
    have : IsFinite pX := inferInstance
  exact ⟨inferInstance, inferInstance⟩

-- Relative pairs and inverse-image graphs are not silently made integral.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    graphSlicePullPush pX ℚ τ (graphCycle pX ℚ σ) = graphIntersectionCycle pX ℚ σ τ := by
  fail_if_success
    have : IsIntegral (pullback pX pX) := inferInstance
  exact graphSlicePullPush_graphCycle pX ℚ σ τ

-- The generic cycle law acts by RIGHT multiplication on the graph index.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    graphRightPullback pX ℚ τ (graphCycle pX ℚ σ) = graphCycle pX ℚ (σ * τ) :=
  graphRightPullback_graphCycle pX ℚ σ τ

-- A supportwise outer pushforward requires no globally proper projection.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    closedImageCycle (tripleProductP13 pX) ℚ (graphIntersectionIntegralSubscheme pX σ τ) =
      graphCycle pX ℚ (σ * τ) := by
  fail_if_success
    have : IsProper (tripleProductP13 pX) := inferInstance
  exact graphIntersectionCycle_image_p13 pX ℚ σ τ

-- The geometric slice map preserves rational weights, not only positive generators.
example {S X : Scheme} (pX : X ⟶ S) [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    graphSlicePullPush pX ℚ τ (graphCycleLinearMap pX (MonoidAlgebra.single σ (-3 / 2 : ℚ))) =
      (-3 / 2 : ℚ) • graphIntersectionCycle pX ℚ σ τ :=
  graphSlicePullPush_graphCycleLinearMap_single pX σ τ (-3 / 2)

end GraphSliceCycleRegressions

-- SP34: actual relative-to-structural-base geometry and cycle transport.
#check HodgeConjecture.SchemeCorrespondence.forgetDeckBase
#check HodgeConjecture.SchemeCorrespondence.pairBaseComparison
#check HodgeConjecture.SchemeCorrespondence.tripleBaseComparison
#check HodgeConjecture.SchemeCorrespondence.graphMorphism_pairBaseComparison
#check HodgeConjecture.SchemeCorrespondence.graphCompositionMorphism_tripleBaseComparison
#check HodgeConjecture.SchemeCorrespondence.graphCycleLinearMap_baseComparison

#print axioms HodgeConjecture.SchemeCorrespondence.forgetDeckBase
#print axioms HodgeConjecture.SchemeCorrespondence.forgetDeckBase_injective
#print axioms HodgeConjecture.SchemeCorrespondence.pairBaseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.pairBaseComparison_isClosedImmersion
#print axioms HodgeConjecture.SchemeCorrespondence.tripleBaseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.tripleBaseComparison_isClosedImmersion
#print axioms HodgeConjecture.SchemeCorrespondence.graphIdeal_map_pairBaseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionIdeal_map_tripleBaseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphSlicePairMap_baseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphSliceMorphism_baseComparison
#print axioms HodgeConjecture.SchemeCycles.ideal_comap_iso_eq_map_inv
#print axioms HodgeConjecture.SchemeCycles.openRestriction_iso_eq_pushforward_inv
#print axioms HodgeConjecture.SchemeCycles.pushforward_openRestriction_iso
#print axioms HodgeConjecture.SchemeCorrespondence.graphCycle_pairBaseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphIntersectionCycle_tripleBaseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphRightPullback_baseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphSlicePullPush_baseComparison
#print axioms HodgeConjecture.SchemeCorrespondence.graphCycleLinearMap_baseComparison

noncomputable section RelativeProductCycleRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence HodgeConjecture.SchemeCycles

-- Closedness of the pair comparison needs only separatedness of the base map.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B) [IsSeparated b] :
    IsClosedImmersion (pairBaseComparison p b) := by
  fail_if_success
    have : IsSeparated p := inferInstance
  infer_instance

-- The same minimal hypothesis suffices for the actual triple comparison.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B) [IsSeparated b] :
    IsClosedImmersion (tripleBaseComparison p b) := by
  fail_if_success
    have : IsEtale p := inferInstance
  infer_instance

-- Forgetting the base retains the actual maps and noncommutative order.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B)
    (σ τ : DeckTransformation p) :
    (forgetDeckBase p b (σ * τ)).toSchemeHom = τ.toSchemeHom ≫ σ.toSchemeHom ∧
      graphCompositionMorphism p σ τ ≫ tripleBaseComparison p b ≫
          tripleProductP13 (p ≫ b) =
        graphMorphism (p ≫ b) (forgetDeckBase p b (σ * τ)) := by
  constructor
  · exact forgetDeckBase_mul_toSchemeHom p b σ τ
  · simp

-- A signed graph coefficient survives the actual closed pair pushforward.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B)
    [IsSeparated p] [IsSeparated b] [IsIntegral X] (σ : DeckTransformation p) :
    closedImmersionPushforward ℚ (pairBaseComparison p b)
        ((-3 / 2 : ℚ) • graphCycle p ℚ σ) =
      (-3 / 2 : ℚ) • graphCycle (p ≫ b) ℚ (forgetDeckBase p b σ) := by
  simp only [map_smul, graphCycle_pairBaseComparison]

-- The triple comparison transports the actual integral intersection support.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B)
    [IsSeparated p] [IsSeparated b] [IsIntegral X] (σ τ : DeckTransformation p) :
    closedImmersionPushforward ℚ (tripleBaseComparison p b)
        (graphIntersectionCycle p ℚ σ τ) =
      graphIntersectionCycle (p ≫ b) ℚ
        (forgetDeckBase p b σ) (forgetDeckBase p b τ) :=
  graphIntersectionCycle_tripleBaseComparison p b ℚ σ τ

-- The R-square holds on every finite cycle, without source integrality or separatedness.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B) [IsSeparated b]
    (R : Type) [Semiring R] (τ : DeckTransformation p) (z : Cycles (pullback p p) R) :
    closedImmersionPushforward R (pairBaseComparison p b) (graphRightPullback p R τ z) =
      graphRightPullback (p ≫ b) R (forgetDeckBase p b τ)
        (closedImmersionPushforward R (pairBaseComparison p b) z) := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsSeparated p := inferInstance
  exact LinearMap.congr_fun (graphRightPullback_baseComparison p b R τ) z

-- The K-square also acts on all cycles, without integrality or étaleness.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B)
    [IsSeparated p] [IsSeparated b] (R : Type) [Semiring R]
    (τ : DeckTransformation p) (z : Cycles (pullback p p) R) :
    closedImmersionPushforward R (tripleBaseComparison p b) (graphSlicePullPush p R τ z) =
      graphSlicePullPush (p ≫ b) R (forgetDeckBase p b τ)
        (closedImmersionPushforward R (pairBaseComparison p b) z) := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsEtale p := inferInstance
  exact LinearMap.congr_fun (graphSlicePullPush_baseComparison p b R τ) z

-- The weighted comparison applies to an arbitrary rational group-algebra element ζ.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B)
    [IsSeparated p] [IsSeparated b] [IsIntegral X]
    (ζ : MonoidAlgebra ℚ (DeckTransformation p)) :
    closedImmersionPushforward ℚ (pairBaseComparison p b) (graphCycleLinearMap p ζ) =
      graphCycleLinearMap (p ≫ b)
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b) ζ) :=
  LinearMap.congr_fun (graphCycleLinearMap_baseComparison p b) ζ

-- Taking B = Spec k instantiates actual absolute pair and triple products.
example (k : Type) [Field k] {X S : Scheme} (p : X ⟶ S)
    (b : S ⟶ Spec (CommRingCat.of k)) [IsSeparated b] :
    IsClosedImmersion (pairBaseComparison p b) ∧
      IsClosedImmersion (tripleBaseComparison p b) :=
  ⟨inferInstance, inferInstance⟩

-- Étaleness over S plus separatedness of S → B does not install étaleness over B.
example {X S B : Scheme} (p : X ⟶ S) (b : S ⟶ B)
    [IsEtale p] [IsSeparated b] : IsClosedImmersion (pairBaseComparison p b) := by
  fail_if_success
    have : IsEtale (p ≫ b) := inferInstance
  infer_instance

end RelativeProductCycleRegressions

-- SP35: actual local quotient lengths, signed orders, and divisor-point transport.
#check HodgeConjecture.SchemeCycles.ord_ringEquiv
#check HodgeConjecture.SchemeCycles.ordFrac_ringEquiv
#check HodgeConjecture.SchemeCycles.localOrder
#check HodgeConjecture.SchemeCycles.functionFieldEquiv
#check HodgeConjecture.SchemeCycles.DivisorPoint
#check HodgeConjecture.SchemeCycles.divisorPointOfAffineHeightOne
#check HodgeConjecture.SchemeCycles.divisorOrder_iso
#check HodgeConjecture.SchemeCycles.Examples.localOrder_int_two_inv

#print axioms HodgeConjecture.SchemeCycles.localOrder
#print axioms HodgeConjecture.SchemeCycles.localOrder_mul
#print axioms HodgeConjecture.SchemeCycles.localOrder_inv
#print axioms HodgeConjecture.SchemeCycles.principalQuotient_length_ne_top
#print axioms HodgeConjecture.SchemeCycles.localOrder_algebraMap
#print axioms HodgeConjecture.SchemeCycles.localOrder_fraction
#print axioms HodgeConjecture.SchemeCycles.localOrder_map_unit
#print axioms HodgeConjecture.SchemeCycles.ord_ringEquiv
#print axioms HodgeConjecture.SchemeCycles.ordMonoidWithZeroHom_ringEquiv
#print axioms HodgeConjecture.SchemeCycles.ordFrac_ringEquiv
#print axioms HodgeConjecture.SchemeCycles.functionFieldEquiv
#print axioms HodgeConjecture.SchemeCycles.functionFieldIso_stalkSpecializes
#print axioms HodgeConjecture.SchemeCycles.functionFieldEquiv_algebraMap
#print axioms HodgeConjecture.SchemeCycles.DivisorPoint
#print axioms HodgeConjecture.SchemeCycles.stalkDimension_iso
#print axioms HodgeConjecture.SchemeCycles.divisorPointEquiv
#print axioms HodgeConjecture.SchemeCycles.divisorPointOfAffineHeightOne
#print axioms HodgeConjecture.SchemeCycles.divisorOrder
#print axioms HodgeConjecture.SchemeCycles.divisorOrder_mul
#print axioms HodgeConjecture.SchemeCycles.divisorOrder_algebraMap
#print axioms HodgeConjecture.SchemeCycles.divisorOrder_iso
#print axioms HodgeConjecture.SchemeCycles.Examples.int_two_quotient_length
#print axioms HodgeConjecture.SchemeCycles.Examples.localOrder_int_two
#print axioms HodgeConjecture.SchemeCycles.Examples.localOrder_int_two_inv

noncomputable section SignedLocalOrderRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- Ring transport compares the actual quotient-module lengths, not a chosen divisor function.
example {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    Module.length S (S ⧸ Ideal.span {e a}) = Module.length R (R ⧸ Ideal.span {a}) :=
  ord_ringEquiv e a

-- A genuine multiplicative inverse changes the sign in the product formula.
example (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] (f g : Kˣ) :
    localOrder R (f * g⁻¹) = localOrder R f - localOrder R g := by
  rw [localOrder_mul, localOrder_inv, sub_eq_add_neg]

-- Invertible local elements contribute zero through the actual fraction-ring map.
example (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K] (a : Rˣ) :
    localOrder R (Units.map (algebraMap R K).toMonoidHom a) = 0 :=
  localOrder_map_unit R a

-- The contravariant function-field isomorphism commutes with the actual stalk map.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) (x : X)
    (a : Y.presheaf.stalk (e.hom.base x)) :
    functionFieldEquiv e (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField ((e.hom.stalkMap x).hom a) := by
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact functionFieldEquiv_algebraMap e x a

-- Divisor-point transport is geometric even without integrality or Noetherianity.
example {X Y : Scheme} (e : X ≅ Y) (x : DivisorPoint X) :
    (divisorPointEquiv e x).val = e.hom.base x.val := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact divisorPointEquiv_val e x

-- An actual height-one prime in an affine chart gives the same underlying scheme point.
example (X : Scheme) {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (h : (hU.primeIdealOf x).asIdeal.height = 1) :
    (divisorPointOfAffineHeightOne X hU x h).val = x.val ∧
      ringKrullDim (X.presheaf.stalk (divisorPointOfAffineHeightOne X hU x h).val) = 1 :=
  ⟨rfl, (divisorPointOfAffineHeightOne X hU x h).property⟩

-- Local coefficient transport needs neither normality nor a DVR hypothesis.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (x : DivisorPoint X) (f : Y.functionFieldˣ) :
    divisorOrder X x (Units.map (functionFieldEquiv e).toMonoidHom f) =
      divisorOrder Y (divisorPointEquiv e x) f := by
  fail_if_success
    have : IsIntegrallyClosed (X.presheaf.stalk x.val) := inferInstance
  fail_if_success
    have : IsDiscreteValuationRing (X.presheaf.stalk x.val) := inferInstance
  exact divisorOrder_iso e x f

-- Apply the coefficient theorem to the existing actual support-to-image isomorphism.
-- Image integrality and local Noetherianity are derived, not supplied as new inputs.
example {X Y : Scheme} (f : X ⟶ Y) (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] [IsLocallyNoetherian Z.val.subscheme]
    (x : DivisorPoint Z.val.subscheme) :
    letI := Z.property
    letI := closedImageSubscheme_isIntegral f Z
    letI : IsLocallyNoetherian (Z.val.map f).subscheme :=
      isLocallyNoetherian_of_isOpenImmersion (closedImageSubschemeIso f Z).inv
    ∀ g : (Z.val.map f).subscheme.functionFieldˣ,
      divisorOrder Z.val.subscheme x
          (Units.map (functionFieldEquiv (closedImageSubschemeIso f Z)).toMonoidHom g) =
        divisorOrder (Z.val.map f).subscheme
          (divisorPointEquiv (closedImageSubschemeIso f Z) x) g := by
  letI := Z.property
  letI := closedImageSubscheme_isIntegral f Z
  letI : IsLocallyNoetherian (Z.val.map f).subscheme :=
    isLocallyNoetherian_of_isOpenImmersion (closedImageSubschemeIso f Z).inv
  intro g
  fail_if_success
    have : IsProper f := inferInstance
  exact divisorOrder_iso (closedImageSubschemeIso f Z) x g

-- A computed nonzero value: ℤ/(2) is actually simple, hence the order of 2 is 1.
example : localOrder ℤ (Units.mk0 (2 : ℚ) two_ne_zero) = 1 :=
  Examples.localOrder_int_two

-- The negative value is proved, not made conditional on an assumed order.
example : localOrder ℤ (Units.mk0 (2 : ℚ) two_ne_zero)⁻¹ = -1 :=
  Examples.localOrder_int_two_inv

-- Identify that inverse with the explicit rational function 1/2.
example : localOrder ℤ (Units.mk0 ((1 : ℚ) / 2) (div_ne_zero one_ne_zero two_ne_zero)) = -1 := by
  have h : Units.mk0 ((1 : ℚ) / 2) (div_ne_zero one_ne_zero two_ne_zero) =
      (Units.mk0 (2 : ℚ) two_ne_zero)⁻¹ := by
    apply Units.ext
    simp [one_div]
  rw [h]
  exact Examples.localOrder_int_two_inv

end SignedLocalOrderRegressions

-- SP36: actual reduced point closures, support codimension, and prime-divisor transport.
#check HodgeConjecture.SchemeCycles.pointEquivIntegralClosedSubscheme
#check HodgeConjecture.SchemeCycles.point_coheight_eq_stalkDim
#check HodgeConjecture.SchemeCycles.supportCodimension_eq_stalkDim
#check HodgeConjecture.SchemeCycles.divisorPointEquivPrimeDivisor
#check HodgeConjecture.SchemeCycles.primeDivisorEquiv_val
#check HodgeConjecture.SchemeCycles.primeDivisorOrder_iso

#print axioms HodgeConjecture.SchemeCycles.vanishingIdeal_subscheme_isReduced
#print axioms HodgeConjecture.SchemeCycles.radical_eq_of_subscheme_isReduced
#print axioms HodgeConjecture.SchemeCycles.pointSupport
#print axioms HodgeConjecture.SchemeCycles.pointSupport_support
#print axioms HodgeConjecture.SchemeCycles.ambientGenericPoint
#print axioms HodgeConjecture.SchemeCycles.ambientGenericPoint_isGenericPoint
#print axioms HodgeConjecture.SchemeCycles.ambientGenericPoint_pointSupport
#print axioms HodgeConjecture.SchemeCycles.pointSupport_ambientGenericPoint
#print axioms HodgeConjecture.SchemeCycles.pointEquivIntegralClosedSubscheme
#print axioms HodgeConjecture.SchemeCycles.pointClosureOrderIso
#print axioms HodgeConjecture.SchemeCycles.pointClosure_coheight
#print axioms HodgeConjecture.SchemeCycles.point_coheight_eq_stalkDim
#print axioms HodgeConjecture.SchemeCycles.integralSupport
#print axioms HodgeConjecture.SchemeCycles.supportCodimension
#print axioms HodgeConjecture.SchemeCycles.supportCodimension_eq_stalkDim
#print axioms HodgeConjecture.SchemeCycles.supportCodimension_eq_one_iff
#print axioms HodgeConjecture.SchemeCycles.PrimeDivisor
#print axioms HodgeConjecture.SchemeCycles.divisorPointEquivPrimeDivisor
#print axioms HodgeConjecture.SchemeCycles.ambientGenericPoint_closedImageSubscheme
#print axioms HodgeConjecture.SchemeCycles.closedImage_pointSupport
#print axioms HodgeConjecture.SchemeCycles.supportCodimension_iso
#print axioms HodgeConjecture.SchemeCycles.primeDivisorEquiv
#print axioms HodgeConjecture.SchemeCycles.primeDivisorEquiv_val
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_pointSupport
#print axioms HodgeConjecture.SchemeCycles.primeDivisorOrder
#print axioms HodgeConjecture.SchemeCycles.primeDivisorOrder_pointSupport
#print axioms HodgeConjecture.SchemeCycles.primeDivisorOrder_iso

noncomputable section PrimeDivisorSupportRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- The support and its ambient generic point are constructed on arbitrary schemes.
example (X : Scheme) (x : X) :
    ((pointSupport X x).val.support : Set X) = closure {x} ∧
      ambientGenericPoint (pointSupport X x) = x := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact ⟨congrArg (fun C : TopologicalSpace.Closeds X ↦ (C : Set X))
    (pointSupport_support X x), ambientGenericPoint_pointSupport X x⟩

-- Every existing integral ideal-sheaf generator is recovered, not just chosen representatives.
example {X : Scheme} (Z : IntegralClosedSubscheme X) :
    pointSupport X (ambientGenericPoint Z) = Z :=
  pointSupport_ambientGenericPoint Z

-- Codimension counts closed supersets; it is not absolute ambient dimension minus support dimension.
example {X : Scheme} (Z : IntegralClosedSubscheme X) :
    (Order.coheight (integralSupport Z) : WithBot ℕ∞) =
      ringKrullDim (X.presheaf.stalk (ambientGenericPoint Z)) :=
  supportCodimension_eq_stalkDim Z

-- Codimension one is proved from the actual stalk condition.
example {X : Scheme} (x : DivisorPoint X) :
    supportCodimension (pointSupport X x.val) = 1 ∧
      ambientGenericPoint (divisorPointEquivPrimeDivisor X x).val = x.val :=
  ⟨(divisorPointEquivPrimeDivisor X x).property, ambientGenericPoint_pointSupport X x.val⟩

-- The earlier affine height-one constructor now has its literal reduced closed support.
example (X : Scheme) {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (h : (hU.primeIdealOf x).asIdeal.height = 1) :
    (divisorPointEquivPrimeDivisor X (divisorPointOfAffineHeightOne X hU x h)).val =
      pointSupport X x.val := rfl

-- Signed coefficients use the existing cycle module and closed pushforward.
example {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    closedImmersionPushforward ℤ f (-fundamentalCycle ℤ (pointSupport X x)) =
      -fundamentalCycle ℤ (pointSupport Y (f.base x)) := by
  rw [map_neg, closedImmersionPushforward_pointSupport]

-- Prime-support transport is the actual image ideal, even without ambient integrality.
example {X Y : Scheme} (e : X ≅ Y) (Z : PrimeDivisor X) :
    (primeDivisorEquiv e Z).val.val = Z.val.val.map e.hom := by
  fail_if_success
    have : IsIntegral X := inferInstance
  rw [primeDivisorEquiv_val]
  rfl

-- The support presentation introduces no second independent order.
example {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (x : DivisorPoint X) (f : X.functionFieldˣ) :
    primeDivisorOrder X (divisorPointEquivPrimeDivisor X x) f = divisorOrder X x f :=
  primeDivisorOrder_pointSupport x f

-- The coefficient comparison is on actual prime supports, with no normality input.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (Z : PrimeDivisor X) (f : Y.functionFieldˣ) :
    primeDivisorOrder X Z (Units.map (functionFieldEquiv e).toMonoidHom f) =
      primeDivisorOrder Y (primeDivisorEquiv e Z) f := by
  fail_if_success
    have : IsIntegrallyClosed (X.presheaf.stalk (ambientGenericPoint Z.val)) := inferInstance
  exact primeDivisorOrder_iso e Z f

-- Passing to the inverse rational function still negates the support coefficient.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) (Z : PrimeDivisor X) (f : Y.functionFieldˣ) :
    primeDivisorOrder X Z (Units.map (functionFieldEquiv e).toMonoidHom f⁻¹) =
      -primeDivisorOrder Y (primeDivisorEquiv e Z) f := by
  rw [primeDivisorOrder_iso]
  exact divisorOrder_inv Y _ f

-- Supportwise closedness suffices for the actual generic-point image formula.
example {X Y : Scheme} (f : X ⟶ Y) (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)] :
    ambientGenericPoint (closedImageSubscheme f Z) = f.base (ambientGenericPoint Z) := by
  fail_if_success
    have : IsProper f := inferInstance
  exact ambientGenericPoint_closedImageSubscheme f Z

-- Point transport and prime-support transport give the same underlying cycle generator.
example {X Y : Scheme} (e : X ≅ Y) (x : DivisorPoint X) :
    (divisorPointEquivPrimeDivisor Y (divisorPointEquiv e x)).val =
      closedImageSubscheme e.hom (divisorPointEquivPrimeDivisor X x).val := by
  exact (closedImage_pointSupport e.hom x.val).symm

-- Empty schemes do not acquire phantom integral generators under the classification.
example (X : Scheme) [IsEmpty X] : IsEmpty (IntegralClosedSubscheme X) :=
  ⟨fun Z ↦ isEmptyElim (ambientGenericPoint Z)⟩

end PrimeDivisorSupportRegressions

-- SP37: actual affine fractions and local/global finiteness of prime-divisor support.
#check HodgeConjecture.SchemeCycles.heightOne_mem_minimalPrimes_span
#check HodgeConjecture.SchemeCycles.finite_heightOne_primes_containing_either
#check HodgeConjecture.SchemeCycles.exists_affine_fraction
#check HodgeConjecture.SchemeCycles.divisorOrder_eq_zero_of_affine_fraction
#check HodgeConjecture.SchemeCycles.primeDivisorSupports_locallyFinite
#check HodgeConjecture.SchemeCycles.finite_primeDivisorOrder_support

#print axioms HodgeConjecture.SchemeCycles.heightOne_mem_minimalPrimes_span
#print axioms HodgeConjecture.SchemeCycles.finite_heightOne_ideals_containing
#print axioms HodgeConjecture.SchemeCycles.finite_heightOne_primes_containing
#print axioms HodgeConjecture.SchemeCycles.finite_heightOne_primes_containing_either
#print axioms HodgeConjecture.SchemeCycles.exists_affine_fraction
#print axioms HodgeConjecture.SchemeCycles.sectionToFunctionField_through_stalk
#print axioms HodgeConjecture.SchemeCycles.affineGerm_isUnit_iff
#print axioms HodgeConjecture.SchemeCycles.divisorOrder_eq_zero_of_affine_fraction
#print axioms HodgeConjecture.SchemeCycles.finite_divisorPoints_in_affine
#print axioms HodgeConjecture.SchemeCycles.primeDivisorSupports_locallyFinite
#print axioms HodgeConjecture.SchemeCycles.finite_primeDivisorOrder_support
#print axioms HodgeConjecture.SchemeCycles.finite_divisorOrder_support

noncomputable section DivisorFinitenessRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- Height one controls minimality without Noetherianity or a global dimension bound.
example (A : Type) [CommRing A] [IsDomain A] (a : A) (ha : a ≠ 0)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (haP : a ∈ P) :
    P ∈ (Ideal.span {a}).minimalPrimes := by
  fail_if_success
    have : IsNoetherianRing A := inferInstance
  fail_if_success
    have : Ring.KrullDimLE 1 A := inferInstance
  exact heightOne_mem_minimalPrimes_span a ha P hP haP

-- Noetherianity supplies finiteness, not normality or dimension at most one.
example (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha : a ≠ 0) :
    Set.Finite {p : PrimeSpectrum A | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal} := by
  fail_if_success
    have : Ring.KrullDimLE 1 A := inferInstance
  fail_if_success
    have : IsIntegrallyClosed A := inferInstance
  exact finite_heightOne_primes_containing A a ha

-- A numerator and denominator give a finite union of genuine height-one loci.
example (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Set.Finite {p : PrimeSpectrum A |
      p.asIdeal.height = 1 ∧ (a ∈ p.asIdeal ∨ b ∈ p.asIdeal)} :=
  finite_heightOne_primes_containing_either A a b ha hb

-- Affine fraction presentation uses the actual generic stalk and no Noetherianity.
example (X : Scheme) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] (f : X.functionFieldˣ) :
    ∃ a b : Γ(X, U), a ≠ 0 ∧ b ≠ 0 ∧
      (f : X.functionField) =
        algebraMap Γ(X, U) X.functionField a / algebraMap Γ(X, U) X.functionField b := by
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact exists_affine_fraction X hU f

-- The field map factors through every actual germ, not a supplied compatibility square.
example (X : Scheme) [IsIntegral X] (U : X.Opens) [Nonempty U]
    (x : U) (a : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x.val) X.functionField
        ((X.presheaf.germ U x.val x.property).hom a) =
      algebraMap Γ(X, U) X.functionField a :=
  sectionToFunctionField_through_stalk X U x a

-- Localization detects unit germs on arbitrary schemes, even nonintegral ones.
example (X : Scheme) {U : X.Opens} (hU : IsAffineOpen U)
    (x : U) (a : Γ(X, U)) :
    IsUnit ((X.presheaf.germ U x.val x.property).hom a) ↔
      a ∉ (hU.primeIdealOf x).asIdeal := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact affineGerm_isUnit_iff X hU x a

-- Outside both chart primes, the unique existing coefficient vanishes without normality.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (x : DivisorPoint X) (hx : x.val ∈ U) (f : X.functionFieldˣ) (a b : Γ(X, U))
    (hf : (f : X.functionField) =
      algebraMap Γ(X, U) X.functionField a / algebraMap Γ(X, U) X.functionField b)
    (ha : a ∉ (hU.primeIdealOf ⟨x.val, hx⟩).asIdeal)
    (hb : b ∉ (hU.primeIdealOf ⟨x.val, hx⟩).asIdeal) : divisorOrder X x f = 0 := by
  fail_if_success
    have : IsIntegrallyClosed (X.presheaf.stalk x.val) := inferInstance
  fail_if_success
    have : IsDiscreteValuationRing (X.presheaf.stalk x.val) := inferInstance
  exact divisorOrder_eq_zero_of_affine_fraction X hU x hx f a b hf ha hb

-- An affine chart bounds coefficients without compactness of the whole scheme.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsAffineOpen U) (f : X.functionFieldˣ) :
    Set.Finite {x : DivisorPoint X | x.val ∈ U ∧ divisorOrder X x f ≠ 0} := by
  fail_if_success
    have : CompactSpace X := inferInstance
  exact finite_divisorPoints_in_affine X hU f

-- The affine endpoint also accepts empty charts, where its indexed set is literally empty.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    {U : X.Opens} (hU : IsAffineOpen U) [IsEmpty {x : X // x ∈ U}]
    (f : X.functionFieldˣ) :
    {x : DivisorPoint X | x.val ∈ U ∧ divisorOrder X x f ≠ 0} = ∅ ∧
      Set.Finite {x : DivisorPoint X | x.val ∈ U ∧ divisorOrder X x f ≠ 0} := by
  refine ⟨Set.eq_empty_iff_forall_notMem.mpr ?_, finite_divisorPoints_in_affine X hU f⟩
  intro x hx
  exact isEmptyElim (⟨x.val, hx.1⟩ : {x : X // x ∈ U})

-- Local finiteness concerns actual closed supports and needs no global compactness.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionFieldˣ) :
    LocallyFinite (fun Z : {Z : PrimeDivisor X // primeDivisorOrder X Z f ≠ 0} ↦
      (Z.val.val.val.support : Set X)) := by
  fail_if_success
    have : CompactSpace X := inferInstance
  exact primeDivisorSupports_locallyFinite X f

-- A globally Noetherian scheme already supplies the compactness needed for finite support.
example (X : Scheme) [IsIntegral X] [IsNoetherian X] (f : X.functionFieldˣ) :
    Set.Finite {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} := by
  have : CompactSpace X := inferInstance
  exact finite_primeDivisorOrder_support X f

-- Both equivalent indices have finite support under exactly the global compactness input.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    Set.Finite {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} ∧
      Set.Finite {x : DivisorPoint X | divisorOrder X x f ≠ 0} :=
  ⟨finite_primeDivisorOrder_support X f, finite_divisorOrder_support X f⟩

-- Taking an inverse reverses signs but leaves the nonzero prime-support set unchanged.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] (f : X.functionFieldˣ) :
    {Z : PrimeDivisor X | primeDivisorOrder X Z f⁻¹ ≠ 0} =
      {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} := by
  ext Z
  simp only [Set.mem_setOf_eq, primeDivisorOrder, divisorOrder_inv, neg_ne_zero]

-- The constant function one has empty support even without compactness.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] :
    {Z : PrimeDivisor X | primeDivisorOrder X Z (1 : X.functionFieldˣ) ≠ 0} = ∅ := by
  ext Z
  simp only [Set.mem_setOf_eq, primeDivisorOrder, divisorOrder_one, ne_eq, not_true_eq_false,
    Set.mem_empty_iff_false]

-- Cancellation may shrink product support; only inclusion in the union is asserted.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] (f g : X.functionFieldˣ) :
    {Z : PrimeDivisor X | primeDivisorOrder X Z (f * g) ≠ 0} ⊆
      {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} ∪
        {Z : PrimeDivisor X | primeDivisorOrder X Z g ≠ 0} := by
  intro Z hZ
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  apply hZ
  change divisorOrder X _ (f * g) = 0
  rw [divisorOrder_mul]
  change primeDivisorOrder X Z f + primeDivisorOrder X Z g = 0
  rw [h.1, h.2, add_zero]

end DivisorFinitenessRegressions

-- SP38: assembled principal-divisor cycles and actual isomorphism transport.
#check HodgeConjecture.SchemeCycles.principalDivisor
#check HodgeConjecture.SchemeCycles.principalDivisor_apply
#check HodgeConjecture.SchemeCycles.principalDivisor_support
#check HodgeConjecture.SchemeCycles.principalDivisorAddHom
#check HodgeConjecture.SchemeCycles.closedImmersionPushforward_iso_apply
#check HodgeConjecture.SchemeCycles.principalDivisor_iso
#check HodgeConjecture.SchemeCycles.openRestriction_principalDivisor

#print axioms HodgeConjecture.SchemeCycles.principalDivisor
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_apply_prime
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_apply_of_not_prime
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_apply
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_support
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_eq_zero_iff
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_one
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_mul
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_inv
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_div
#print axioms HodgeConjecture.SchemeCycles.principalDivisorAddHom
#print axioms HodgeConjecture.SchemeCycles.principalDivisorAddHom_ofMul
#print axioms HodgeConjecture.SchemeCycles.closedImageSubschemeEquiv
#print axioms HodgeConjecture.SchemeCycles.closedImageSubschemeEquiv_apply
#print axioms HodgeConjecture.SchemeCycles.closedImageSubschemeEquiv_symm_apply
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_iso_eq_lmapDomain
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_iso_apply_image
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_iso_apply
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_iso
#print axioms HodgeConjecture.SchemeCycles.openRestriction_principalDivisor

noncomputable section PrincipalDivisorRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- The coefficient in the existing cycle module is the existing signed order.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    (principalDivisor X f : Cycles X ℤ) Z.val = primeDivisorOrder X Z f :=
  principalDivisor_apply_prime X f Z

-- No absolute-dimension grading is inferred: other codimensions have coefficient zero.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) (Z : IntegralClosedSubscheme X)
    (hZ : supportCodimension Z ≠ 1) : principalDivisor X f Z = 0 :=
  principalDivisor_apply_of_not_prime X f Z hZ

-- The exact cycle support consists of the actual prime supports with nonzero order.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    ((principalDivisor X f).support : Set (IntegralClosedSubscheme X)) =
      Subtype.val '' {Z : PrimeDivisor X | primeDivisorOrder X Z f ≠ 0} :=
  principalDivisor_support X f

-- Zero means vanishing local coefficients, not a converse assertion of global invertibility.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) :
    principalDivisor X f = 0 ↔ ∀ Z : PrimeDivisor X, primeDivisorOrder X Z f = 0 :=
  principalDivisor_eq_zero_iff X f

example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X] :
    principalDivisor X (1 : X.functionFieldˣ) = 0 :=
  principalDivisor_one X

-- Multiplicative rational functions map to additive integral cycles.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f g : X.functionFieldˣ) :
    principalDivisor X (f * g) = principalDivisor X f + principalDivisor X g :=
  principalDivisor_mul X f g

example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) : principalDivisor X f⁻¹ = -principalDivisor X f :=
  principalDivisor_inv X f

example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f g : X.functionFieldˣ) :
    principalDivisor X (f / g) = principalDivisor X f - principalDivisor X g :=
  principalDivisor_div X f g

-- Genuine cancellation is retained when coefficients are assembled into a cycle.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X.functionFieldˣ) : principalDivisor X (f / f) = 0 := by
  rw [principalDivisor_div, sub_self]

-- The bundled homomorphism has the same principal-divisor function, not a second assignment.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f g : X.functionFieldˣ) :
    principalDivisorAddHom X (Additive.ofMul f + Additive.ofMul g) =
      principalDivisor X f + principalDivisor X g := by
  rw [map_add, principalDivisorAddHom_ofMul, principalDivisorAddHom_ofMul]

-- Inverse image operations on actual integral supports are proved for arbitrary schemes.
example {X Y : Scheme} (e : X ≅ Y) (Z : IntegralClosedSubscheme X) :
    closedImageSubscheme e.inv (closedImageSubscheme e.hom Z) = Z := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact (closedImageSubschemeEquiv e).left_inv Z

-- The already-defined pushforward preserves all-cycle coefficients over any semiring.
example {X Y : Scheme} (R : Type) [Semiring R] (e : X ≅ Y)
    (c : Cycles X R) (Z : IntegralClosedSubscheme X) (W : IntegralClosedSubscheme Y) :
    closedImmersionPushforward R e.hom c (closedImageSubscheme e.hom Z) = c Z ∧
      closedImmersionPushforward R e.hom c W = c (closedImageSubscheme e.inv W) := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact ⟨closedImmersionPushforward_iso_apply_image R e c Z,
    closedImmersionPushforward_iso_apply R e c W⟩

-- A pushed principal cycle keeps its signed coefficient at the actual image support.
example {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (e : X ≅ Y) (f : X.functionFieldˣ) (Z : PrimeDivisor X) :
    closedImmersionPushforward ℤ e.hom (principalDivisor X f)
      (closedImageSubscheme e.hom Z.val) = primeDivisorOrder X Z f := by
  rw [closedImmersionPushforward_iso_apply_image, principalDivisor_apply_prime]

-- Rational functions pull contravariantly while the same integral cycle pushes forward.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [CompactSpace X] [CompactSpace Y]
    (e : X ≅ Y) (f : Y.functionFieldˣ) :
    closedImmersionPushforward ℤ e.hom
        (principalDivisor X (Units.map (functionFieldEquiv e).toMonoidHom f)) =
      principalDivisor Y f :=
  principalDivisor_iso e f

-- The existing open-restriction map gives the same contravariant principal divisor.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [CompactSpace X] [CompactSpace Y]
    (e : X ≅ Y) (f : Y.functionFieldˣ) :
    openRestriction ℤ e.hom (principalDivisor Y f) =
      principalDivisor X (Units.map (functionFieldEquiv e).toMonoidHom f) :=
  openRestriction_principalDivisor e f

-- Inversion retains the negative sign through the actual scheme/cycle comparison.
example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [CompactSpace X] [CompactSpace Y]
    (e : X ≅ Y) (f : Y.functionFieldˣ) :
    closedImmersionPushforward ℤ e.hom
        (principalDivisor X (Units.map (functionFieldEquiv e).toMonoidHom f⁻¹)) =
      -principalDivisor Y f := by
  rw [principalDivisor_iso, principalDivisor_inv]

-- Apply whole-cycle transport to the actual support-to-image isomorphism.
-- Only the support composite is closed; the ambient morphism need not be closed or proper.
example {X Y : Scheme} (f : X ⟶ Y) (Z : IntegralClosedSubscheme X)
    [IsClosedImmersion (Z.val.subschemeι ≫ f)]
    [IsLocallyNoetherian Z.val.subscheme] [CompactSpace Z.val.subscheme] :
    letI := Z.property
    letI := closedImageSubscheme_isIntegral f Z
    letI : IsLocallyNoetherian (Z.val.map f).subscheme :=
      isLocallyNoetherian_of_isOpenImmersion (closedImageSubschemeIso f Z).inv
    letI : CompactSpace (Z.val.map f).subscheme :=
      (Scheme.homeoOfIso (closedImageSubschemeIso f Z)).compactSpace
    ∀ g : (Z.val.map f).subscheme.functionFieldˣ,
      closedImmersionPushforward ℤ (closedImageSubschemeIso f Z).hom
          (principalDivisor Z.val.subscheme
            (Units.map (functionFieldEquiv (closedImageSubschemeIso f Z)).toMonoidHom g)) =
        principalDivisor (Z.val.map f).subscheme g := by
  letI := Z.property
  letI := closedImageSubscheme_isIntegral f Z
  letI : IsLocallyNoetherian (Z.val.map f).subscheme :=
    isLocallyNoetherian_of_isOpenImmersion (closedImageSubschemeIso f Z).inv
  letI : CompactSpace (Z.val.map f).subscheme :=
    (Scheme.homeoOfIso (closedImageSubschemeIso f Z)).compactSpace
  intro g
  fail_if_success
    have : IsClosedImmersion f := inferInstance
  fail_if_success
    have : IsProper f := inferInstance
  exact principalDivisor_iso (closedImageSubschemeIso f Z) g

end PrincipalDivisorRegressions

-- SP39: explicit dimension functions and homogeneous existing finite cycles.
#check HodgeConjecture.SchemeCycles.DimensionFunction
#check HodgeConjecture.SchemeCycles.DimensionFunction.strictMono
#check HodgeConjecture.SchemeCycles.DimensionFunction.map_covBy
#check HodgeConjecture.SchemeCycles.supportDegree_primeDivisor
#check HodgeConjecture.SchemeCycles.DimensionFunction.comapClosedImmersion
#check HodgeConjecture.SchemeCycles.cyclesOfDegree
#check HodgeConjecture.SchemeCycles.principalDivisor_mem_cyclesOfDegree
#check HodgeConjecture.SchemeCycles.principalDivisor_closedSupport_mem_cyclesOfDegree

#print axioms HodgeConjecture.SchemeCycles.DimensionFunction
#print axioms HodgeConjecture.SchemeCycles.supportDegree
#print axioms HodgeConjecture.SchemeCycles.primeDivisor_covBy_genericPoint
#print axioms HodgeConjecture.SchemeCycles.supportDegree_primeDivisor
#print axioms HodgeConjecture.SchemeCycles.supportDegree_closedImageSubscheme
#print axioms HodgeConjecture.SchemeCycles.closedImmersion_covBy
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.comapClosedImmersion
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.comapClosedImmersion_apply
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.comapClosedImmersion_id
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.comapClosedImmersion_comp
#print axioms HodgeConjecture.SchemeCycles.supportDegree_comapClosedImmersion
#print axioms HodgeConjecture.SchemeCycles.cyclesOfDegree
#print axioms HodgeConjecture.SchemeCycles.mem_cyclesOfDegree_iff
#print axioms HodgeConjecture.SchemeCycles.single_mem_cyclesOfDegree
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_cyclesOfDegree
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_cyclesOfDegree_iff
#print axioms HodgeConjecture.SchemeCycles.cyclesOfDegree_disjoint
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_mem_cyclesOfDegree
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_mem_cyclesOfDegree
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_mem_cyclesOfDegree_comap
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree
#print axioms HodgeConjecture.SchemeCycles.principalDivisor_closedSupport_mem_cyclesOfDegree

noncomputable section DimensionFunctionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory TopologicalSpace
open HodgeConjecture.SchemeCycles

-- Both conditions are retained on arbitrary schemes, not just the unit step on covers.
example (X : Scheme) (δ : DimensionFunction X) :
    StrictMono (fun x : X ↦ δ x) ∧ ∀ x y : X, x ⋖ y → δ y = δ x + 1 :=
  ⟨δ.strictMono, fun _ _ h ↦ δ.map_covBy h⟩

-- Actual codimension one gives an immediate specialization without Noetherianity.
example (X : Scheme) [IsIntegral X] (Z : PrimeDivisor X) :
    ambientGenericPoint Z.val ⋖ genericPoint X := by
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact primeDivisor_covBy_genericPoint X Z

-- The shift is minus one in the supplied dimension function, not absolute dimension.
example (X : Scheme) [IsIntegral X] (δ : DimensionFunction X) (Z : PrimeDivisor X) :
    supportDegree δ Z.val = δ (genericPoint X) - 1 := by
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  exact supportDegree_primeDivisor δ Z

-- Restriction is evaluation on the actual closed-immersion point map.
example {X Y : Scheme} (δ : DimensionFunction Y) (i : X ⟶ Y)
    [IsClosedImmersion i] (x : X) : δ.comapClosedImmersion i x = δ (i.base x) := by
  fail_if_success
    have : IsIntegral Y := inferInstance
  fail_if_success
    have : IsLocallyNoetherian Y := inferInstance
  exact DimensionFunction.comapClosedImmersion_apply δ i x

-- Actual identity and composition give literal restriction identities.
example {X Y Z : Scheme} (δ : DimensionFunction Z) (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    δ.comapClosedImmersion (𝟙 Z) = δ ∧
      (δ.comapClosedImmersion j).comapClosedImmersion i =
        δ.comapClosedImmersion (i ≫ j) :=
  ⟨DimensionFunction.comapClosedImmersion_id Z δ,
    DimensionFunction.comapClosedImmersion_comp δ i j⟩

-- Restriction compares degrees of actual image supports, not their ambient codimensions.
example {X Y : Scheme} (δ : DimensionFunction Y) (i : X ⟶ Y)
    [IsClosedImmersion i] (W : IntegralClosedSubscheme X) :
    supportDegree (δ.comapClosedImmersion i) W =
      supportDegree δ (closedImageSubscheme i W) :=
  supportDegree_comapClosedImmersion δ i W

-- The homogeneous object is a supported submodule of the original cycle module.
example (X : Scheme) (R : Type) [Semiring R] (δ : DimensionFunction X) (n : ℤ) :
    (cyclesOfDegree R δ n : Submodule R (Cycles X R)) =
      Finsupp.supported R R {W : IntegralClosedSubscheme X | supportDegree δ W = n} := rfl

-- Distinct degrees are disjoint over arbitrary, possibly trivial, coefficient semirings.
example (X : Scheme) (R : Type) [Semiring R] (δ : DimensionFunction X)
    (n m : ℤ) (hnm : n ≠ m) :
    Disjoint (cyclesOfDegree R δ n) (cyclesOfDegree R δ m) :=
  cyclesOfDegree_disjoint R δ n m hnm

-- With trivial coefficients the fundamental cycle is zero and belongs to every degree.
example (X : Scheme) (R : Type) [Semiring R] [Subsingleton R]
    (δ : DimensionFunction X) (W : IntegralClosedSubscheme X) (n : ℤ) :
    fundamentalCycle R W ∈ cyclesOfDegree R δ n := by
  have hzero : fundamentalCycle R W = 0 := Subsingleton.elim _ _
  rw [hzero]
  exact (cyclesOfDegree R δ n).zero_mem

-- Detecting the degree from a fundamental cycle explicitly requires nontrivial coefficients.
example (X : Scheme) (R : Type) [Semiring R] [Nontrivial R]
    (δ : DimensionFunction X) (W : IntegralClosedSubscheme X) (n : ℤ) :
    fundamentalCycle R W ∈ cyclesOfDegree R δ n ↔ supportDegree δ W = n :=
  fundamentalCycle_mem_cyclesOfDegree_iff R δ n W

-- The existing principal cycle is homogeneous in the chosen dimension function.
example (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (δ : DimensionFunction X) (f : X.functionFieldˣ) :
    principalDivisor X f ∈ cyclesOfDegree ℤ δ (δ (genericPoint X) - 1) :=
  principalDivisor_mem_cyclesOfDegree δ f

-- Actual restricted degree suffices for closed pushforward, with no supplied comparison law.
example {X Y : Scheme} (R : Type) [Semiring R] (δ : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i] (n : ℤ) (c : Cycles X R)
    (hc : c ∈ cyclesOfDegree R (δ.comapClosedImmersion i) n) :
    closedImmersionPushforward R i c ∈ cyclesOfDegree R δ n := by
  fail_if_success
    have : IsIntegral Y := inferInstance
  fail_if_success
    have : IsLocallyNoetherian Y := inferInstance
  exact closedImmersionPushforward_mem_cyclesOfDegree_comap R δ i n c hc

-- Only the integral source of the principal divisor needs Noetherianity and compactness.
example {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (f : X.functionFieldˣ) :
    closedImmersionPushforward ℤ i (principalDivisor X f) ∈
      cyclesOfDegree ℤ δ (δ (i.base (genericPoint X)) - 1) := by
  fail_if_success
    have : IsIntegral Y := inferInstance
  exact closedImmersionPushforward_principalDivisor_mem_cyclesOfDegree δ i f

-- An actual closed relation carrier supplies a homogeneous ambient cycle on any ambient scheme.
example (X : Scheme) (δ : DimensionFunction X) (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ∀ f : W.val.subscheme.functionFieldˣ,
    closedImmersionPushforward ℤ W.val.subschemeι (principalDivisor W.val.subscheme f) ∈
      cyclesOfDegree ℤ δ (supportDegree δ W - 1) := by
  letI := W.property
  intro f
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsLocallyNoetherian X := inferInstance
  fail_if_success
    have : CompactSpace X := inferInstance
  exact principalDivisor_closedSupport_mem_cyclesOfDegree δ W f

-- Nonvacuous example: Spec of a field has an actual point and admits the constant-zero function.
-- Both dimension-function fields are constructed, not supplied as additional inputs.
example (K : Type) [Field K] :
    ∃ δ : DimensionFunction (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))),
      ∃ x : Scheme.Spec.obj (Opposite.op (CommRingCat.of K)), δ x = 0 := by
  let X : Scheme := Scheme.Spec.obj (Opposite.op (CommRingCat.of K))
  letI : Subsingleton X := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let δ : DimensionFunction X :=
    { toFun := fun _ ↦ 0
      strictMono := fun x y h ↦ False.elim (h.ne (Subsingleton.elim x y))
      map_covBy := fun {x y} h ↦ False.elim (h.lt.ne (Subsingleton.elim x y)) }
  exact ⟨δ, (show X from (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum K)), rfl⟩

-- The generic-point degree formula also applies when only the support composite is closed.
example {X Y : Scheme} (δ : DimensionFunction Y) (f : X ⟶ Y)
    (W : IntegralClosedSubscheme X) [IsClosedImmersion (W.val.subschemeι ≫ f)] :
    supportDegree δ (closedImageSubscheme f W) = δ (f.base (ambientGenericPoint W)) := by
  fail_if_success
    have : IsClosedImmersion f := inferInstance
  exact supportDegree_closedImageSubscheme δ f W

end DimensionFunctionRegressions

-- SP40: actual finite principal relations, their quotient, and geometric descent.
#check HodgeConjecture.SchemeCycles.ambientPrincipalDivisor
#check HodgeConjecture.SchemeCycles.PrincipalRelationData
#check HodgeConjecture.SchemeCycles.principalRelationData_family_locallyFinite_iff
#check HodgeConjecture.SchemeCycles.mem_principalRelations_iff_exists_list
#check HodgeConjecture.SchemeCycles.ChowGroup
#check HodgeConjecture.SchemeCycles.classMap_eq_iff
#check HodgeConjecture.SchemeCycles.PrincipalRelationData.closedImage
#check HodgeConjecture.SchemeCycles.chowClosedImmersionPushforward
#check HodgeConjecture.SchemeCycles.chowIsoEquiv
#check HodgeConjecture.SchemeCycles.gradedIsoEquiv_symm_val

#print axioms HodgeConjecture.SchemeCycles.idealSubscheme_isLocallyNoetherian
#print axioms HodgeConjecture.SchemeCycles.idealSubscheme_compactSpace
#print axioms HodgeConjecture.SchemeCycles.ambientPrincipalDivisor
#print axioms HodgeConjecture.SchemeCycles.ambientPrincipalDivisor_mul
#print axioms HodgeConjecture.SchemeCycles.closedImmersionPushforward_ambientPrincipalDivisor
#print axioms HodgeConjecture.SchemeCycles.exists_ambientPrincipalDivisor_image
#print axioms HodgeConjecture.SchemeCycles.gradedClosedImmersionPushforward
#print axioms HodgeConjecture.SchemeCycles.gradedClosedImmersionPushforward_id
#print axioms HodgeConjecture.SchemeCycles.gradedClosedImmersionPushforward_comp
#print axioms HodgeConjecture.SchemeCycles.idealSubscheme_isNoetherian
#print axioms HodgeConjecture.SchemeCycles.PrincipalRelationData
#print axioms HodgeConjecture.SchemeCycles.PrincipalRelationData.zpow
#print axioms HodgeConjecture.SchemeCycles.principalRelationData_family_locallyFinite_iff
#print axioms HodgeConjecture.SchemeCycles.principalRelation
#print axioms HodgeConjecture.SchemeCycles.principalRelation_zpow
#print axioms HodgeConjecture.SchemeCycles.principalRelations
#print axioms HodgeConjecture.SchemeCycles.mem_principalRelations_iff_exists_list
#print axioms HodgeConjecture.SchemeCycles.RationallyEquivalent
#print axioms HodgeConjecture.SchemeCycles.rationallyEquivalent_iff_exists_list
#print axioms HodgeConjecture.SchemeCycles.ChowGroup
#print axioms HodgeConjecture.SchemeCycles.classMap
#print axioms HodgeConjecture.SchemeCycles.classMap_eq_iff
#print axioms HodgeConjecture.SchemeCycles.classMap_eq_zero_iff
#print axioms HodgeConjecture.SchemeCycles.classMap_principalRelation
#print axioms HodgeConjecture.SchemeCycles.PrincipalRelationData.closedImage
#print axioms HodgeConjecture.SchemeCycles.gradedClosedImmersionPushforward_principalRelation
#print axioms HodgeConjecture.SchemeCycles.principalRelations_le_comap_closedImmersionPushforward
#print axioms HodgeConjecture.SchemeCycles.chowClosedImmersionPushforward
#print axioms HodgeConjecture.SchemeCycles.chowClosedImmersionPushforward_classMap
#print axioms HodgeConjecture.SchemeCycles.chowClosedImmersionPushforward_restricted_classMap
#print axioms HodgeConjecture.SchemeCycles.chowClosedImmersionPushforward_id
#print axioms HodgeConjecture.SchemeCycles.chowClosedImmersionPushforward_comp
#print axioms HodgeConjecture.SchemeCycles.gradedIsoEquiv
#print axioms HodgeConjecture.SchemeCycles.gradedIsoEquiv_val
#print axioms HodgeConjecture.SchemeCycles.gradedIsoEquiv_symm_val
#print axioms HodgeConjecture.SchemeCycles.principalRelations_map_gradedIsoEquiv
#print axioms HodgeConjecture.SchemeCycles.chowIsoEquiv
#print axioms HodgeConjecture.SchemeCycles.chowIsoEquiv_classMap
#print axioms HodgeConjecture.SchemeCycles.chowIsoEquiv_symm_classMap
#print axioms HodgeConjecture.SchemeCycles.chowIsoEquiv_toLinearMap

noncomputable section PrincipalRelationsRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- Closed carriers inherit Noetherianity from the actual affine quotient construction.
example (X : Scheme) [IsNoetherian X] (I : X.IdealSheafData) :
    IsNoetherian I.subscheme := by
  fail_if_success
    have : IsIntegral X := inferInstance
  infer_instance

-- Ambient principal cycles use only the actual carrier's finiteness properties.
example {X : Scheme} (W : IntegralClosedSubscheme X)
    [IsLocallyNoetherian W.val.subscheme] [CompactSpace W.val.subscheme] :
    letI := W.property
    ∀ f g : W.val.subscheme.functionFieldˣ,
      ambientPrincipalDivisor W (f * g) =
          ambientPrincipalDivisor W f + ambientPrincipalDivisor W g ∧
        ambientPrincipalDivisor W f⁻¹ = -ambientPrincipalDivisor W f ∧
        ambientPrincipalDivisor W (1 : W.val.subscheme.functionFieldˣ) = 0 := by
  letI := W.property
  intro f g
  exact ⟨ambientPrincipalDivisor_mul W f g,
    ambientPrincipalDivisor_inv W f, ambientPrincipalDivisor_one W⟩

-- Local finiteness is tested on actual carrier supports, with no Noetherianity needed.
example (X : Scheme) [CompactSpace X] {ι : Type}
    (δ : DimensionFunction X) (n : ℤ) (d : ι → PrincipalRelationData δ n) :
    LocallyFinite (fun i ↦ ((d i).1.val.val.support : Set X)) ↔ Finite ι := by
  fail_if_success
    have : IsNoetherian X := inferInstance
  exact principalRelationData_family_locallyFinite_iff δ n d

-- Even when every principal cycle is zero, an infinitely repeated nonempty carrier
-- is not a locally finite carrier family. No divisor-support surrogate is used.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (d : PrincipalRelationData δ n) :
    (∀ k : ℕ, principalRelation δ n ((fun _ : ℕ ↦ d.zpow 0) k) = 0) ∧
      ¬ LocallyFinite (fun k : ℕ ↦ (((fun _ : ℕ ↦ d.zpow 0) k).1.val.val.support : Set X)) := by
  constructor
  · intro k
    simpa only [zero_smul] using principalRelation_zpow δ n d 0
  · intro h
    letI : Finite ℕ :=
      (principalRelationData_family_locallyFinite_iff δ n (fun _ : ℕ ↦ d.zpow 0)).mp h
    exact not_finite ℕ

-- A homogeneous generator is literally the existing ambient principal divisor.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (d : PrincipalRelationData δ n) :
    letI := d.1.val.property
    (principalRelation δ n d : Cycles X ℤ) = ambientPrincipalDivisor d.1.val d.2 :=
  principalRelation_coe δ n d

-- Negative integer weights are absorbed into actual inverse powers of the same function.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (d : PrincipalRelationData δ n) :
    principalRelation δ n (d.zpow (-3)) = (-3 : ℤ) • principalRelation δ n d :=
  principalRelation_zpow δ n d (-3)

-- The relation span equals unweighted finite sums of actual relation data.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    c ∈ principalRelations δ n ↔
      ∃ l : List (PrincipalRelationData δ n), (l.map (principalRelation δ n)).sum = c :=
  mem_principalRelations_iff_exists_list δ n c

-- Rational equivalence uses that same finite-sum difference criterion.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (c e : cyclesOfDegree ℤ δ n) :
    RationallyEquivalent δ n c e ↔
      ∃ l : List (PrincipalRelationData δ n), (l.map (principalRelation δ n)).sum = c - e :=
  rationallyEquivalent_iff_exists_list δ n c e

-- Quotient equality and the zero class detect precisely the actual relation submodule.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (c e : cyclesOfDegree ℤ δ n) :
    (classMap δ n c = classMap δ n e ↔ RationallyEquivalent δ n c e) ∧
      (classMap δ n c = 0 ↔ c ∈ principalRelations δ n) :=
  ⟨classMap_eq_iff δ n c e, classMap_eq_zero_iff δ n c⟩

example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (d : PrincipalRelationData δ n) : classMap δ n (principalRelation δ n d) = 0 :=
  classMap_principalRelation δ n d

-- Every quotient element has a representative in the existing homogeneous cycle module.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)
    (q : ChowGroup δ n) : ∃ c : cyclesOfDegree ℤ δ n, classMap δ n c = q :=
  classMap_surjective δ n q

-- Relation data transport has the actual scheme-theoretic image as its carrier.
example {X Y : Scheme} (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (d : PrincipalRelationData δX n) :
    (d.closedImage δX δY i hdeg n).1.val = closedImageSubscheme i d.1.val := rfl

-- The actual geometric principal-divisor identity supplies generator preservation.
example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (d : PrincipalRelationData δX n) :
    gradedClosedImmersionPushforward δX δY i hdeg n (principalRelation δX n d) =
      principalRelation δY n (d.closedImage δX δY i hdeg n) :=
  gradedClosedImmersionPushforward_principalRelation δX δY i hdeg n d

-- Preservation of the entire relation submodule is proved, not supplied as an input.
example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δX : DimensionFunction X) (δY : DimensionFunction Y)
    (i : X ⟶ Y) [IsClosedImmersion i]
    (hdeg : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (n : ℤ) (c : cyclesOfDegree ℤ δX n) (hc : c ∈ principalRelations δX n) :
    gradedClosedImmersionPushforward δX δY i hdeg n c ∈ principalRelations δY n :=
  principalRelations_le_comap_closedImmersionPushforward δX δY i hdeg n hc

-- Canonical dimension restriction gives the quotient square without a comparison hypothesis.
example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (i : X ⟶ Y) [IsClosedImmersion i]
    (n : ℤ) (c : cyclesOfDegree ℤ (δ.comapClosedImmersion i) n) :
    chowClosedImmersionPushforward (δ.comapClosedImmersion i) δ i
        (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n
        (classMap (δ.comapClosedImmersion i) n c) =
      classMap δ n (gradedClosedImmersionPushforward (δ.comapClosedImmersion i) δ i
        (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n c) :=
  chowClosedImmersionPushforward_restricted_classMap δ i n c

-- The identity acts identically on quotient classes, using the actual degree formula.
example (X : Scheme) [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ) :
    chowClosedImmersionPushforward δ δ (𝟙 X)
      (fun W ↦ supportDegree_closedImageSubscheme δ (𝟙 X) W) n = LinearMap.id :=
  chowClosedImmersionPushforward_id X δ _ n

-- Composition is inherited by the quotient from the existing closed cycle maps.
example {X Y Z : Scheme} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (δX : DimensionFunction X) (δY : DimensionFunction Y) (δZ : DimensionFunction Z)
    (i : X ⟶ Y) (j : Y ⟶ Z) [IsClosedImmersion i] [IsClosedImmersion j]
    (hi : ∀ W : IntegralClosedSubscheme X,
      supportDegree δY (closedImageSubscheme i W) = supportDegree δX W)
    (hj : ∀ W : IntegralClosedSubscheme Y,
      supportDegree δZ (closedImageSubscheme j W) = supportDegree δY W)
    (hij : ∀ W : IntegralClosedSubscheme X,
      supportDegree δZ (closedImageSubscheme (i ≫ j) W) = supportDegree δX W)
    (n : ℤ) :
    (chowClosedImmersionPushforward δY δZ j hj n).comp
      (chowClosedImmersionPushforward δX δY i hi n) =
        chowClosedImmersionPushforward δX δZ (i ≫ j) hij n :=
  chowClosedImmersionPushforward_comp δX δY δZ i j hi hj hij n

-- Before quotienting, the graded inverse is the existing geometric open restriction.
example {X Y : Scheme} (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    ((gradedIsoEquiv δ e n).symm c).val = openRestriction ℤ e.hom c.val := by
  fail_if_success
    have : IsNoetherian X := inferInstance
  exact gradedIsoEquiv_symm_val δ e n c

example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ (δ.comapClosedImmersion e.hom) n) :
    chowIsoEquiv δ e n (classMap (δ.comapClosedImmersion e.hom) n c) =
      classMap δ n (gradedIsoEquiv δ e n c) :=
  chowIsoEquiv_classMap δ e n c

-- The inverse representative square explicitly retains the same open-restriction map.
example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (c : cyclesOfDegree ℤ δ n) :
    (chowIsoEquiv δ e n).symm (classMap δ n c) =
        classMap (δ.comapClosedImmersion e.hom) n ((gradedIsoEquiv δ e n).symm c) ∧
      ((gradedIsoEquiv δ e n).symm c).val = openRestriction ℤ e.hom c.val :=
  ⟨chowIsoEquiv_symm_classMap δ e n c, gradedIsoEquiv_symm_val δ e n c⟩

-- Actual scheme isomorphisms yield inverse maps on all quotient classes.
example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ)
    (q : ChowGroup (δ.comapClosedImmersion e.hom) n) (r : ChowGroup δ n) :
    (chowIsoEquiv δ e n).symm (chowIsoEquiv δ e n q) = q ∧
      chowIsoEquiv δ e n ((chowIsoEquiv δ e n).symm r) = r :=
  ⟨(chowIsoEquiv δ e n).symm_apply_apply q, (chowIsoEquiv δ e n).apply_symm_apply r⟩

-- The quotient isomorphism's forward map is not a second pushforward assignment.
example {X Y : Scheme} [IsNoetherian X] [IsNoetherian Y]
    (δ : DimensionFunction Y) (e : X ≅ Y) (n : ℤ) :
    (chowIsoEquiv δ e n).toLinearMap =
      chowClosedImmersionPushforward (δ.comapClosedImmersion e.hom) δ e.hom
        (fun W ↦ (supportDegree_comapClosedImmersion δ e.hom W).symm) n :=
  chowIsoEquiv_toLinearMap δ e n

end PrincipalRelationsRegressions

-- SP41: actual finite geometric dimension and constructed low-dimensional grading.
#check HodgeConjecture.SchemeCycles.integralSubschemePointOrderIso
#check HodgeConjecture.SchemeCycles.ambientGenericPoint_height_eq_supportDim
#check HodgeConjecture.SchemeCycles.ringKrullDim_lt_top_of_finiteType
#check HodgeConjecture.SchemeCycles.topologicalKrullDim_lt_top_of_finiteType
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofKrullDimLEOne
#check HodgeConjecture.SchemeCycles.supportDegree_ofKrullDimLEOne_eq_iff
#check HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofKrullDimLEOne_iff
#check HodgeConjecture.SchemeCycles.Examples.affineLineDimensionFunction

#print axioms HodgeConjecture.SchemeCycles.integralSubschemePointOrderIso
#print axioms HodgeConjecture.SchemeCycles.integralSubschemePointOrderIso_val
#print axioms HodgeConjecture.SchemeCycles.topologicalKrullDim_eq_pointKrullDim
#print axioms HodgeConjecture.SchemeCycles.genericPoint_height_eq_topologicalKrullDim
#print axioms HodgeConjecture.SchemeCycles.ambientGenericPoint_height_eq_supportDim
#print axioms HodgeConjecture.SchemeCycles.point_height_eq_supportDim
#print axioms HodgeConjecture.SchemeCycles.point_height_ne_top
#print axioms HodgeConjecture.SchemeCycles.point_height_toNat_eq
#print axioms HodgeConjecture.SchemeCycles.point_height_toNat_strictMono
#print axioms HodgeConjecture.SchemeCycles.polynomialDimensionBound
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_ringKrullDim_le_bound
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_le_bound_of_surjective
#print axioms HodgeConjecture.SchemeCycles.exists_ringKrullDim_le_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_lt_top_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.finiteRingKrullDim_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.spec_topologicalKrullDim_lt_top_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.quotientSpec_topologicalKrullDim_lt_top_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.affine_topologicalKrullDim_lt_top_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.point_coheight_eq_of_isOpenImmersion
#print axioms HodgeConjecture.SchemeCycles.topologicalKrullDim_lt_top_of_finite_openCover
#print axioms HodgeConjecture.SchemeCycles.affine_topologicalKrullDim_lt_top_of_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.topologicalKrullDim_lt_top_of_compact_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.topologicalKrullDim_lt_top_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.point_height_le_one
#print axioms HodgeConjecture.SchemeCycles.point_height_eq_zero_and_eq_one_of_lt
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofKrullDimLEOne
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofKrullDimLEOne_apply
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofKrullDimLEOne_nonneg
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofKrullDimLEOne_eq_zero_or_eq_one
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofKrullDimLEOne_values_of_lt
#print axioms HodgeConjecture.SchemeCycles.supportDegree_ofKrullDimLEOne_eq_iff
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofKrullDimLEOne_iff
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLine
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLine_dimension
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLineDimensionFunction
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLineDimensionFunction_genericPoint
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLineOriginIdeal_isMaximal
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLineOrigin
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLineOrigin_isClosed
#print axioms HodgeConjecture.SchemeCycles.Examples.affineLineDimensionFunction_origin

noncomputable section GeometricDimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles
open HodgeConjecture.SchemeCycles.Examples

-- The carrier/interval comparison retains the literal closed-inclusion point map.
example {X : Scheme} (W : IntegralClosedSubscheme X) (x : W.val.subscheme) :
    (integralSubschemePointOrderIso W x).val = W.val.subschemeι.base x := rfl

-- This is dimension of the actual carrier, with no ambient integrality or Noetherianity.
example {X : Scheme} (W : IntegralClosedSubscheme X) :
    (Order.height (ambientGenericPoint W) : WithBot ℕ∞) =
      topologicalKrullDim W.val.subscheme := by
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : IsNoetherian X := inferInstance
  exact ambientGenericPoint_height_eq_supportDim W

example (X : Scheme) (x : X) :
    (Order.height x : WithBot ℕ∞) =
      topologicalKrullDim (pointSupport X x).val.subscheme :=
  point_height_eq_supportDim X x

-- Finite dimension proves strict monotonicity, without an immediate-step premise.
example (X : Scheme) (h : topologicalKrullDim X < ⊤) :
    StrictMono (fun x : X ↦ ((Order.height x).toNat : ℤ)) :=
  point_height_toNat_strictMono X h

-- The zero-variable bound comes from the field's actual dimension.
example (k : Type) [Field k] :
    ringKrullDim (MvPolynomial (Fin 0) k) ≤ 0 := by
  simpa only [polynomialDimensionBound, Nat.cast_zero] using
    mvPolynomial_ringKrullDim_le_bound k 0

-- Three variables give the proved upper bound seven, not a claimed sharp formula.
example (k : Type) [Field k] :
    ringKrullDim (MvPolynomial (Fin 3) k) ≤ 7 := by
  simpa [polynomialDimensionBound] using mvPolynomial_ringKrullDim_le_bound k 3

-- The finite bound does not require a domain or even a nontrivial target algebra.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A ≤ n := by
  fail_if_success
    have : Nontrivial A := inferInstance
  fail_if_success
    have : IsDomain A := inferInstance
  exact exists_ringKrullDim_le_of_finiteType k A

-- Only the nonempty finite-dimensional-order package adds nontriviality.
example (k A : Type) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] : FiniteRingKrullDim A :=
  finiteRingKrullDim_of_finiteType k A

-- The quotient by the unit ideal is genuinely empty, but still has dimension below infinity.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    topologicalKrullDim (Spec (CommRingCat.of (A ⧸ (⊤ : Ideal A)))) = ⊥ ∧
      topologicalKrullDim (Spec (CommRingCat.of (A ⧸ (⊤ : Ideal A)))) < ⊤ := by
  constructor
  · change topologicalKrullDim (PrimeSpectrum (A ⧸ (⊤ : Ideal A))) = ⊥
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact ringKrullDim_eq_bot_of_subsingleton
  · exact quotientSpec_topologicalKrullDim_lt_top_of_finiteType k A ⊤

-- The actual structural morphism supplies all finite-generation data on affine charts.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [QuasiCompact p] :
    topologicalKrullDim X < ⊤ :=
  topologicalKrullDim_lt_top_of_finiteType k X p

-- Globalization uses an actual finite open cover and needs no integral ambient scheme.
example (X : Scheme) (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    (h𝒰 : ∀ i, topologicalKrullDim (𝒰.X i) < ⊤) :
    topologicalKrullDim X < ⊤ := by
  fail_if_success
    have : IsIntegral X := inferInstance
  exact topologicalKrullDim_lt_top_of_finite_openCover 𝒰 h𝒰

-- Both dimension-function conditions are outputs of the proved low-dimensional construction.
example (X : Scheme) (h : topologicalKrullDim X ≤ 1) :
    StrictMono (DimensionFunction.ofKrullDimLEOne X h) ∧
      ∀ {x y : X}, x ⋖ y →
        DimensionFunction.ofKrullDimLEOne X h y =
          DimensionFunction.ofKrullDimLEOne X h x + 1 :=
  ⟨(DimensionFunction.ofKrullDimLEOne X h).strictMono,
    (DimensionFunction.ofKrullDimLEOne X h).map_covBy⟩

example (X : Scheme) (h : topologicalKrullDim X ≤ 1) (x : X) :
    0 ≤ DimensionFunction.ofKrullDimLEOne X h x ∧
      (DimensionFunction.ofKrullDimLEOne X h x = 0 ∨
        DimensionFunction.ofKrullDimLEOne X h x = 1) :=
  ⟨DimensionFunction.ofKrullDimLEOne_nonneg X h x,
    DimensionFunction.ofKrullDimLEOne_eq_zero_or_eq_one X h x⟩

-- The existing support degree is now the dimension of the actual closed scheme.
example {X : Scheme} (h : topologicalKrullDim X ≤ 1)
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofKrullDimLEOne X h) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  supportDegree_ofKrullDimLEOne_eq_iff h W n

example {X : Scheme} (R : Type) [Semiring R] [Nontrivial R]
    (h : topologicalKrullDim X ≤ 1) (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofKrullDimLEOne X h) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  fundamentalCycle_mem_ofKrullDimLEOne_iff R h W n

-- With trivial coefficients every fundamental cycle is zero: no dimension converse is inferred.
example {X : Scheme} (R : Type) [Semiring R] [Subsingleton R]
    (h : topologicalKrullDim X ≤ 1) (W : IntegralClosedSubscheme X) (n : ℤ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofKrullDimLEOne X h) n := by
  have hz : fundamentalCycle R W = 0 := Subsingleton.elim _ _
  rw [hz]
  exact Submodule.zero_mem _

-- The constructor works without Noetherianity or integrality, and strict pairs have exact values.
example (X : Scheme) (h : topologicalKrullDim X ≤ 1) {x y : X} (hxy : x < y) :
    DimensionFunction.ofKrullDimLEOne X h x = 0 ∧
      DimensionFunction.ofKrullDimLEOne X h y = 1 := by
  fail_if_success
    have : IsNoetherian X := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  exact DimensionFunction.ofKrullDimLEOne_values_of_lt X h hxy

-- Nonvacuous geometry: Spec k[T] has dimension one, generic degree one and origin degree zero.
example (k : Type) [Field k] :
    topologicalKrullDim (affineLine k) = 1 ∧
      affineLineDimensionFunction k (genericPoint (affineLine k)) = 1 ∧
      affineLineDimensionFunction k (affineLineOrigin k) = 0 :=
  ⟨affineLine_dimension k, affineLineDimensionFunction_genericPoint k,
    affineLineDimensionFunction_origin k⟩

-- The origin is the actual constant-coefficient kernel, not an auxiliary label.
example (k : Type) [Field k] :
    (affineLineOrigin k).asIdeal =
      RingHom.ker (Polynomial.constantCoeff : Polynomial k →+* k) := rfl

-- Existing cycle grading specializes to the actual generic carrier and actual origin.
example (k : Type) [Field k] :
    fundamentalCycle ℤ (pointSupport (affineLine k) (genericPoint (affineLine k))) ∈
        cyclesOfDegree ℤ (affineLineDimensionFunction k) 1 ∧
      fundamentalCycle ℤ (pointSupport (affineLine k) (affineLineOrigin k)) ∈
        cyclesOfDegree ℤ (affineLineDimensionFunction k) 0 := by
  constructor
  · apply fundamentalCycle_mem_cyclesOfDegree
    simpa only [supportDegree, ambientGenericPoint_pointSupport] using
      affineLineDimensionFunction_genericPoint k
  · apply fundamentalCycle_mem_cyclesOfDegree
    simpa only [supportDegree, ambientGenericPoint_pointSupport] using
      affineLineDimensionFunction_origin k

-- This is the existing Chow quotient on the actual affine line, with no supplied δ.
example (k : Type) [Field k]
    (c : cyclesOfDegree ℤ (affineLineDimensionFunction k) 0) :
    (classMap (affineLineDimensionFunction k) 0 c :
        ChowGroup (affineLineDimensionFunction k) 0) = 0 ↔
      ∃ l : List (PrincipalRelationData (affineLineDimensionFunction k) 0),
        (l.map (principalRelation (affineLineDimensionFunction k) 0)).sum = c :=
  (classMap_eq_zero_iff _ _ c).trans (mem_principalRelations_iff_exists_list _ _ c)

-- The degree-one actual generic carrier supplies real relation data; its unit function
-- has zero principal cycle and zero class, using no assumed grading laws.
example (k : Type) [Field k] :
    ∃ d : PrincipalRelationData (affineLineDimensionFunction k) 0,
      d.1.val = pointSupport (affineLine k) (genericPoint (affineLine k)) ∧
        principalRelation (affineLineDimensionFunction k) 0 d = 0 ∧
        classMap (affineLineDimensionFunction k) 0
          (principalRelation (affineLineDimensionFunction k) 0 d) = 0 := by
  let W := pointSupport (affineLine k) (genericPoint (affineLine k))
  have hW : supportDegree (affineLineDimensionFunction k) W = (0 : ℤ) + 1 := by
    simpa only [W, supportDegree, ambientGenericPoint_pointSupport, zero_add] using
      affineLineDimensionFunction_genericPoint k
  letI := W.property
  let d : PrincipalRelationData (affineLineDimensionFunction k) 0 := ⟨⟨W, hW⟩, 1⟩
  refine ⟨d, rfl, ?_, classMap_principalRelation _ _ d⟩
  apply Subtype.ext
  change ambientPrincipalDivisor W (1 : W.val.subscheme.functionFieldˣ) = 0
  exact ambientPrincipalDivisor_one W

end GeometricDimensionRegressions

-- SP42: sharp affine dimension from actual quotients, integral chains and normalization.
#check HodgeConjecture.SchemeCycles.trdeg_lt_of_surjective_of_not_injective
#check HodgeConjecture.SchemeCycles.exists_primeSeries_lift_of_injective_integral
#check HodgeConjecture.SchemeCycles.ringKrullDim_eq_of_injective_integral
#check HodgeConjecture.SchemeCycles.trdeg_eq_normalization_size
#check HodgeConjecture.SchemeCycles.ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType
#check HodgeConjecture.SchemeCycles.mvPolynomial_ringKrullDim_eq_card
#check HodgeConjecture.SchemeCycles.spec_pointSupport_dimension_eq_residueField_trdeg
#check HodgeConjecture.SchemeCycles.prime_residueField_trdeg_toNat_strictAnti

#print axioms HodgeConjecture.SchemeCycles.trdeg_lt_of_surjective_of_not_injective
#print axioms HodgeConjecture.SchemeCycles.primeQuotient_trdeg_strictAnti
#print axioms HodgeConjecture.SchemeCycles.primeQuotient_trdeg_toNat_strictAnti
#print axioms HodgeConjecture.SchemeCycles.integral_specComap_strictMono
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_le_of_integral
#print axioms HodgeConjecture.SchemeCycles.exists_primeSeries_lift_of_injective_integral
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_le_of_injective_integral
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_eq_of_injective_integral
#print axioms HodgeConjecture.SchemeCycles.trdeg_eq_normalization_size
#print axioms HodgeConjecture.SchemeCycles.normalization_size_le_ringKrullDim
#print axioms HodgeConjecture.SchemeCycles.trdeg_toNat_le_ringKrullDim_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.trdeg_eq_of_isFractionRing
#print axioms HodgeConjecture.SchemeCycles.trdeg_eq_fractionRing
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_le_trdeg_toNat_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_eq_trdeg_toNat_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_ringKrullDim_eq_card
#print axioms HodgeConjecture.SchemeCycles.spec_topologicalKrullDim_eq_trdeg_toNat_of_finiteType
#print axioms HodgeConjecture.SchemeCycles.prime_coheight_eq_quotientDim
#print axioms HodgeConjecture.SchemeCycles.spec_point_height_eq_prime_coheight
#print axioms HodgeConjecture.SchemeCycles.spec_pointSupport_dimension_eq_quotientDim
#print axioms HodgeConjecture.SchemeCycles.primeQuotient_trdeg_eq_residueField
#print axioms HodgeConjecture.SchemeCycles.spec_pointSupport_dimension_eq_residueField_trdeg
#print axioms HodgeConjecture.SchemeCycles.spec_point_height_toNat_eq_residueField_trdeg
#print axioms HodgeConjecture.SchemeCycles.prime_residueField_trdeg_toNat_strictAnti

noncomputable section AffineTranscendenceDimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- Finite transcendence degree suffices for a genuine proper domain quotient;
-- finite generation is not an additional input to this theorem.
example (k A B : Type) [Field k] [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Surjective f) (hn : ¬ Function.Injective f)
    (hfin : Algebra.trdeg k A < Cardinal.aleph0) :
    Algebra.trdeg k B < Algebra.trdeg k A := by
  fail_if_success
    have : Algebra.FiniteType k A := inferInstance
  exact trdeg_lt_of_surjective_of_not_injective k f hf hn hfin

-- Concrete proper quotient: evaluation at zero on the actual polynomial algebra.
example (k : Type) [Field k] :
    Algebra.trdeg k k < Algebra.trdeg k (Polynomial k) := by
  let f : Polynomial k →ₐ[k] k := Polynomial.aeval 0
  apply trdeg_lt_of_surjective_of_not_injective k f
  · intro a
    exact ⟨Polynomial.C a, by simp [f]⟩
  · intro h
    apply Polynomial.X_ne_zero (R := k)
    apply h
    simp [f]
  · exact trdeg_lt_aleph0 (R := k) (S := Polynomial k)

-- Actual prime quotients are domains even when their ambient algebra is not.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (p q : PrimeSpectrum A) (hpq : p < q) :
    Algebra.trdeg k (A ⧸ q.asIdeal) < Algebra.trdeg k (A ⧸ p.asIdeal) ∧
      (Algebra.trdeg k (A ⧸ q.asIdeal)).toNat < (Algebra.trdeg k (A ⧸ p.asIdeal)).toNat ∧
      ringKrullDim A ≤ ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  fail_if_success
    have : IsDomain A := inferInstance
  exact ⟨primeQuotient_trdeg_strictAnti k A hpq,
    primeQuotient_trdeg_toNat_strictAnti k A hpq,
    ringKrullDim_le_trdeg_toNat_of_finiteType k A⟩

-- Incomparability needs integrality but not injectivity of the algebra map.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (p q : PrimeSpectrum S) (hpq : p < q) :
    (algebraMap R S).specComap p < (algebraMap R S).specComap q :=
  integral_specComap_strictMono R S hpq

-- Lying over and going up produce an actual finite prime chain of the same length.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hi : Function.Injective (algebraMap R S)) (s : LTSeries (PrimeSpectrum R)) :
    ∃ t : LTSeries (PrimeSpectrum S), t.length = s.length ∧
      (algebraMap R S).specComap t.last = s.last := by
  fail_if_success
    have : IsDomain R := inferInstance
  fail_if_success
    have : IsNoetherianRing R := inferInstance
  exact exists_primeSeries_lift_of_injective_integral R S hi s

-- The integral dimension equality does not require domains or finite dimensions.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    (hi : Function.Injective (algebraMap R S)) : ringKrullDim R = ringKrullDim S := by
  fail_if_success
    have : FiniteRingKrullDim R := inferInstance
  exact ringKrullDim_eq_of_injective_integral R S hi

-- A finite field extension supplies the integral instance and is genuinely dimension zero.
example (k L : Type) [Field k] [Field L] [Algebra k L] [Module.Finite k L] :
    ringKrullDim k = ringKrullDim L ∧ ringKrullDim L = 0 :=
  ⟨ringKrullDim_eq_of_injective_integral k L (FaithfulSMul.algebraMap_injective k L),
    ringKrullDim_eq_zero_of_field L⟩

-- A noninjective integral map can lose dimension: the unit-ideal quotient is empty.
example (k : Type) [Field k] :
    ringKrullDim (k ⧸ (⊤ : Ideal k)) ≤ ringKrullDim k ∧
      ringKrullDim (k ⧸ (⊤ : Ideal k)) < ringKrullDim k := by
  constructor
  · exact ringKrullDim_le_of_integral k (k ⧸ (⊤ : Ideal k))
  · rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_zero_of_field]
    exact WithBot.bot_lt_coe (0 : ℕ∞)

-- An actual integral polynomial normalization determines transcendence degree
-- without a finite-generation assumption on the target.
example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hi : Function.Injective g) (hint : g.IsIntegral) : Algebra.trdeg k A = s := by
  fail_if_success
    have : Algebra.FiniteType k A := inferInstance
  exact trdeg_eq_normalization_size k A s g hi hint

-- The lower dimension bound through an injective integral map does not need a target domain.
example (k A : Type) [Field k] [CommRing A] [Algebra k A]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hi : Function.Injective g) (hint : g.IsIntegral) :
    (s : WithBot ℕ∞) ≤ ringKrullDim A := by
  fail_if_success
    have : IsDomain A := inferInstance
  exact normalization_size_le_ringKrullDim k A s g hi hint

-- The sharp equality joins the independently proved lower and upper bounds.
example (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ((Algebra.trdeg k A).toNat : WithBot ℕ∞) ≤ ringKrullDim A ∧
      ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞) :=
  ⟨trdeg_toNat_le_ringKrullDim_of_finiteType k A,
    ringKrullDim_eq_trdeg_toNat_of_finiteType k A⟩

-- Fraction-field transport uses the actual scalar tower, without finite generation.
example (k A K : Type) [Field k] [CommRing A] [IsDomain A] [Field K]
    [Algebra k A] [Algebra A K] [Algebra k K] [IsScalarTower k A K] [IsFractionRing A K] :
    Algebra.trdeg k A = Algebra.trdeg k K :=
  trdeg_eq_of_isFractionRing k A K

example (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k (FractionRing A)).toNat : WithBot ℕ∞) :=
  ringKrullDim_eq_fractionRing_trdeg_toNat_of_finiteType k A

-- This sharp formula is proved locally; no unfinished polynomial-dimension theorem is used.
example (k : Type) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) :=
  mvPolynomial_ringKrullDim_eq_card k n

-- Nontrivial higher-dimensional example: the actual affine three-space has dimension three.
example (k : Type) [Field k] :
    topologicalKrullDim (Spec (CommRingCat.of (MvPolynomial (Fin 3) k))) = 3 := by
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin 3) k)) = 3
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact mvPolynomial_ringKrullDim_eq_card k 3

example (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    topologicalKrullDim (Spec (CommRingCat.of A)) =
      ((Algebra.trdeg k A).toNat : WithBot ℕ∞) :=
  spec_topologicalKrullDim_eq_trdeg_toNat_of_finiteType k A

-- Prime coheight concerns the quotient dimension, without finite generation or ambient domain.
example (A : Type) [CommRing A] (p : PrimeSpectrum A) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by
  fail_if_success
    have : IsDomain A := inferInstance
  fail_if_success
    have : IsNoetherianRing A := inferInstance
  exact prime_coheight_eq_quotientDim A p

-- Scheme point height reverses the prime order: it is prime coheight, not prime height.
example (A : Type) [CommRing A] (p : PrimeSpectrum A) :
    Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p = Order.coheight p :=
  spec_point_height_eq_prime_coheight A p

-- The actual reduced closed carrier remains the existing pointSupport object.
example (A : Type) [CommRing A] (p : PrimeSpectrum A) :
    topologicalKrullDim (pointSupport (Spec (CommRingCat.of A)) p).val.subscheme =
      ringKrullDim (A ⧸ p.asIdeal) :=
  spec_pointSupport_dimension_eq_quotientDim A p

-- The actual prime residue field is compared through its quotient fraction-field structure.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] (p : PrimeSpectrum A) :
    Algebra.trdeg k (A ⧸ p.asIdeal) = Algebra.trdeg k p.asIdeal.ResidueField := by
  fail_if_success
    have : Algebra.FiniteType k A := inferInstance
  exact primeQuotient_trdeg_eq_residueField k A p

-- Actual carrier dimension and finite integer point height both use the actual residue field.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) :
    topologicalKrullDim (pointSupport (Spec (CommRingCat.of A)) p).val.subscheme =
        ((Algebra.trdeg k p.asIdeal.ResidueField).toNat : WithBot ℕ∞) ∧
      (Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p).toNat =
        (Algebra.trdeg k p.asIdeal.ResidueField).toNat := by
  fail_if_success
    have : IsDomain A := inferInstance
  exact ⟨spec_pointSupport_dimension_eq_residueField_trdeg k A p,
    spec_point_height_toNat_eq_residueField_trdeg k A p⟩

-- Every existing integral closed carrier is recovered from its actual ambient generic point.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (W : IntegralClosedSubscheme (Spec (CommRingCat.of A))) :
    topologicalKrullDim W.val.subscheme =
      ((Algebra.trdeg k (show PrimeSpectrum A from ambientGenericPoint W).asIdeal.ResidueField).toNat :
        WithBot ℕ∞) := by
  exact (congrArg (fun Z : IntegralClosedSubscheme (Spec (CommRingCat.of A)) ↦
      topologicalKrullDim Z.val.subscheme) (pointSupport_ambientGenericPoint W)).symm.trans
    (spec_pointSupport_dimension_eq_residueField_trdeg k A (ambientGenericPoint W))

-- Proper specialization strictly decreases residue-field degree on reducible affine schemes too.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (p q : PrimeSpectrum A) (hpq : p < q) :
    (Algebra.trdeg k q.asIdeal.ResidueField).toNat <
      (Algebra.trdeg k p.asIdeal.ResidueField).toNat :=
  prime_residueField_trdeg_toNat_strictAnti k A hpq

end AffineTranscendenceDimensionRegressions

-- SP43: maximal polynomial heights from actual prime extension and contraction.
#check HodgeConjecture.SchemeCycles.polynomialPrimeExtension
#check HodgeConjecture.SchemeCycles.polynomial_primeHeight_comap_add_one_le
#check HodgeConjecture.SchemeCycles.mvPolynomial_primeHeight_eq_card_of_isMaximal
#check HodgeConjecture.SchemeCycles.mvPolynomial_localization_dimension_of_isMaximal
#check HodgeConjecture.SchemeCycles.mvPolynomial_stalk_dimension_of_isClosed
#check HodgeConjecture.SchemeCycles.mvPolynomial_closedPoint_coheight

#print axioms HodgeConjecture.SchemeCycles.polynomial_comap_map_C
#print axioms HodgeConjecture.SchemeCycles.polynomialPrimeExtension
#print axioms HodgeConjecture.SchemeCycles.polynomialPrimeExtension_height_le
#print axioms HodgeConjecture.SchemeCycles.polynomial_map_C_not_isMaximal
#print axioms HodgeConjecture.SchemeCycles.polynomial_map_comap_C_lt
#print axioms HodgeConjecture.SchemeCycles.polynomial_primeHeight_comap_add_one_le
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_primeHeight_eq_card_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_height_eq_card_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_localization_dimension_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_stalk_dimension_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_stalk_dimension_of_isClosed
#print axioms HodgeConjecture.SchemeCycles.mvPolynomial_closedPoint_coheight

noncomputable section PolynomialMaximalHeightRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- Actual ideal extension/contraction works over arbitrary commutative rings.
example (R : Type) [CommRing R] (p : Ideal R) :
    (p.map (Polynomial.C : R →+* Polynomial R)).comap Polynomial.C = p := by
  fail_if_success
    have : IsDomain R := inferInstance
  fail_if_success
    have : IsNoetherianRing R := inferInstance
  exact polynomial_comap_map_C R p

-- The order embedding uses the actual extension of the original prime ideal.
example (R : Type) [CommRing R] (p : PrimeSpectrum R) :
    (polynomialPrimeExtension R p).asIdeal = p.asIdeal.map Polynomial.C := rfl

example (R : Type) [CommRing R] (p q : PrimeSpectrum R) (hpq : p < q) :
    polynomialPrimeExtension R p < polynomialPrimeExtension R q :=
  (polynomialPrimeExtension R).strictMono hpq

example (R : Type) [CommRing R] (p : PrimeSpectrum R) :
    Order.height p ≤ Order.height (polynomialPrimeExtension R p) :=
  polynomialPrimeExtension_height_le R p

-- Nonmaximality concerns every extended ideal, not just primes or proper ideals.
example (R : Type) [CommRing R] (p : Ideal R) :
    ¬ (p.map (Polynomial.C : R →+* Polynomial R)).IsMaximal :=
  polynomial_map_C_not_isMaximal R p

-- This strict extension step does not require maximality of the contraction.
example (R : Type) [CommRing R] (m : Ideal (Polynomial R)) [m.IsMaximal] :
    (m.comap Polynomial.C).map (Polynomial.C : R →+* Polynomial R) < m := by
  fail_if_success
    have : IsJacobsonRing R := inferInstance
  exact polynomial_map_comap_C_lt R m

example (R : Type) [CommRing R] (m : Ideal (Polynomial R)) [m.IsMaximal] :
    (m.comap (Polynomial.C : R →+* Polynomial R)).primeHeight + 1 ≤ m.primeHeight := by
  fail_if_success
    have : IsDomain R := inferInstance
  fail_if_success
    have : IsJacobsonRing R := inferInstance
  exact polynomial_primeHeight_comap_add_one_le R m

-- Every maximal ideal and every field characteristic are included.
example (k : Type) [Field k] (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k))
    [m.IsMaximal] : m.primeHeight = (n : ℕ∞) := by
  fail_if_success
    have : CharZero k := inferInstance
  exact mvPolynomial_primeHeight_eq_card_of_isMaximal k n m

-- The zero-variable base case concerns the actual zero-variable polynomial ring.
example (k : Type) [Field k] (m : Ideal (MvPolynomial (Fin 0) k)) [m.IsMaximal] :
    m.primeHeight = 0 := by
  simpa using mvPolynomial_primeHeight_eq_card_of_isMaximal k 0 m

example (k : Type) [Field k] (m : Ideal (MvPolynomial (Fin 3) k)) [m.IsMaximal] :
    m.height = 3 := by
  simpa using mvPolynomial_height_eq_card_of_isMaximal k 3 m

-- Local dimension uses the actual localization, with no degree-one residue-field premise.
example (k : Type) [Field k] (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k))
    [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) :=
  mvPolynomial_localization_dimension_of_isMaximal k n m

-- The scheme endpoint concerns its actual structure-sheaf stalk.
example (k : Type) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    [p.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.stalk p) =
      (n : WithBot ℕ∞) :=
  mvPolynomial_stalk_dimension_of_isMaximal k n p

-- Closedness is sufficient; a separate maximal-ideal instance is not a premise.
example (k : Type) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hp : IsClosed ({p} : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))) :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin n) k))).presheaf.stalk p) =
      (n : WithBot ℕ∞) :=
  mvPolynomial_stalk_dimension_of_isClosed k n p hp

-- At a closed point, Scheme coheight is n but Scheme height is zero.
example (k : Type) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    (hp : IsClosed ({p} : Set (PrimeSpectrum (MvPolynomial (Fin n) k)))) :
    Order.coheight (α := (Spec (CommRingCat.of (MvPolynomial (Fin n) k)) : Scheme)) p =
        (n : ℕ∞) ∧
      Order.height (α := (Spec (CommRingCat.of (MvPolynomial (Fin n) k)) : Scheme)) p = 0 := by
  refine ⟨mvPolynomial_closedPoint_coheight k n p hp, ?_⟩
  rw [spec_point_height_eq_prime_coheight]
  exact Order.coheight_eq_zero.mpr
    (PrimeSpectrum.isMax_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp))

-- A concrete higher-dimensional point is the actual evaluation-at-zero kernel.
example (k : Type) [Field k] :
    let e : MvPolynomial (Fin 3) k →ₐ[k] k := MvPolynomial.aeval (fun _ ↦ 0)
    let m : Ideal (MvPolynomial (Fin 3) k) := RingHom.ker e.toRingHom
    ∃ (hm : m.IsPrime),
      ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin 3) k))).presheaf.stalk
        (⟨m, hm⟩ : PrimeSpectrum (MvPolynomial (Fin 3) k))) = 3 := by
  dsimp only
  let e : MvPolynomial (Fin 3) k →ₐ[k] k := MvPolynomial.aeval (fun _ ↦ 0)
  have he : Function.Surjective e := by
    intro a
    exact ⟨MvPolynomial.C a, by simp [e]⟩
  letI : (RingHom.ker e.toRingHom).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective e.toRingHom he
  refine ⟨inferInstance, ?_⟩
  simpa using mvPolynomial_stalk_dimension_of_isMaximal k 3
    (⟨RingHom.ker e.toRingHom, inferInstance⟩ : PrimeSpectrum (MvPolynomial (Fin 3) k))

-- The actual zero-variable localization/stalk endpoint has dimension zero.
example (k : Type) [Field k] (p : PrimeSpectrum (MvPolynomial (Fin 0) k))
    [p.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin 0) k))).presheaf.stalk p) = 0 := by
  simpa using mvPolynomial_stalk_dimension_of_isMaximal k 0 p

end PolynomialMaximalHeightRegressions

-- SP44: proved normal-base going down and actual maximal-local dimensions.
#check HodgeConjecture.CommutativeAlgebra.exists_monic_annihilator_coeff_mem_pow_of_mem_map
#check HodgeConjecture.CommutativeAlgebra.exists_monic_annihilator_of_mem_map
#check HodgeConjecture.CommutativeAlgebra.monic_map_eq_X_pow_of_lower_coeff_zero
#check HodgeConjecture.CommutativeAlgebra.coeff_mem_prime_of_monic_dvd_scaled
#check HodgeConjecture.CommutativeAlgebra.coeff_mem_prime_of_monic_dvd
#check HodgeConjecture.CommutativeAlgebra.mem_prime_of_mul_mem_map_of_isIntegrallyClosed
#check HodgeConjecture.CommutativeAlgebra.hasGoingDown_of_isIntegrallyClosed
#check HodgeConjecture.SchemeCycles.primeHeight_eq_under_of_isIntegral_of_hasGoingDown
#check HodgeConjecture.SchemeCycles.normalization_primeHeight_eq_size
#check HodgeConjecture.SchemeCycles.primeHeight_eq_trdeg_toNat_of_isMaximal
#check HodgeConjecture.SchemeCycles.height_eq_trdeg_toNat_of_isMaximal
#check HodgeConjecture.SchemeCycles.localization_dimension_eq_of_isMaximal
#check HodgeConjecture.SchemeCycles.affine_stalk_dimension_of_isMaximal
#check HodgeConjecture.SchemeCycles.affine_stalk_dimension_of_isClosed
#check HodgeConjecture.SchemeCycles.affine_closedPoint_coheight_eq_trdeg

#print axioms HodgeConjecture.CommutativeAlgebra.exists_monic_annihilator_coeff_mem_pow_of_mem_map
#print axioms HodgeConjecture.CommutativeAlgebra.exists_monic_annihilator_of_mem_map
#print axioms HodgeConjecture.CommutativeAlgebra.monic_map_eq_X_pow_of_lower_coeff_zero
#print axioms HodgeConjecture.CommutativeAlgebra.coeff_mem_prime_of_monic_dvd_scaled
#print axioms HodgeConjecture.CommutativeAlgebra.coeff_mem_prime_of_monic_dvd
#print axioms HodgeConjecture.CommutativeAlgebra.mem_prime_of_mul_mem_map_of_isIntegrallyClosed
#print axioms HodgeConjecture.CommutativeAlgebra.hasGoingDown_of_isIntegrallyClosed
#print axioms HodgeConjecture.SchemeCycles.primeHeight_eq_under_of_isIntegral_of_hasGoingDown
#print axioms HodgeConjecture.SchemeCycles.normalization_primeHeight_eq_size
#print axioms HodgeConjecture.SchemeCycles.primeHeight_eq_trdeg_toNat_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.height_eq_trdeg_toNat_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.localization_dimension_eq_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.affine_stalk_dimension_of_isMaximal
#print axioms HodgeConjecture.SchemeCycles.affine_stalk_dimension_of_isClosed
#print axioms HodgeConjecture.SchemeCycles.affine_closedPoint_coheight_eq_trdeg

noncomputable section NormalGoingDownLocalDimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

-- The determinant argument needs neither domains nor global module finiteness.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (I : Ideal R) (y : S)
    (hy : y ∈ I.map (algebraMap R S)) :
    ∃ F : Polynomial R, F.Monic ∧ Polynomial.aeval y F = 0 ∧
      ∀ i, F.coeff i ∈ I ^ (F.natDegree - i) := by
  fail_if_success
    have : IsDomain R := inferInstance
  fail_if_success
    have : IsDomain S := inferInstance
  fail_if_success
    have : Module.Finite R S := inferInstance
  fail_if_success
    have : IsNoetherianRing R := inferInstance
  exact exists_monic_annihilator_coeff_mem_pow_of_mem_map R S I y hy

-- The zero ideal and zero element are allowed; no injectivity premise is introduced.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    ∃ F : Polynomial R, F.Monic ∧ Polynomial.aeval (0 : S) F = 0 ∧
      ∀ i < F.natDegree, F.coeff i ∈ (⊥ : Ideal R) :=
  exists_monic_annihilator_of_mem_map R S ⊥ 0 (Ideal.zero_mem _)

-- Reduction of a monic polynomial is literal coefficient reduction, over any rings.
example (R A : Type) [CommRing R] [CommRing A] (f : R →+* A)
    (F : Polynomial R) (hF : F.Monic)
    (hcoeff : ∀ i < F.natDegree, f (F.coeff i) = 0) :
    F.map f = Polynomial.X ^ F.natDegree :=
  monic_map_eq_X_pow_of_lower_coeff_zero f hF hcoeff

-- Prime-coefficient descent does not assume a domain or normal ambient ring.
example (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime]
    (a : R) (ha : a ∉ p) (F g : Polynomial R) (hF : F.Monic) (hg : g.Monic)
    (hcoeff : ∀ i < F.natDegree, F.coeff i ∈ p)
    (hdiv : g ∣ F.comp (Polynomial.C a * Polynomial.X)) :
    ∀ i < g.natDegree, g.coeff i ∈ p := by
  fail_if_success
    have : IsDomain R := inferInstance
  exact coeff_mem_prime_of_monic_dvd_scaled p ha hF hg hcoeff hdiv

example (R : Type) [CommRing R] (p : Ideal R) [p.IsPrime]
    (F g : Polynomial R) (hF : F.Monic) (hg : g.Monic) (hdiv : g ∣ F)
    (hcoeff : ∀ i < F.natDegree, F.coeff i ∈ p) :
    ∀ i < g.natDegree, g.coeff i ∈ p :=
  coeff_mem_prime_of_monic_dvd p hF hg hdiv hcoeff

-- Normality is on the base only. Neither Noetherianity nor finiteness is assumed.
example (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [IsIntegrallyClosed R] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) : Algebra.HasGoingDown R S := by
  fail_if_success
    have : IsIntegrallyClosed S := inferInstance
  fail_if_success
    have : IsNoetherianRing R := inferInstance
  fail_if_success
    have : Module.Finite R S := inferInstance
  exact hasGoingDown_of_isIntegrallyClosed R S hinj

-- The cancellation statement retains the actual selected prime upstairs.
example (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [IsIntegrallyClosed R] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) [p.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hpQ : p ≤ Q.under R) (a : R) (b : S) (ha : a ∉ p)
    (hab : algebraMap R S a * b ∈ p.map (algebraMap R S)) : b ∈ Q :=
  mem_prime_of_mul_mem_map_of_isIntegrallyClosed R S hinj p Q hpQ a b ha hab

-- Going down lifts below this Q, not just to some prime over p.
example (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [IsIntegrallyClosed R] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S))
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver q] (hpq : p ≤ q) : ∃ P ≤ Q, P.IsPrime ∧ P.LiesOver p := by
  letI := hasGoingDown_of_isIntegrallyClosed R S hinj
  exact Q.exists_ideal_le_liesOver_of_le (p := p) (q := q) hpq

-- The same terminal-prime condition is retained for an entire finite strict chain.
example (R S : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [IsIntegrallyClosed R] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (l : LTSeries (PrimeSpectrum R))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver l.last.asIdeal] :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      L.last = ⟨Q, inferInstance⟩ ∧
      List.map (algebraMap R S).specComap L.toList = l.toList := by
  letI := hasGoingDown_of_isIntegrallyClosed R S hinj
  exact Ideal.exists_ltSeries_of_hasGoingDown l Q

-- The height comparison itself requires no extra domain hypotheses.
example (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (Q : Ideal S) [Q.IsPrime] : Q.primeHeight = (Q.under R).primeHeight := by
  fail_if_success
    have : IsDomain R := inferInstance
  fail_if_success
    have : IsDomain S := inferInstance
  exact primeHeight_eq_under_of_isIntegral_of_hasGoingDown R S Q

-- An actual normalization map suffices, even without finite type of the upstairs algebra.
example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    (s : ℕ) (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) (m : Ideal A) [m.IsMaximal] :
    m.primeHeight = (s : ℕ∞) := by
  fail_if_success
    have : Algebra.FiniteType k A := inferInstance
  fail_if_success
    have : IsIntegrallyClosed A := inferInstance
  exact normalization_primeHeight_eq_size k A s g hinj hint m

-- No normality, characteristic-zero, or rational-closed-point condition is required.
example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal] :
    m.primeHeight = ((Algebra.trdeg k A).toNat : ℕ∞) ∧
      m.height = ((Algebra.trdeg k A).toNat : ℕ∞) := by
  fail_if_success
    have : IsIntegrallyClosed A := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  exact ⟨primeHeight_eq_trdeg_toNat_of_isMaximal k A m,
    height_eq_trdeg_toNat_of_isMaximal k A m⟩

example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim A :=
  localization_dimension_eq_of_isMaximal k A m

-- The actual stalk result is valid at every maximal ideal of the affine domain.
example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk p) = ringKrullDim A :=
  affine_stalk_dimension_of_isMaximal k A p

-- Closedness suffices without supplying a separate maximal-ideal instance.
example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (p : PrimeSpectrum A)
    (hp : IsClosed ({p} : Set (PrimeSpectrum A))) :
    ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk p) = ringKrullDim A :=
  affine_stalk_dimension_of_isClosed k A p hp

-- The scheme-order coheight is local dimension, not closed-carrier height.
example (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (p : PrimeSpectrum A)
    (hp : IsClosed ({p} : Set (PrimeSpectrum A))) :
    Order.coheight (α := (Spec (CommRingCat.of A) : Scheme)) p =
        ((Algebra.trdeg k A).toNat : ℕ∞) ∧
      Order.height (α := (Spec (CommRingCat.of A) : Scheme)) p = 0 := by
  refine ⟨affine_closedPoint_coheight_eq_trdeg k A p hp, ?_⟩
  rw [spec_point_height_eq_prime_coheight]
  exact Order.coheight_eq_zero.mpr
    (PrimeSpectrum.isMax_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hp))

-- The general local-ring theorem agrees with the earlier polynomial calculation.
example (k : Type) [Field k] (n : ℕ) (m : Ideal (MvPolynomial (Fin n) k))
    [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
  rw [localization_dimension_eq_of_isMaximal k (MvPolynomial (Fin n) k) m,
    mvPolynomial_ringKrullDim_eq_card]

-- The actual zero-variable stalk is still zero-dimensional through the general endpoint.
example (k : Type) [Field k] (p : PrimeSpectrum (MvPolynomial (Fin 0) k))
    [p.asIdeal.IsMaximal] :
    ringKrullDim ((Spec (CommRingCat.of (MvPolynomial (Fin 0) k))).presheaf.stalk p) = 0 := by
  rw [affine_stalk_dimension_of_isMaximal k (MvPolynomial (Fin 0) k) p,
    mvPolynomial_ringKrullDim_eq_card]
  rfl

-- Actual evaluation is integral but not injective, and going down fails.
example (k : Type) [Field k] :
    letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
    Algebra.IsIntegral (Polynomial k) k ∧ ¬ Algebra.HasGoingDown (Polynomial k) k := by
  letI : Algebra (Polynomial k) k := (Polynomial.evalRingHom (0 : k)).toAlgebra
  have he : Function.Surjective (algebraMap (Polynomial k) k) := by
    intro a
    exact ⟨Polynomial.C a, by simp [RingHom.algebraMap_toAlgebra]⟩
  refine ⟨Algebra.isIntegral_of_surjective he, ?_⟩
  intro hdown
  letI := hdown
  letI : (⊥ : Ideal (Polynomial k)).IsPrime := Ideal.bot_prime
  letI : (⊥ : Ideal k).IsPrime := Ideal.bot_prime
  have hX : Polynomial.X ∈ (⊥ : Ideal k).under (Polynomial k) := by
    change Polynomial.evalRingHom (0 : k) Polynomial.X ∈ (⊥ : Ideal k)
    simp
  have hlt : (⊥ : Ideal (Polynomial k)) < (⊥ : Ideal k).under (Polynomial k) := by
    apply bot_lt_iff_ne_bot.mpr
    intro heq
    rw [heq, Ideal.mem_bot] at hX
    exact Polynomial.X_ne_zero hX
  obtain ⟨P, hP, hp, hlie⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (p := (⊥ : Ideal (Polynomial k)))
      (⊥ : Ideal k) hlt
  have hPbot : P = ⊥ := le_bot_iff.mp hP
  subst P
  rw [← hlie.over, Ideal.mem_bot] at hX
  exact Polynomial.X_ne_zero hX

end NormalGoingDownLocalDimensionRegressions

-- SP45: actual lifted residue normalization and its generic-fiber localization.
#check HodgeConjecture.SchemeCycles.quotientPolynomialLift
#check HodgeConjecture.SchemeCycles.quotient_comp_quotientPolynomialLift
#check HodgeConjecture.SchemeCycles.quotientPolynomialLift_injective
#check HodgeConjecture.SchemeCycles.polynomial_notMem_of_quotient_injective
#check HodgeConjecture.SchemeCycles.quotientPolynomialLift_notMem
#check HodgeConjecture.SchemeCycles.polynomial_map_nonZeroDivisors_le_primeCompl
#check HodgeConjecture.SchemeCycles.polynomial_map_nonZeroDivisors_disjoint
#check HodgeConjecture.SchemeCycles.exists_lifted_residue_normalization
#check HodgeConjecture.CommutativeAlgebra.genericFiberAlgebra
#check HodgeConjecture.CommutativeAlgebra.genericFiberAlgebra_algebraMap_eq
#check HodgeConjecture.CommutativeAlgebra.genericFiberAlgebra_isScalarTower
#check HodgeConjecture.CommutativeAlgebra.genericFiber_finiteType
#check HodgeConjecture.CommutativeAlgebra.genericFiber_denominators_le_nonZeroDivisors
#check HodgeConjecture.CommutativeAlgebra.genericFiber_isDomain
#check HodgeConjecture.CommutativeAlgebra.genericFiber_localization_injective
#check HodgeConjecture.CommutativeAlgebra.genericFiber_baseField_injective
#check HodgeConjecture.CommutativeAlgebra.genericFiber_isScalarTower_base
#check HodgeConjecture.CommutativeAlgebra.residueLocalization_comap_map
#check HodgeConjecture.CommutativeAlgebra.residueLocalization_map_isPrime
#check HodgeConjecture.CommutativeAlgebra.residueLocalization_map_isMaximal
#check HodgeConjecture.CommutativeAlgebra.residueLocalization_primeHeight_map
#check HodgeConjecture.SchemeCycles.residueNormalization_localization
#check HodgeConjecture.SchemeCycles.exists_residueNormalization_localization
#check HodgeConjecture.SchemeCycles.primeHeight_eq_residueNormalization_trdeg

#print axioms HodgeConjecture.SchemeCycles.quotientPolynomialLift
#print axioms HodgeConjecture.SchemeCycles.quotient_comp_quotientPolynomialLift
#print axioms HodgeConjecture.SchemeCycles.quotientPolynomialLift_injective
#print axioms HodgeConjecture.SchemeCycles.polynomial_notMem_of_quotient_injective
#print axioms HodgeConjecture.SchemeCycles.quotientPolynomialLift_notMem
#print axioms HodgeConjecture.SchemeCycles.polynomial_map_nonZeroDivisors_le_primeCompl
#print axioms HodgeConjecture.SchemeCycles.polynomial_map_nonZeroDivisors_disjoint
#print axioms HodgeConjecture.SchemeCycles.exists_lifted_residue_normalization
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiberAlgebra
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiberAlgebra_algebraMap_eq
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiberAlgebra_isScalarTower
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiber_finiteType
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiber_denominators_le_nonZeroDivisors
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiber_isDomain
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiber_localization_injective
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiber_baseField_injective
#print axioms HodgeConjecture.CommutativeAlgebra.genericFiber_isScalarTower_base
#print axioms HodgeConjecture.CommutativeAlgebra.residueLocalization_comap_map
#print axioms HodgeConjecture.CommutativeAlgebra.residueLocalization_map_isPrime
#print axioms HodgeConjecture.CommutativeAlgebra.residueLocalization_map_isMaximal
#print axioms HodgeConjecture.CommutativeAlgebra.residueLocalization_primeHeight_map
#print axioms HodgeConjecture.SchemeCycles.residueNormalization_localization
#print axioms HodgeConjecture.SchemeCycles.exists_residueNormalization_localization
#print axioms HodgeConjecture.SchemeCycles.primeHeight_eq_residueNormalization_trdeg

noncomputable section ResidueNormalizationLocalizationRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

-- The actual lift square does not need primality, a domain, or finite type.
example (k B : Type) [CommRing k] [CommRing B] [Algebra k B]
    (q : Ideal B) (n : ℕ) (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q) :
    (Ideal.Quotient.mkₐ k q).comp (quotientPolynomialLift k B q n g) = g := by
  fail_if_success
    have : q.IsPrime := inferInstance
  fail_if_success
    have : IsDomain B := inferInstance
  fail_if_success
    have : Algebra.FiniteType k B := inferInstance
  exact quotient_comp_quotientPolynomialLift k B q n g

example (k B : Type) [CommRing k] [CommRing B] [Algebra k B]
    (q : Ideal B) (n : ℕ) (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q)
    (hinj : Function.Injective g) :
    Function.Injective (quotientPolynomialLift k B q n g) :=
  quotientPolynomialLift_injective k B q n g hinj

-- Disjointness concerns the actual lifted polynomial images, not a replacement subring.
example (k B : Type) [Field k] [CommRing B] [Algebra k B]
    (q : Ideal B) [q.IsPrime] (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f)) :
    (nonZeroDivisors (MvPolynomial (Fin n) k)).map f.toMonoidHom ≤ q.primeCompl ∧
      Disjoint (↑((nonZeroDivisors (MvPolynomial (Fin n) k)).map f.toMonoidHom) : Set B)
        (q : Set B) := by
  fail_if_success
    have : IsDomain B := inferInstance
  exact ⟨polynomial_map_nonZeroDivisors_le_primeCompl k B q n f hinj,
    polynomial_map_nonZeroDivisors_disjoint k B q n f hinj⟩

example (k B : Type) [CommRing k] [CommRing B] [Algebra k B]
    (q : Ideal B) (n : ℕ) (g : MvPolynomial (Fin n) k →ₐ[k] B ⧸ q)
    (hinj : Function.Injective g) (a : MvPolynomial (Fin n) k) (ha : a ≠ 0) :
    quotientPolynomialLift k B q n g a ∉ q :=
  quotientPolynomialLift_notMem k B q n g hinj a ha

-- The zero-variable lift is literally the scalar map, with no variables to choose.
example (k B : Type) [CommRing k] [CommRing B] [Algebra k B]
    (q : Ideal B) (g : MvPolynomial (Fin 0) k →ₐ[k] B ⧸ q) :
    quotientPolynomialLift k B q 0 g =
      (Algebra.ofId k B).comp (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  exact Fin.elim0 i

-- Normalization is applied to the prime quotient; the original algebra may be reducible.
example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (q : Ideal B) [q.IsPrime] :
    ∃ n, ∃ f : MvPolynomial (Fin n) k →ₐ[k] B,
      Function.Injective f ∧ Function.Injective ((Ideal.Quotient.mkₐ k q).comp f) ∧
        ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral := by
  fail_if_success
    have : IsDomain B := inferInstance
  exact exists_lifted_residue_normalization k B q

section GenericFiberRegressions

variable (R S S' : Type) [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra S S']
  [IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S']

-- The algebra map is the actual localization map, definitionally.
example :
    letI := genericFiberAlgebra R S S'
    algebraMap (FractionRing R) S' =
      (IsLocalization.map (M := nonZeroDivisors R) (S := FractionRing R)
        (T := Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S' (algebraMap R S)
        (Submonoid.le_comap_map (nonZeroDivisors R)) : FractionRing R →+* S') := rfl

example [Algebra R S'] [IsScalarTower R S S'] :
    letI := genericFiberAlgebra R S S'
    IsScalarTower R (FractionRing R) S' :=
  genericFiberAlgebra_isScalarTower R S S'

-- Canonical finite type follows from the actual pushout without domain assumptions.
example [Algebra R S'] [IsScalarTower R S S'] [Algebra.FiniteType R S] :
    letI := genericFiberAlgebra R S S'
    Algebra.FiniteType (FractionRing R) S' := by
  letI := genericFiberAlgebra R S S'
  letI := genericFiberAlgebra_isScalarTower R S S'
  fail_if_success
    have : IsDomain R := inferInstance
  fail_if_success
    have : IsDomain S := inferInstance
  exact genericFiber_finiteType R S S'

-- Domain and localization injectivity are conclusions when the upper ring is a domain.
example [IsDomain S] (hinj : Function.Injective (algebraMap R S)) :
    IsDomain S' ∧ Function.Injective (algebraMap S S') :=
  ⟨genericFiber_isDomain R S S' hinj, genericFiber_localization_injective R S S' hinj⟩

example [IsDomain R] [IsDomain S] (hinj : Function.Injective (algebraMap R S)) :
    letI := genericFiberAlgebra R S S'
    Function.Injective (algebraMap (FractionRing R) S') := by
  letI := genericFiberAlgebra R S S'
  exact genericFiber_baseField_injective R S S' hinj

end GenericFiberRegressions

-- The smaller-base tower comparison needs no domain or integrality hypotheses.
example (R S' k K : Type) [CommRing R] [CommRing S'] [CommRing k] [CommRing K]
    [Algebra R K] [IsFractionRing R K] [Algebra k R] [Algebra k K]
    [Algebra k S'] [Algebra R S'] [Algebra K S']
    [IsScalarTower k R K] [IsScalarTower k R S'] [IsScalarTower R K S'] :
    IsScalarTower k K S' :=
  genericFiber_isScalarTower_base R S' k K

section ResidueLocalizationCoreRegressions

variable (R S S' : Type) [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [CommRing S'] [Algebra S S']
  [IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) S']
  (q : Ideal S) [q.IsPrime] (hinj : Function.Injective (algebraMap R (S ⧸ q)))

-- Prime preservation and contraction use no integral extension assumption.
example : (q.map (algebraMap S S')).IsPrime ∧
    (q.map (algebraMap S S')).comap (algebraMap S S') = q := by
  fail_if_success
    have : Algebra.IsIntegral R (S ⧸ q) := inferInstance
  fail_if_success
    have : IsDomain S := inferInstance
  exact ⟨residueLocalization_map_isPrime R S S' q hinj,
    residueLocalization_comap_map R S S' q hinj⟩

-- The whole prime height is unchanged, also without an integrality hypothesis.
example :
    letI := residueLocalization_map_isPrime R S S' q hinj
    (q.map (algebraMap S S')).primeHeight = q.primeHeight := by
  fail_if_success
    have : Algebra.IsIntegral R (S ⧸ q) := inferInstance
  exact residueLocalization_primeHeight_map R S S' q hinj

-- Quotient integrality is used for maximality; the ambient algebra need not be a domain.
example (hint : (algebraMap R (S ⧸ q)).IsIntegral) :
    (q.map (algebraMap S S')).IsMaximal := by
  fail_if_success
    have : IsDomain S := inferInstance
  fail_if_success
    have : IsNoetherianRing S := inferInstance
  fail_if_success
    have : Module.Finite R S := inferInstance
  exact residueLocalization_map_isMaximal R S S' q hinj hint

end ResidueLocalizationCoreRegressions

-- A genuine non-domain ambient algebra: the product of two copies of a field.
example (K : Type) [Field K] :
    let q := RingHom.ker (RingHom.fst K K)
    let S' := Localization (Algebra.algebraMapSubmonoid (K × K) (nonZeroDivisors K))
    (q.map (algebraMap (K × K) S')).IsMaximal := by
  let q := RingHom.ker (RingHom.fst K K)
  let S' := Localization (Algebra.algebraMapSubmonoid (K × K) (nonZeroDivisors K))
  letI : q.IsMaximal := RingHom.ker_isMaximal_of_surjective (RingHom.fst K K)
    (fun a ↦ ⟨(a, 0), rfl⟩)
  have hsurj : Function.Surjective (algebraMap K ((K × K) ⧸ q)) := by
    intro x
    obtain ⟨⟨a, b⟩, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨a, ?_⟩
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    change (a, a).1 - (a, b).1 = 0
    simp
  letI : Algebra.IsIntegral K ((K × K) ⧸ q) := Algebra.isIntegral_of_surjective hsurj
  exact residueLocalization_map_isMaximal K (K × K) S' q
    (algebraMap K ((K × K) ⧸ q)).injective
    (algebraMap_isIntegral_iff.mpr inferInstance)

-- The constructed finite-type generic fiber and its maximal prime require no domain B.
example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (q : Ideal B) [q.IsPrime] (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f))
    (hint : ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral) :
    letI := f.toRingHom.toAlgebra
    let B' := Localization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
    letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
    Algebra.FiniteType (FractionRing (MvPolynomial (Fin n) k)) B' ∧
      (q.map (algebraMap B B')).IsMaximal ∧
      (q.map (algebraMap B B')).comap (algebraMap B B') = q ∧
      (q.map (algebraMap B B')).height = q.height := by
  fail_if_success
    have : IsDomain B := inferInstance
  exact residueNormalization_localization k B q n f hinj hint

-- Existence supplies the actual map and carrier, not a selected localization hypothesis.
example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (q : Ideal B) [q.IsPrime] :
    ∃ n, ∃ f : MvPolynomial (Fin n) k →ₐ[k] B,
      Function.Injective f ∧
      (letI := f.toRingHom.toAlgebra
       let B' := Localization
         (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
       (q.map (algebraMap B B')).IsMaximal ∧
         (q.map (algebraMap B B')).height = q.height) := by
  obtain ⟨n, f, hf, _, _, h⟩ := exists_residueNormalization_localization k B q
  exact ⟨n, f, hf, h.2.1, h.2.2.2⟩

-- The transcendence-degree computation is the separate domain-only consumer.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime]
    (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ k q).comp f))
    (hint : ((Ideal.Quotient.mkₐ k q).comp f).IsIntegral) :
    letI := f.toRingHom.toAlgebra
    let B' := Localization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
    letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
    q.primeHeight =
      ((Algebra.trdeg (FractionRing (MvPolynomial (Fin n) k)) B').toNat : ℕ∞) := by
  fail_if_success
    have : IsIntegrallyClosed B := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  exact primeHeight_eq_residueNormalization_trdeg k B q n f hinj hint

end ResidueNormalizationLocalizationRegressions

-- SP46: original-field affine prime dimension and actual localization invariance.
#check HodgeConjecture.SchemeCycles.lift_trdeg_eq_of_isLocalization
#check HodgeConjecture.SchemeCycles.trdeg_eq_of_isLocalization
#check HodgeConjecture.SchemeCycles.trdeg_toNat_eq_of_isLocalization
#check HodgeConjecture.SchemeCycles.polynomial_genericFiber_trdeg_toNat_add
#check HodgeConjecture.SchemeCycles.primeHeight_add_quotient_trdeg_eq
#check HodgeConjecture.SchemeCycles.height_add_quotient_trdeg_eq
#check HodgeConjecture.SchemeCycles.primeHeight_add_residueField_trdeg_eq
#check HodgeConjecture.SchemeCycles.height_add_quotient_dimension_eq
#check HodgeConjecture.SchemeCycles.localization_dimension_add_quotient_dimension_eq

#print axioms HodgeConjecture.SchemeCycles.lift_trdeg_eq_of_isLocalization
#print axioms HodgeConjecture.SchemeCycles.trdeg_eq_of_isLocalization
#print axioms HodgeConjecture.SchemeCycles.trdeg_toNat_eq_of_isLocalization
#print axioms HodgeConjecture.SchemeCycles.polynomial_genericFiber_trdeg_toNat_add
#print axioms HodgeConjecture.SchemeCycles.primeHeight_add_quotient_trdeg_eq
#print axioms HodgeConjecture.SchemeCycles.height_add_quotient_trdeg_eq
#print axioms HodgeConjecture.SchemeCycles.primeHeight_add_residueField_trdeg_eq
#print axioms HodgeConjecture.SchemeCycles.height_add_quotient_dimension_eq
#print axioms HodgeConjecture.SchemeCycles.localization_dimension_add_quotient_dimension_eq

noncomputable section AffinePrimeDimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

universe sp46u sp46v sp46w

-- Cardinal invariance precedes any numeric truncation and allows independent universes.
example (k : Type sp46u) [Field k] (B : Type sp46v) [CommRing B] [IsDomain B]
    (B' : Type sp46w) [CommRing B'] [Algebra k B] [Algebra B B'] [Algebra k B']
    [IsScalarTower k B B'] (M : Submonoid B) [IsLocalization M B']
    (hM : M ≤ nonZeroDivisors B) :
    Cardinal.lift.{sp46w} (Algebra.trdeg k B) =
      Cardinal.lift.{sp46v} (Algebra.trdeg k B') := by
  fail_if_success
    have : Algebra.FiniteType k B := inferInstance
  fail_if_success
    have : IsDomain B' := inferInstance
  exact lift_trdeg_eq_of_isLocalization k B B' M hM

example (k : Type sp46u) [Field k] (B : Type sp46v) [CommRing B] [IsDomain B]
    (B' : Type sp46w) [CommRing B'] [Algebra k B] [Algebra B B'] [Algebra k B']
    [IsScalarTower k B B'] (M : Submonoid B) [IsLocalization M B']
    (hM : M ≤ nonZeroDivisors B) :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k B').toNat :=
  trdeg_toNat_eq_of_isLocalization k B B' M hM

-- The existing actual fraction field is one localization covered by the theorem.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] :
    Algebra.trdeg k B = Algebra.trdeg k (FractionRing B) :=
  trdeg_eq_of_isLocalization k B (FractionRing B) (nonZeroDivisors B) le_rfl

-- A genuinely infinite degree is retained by the primary cardinal statement.
example (k : Type) [Field k] :
    Algebra.trdeg k (FractionRing (MvPolynomial ℕ k)) = Cardinal.aleph0 := by
  rw [← trdeg_eq_of_isLocalization k (MvPolynomial ℕ k)
    (FractionRing (MvPolynomial ℕ k)) (nonZeroDivisors (MvPolynomial ℕ k)) le_rfl]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_nat, Cardinal.lift_aleph0]

-- The scalar-tower splitting needs only an injective polynomial map, not integrality.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] B)
    (hinj : Function.Injective f) :
    letI := f.toRingHom.toAlgebra
    let B' := Localization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors (MvPolynomial (Fin n) k)))
    letI := genericFiberAlgebra (MvPolynomial (Fin n) k) B B'
    n + (Algebra.trdeg (FractionRing (MvPolynomial (Fin n) k)) B').toNat =
      (Algebra.trdeg k B).toNat := by
  letI := f.toRingHom.toAlgebra
  fail_if_success
    have : Algebra.IsIntegral (MvPolynomial (Fin n) k) B := inferInstance
  exact polynomial_genericFiber_trdeg_toNat_add k B n f hinj

-- The affine formula is for every prime, with no normality or characteristic restriction.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    q.primeHeight + ((Algebra.trdeg k (B ⧸ q)).toNat : ℕ∞) =
      ((Algebra.trdeg k B).toNat : ℕ∞) := by
  fail_if_success
    have : q.IsMaximal := inferInstance
  fail_if_success
    have : IsIntegrallyClosed B := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  exact primeHeight_add_quotient_trdeg_eq k B q

example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    q.height + ((Algebra.trdeg k (B ⧸ q)).toNat : ℕ∞) =
      ((Algebra.trdeg k B).toNat : ℕ∞) :=
  height_add_quotient_trdeg_eq k B q

-- The residue-field term is the actual Ideal.ResidueField of the selected prime.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    q.primeHeight + ((Algebra.trdeg k q.ResidueField).toNat : ℕ∞) =
      ((Algebra.trdeg k B).toNat : ℕ∞) :=
  primeHeight_add_residueField_trdeg_eq k B q

example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = ringKrullDim B :=
  height_add_quotient_dimension_eq k B q

-- The local term uses the actual localization at an arbitrary prime.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (q : Ideal B) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) + ringKrullDim (B ⧸ q) = ringKrullDim B :=
  localization_dimension_add_quotient_dimension_eq k B q

-- At the zero prime the formula recovers the full dimension of the zero quotient.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] :
    ringKrullDim (B ⧸ (⊥ : Ideal B)) = ringKrullDim B := by
  letI : (⊥ : Ideal B).IsPrime := Ideal.bot_prime
  simpa only [Ideal.height_bot, WithBot.coe_zero, zero_add] using
    height_add_quotient_dimension_eq k B (⊥ : Ideal B)

-- At maximal primes it agrees with the earlier full-height theorem.
example (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.FiniteType k B] (m : Ideal B) [m.IsMaximal] :
    (Algebra.trdeg k (B ⧸ m)).toNat = 0 := by
  have h := primeHeight_add_quotient_trdeg_eq k B m
  rw [primeHeight_eq_trdeg_toNat_of_isMaximal k B m] at h
  have hnat : (Algebra.trdeg k B).toNat + (Algebra.trdeg k (B ⧸ m)).toNat =
      (Algebra.trdeg k B).toNat := by exact_mod_cast h
  omega

-- A concrete positive-height, nonmaximal prime in k[X][Y] is covered as well.
example (k : Type) [Field k] :
    let m := RingHom.ker (Polynomial.evalRingHom (0 : k))
    let q := m.map (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k))
    q.IsPrime ∧ ¬ q.IsMaximal ∧ (1 : ℕ∞) ≤ q.height ∧
      (q.height : WithBot ℕ∞) + ringKrullDim (Polynomial (Polynomial k) ⧸ q) =
        ringKrullDim (Polynomial (Polynomial k)) := by
  let m := RingHom.ker (Polynomial.evalRingHom (0 : k))
  let q := m.map (Polynomial.C : Polynomial k →+* Polynomial (Polynomial k))
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (Polynomial.evalRingHom (0 : k)) (fun a ↦ ⟨Polynomial.C a, by simp⟩)
  letI : q.IsPrime := Ideal.isPrime_map_C_of_isPrime (inferInstance : m.IsPrime)
  refine ⟨inferInstance, polynomial_map_C_not_isMaximal (Polynomial k) m, ?_,
    height_add_quotient_dimension_eq k (Polynomial (Polynomial k)) q⟩
  rw [Ideal.height_eq_primeHeight]
  have hm : (1 : ℕ∞) ≤ m.primeHeight := by
    calc
      1 = 0 + 1 := by simp
      _ ≤ (m.comap (Polynomial.C : k →+* Polynomial k)).primeHeight + 1 :=
        add_le_add_right (zero_le _) 1
      _ ≤ m.primeHeight := polynomial_primeHeight_comap_add_one_le k m
  exact hm.trans (polynomialPrimeExtension_height_le (Polynomial k) ⟨m, inferInstance⟩)

-- The actual zero-variable polynomial ring gives a zero-dimensional sum.
example (k : Type) [Field k] (q : Ideal (MvPolynomial (Fin 0) k)) [q.IsPrime] :
    ringKrullDim (Localization.AtPrime q) + ringKrullDim (MvPolynomial (Fin 0) k ⧸ q) = 0 := by
  rw [localization_dimension_add_quotient_dimension_eq k (MvPolynomial (Fin 0) k) q,
    mvPolynomial_ringKrullDim_eq_card]
  rfl

end AffinePrimeDimensionRegressions

-- SP47: consecutive prime-spectrum covers and the exact quotient dimension drop.
#check HodgeConjecture.CommutativeAlgebra.primeQuotient_map_isPrime
#check HodgeConjecture.CommutativeAlgebra.primeQuotient_bot_covBy_map
#check HodgeConjecture.CommutativeAlgebra.primeQuotient_primeHeight_eq_one_of_covBy
#check HodgeConjecture.SchemeCycles.primeQuotient_trdeg_toNat_add_one_of_covBy
#check HodgeConjecture.SchemeCycles.prime_residueField_trdeg_toNat_add_one_of_covBy
#check HodgeConjecture.SchemeCycles.primeQuotient_dimension_add_one_of_covBy

#print axioms HodgeConjecture.CommutativeAlgebra.primeQuotient_map_isPrime
#print axioms HodgeConjecture.CommutativeAlgebra.primeQuotient_bot_covBy_map
#print axioms HodgeConjecture.CommutativeAlgebra.primeQuotient_primeHeight_eq_one_of_covBy
#print axioms HodgeConjecture.SchemeCycles.primeQuotient_trdeg_toNat_add_one_of_covBy
#print axioms HodgeConjecture.SchemeCycles.prime_residueField_trdeg_toNat_add_one_of_covBy
#print axioms HodgeConjecture.SchemeCycles.primeQuotient_dimension_add_one_of_covBy

noncomputable section ConsecutivePrimeDimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

-- Actual quotient primality does not require a domain or Noetherian ambient ring.
example (B : Type) [CommRing B] (p q : PrimeSpectrum B) (hpq : p ≤ q) :
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime := by
  fail_if_success
    have : IsDomain B := inferInstance
  fail_if_success
    have : IsNoetherianRing B := inferInstance
  exact primeQuotient_map_isPrime B p q hpq

-- The actual quotient image contracts to q, with no cover assumption needed.
example (B : Type) [CommRing B] (p q : PrimeSpectrum B) (hpq : p ≤ q) :
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).comap (Ideal.Quotient.mk p.asIdeal) =
      q.asIdeal := by
  exact (q.asIdeal.comap_map_of_surjective (Ideal.Quotient.mk p.asIdeal)
    Ideal.Quotient.mk_surjective).trans (by
      change q.asIdeal ⊔ RingHom.ker (Ideal.Quotient.mk p.asIdeal) = q.asIdeal
      rw [Ideal.mk_ker]
      exact sup_eq_left.mpr hpq)

-- The covering relation is in PrimeSpectrum, not in the full ideal lattice.
example (B : Type) [CommRing B] (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    letI : p.asIdeal.IsPrime := p.isPrime
    letI := primeQuotient_map_isPrime B p q hpq.le
    (⊥ : PrimeSpectrum (B ⧸ p.asIdeal)) ⋖
      (⟨q.asIdeal.map (Ideal.Quotient.mk p.asIdeal), inferInstance⟩ :
        PrimeSpectrum (B ⧸ p.asIdeal)) := by
  fail_if_success
    have : p.asIdeal ⋖ q.asIdeal := hpq
  exact primeQuotient_bot_covBy_map B p q hpq

-- Height one in the quotient requires neither catenarity nor Noetherianity.
example (B : Type) [CommRing B] (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    letI := primeQuotient_map_isPrime B p q hpq.le
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).primeHeight = 1 := by
  fail_if_success
    have : IsDomain B := inferInstance
  fail_if_success
    have : IsNoetherianRing B := inferInstance
  exact primeQuotient_primeHeight_eq_one_of_covBy B p q hpq

-- Ordinary height agrees with the same actual quotient-prime calculation.
example (B : Type) [CommRing B] (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height = 1 := by
  letI := primeQuotient_map_isPrime B p q hpq.le
  rw [Ideal.height_eq_primeHeight]
  exact primeQuotient_primeHeight_eq_one_of_covBy B p q hpq

-- The unit drop allows a non-domain and nonreduced ambient finite-type algebra.
example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    (Algebra.trdeg k (B ⧸ q.asIdeal)).toNat + 1 =
      (Algebra.trdeg k (B ⧸ p.asIdeal)).toNat := by
  fail_if_success
    have : IsDomain B := inferInstance
  fail_if_success
    have : IsReduced B := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  exact primeQuotient_trdeg_toNat_add_one_of_covBy k B p q hpq

-- The adapter uses each actual prime-localization residue field.
example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    (Algebra.trdeg k q.asIdeal.ResidueField).toNat + 1 =
      (Algebra.trdeg k p.asIdeal.ResidueField).toNat :=
  prime_residueField_trdeg_toNat_add_one_of_covBy k B p q hpq

example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    ringKrullDim (B ⧸ q.asIdeal) + 1 = ringKrullDim (B ⧸ p.asIdeal) :=
  primeQuotient_dimension_add_one_of_covBy k B p q hpq

-- Direction check: proper specialization lowers the residue-field value by one.
example (k B : Type) [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (p q : PrimeSpectrum B) (hpq : p ⋖ q) :
    (Algebra.trdeg k q.asIdeal.ResidueField).toNat <
      (Algebra.trdeg k p.asIdeal.ResidueField).toNat := by
  have h := prime_residueField_trdeg_toNat_add_one_of_covBy k B p q hpq
  omega

-- A nonprime ideal really lies between (0) and (T) in the full ideal lattice.
example (k : Type) [Field k] :
    ¬ ((⊥ : Ideal (Polynomial k)) ⋖ Ideal.span {Polynomial.X}) := by
  intro h
  have hbot : (⊥ : Ideal (Polynomial k)) < Ideal.span {Polynomial.X ^ 2} := by
    apply bot_lt_iff_ne_bot.mpr
    intro heq
    exact (pow_ne_zero 2 Polynomial.X_ne_zero) (Ideal.span_singleton_eq_bot.mp heq)
  have hstrict : (Ideal.span {Polynomial.X ^ 2} : Ideal (Polynomial k)) <
      Ideal.span {Polynomial.X} :=
    Ideal.span_singleton_lt_span_singleton.mpr
      ⟨Polynomial.X_ne_zero, Polynomial.X, Polynomial.not_isUnit_X, pow_two _⟩
  exact h.2 hbot hstrict

-- A constructed cover in the genuinely reducible algebra k[T] × k satisfies the unit law.
example (k : Type) [Field k] :
    ∃ p q : PrimeSpectrum (Polynomial k × k), p ⋖ q ∧
      (Algebra.trdeg k ((Polynomial k × k) ⧸ q.asIdeal)).toNat + 1 =
        (Algebra.trdeg k ((Polynomial k × k) ⧸ p.asIdeal)).toNat := by
  let m := RingHom.ker (Polynomial.evalRingHom (0 : k))
  letI : m.IsMaximal := RingHom.ker_isMaximal_of_surjective
    (Polynomial.evalRingHom (0 : k)) (fun a ↦ ⟨Polynomial.C a, by simp⟩)
  let p : PrimeSpectrum (Polynomial k) := ⟨⊥, Ideal.bot_prime⟩
  let q : PrimeSpectrum (Polynomial k) := ⟨m, inferInstance⟩
  have hm : m ≠ ⊥ := by
    intro heq
    have hx : Polynomial.X ∈ m := by simp [m, RingHom.mem_ker]
    rw [heq, Ideal.mem_bot] at hx
    exact Polynomial.X_ne_zero hx
  have hpq : p ⋖ q := by
    refine ⟨show (⊥ : Ideal (Polynomial k)) < m from bot_lt_iff_ne_bot.mpr hm, ?_⟩
    intro r hpr hrq
    have hrne : r.asIdeal ≠ ⊥ := by
      intro heq
      exact hpr.ne (PrimeSpectrum.ext heq.symm)
    have hrmax := r.isPrime.isMaximal hrne
    exact hrq.ne (PrimeSpectrum.ext (hrmax.eq_of_le (inferInstance : m.IsPrime).ne_top hrq.le))
  let π := RingHom.fst (Polynomial k) k
  have hπ : Function.Surjective π := fun a ↦ ⟨(a, 0), rfl⟩
  let e : PrimeSpectrum (Polynomial k) ↪o PrimeSpectrum (Polynomial k × k) :=
    { toFun := π.specComap
      inj' := PrimeSpectrum.specComap_injective_of_surjective π hπ
      map_rel_iff' := fun {x y} ↦
        Ideal.comap_le_comap_iff_of_surjective π hπ x.asIdeal y.asIdeal }
  have he : (Set.range e).OrdConnected := by
    refine ⟨?_⟩
    rintro a ⟨a₀, rfl⟩ b _ c hc
    have hker : RingHom.ker π ≤ c.asIdeal := (Ideal.ker_le_comap π).trans hc.1
    refine ⟨⟨c.asIdeal.map π, c.asIdeal.map_isPrime_of_surjective hπ hker⟩, ?_⟩
    apply PrimeSpectrum.ext
    exact (c.asIdeal.comap_map_of_surjective π hπ).trans (sup_eq_left.mpr hker)
  have hcover := hpq.image e he
  exact ⟨e p, e q, hcover,
    primeQuotient_trdeg_toNat_add_one_of_covBy k (Polynomial k × k) (e p) (e q) hcover⟩

end ConsecutivePrimeDimensionRegressions

-- SP48: actual finite-type affine dimension functions and carrier grading.
#check HodgeConjecture.SchemeCycles.specPointOrderIso
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_apply
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_eq_pointHeight
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_nonneg
#check HodgeConjecture.SchemeCycles.supportDegree_ofSpecFiniteType_eq_iff
#check HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofSpecFiniteType_iff
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_apply
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_nonneg
#check HodgeConjecture.SchemeCycles.supportDegree_ofAffineLocallyOfFiniteType_eq_iff
#check HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff

#print axioms HodgeConjecture.SchemeCycles.specPointOrderIso
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_apply
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_eq_pointHeight
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_nonneg
#print axioms HodgeConjecture.SchemeCycles.supportDegree_ofSpecFiniteType_eq_iff
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofSpecFiniteType_iff
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_apply
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_nonneg
#print axioms HodgeConjecture.SchemeCycles.supportDegree_ofAffineLocallyOfFiniteType_eq_iff
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff

noncomputable section AffineDimensionFunctionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- The canonical order isomorphism preserves the actual point and reverses prime order.
example (A : Type) [CommRing A] (x : Spec (CommRingCat.of A)) :
    specPointOrderIso A x = OrderDual.toDual (show PrimeSpectrum A from x) := rfl

example (A : Type) [CommRing A] (p q : PrimeSpectrum A) (hpq : p ≤ q) :
    (show (Spec (CommRingCat.of A) : Scheme) from q) ≤
      (show (Spec (CommRingCat.of A) : Scheme) from p) :=
  (specPointOrderIso A).le_iff_le.mp hpq

-- Evaluation is the actual prime-localization residue degree, not an assumed grading law.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    DimensionFunction.ofSpecFiniteType k A x =
      ((Algebra.trdeg k x.asIdeal.ResidueField).toNat : ℤ) := by
  fail_if_success
    have : IsDomain A := inferInstance
  fail_if_success
    have : IsReduced A := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  rfl

-- Increasing prime ideals decrease the actual scheme dimension-function value.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (p q : PrimeSpectrum A) (hpq : p < q) :
    DimensionFunction.ofSpecFiniteType k A q < DimensionFunction.ofSpecFiniteType k A p := by
  apply (DimensionFunction.ofSpecFiniteType k A).strictMono
  exact (specPointOrderIso A).lt_iff_lt.mp hpq

-- Prime-spectrum covers and scheme covers have the opposite orientation.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (p q : PrimeSpectrum A) (hpq : p ⋖ q) :
    DimensionFunction.ofSpecFiniteType k A p =
      DimensionFunction.ofSpecFiniteType k A q + 1 := by
  apply (DimensionFunction.ofSpecFiniteType k A).map_covBy
  exact (specPointOrderIso A).map_covBy.mp hpq.toDual

example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    0 ≤ DimensionFunction.ofSpecFiniteType k A x ∧
      DimensionFunction.ofSpecFiniteType k A x = ((Order.height x).toNat : ℤ) :=
  ⟨DimensionFunction.ofSpecFiniteType_nonneg k A x,
    DimensionFunction.ofSpecFiniteType_eq_pointHeight k A x⟩

-- Existing integral supports retain the exact actual carrier-dimension criterion.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (W : IntegralClosedSubscheme (Spec (CommRingCat.of A))) (n : ℕ) :
    supportDegree (DimensionFunction.ofSpecFiniteType k A) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  supportDegree_ofSpecFiniteType_eq_iff k A W n

example (k A R : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [Semiring R] [Nontrivial R]
    (W : IntegralClosedSubscheme (Spec (CommRingCat.of A))) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofSpecFiniteType k A) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  fundamentalCycle_mem_ofSpecFiniteType_iff k A R W n

-- The actual empty spectrum of the zero algebra is allowed.
example (k : Type) [Field k] :
    IsEmpty (Spec (CommRingCat.of PUnit) : Scheme) ∧
      Nonempty (DimensionFunction (Spec (CommRingCat.of PUnit))) :=
  ⟨inferInstance, ⟨DimensionFunction.ofSpecFiniteType k PUnit⟩⟩

-- The actual reducible algebra k[T] × k also receives a constructed grading.
example (k : Type) [Field k] :
    Nonempty (DimensionFunction (Spec (CommRingCat.of (Polynomial k × k)))) := by
  fail_if_success
    have : IsDomain (Polynomial k × k) := inferInstance
  exact ⟨DimensionFunction.ofSpecFiniteType k (Polynomial k × k)⟩

-- In every number of variables, the generic point receives the full dimension.
example (k : Type) [Field k] (n : ℕ) :
    DimensionFunction.ofSpecFiniteType k (MvPolynomial (Fin n) k)
      (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))) = (n : ℤ) := by
  rw [DimensionFunction.ofSpecFiniteType_eq_pointHeight]
  have h : Order.height (genericPoint (Spec (CommRingCat.of (MvPolynomial (Fin n) k)))) =
      (n : ℕ∞) := by
    apply WithBot.coe_injective
    rw [genericPoint_height_eq_topologicalKrullDim]
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      mvPolynomial_ringKrullDim_eq_card]
    rfl
  simp only [h, ENat.toNat_coe]

-- Every closed polynomial point has degree zero, not just rational points.
example (k : Type) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k))
    [p.asIdeal.IsMaximal] : DimensionFunction.ofSpecFiniteType k (MvPolynomial (Fin n) k) p = 0 := by
  rw [DimensionFunction.ofSpecFiniteType_eq_pointHeight, spec_point_height_eq_prime_coheight]
  simp only [Order.coheight_eq_zero.mpr (PrimeSpectrum.isMax_iff.mpr inferInstance),
    ENat.toNat_zero, Nat.cast_zero]

-- The new constructor agrees pointwise with the existing low-dimensional constructor.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (hdim : topologicalKrullDim (Spec (CommRingCat.of A)) ≤ 1)
    (x : Spec (CommRingCat.of A)) :
    DimensionFunction.ofSpecFiniteType k A x =
      DimensionFunction.ofKrullDimLEOne (Spec (CommRingCat.of A)) hdim x := by
  rw [DimensionFunction.ofSpecFiniteType_eq_pointHeight,
    DimensionFunction.ofKrullDimLEOne_apply]

-- The actual affine-X input is a structural morphism, not a sections-algebra premise.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    DimensionFunction.ofAffineLocallyOfFiniteType k X p x = ((Order.height x).toNat : ℤ) := by
  fail_if_success
    have : Algebra k Γ(X, ⊤) := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : AlgebraicGeometry.IsReduced X := inferInstance
  rfl

example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x y : X) (hxy : x ⋖ y) :
    DimensionFunction.ofAffineLocallyOfFiniteType k X p y =
      DimensionFunction.ofAffineLocallyOfFiniteType k X p x + 1 :=
  (DimensionFunction.ofAffineLocallyOfFiniteType k X p).map_covBy hxy

example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    0 ≤ DimensionFunction.ofAffineLocallyOfFiniteType k X p x :=
  DimensionFunction.ofAffineLocallyOfFiniteType_nonneg k X p x

example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofAffineLocallyOfFiniteType k X p) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  supportDegree_ofAffineLocallyOfFiniteType_eq_iff k X p W n

example (k R : Type) [Field k] [Semiring R] [Nontrivial R] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈
        cyclesOfDegree R (DimensionFunction.ofAffineLocallyOfFiniteType k X p) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  fundamentalCycle_mem_ofAffineLocallyOfFiniteType_iff k X p R W n

-- The spectrum and structural-morphism presentations give the same intrinsic value.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x : Spec (CommRingCat.of A)) :
    DimensionFunction.ofAffineLocallyOfFiniteType k (Spec (CommRingCat.of A)) p x =
      DimensionFunction.ofSpecFiniteType k A x := by
  rw [DimensionFunction.ofAffineLocallyOfFiniteType_apply,
    DimensionFunction.ofSpecFiniteType_eq_pointHeight]

end AffineDimensionFunctionRegressions

-- SP49: structural scalar actions on actual scheme residue fields and affine comparison.
#check HodgeConjecture.SchemeCycles.residueFieldBaseMap
#check HodgeConjecture.SchemeCycles.residueFieldBaseAlgebra
#check HodgeConjecture.SchemeCycles.residueFieldBaseAlgebra_algebraMap
#check HodgeConjecture.SchemeCycles.residueFieldBaseMap_comp
#check HodgeConjecture.SchemeCycles.residueFieldBaseAlgHom
#check HodgeConjecture.SchemeCycles.residueFieldBaseAlgHom_apply
#check HodgeConjecture.SchemeCycles.residueFieldBaseAlgEquivOfIsOpenImmersion
#check HodgeConjecture.SchemeCycles.residueFieldBaseAlgEquivOfIsOpenImmersion_apply
#check HodgeConjecture.SchemeCycles.specResidueFieldEquiv
#check HodgeConjecture.SchemeCycles.specResidueFieldEquiv_evaluation
#check HodgeConjecture.SchemeCycles.specResidueFieldAlgEquiv
#check HodgeConjecture.SchemeCycles.specResidueFieldAlgEquiv_apply
#check HodgeConjecture.SchemeCycles.spec_schemeResidueField_trdeg_eq
#check HodgeConjecture.SchemeCycles.spec_schemeResidueField_trdeg_lt_aleph0
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg
#check HodgeConjecture.SchemeCycles.residueFieldBase_trdeg_eq_of_isOpenImmersion

#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseMap
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseAlgebra
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseAlgebra_algebraMap
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseMap_comp
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseAlgHom
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseAlgHom_apply
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseAlgEquivOfIsOpenImmersion
#print axioms HodgeConjecture.SchemeCycles.residueFieldBaseAlgEquivOfIsOpenImmersion_apply
#print axioms HodgeConjecture.SchemeCycles.specResidueFieldEquiv
#print axioms HodgeConjecture.SchemeCycles.specResidueFieldEquiv_evaluation
#print axioms HodgeConjecture.SchemeCycles.specResidueFieldAlgEquiv
#print axioms HodgeConjecture.SchemeCycles.specResidueFieldAlgEquiv_apply
#print axioms HodgeConjecture.SchemeCycles.spec_schemeResidueField_trdeg_eq
#print axioms HodgeConjecture.SchemeCycles.spec_schemeResidueField_trdeg_lt_aleph0
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg
#print axioms HodgeConjecture.SchemeCycles.residueFieldBase_trdeg_eq_of_isOpenImmersion

noncomputable section StructuralResidueFieldRegressions
open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- Structural constants come from the actual map and evaluation, before any comparison.
example (k : Type) [CommRing k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    residueFieldBaseMap k p x =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.Γevaluation x).hom := by
  fail_if_success
    have : Field k := inferInstance
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : LocallyOfFiniteType p := inferInstance
  fail_if_success
    have : Algebra k (X.residueField x) := inferInstance
  rfl

example (k : Type) [CommRing k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    letI := residueFieldBaseAlgebra k p x
    algebraMap k (X.residueField x) = residueFieldBaseMap k p x := rfl

-- Scalar compatibility is proved for the geometric residue map itself.
example (k : Type) [CommRing k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X) (a : k) :
    f.residueFieldMap x (residueFieldBaseMap k p (f.base x) a) =
      residueFieldBaseMap k (f ≫ p) x a :=
  DFunLike.congr_fun (residueFieldBaseMap_comp k p f x) a

example (k : Type) [CommRing k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (x : X)
    (a : Y.residueField (f.base x)) :
    residueFieldBaseAlgHom k p f x a = f.residueFieldMap x a := rfl

example (k : Type) [CommRing k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) (a : X.residueField x) :
    residueFieldBaseAlgHom k p (𝟙 X) x a = a := by
  simp only [residueFieldBaseAlgHom_apply, Scheme.residueFieldMap_id]
  rfl

example (k : Type) [CommRing k] (X Y Z : Scheme)
    (p : Z ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
    (a : Z.residueField (g.base (f.base x))) :
    residueFieldBaseAlgHom k p (f ≫ g) x a =
      residueFieldBaseAlgHom k (g ≫ p) f x
        (residueFieldBaseAlgHom k p g (f.base x) a) := by
  simp only [residueFieldBaseAlgHom_apply, Scheme.residueFieldMap_comp]
  rfl

-- The open-immersion equivalence retains the actual field map and its inverse.
example (k : Type) [CommRing k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (a : Y.residueField (f.base x)) :
    residueFieldBaseAlgEquivOfIsOpenImmersion k p f x a = f.residueFieldMap x a := rfl

example (k : Type) [CommRing k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsOpenImmersion f] (x : X)
    (a : Y.residueField (f.base x)) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    (residueFieldBaseAlgEquivOfIsOpenImmersion k p f x).symm
      (f.residueFieldMap x a) = a := by
  letI := residueFieldBaseAlgebra k p (f.base x)
  letI := residueFieldBaseAlgebra k (f ≫ p) x
  exact (residueFieldBaseAlgEquivOfIsOpenImmersion k p f x).symm_apply_apply a


-- The affine ring comparison is induced by the actual stalk isomorphism.
example (A : Type) [CommRing A] (x : Spec (CommRingCat.of A)) :
    letI : IsLocalRing ((Spec.structureSheaf A).presheaf.stalk x) :=
      inferInstanceAs (IsLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk x))
    specResidueFieldEquiv A x = IsLocalRing.ResidueField.mapEquiv
      (StructureSheaf.stalkIso A x).commRingCatIsoToRingEquiv := rfl

example (A : Type) [CommRing A] (x : Spec (CommRingCat.of A)) (a : A) :
    specResidueFieldEquiv A x
        ((Spec (CommRingCat.of A)).Γevaluation x ((Scheme.ΓSpecIso (.of A)).inv a)) =
      algebraMap A x.asIdeal.ResidueField a :=
  specResidueFieldEquiv_evaluation A x a

-- Base linearity is proved against the independently defined structural action.
example (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    (x : Spec (CommRingCat.of A)) (a : k) :
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    specResidueFieldAlgEquiv k A x
        (algebraMap k ((Spec (CommRingCat.of A)).residueField x) a) =
      algebraMap k x.asIdeal.ResidueField a := by
  fail_if_success
    have : Field k := inferInstance
  fail_if_success
    have : IsDomain A := inferInstance
  fail_if_success
    have : Algebra.FiniteType k A := inferInstance
  letI := residueFieldBaseAlgebra k
    (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
  exact (specResidueFieldAlgEquiv k A x).commutes a

example (k A : Type) [CommRing k] [CommRing A] [Algebra k A]
    (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    (specResidueFieldAlgEquiv k A x).toRingEquiv = specResidueFieldEquiv A x := rfl

-- A genuinely nonreduced algebra over the non-field base ℤ is allowed.
example :
    ¬ IsReduced (ZMod 4) ∧
      ∀ x : Spec (CommRingCat.of (ZMod 4)),
        letI := residueFieldBaseAlgebra ℤ
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 4)))) x
        Nonempty ((Spec (CommRingCat.of (ZMod 4))).residueField x ≃ₐ[ℤ]
          x.asIdeal.ResidueField) := by
  constructor
  · intro h
    have ht : IsNilpotent (2 : ZMod 4) := ⟨2, by decide⟩
    exact (by decide : (2 : ZMod 4) ≠ 0) (IsReduced.eq_zero _ ht)
  · intro x
    exact ⟨specResidueFieldAlgEquiv ℤ (ZMod 4) x⟩

-- The zero algebra's empty spectrum requires no artificial residue point.
example :
    IsEmpty (Spec (CommRingCat.of (PUnit : Type)) : Scheme) ∧
      ∀ x : Spec (CommRingCat.of (PUnit : Type)), Nonempty (Algebra ℤ
        ((Spec (CommRingCat.of (PUnit : Type))).residueField x)) :=
  ⟨inferInstance, fun x ↦ ⟨residueFieldBaseAlgebra ℤ
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (PUnit : Type)))) x⟩⟩

-- The full-cardinal comparison has no finite-type or reducedness premise.
example (k A : Type) [Field k] [CommRing A] [Algebra k A]
    (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x) =
      Algebra.trdeg k x.asIdeal.ResidueField := by
  fail_if_success
    have : Algebra.FiniteType k A := inferInstance
  fail_if_success
    have : IsReduced A := inferInstance
  exact spec_schemeResidueField_trdeg_eq k A x

example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x) < Cardinal.aleph0 := by
  fail_if_success
    have : IsDomain A := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  exact spec_schemeResidueField_trdeg_lt_aleph0 k A x

example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k A))) x
    DimensionFunction.ofSpecFiniteType k A x =
      ((Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x)).toNat : ℤ) :=
  DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg k A x

-- Open immersions preserve the actual structural-field cardinal, not merely a truncation.
example (k : Type) [Field k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    letI := residueFieldBaseAlgebra k p (f.base x)
    letI := residueFieldBaseAlgebra k (f ≫ p) x
    Algebra.trdeg k (Y.residueField (f.base x)) =
      Algebra.trdeg k (X.residueField x) := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : LocallyOfFiniteType p := inferInstance
  exact residueFieldBase_trdeg_eq_of_isOpenImmersion k p f x

-- At the zero prime of a countably generated polynomial algebra, the degree is genuinely infinite.
example (k : Type) [Field k] :
    let x : Spec (CommRingCat.of (MvPolynomial ℕ k)) := ⟨⊥, Ideal.bot_prime⟩
    letI := residueFieldBaseAlgebra k
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial ℕ k)))) x
    Algebra.trdeg k ((Spec (CommRingCat.of (MvPolynomial ℕ k))).residueField x) =
      Cardinal.aleph0 := by
  dsimp only
  rw [spec_schemeResidueField_trdeg_eq,
    ← primeQuotient_trdeg_eq_residueField k (MvPolynomial ℕ k)]
  change Algebra.trdeg k (MvPolynomial ℕ k ⧸ (⊥ : Ideal (MvPolynomial ℕ k))) = _
  rw [(AlgEquiv.quotientBot k (MvPolynomial ℕ k)).trdeg_eq]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_nat, Cardinal.lift_aleph0]

end StructuralResidueFieldRegressions

-- SP50: actual structural residue degrees on arbitrary affine schemes and affine-open compatibility.
#check HodgeConjecture.SchemeCycles.point_height_iso
#check HodgeConjecture.SchemeCycles.affine_schemeResidueField_trdeg_lt_aleph0
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion

#print axioms HodgeConjecture.SchemeCycles.point_height_iso
#print axioms HodgeConjecture.SchemeCycles.affine_schemeResidueField_trdeg_lt_aleph0
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion

noncomputable section AffineSchemeResidueDegreeRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory TopologicalSpace
open HodgeConjecture.SchemeCycles

-- The exposed existing height comparison applies to arbitrary scheme isomorphisms.
example (X Y : Scheme) (e : X ≅ Y) (x : X) :
    Order.height (e.hom.base x) = Order.height x := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  exact point_height_iso e x

-- Neither a sections algebra nor a residue-field algebra is an input.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  fail_if_success
    have : Algebra k Γ(X, ⊤) := inferInstance
  fail_if_success
    have : Algebra k (X.residueField x) := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : AlgebraicGeometry.IsReduced X := inferInstance
  fail_if_success
    have : CharZero k := inferInstance
  exact affine_schemeResidueField_trdeg_lt_aleph0 k X p x

example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    DimensionFunction.ofAffineLocallyOfFiniteType k X p x =
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) :=
  DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg k X p x

-- The structural affine-X and literal-spectrum functions agree via the same actual residue action.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    let p := Spec.map (CommRingCat.ofHom (algebraMap k A))
    letI : LocallyOfFiniteType p :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    DimensionFunction.ofAffineLocallyOfFiniteType k (Spec (CommRingCat.of A)) p x =
      DimensionFunction.ofSpecFiniteType k A x := by
  dsimp only
  rw [DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg,
    DimensionFunction.ofSpecFiniteType_eq_schemeResidueField_trdeg]

-- The canonical affine isomorphism respects constants under the actual transported structural map.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) (x : X) (a : k) :
    X.isoSpec.hom.residueFieldMap x
      (residueFieldBaseMap k (X.isoSpec.inv ≫ p) (X.isoSpec.hom.base x) a) =
        residueFieldBaseMap k p x a := by
  calc
    _ = residueFieldBaseMap k (X.isoSpec.hom ≫ (X.isoSpec.inv ≫ p)) x a :=
      DFunLike.congr_fun
        (residueFieldBaseMap_comp k (X.isoSpec.inv ≫ p) X.isoSpec.hom x) a
    _ = _ := by simp only [Iso.hom_inv_id_assoc]

-- Open-immersion compatibility derives the source finite-type condition from the actual maps.
example (k : Type) [Field k] (X Y : Scheme) [IsAffine X] [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    DimensionFunction.ofAffineLocallyOfFiniteType k X (f ≫ p) x =
      DimensionFunction.ofAffineLocallyOfFiniteType k Y p (f.base x) :=
  DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion k p f x

-- This specializes to the actual inclusion of an affine open subset.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (U : X.Opens) [IsAffine (U : Scheme)] (x : U) :
    DimensionFunction.ofAffineLocallyOfFiniteType k U (U.ι ≫ p) x =
      DimensionFunction.ofAffineLocallyOfFiniteType k X p x.val :=
  DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion k p U.ι x

example (k : Type) [Field k] (X Y Z : Scheme) [IsAffine X] [IsAffine Y] [IsAffine Z]
    (p : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z) [IsOpenImmersion g] (x : X) :
    DimensionFunction.ofAffineLocallyOfFiniteType k X ((f ≫ g) ≫ p) x =
      DimensionFunction.ofAffineLocallyOfFiniteType k Z p (g.base (f.base x)) :=
  DimensionFunction.ofAffineLocallyOfFiniteType_apply_of_isOpenImmersion k p (f ≫ g) x

-- The empty affine scheme is permitted, without choosing a residue point.
example (k : Type) [Field k] :
    IsEmpty (Spec (CommRingCat.of (PUnit : Type)) : Scheme) ∧
      ∀ x : Spec (CommRingCat.of (PUnit : Type)),
        let p := Spec.map (CommRingCat.ofHom (algebraMap k (PUnit : Type)))
        letI := residueFieldBaseAlgebra k p x
        Algebra.trdeg k ((Spec (CommRingCat.of (PUnit : Type))).residueField x) <
          Cardinal.aleph0 :=
  ⟨inferInstance, fun x ↦ affine_schemeResidueField_trdeg_lt_aleph0 k
    (Spec (CommRingCat.of (PUnit : Type))) _ x⟩

-- A concrete reducible ambient algebra needs no domain hypothesis.
example (k : Type) [Field k] (x : Spec (CommRingCat.of (k × k))) :
    let p := Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))
    letI : LocallyOfFiniteType p :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    letI := residueFieldBaseAlgebra k p x
    DimensionFunction.ofAffineLocallyOfFiniteType k (Spec (CommRingCat.of (k × k))) p x =
      ((Algebra.trdeg k ((Spec (CommRingCat.of (k × k))).residueField x)).toNat : ℤ) := by
  fail_if_success
    have : IsDomain (k × k) := inferInstance
  letI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg k
    (Spec (CommRingCat.of (k × k))) _ x

-- The existing support grading now has the same actual structural residue-degree criterion.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    letI := residueFieldBaseAlgebra k p (ambientGenericPoint W)
    ((Algebra.trdeg k (X.residueField (ambientGenericPoint W))).toNat : ℤ) = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  letI := residueFieldBaseAlgebra k p (ambientGenericPoint W)
  rw [← DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg k X p]
  exact supportDegree_ofAffineLocallyOfFiniteType_eq_iff k X p W n

example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    letI := residueFieldBaseAlgebra k p x
    DimensionFunction.ofKrullDimLEOne X hdim x =
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) := by
  letI := residueFieldBaseAlgebra k p x
  simpa only [DimensionFunction.ofKrullDimLEOne_apply,
    DimensionFunction.ofAffineLocallyOfFiniteType_apply] using
    DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg k X p x

-- The actual nonreduced dual-number quotient is another valid finite-type source.
example (k : Type) [Field k]
    (x : Spec (CommRingCat.of
      (Polynomial k ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))))) :
    let A := Polynomial k ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))
    let p := Spec.map (CommRingCat.ofHom (algebraMap k A))
    letI : LocallyOfFiniteType p :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    letI := residueFieldBaseAlgebra k p x
    DimensionFunction.ofAffineLocallyOfFiniteType k (Spec (CommRingCat.of A)) p x =
      ((Algebra.trdeg k ((Spec (CommRingCat.of A)).residueField x)).toNat : ℤ) := by
  let A := Polynomial k ⧸ Ideal.span ({Polynomial.X ^ 2} : Set (Polynomial k))
  letI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact DimensionFunction.ofAffineLocallyOfFiniteType_eq_schemeResidueField_trdeg k _ _ x

end AffineSchemeResidueDegreeRegressions

-- SP51: pointwise structural residue degrees and affine-chart agreement in a general ambient scheme.
#check HodgeConjecture.SchemeCycles.schemeResidueField_trdeg_lt_aleph0
#check HodgeConjecture.SchemeCycles.affineChart_dimension_eq_schemeResidueField_trdeg
#check HodgeConjecture.SchemeCycles.affineChart_dimension_eq_of_eq_image

#print axioms HodgeConjecture.SchemeCycles.schemeResidueField_trdeg_lt_aleph0
#print axioms HodgeConjecture.SchemeCycles.affineChart_dimension_eq_schemeResidueField_trdeg
#print axioms HodgeConjecture.SchemeCycles.affineChart_dimension_eq_of_eq_image

noncomputable section ChartResidueDegreeRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles

-- The pointwise theorem needs neither a global affine chart nor a finite cover.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    Algebra.trdeg k (X.residueField x) < Cardinal.aleph0 := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : CompactSpace X := inferInstance
  fail_if_success
    have : IsNoetherian X := inferInstance
  fail_if_success
    have : Algebra k Γ(X, ⊤) := inferInstance
  fail_if_success
    have : Algebra k (X.residueField x) := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  exact schemeResidueField_trdeg_lt_aleph0 k X p x

-- Proven pointwise finiteness makes conversion to a natural number lossless.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    ((Algebra.trdeg k (X.residueField x)).toNat : Cardinal) =
      Algebra.trdeg k (X.residueField x) := by
  letI := residueFieldBaseAlgebra k p x
  exact Cardinal.cast_toNat_of_lt_aleph0 (schemeResidueField_trdeg_lt_aleph0 k X p x)

-- The chart value is compared with the actual ambient field at its image.
example (k : Type) [Field k] (X U : Scheme) [IsAffine U]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    letI := residueFieldBaseAlgebra k p (i.base u)
    DimensionFunction.ofAffineLocallyOfFiniteType k U (i ≫ p) u =
      ((Algebra.trdeg k (X.residueField (i.base u))).toNat : ℤ) := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : CompactSpace X := inferInstance
  exact affineChart_dimension_eq_schemeResidueField_trdeg k p i u

-- This applies to the existing canonical affine-cover maps without new chart data.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : X.affineCover.I₀) (u : X.affineCover.X a) :
    letI := residueFieldBaseAlgebra k p ((X.affineCover.f a).base u)
    DimensionFunction.ofAffineLocallyOfFiniteType k (X.affineCover.X a)
        (X.affineCover.f a ≫ p) u =
      ((Algebra.trdeg k (X.residueField ((X.affineCover.f a).base u))).toNat : ℤ) :=
  affineChart_dimension_eq_schemeResidueField_trdeg k p (X.affineCover.f a) u

-- Every actual point has a chart preimage with that exact ambient point and value.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    ∃ (a : X.affineCover.I₀) (u : X.affineCover.X a),
      (X.affineCover.f a).base u = x ∧
      DimensionFunction.ofAffineLocallyOfFiniteType k (X.affineCover.X a)
          (X.affineCover.f a ≫ p) u =
        ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) := by
  obtain ⟨a, u, rfl⟩ := X.affineCover.exists_eq x
  exact ⟨a, u, rfl, affineChart_dimension_eq_schemeResidueField_trdeg k p
    (X.affineCover.f a) u⟩

-- The comparison consumes equality of actual ambient images.
example (k : Type) [Field k] (X U V : Scheme) [IsAffine U] [IsAffine V]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (i : U ⟶ X) [IsOpenImmersion i] (j : V ⟶ X) [IsOpenImmersion j]
    (u : U) (v : V) (h : i.base u = j.base v) :
    DimensionFunction.ofAffineLocallyOfFiniteType k U (i ≫ p) u =
      DimensionFunction.ofAffineLocallyOfFiniteType k V (j ≫ p) v :=
  affineChart_dimension_eq_of_eq_image k p i j u v h

-- Two actual affine open subsets give the same value at a common ambient point.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (U V : X.Opens) [IsAffine (U : Scheme)] [IsAffine (V : Scheme)]
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    DimensionFunction.ofAffineLocallyOfFiniteType k U (U.ι ≫ p) ⟨x, hxU⟩ =
      DimensionFunction.ofAffineLocallyOfFiniteType k V (V.ι ≫ p) ⟨x, hxV⟩ :=
  affineChart_dimension_eq_of_eq_image k p U.ι V.ι ⟨x, hxU⟩ ⟨x, hxV⟩ rfl

-- The identity chart recovers the preceding affine structural-value theorem.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    DimensionFunction.ofAffineLocallyOfFiniteType k X p x =
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) := by
  simpa only [Category.id_comp] using
    affineChart_dimension_eq_schemeResidueField_trdeg k p (𝟙 X) x

-- Empty schemes require no chosen residue point.
example (k : Type) [Field k] :
    IsEmpty (Spec (CommRingCat.of (PUnit : Type)) : Scheme) ∧
      ∀ x : Spec (CommRingCat.of (PUnit : Type)),
        let p := Spec.map (CommRingCat.ofHom (algebraMap k (PUnit : Type)))
        letI := residueFieldBaseAlgebra k p x
        Algebra.trdeg k ((Spec (CommRingCat.of (PUnit : Type))).residueField x) <
          Cardinal.aleph0 :=
  ⟨inferInstance, fun x ↦ schemeResidueField_trdeg_lt_aleph0 k
    (Spec (CommRingCat.of (PUnit : Type))) _ x⟩

-- One cannot drop the equal-image condition: even the affine line has different point values.
example (k : Type) [Field k] :
    let p := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
    letI : LocallyOfFiniteType p :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    ¬ ∀ x y : Examples.affineLine k,
      DimensionFunction.ofAffineLocallyOfFiniteType k (Examples.affineLine k) p x =
        DimensionFunction.ofAffineLocallyOfFiniteType k (Examples.affineLine k) p y := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
  letI : LocallyOfFiniteType p :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  dsimp only
  intro h
  have hv := h (genericPoint (Examples.affineLine k)) (Examples.affineLineOrigin k)
  change Examples.affineLineDimensionFunction k (genericPoint (Examples.affineLine k)) =
    Examples.affineLineDimensionFunction k (Examples.affineLineOrigin k) at hv
  rw [Examples.affineLineDimensionFunction_genericPoint,
    Examples.affineLineDimensionFunction_origin] at hv
  norm_num at hv

end ChartResidueDegreeRegressions

-- SP52: the constructed global field-induced dimension function and its actual specialization laws.
#check HodgeConjecture.SchemeCycles.exists_isAffineOpen_mem_of_le
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_apply
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_nonneg
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion

#print axioms HodgeConjecture.SchemeCycles.exists_isAffineOpen_mem_of_le
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_apply
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_nonneg
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion

noncomputable section FieldDimensionFunctionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCycles

-- Finding a common affine neighbourhood uses no field or finiteness assumption.
example (X : Scheme) (x y : X) (hxy : x ≤ y) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U :=
  exists_isAffineOpen_mem_of_le X hxy

-- Evaluation retains the independently defined structural scalar action.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    DimensionFunction.ofLocallyOfFiniteType k X p x =
      ((Algebra.trdeg k (X.residueField x)).toNat : ℤ) := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : CompactSpace X := inferInstance
  fail_if_success
    have : IsNoetherian X := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : Algebra k (X.residueField x) := inferInstance
  rfl

-- Both defining laws are proved for the global constructor.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x y : X) (hxy : x < y) :
    DimensionFunction.ofLocallyOfFiniteType k X p x <
      DimensionFunction.ofLocallyOfFiniteType k X p y :=
  (DimensionFunction.ofLocallyOfFiniteType k X p).strictMono hxy

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x y : X) (hxy : x ⋖ y) :
    DimensionFunction.ofLocallyOfFiniteType k X p y =
      DimensionFunction.ofLocallyOfFiniteType k X p x + 1 :=
  (DimensionFunction.ofLocallyOfFiniteType k X p).map_covBy hxy

-- Geometric proper specialization decreases the value, with the correct order orientation.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (x y : X) (hxy : x ⤳ y) (hne : x ≠ y) :
    DimensionFunction.ofLocallyOfFiniteType k X p y <
      DimensionFunction.ofLocallyOfFiniteType k X p x := by
  apply (DimensionFunction.ofLocallyOfFiniteType k X p).strictMono
  apply lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hxy)
  intro hyx
  exact hne (hxy.antisymm (Scheme.le_iff_specializes.mp hyx)).eq

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    0 ≤ DimensionFunction.ofLocallyOfFiniteType k X p x :=
  DimensionFunction.ofLocallyOfFiniteType_nonneg k X p x

-- Affine parity is equality of the entire existing dimension-function objects.
example (k : Type) [Field k] (X : Scheme) [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    DimensionFunction.ofLocallyOfFiniteType k X p =
      DimensionFunction.ofAffineLocallyOfFiniteType k X p :=
  DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType k X p

-- The literal-spectrum presentation is unchanged as well.
example (k A : Type) [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (x : Spec (CommRingCat.of A)) :
    let p := Spec.map (CommRingCat.ofHom (algebraMap k A))
    letI : LocallyOfFiniteType p :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    DimensionFunction.ofLocallyOfFiniteType k (Spec (CommRingCat.of A)) p x =
      DimensionFunction.ofSpecFiniteType k A x := by
  dsimp only
  rw [DimensionFunction.ofLocallyOfFiniteType_eq_ofAffineLocallyOfFiniteType,
    DimensionFunction.ofAffineLocallyOfFiniteType_apply,
    DimensionFunction.ofSpecFiniteType_eq_pointHeight]

-- Open value compatibility has no affine-source or affine-target premise.
example (k : Type) [Field k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    DimensionFunction.ofLocallyOfFiniteType k X (f ≫ p) x =
      DimensionFunction.ofLocallyOfFiniteType k Y p (f.base x) := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : IsAffine Y := inferInstance
  exact DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion k p f x

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (U : X.Opens) (x : U) :
    DimensionFunction.ofLocallyOfFiniteType k U (U.ι ≫ p) x =
      DimensionFunction.ofLocallyOfFiniteType k X p x.val :=
  DimensionFunction.ofLocallyOfFiniteType_apply_of_isOpenImmersion k p U.ι x

-- Existing integral-support degree is literal structural residue degree, not a new cycle type.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    letI := residueFieldBaseAlgebra k p (ambientGenericPoint W)
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W =
      ((Algebra.trdeg k (X.residueField (ambientGenericPoint W))).toNat : ℤ) := rfl

-- The old prime-divisor degree-drop theorem now consumes the constructed global function.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (Z : PrimeDivisor X) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) Z.val =
      DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - 1 :=
  supportDegree_primeDivisor (DimensionFunction.ofLocallyOfFiniteType k X p) Z

-- No point is selected on the empty scheme.
example (k : Type) [Field k] :
    IsEmpty (Spec (CommRingCat.of (PUnit : Type)) : Scheme) ∧
      Nonempty (DimensionFunction (Spec (CommRingCat.of (PUnit : Type)))) :=
  ⟨inferInstance, ⟨DimensionFunction.ofLocallyOfFiniteType k
    (Spec (CommRingCat.of (PUnit : Type)))
    (Spec.map (CommRingCat.ofHom (algebraMap k (PUnit : Type))))⟩⟩

-- The actual countable coproduct of points is noncompact and nonaffine, but has the constructed function.
example (k : Type) [Field k] :
    ∃ (X : Scheme) (p : X ⟶ Spec (CommRingCat.of k)),
      LocallyOfFiniteType p ∧ ¬ CompactSpace X ∧ ¬ IsAffine X ∧
        Nonempty (DimensionFunction X) := by
  let components : ℕ → Scheme := fun _ ↦ Spec (CommRingCat.of k)
  let X : Scheme := ∐ components
  let p : X ⟶ Spec (CommRingCat.of k) := Sigma.desc fun _ ↦ 𝟙 _
  haveI : LocallyOfFiniteType p :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType)
      (fun _ ↦ inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k)))))
  have hnc : ¬ CompactSpace X := by
    intro h
    letI : CompactSpace X := h
    let e := AlgebraicGeometry.sigmaMk components
    letI : CompactSpace (Σ n : ℕ, components n) := e.symm.compactSpace
    letI : Finite (Σ n : ℕ, components n) := finite_of_compact_of_discrete
    have hn : Finite ℕ := Finite.of_surjective
      (fun z : Σ n : ℕ, components n ↦ z.1) (fun n ↦ ⟨⟨n, default⟩, rfl⟩)
    exact hn.false
  have hna : ¬ IsAffine X := by
    intro h
    letI : IsAffine X := h
    exact hnc inferInstance
  exact ⟨X, p, inferInstance, hnc, hna,
    ⟨DimensionFunction.ofLocallyOfFiniteType k X p⟩⟩

end FieldDimensionFunctionRegressions

-- SP53: global point height, actual support dimension and existing finite-cycle grading.
#check HodgeConjecture.SchemeCycles.point_height_eq_ofLocallyOfFiniteType
#check HodgeConjecture.SchemeCycles.point_height_ne_top_of_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight
#check HodgeConjecture.SchemeCycles.pointSupport_dimension_eq_ofLocallyOfFiniteType
#check HodgeConjecture.SchemeCycles.supportDegree_ofLocallyOfFiniteType_eq_iff
#check HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofLocallyOfFiniteType_iff
#check HodgeConjecture.SchemeCycles.point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType

#print axioms HodgeConjecture.SchemeCycles.point_height_eq_ofLocallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.point_height_ne_top_of_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight
#print axioms HodgeConjecture.SchemeCycles.pointSupport_dimension_eq_ofLocallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.supportDegree_ofLocallyOfFiniteType_eq_iff
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_ofLocallyOfFiniteType_iff
#print axioms HodgeConjecture.SchemeCycles.point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType

noncomputable section FieldSupportDimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open HodgeConjecture.SchemeCycles

-- The pointwise comparison imposes no affine or global finiteness hypothesis.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    Order.height x = ((Algebra.trdeg k (X.residueField x)).toNat : ℕ∞) := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : CompactSpace X := inferInstance
  fail_if_success
    have : IsNoetherian X := inferInstance
  fail_if_success
    have : IsIntegral X := inferInstance
  fail_if_success
    have : Algebra k (X.residueField x) := inferInstance
  simpa only [DimensionFunction.ofLocallyOfFiniteType_apply, Int.toNat_natCast] using
    point_height_eq_ofLocallyOfFiniteType k X p x

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    Order.height x ≠ ⊤ :=
  point_height_ne_top_of_locallyOfFiniteType k X p x

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    DimensionFunction.ofLocallyOfFiniteType k X p x = ((Order.height x).toNat : ℤ) :=
  DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight k X p x

-- The carrier is the existing actual reduced closure, not a new dimension label.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    letI := residueFieldBaseAlgebra k p x
    topologicalKrullDim (pointSupport X x).val.subscheme =
      ((Algebra.trdeg k (X.residueField x)).toNat : WithBot ℕ∞) := by
  simpa only [DimensionFunction.ofLocallyOfFiniteType_apply, Int.toNat_natCast] using
    pointSupport_dimension_eq_ofLocallyOfFiniteType k X p x

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  supportDegree_ofLocallyOfFiniteType_eq_iff k X p W n

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type) [Semiring R] [Nontrivial R] (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) :=
  fundamentalCycle_mem_ofLocallyOfFiniteType_iff k X p R W n

-- Arbitrary finite cycles use the same supported submodule and geometric carrier test.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type) [Semiring R] (c : Cycles X R) (n : ℕ) :
    c ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p) n ↔
      ∀ W : IntegralClosedSubscheme X, c W ≠ 0 →
        topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  rw [mem_cyclesOfDegree_iff]
  constructor
  · intro h W hW
    exact (supportDegree_ofLocallyOfFiniteType_eq_iff k X p W n).mp (h W hW)
  · intro h W hW
    exact (supportDegree_ofLocallyOfFiniteType_eq_iff k X p W n).mpr (h W hW)

-- Negative degrees cannot contain a nonzero fundamental cycle.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type) [Semiring R] [Nontrivial R] (W : IntegralClosedSubscheme X)
    (n : ℤ) (hn : n < 0) :
    fundamentalCycle R W ∉ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p) n := by
  intro h
  have hdeg := (fundamentalCycle_mem_cyclesOfDegree_iff R
    (DimensionFunction.ofLocallyOfFiniteType k X p) n W).mp h
  have hnon := DimensionFunction.ofLocallyOfFiniteType_nonneg k X p (ambientGenericPoint W)
  change DimensionFunction.ofLocallyOfFiniteType k X p (ambientGenericPoint W) = n at hdeg
  omega

-- With trivial coefficients every fundamental cycle vanishes; no converse is inferred.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℤ) :
    fundamentalCycle (PUnit : Type) W ∈
      cyclesOfDegree (PUnit : Type) (DimensionFunction.ofLocallyOfFiniteType k X p) n := by
  fail_if_success
    have : Nontrivial (PUnit : Type) := inferInstance
  have hz : fundamentalCycle (PUnit : Type) W = 0 := Subsingleton.elim _ _
  rw [hz]
  exact Submodule.zero_mem _

-- Open-height invariance is qualified by the locally finite-type structural map.
example (k : Type) [Field k] (X Y : Scheme)
    (p : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    Order.height (f.base x) = Order.height x := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : IsAffine Y := inferInstance
  exact (point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType k p f x).symm

example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (U : X.Opens) (x : U) :
    Order.height (x.val : X) =
      @Order.height (U : Scheme) (specializationPreorder (U : Scheme)) x :=
  (point_height_eq_of_isOpenImmersion_of_locallyOfFiniteType k p U.ι x).symm

-- Empty schemes require no selected point or integrality hypothesis.
example (k : Type) [Field k] :
    IsEmpty (Spec (CommRingCat.of (PUnit : Type)) : Scheme) ∧
      ∀ x : Spec (CommRingCat.of (PUnit : Type)), Order.height x ≠ ⊤ :=
  ⟨inferInstance, fun x ↦ point_height_ne_top_of_locallyOfFiniteType k
    (Spec (CommRingCat.of (PUnit : Type)))
    (Spec.map (CommRingCat.ofHom (algebraMap k (PUnit : Type)))) x⟩

-- The same actual noncompact coproduct from SP52 now has finite height at every point.
example (k : Type) [Field k] :
    ∃ (X : Scheme) (p : X ⟶ Spec (CommRingCat.of k)),
      LocallyOfFiniteType p ∧ ¬ CompactSpace X ∧ ¬ IsAffine X ∧
        ∀ x : X, Order.height x ≠ ⊤ := by
  let components : ℕ → Scheme := fun _ ↦ Spec (CommRingCat.of k)
  let X : Scheme := ∐ components
  let p : X ⟶ Spec (CommRingCat.of k) := Sigma.desc fun _ ↦ 𝟙 _
  haveI : LocallyOfFiniteType p :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType)
      (fun _ ↦ inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of k)))))
  have hnc : ¬ CompactSpace X := by
    intro h
    letI : CompactSpace X := h
    let e := AlgebraicGeometry.sigmaMk components
    letI : CompactSpace (Σ n : ℕ, components n) := e.symm.compactSpace
    letI : Finite (Σ n : ℕ, components n) := finite_of_compact_of_discrete
    have hn : Finite ℕ := Finite.of_surjective
      (fun z : Σ n : ℕ, components n ↦ z.1) (fun n ↦ ⟨⟨n, default⟩, rfl⟩)
    exact hn.false
  have hna : ¬ IsAffine X := by
    intro h
    letI : IsAffine X := h
    exact hnc inferInstance
  exact ⟨X, p, inferInstance, hnc, hna, point_height_ne_top_of_locallyOfFiniteType k X p⟩

-- Each actual integral carrier has finite dimension, without asserting a uniform ambient bound.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    topologicalKrullDim W.val.subscheme < ⊤ := by
  rw [← ambientGenericPoint_height_eq_supportDim]
  exact WithBot.coe_lt_coe.mpr (lt_top_iff_ne_top.mpr
    (point_height_ne_top_of_locallyOfFiniteType k X p (ambientGenericPoint W)))

end FieldSupportDimensionRegressions

-- SP54: actual integral codimension, ambient dimension and the existing d-minus-n grading.
#check HodgeConjecture.SchemeCycles.integral_topologicalKrullDim_eq_ofLocallyOfFiniteType
#check HodgeConjecture.SchemeCycles.point_coheight_ne_top_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.point_coheight_add_dimension_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.supportCodimension_ne_top_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.supportCodimension_add_dimension_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
#check HodgeConjecture.SchemeCycles.mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType

#print axioms HodgeConjecture.SchemeCycles.integral_topologicalKrullDim_eq_ofLocallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.point_coheight_ne_top_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.point_coheight_add_dimension_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.supportCodimension_ne_top_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.supportCodimension_add_dimension_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType
#print axioms HodgeConjecture.SchemeCycles.mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType

noncomputable section IntegralCodimensionRegressions

open HodgeConjecture AlgebraicGeometry CategoryTheory TopologicalSpace
open HodgeConjecture.SchemeCycles

-- Integral locally finite-type schemes need no affine or quasi-compact hypothesis here.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    topologicalKrullDim X < ⊤ := by
  fail_if_success
    have : IsAffine X := inferInstance
  fail_if_success
    have : CompactSpace X := inferInstance
  fail_if_success
    have : IsNoetherian X := inferInstance
  rw [integral_topologicalKrullDim_eq_ofLocallyOfFiniteType k X p]
  exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)

example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    Order.coheight x ≠ ⊤ :=
  point_coheight_ne_top_of_integral_locallyOfFiniteType k X p x

-- Actual coheight, not a newly defined dimension difference, measures the degree drop.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    ((Order.coheight x).toNat : ℤ) + DimensionFunction.ofLocallyOfFiniteType k X p x =
      DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) :=
  point_coheight_add_dimension_of_integral_locallyOfFiniteType k X p x

-- Conversion from the actual chain coheight to a natural number loses no information.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (x : X) :
    ((Order.coheight x).toNat : ℕ∞) = Order.coheight x :=
  ENat.coe_toNat (point_coheight_ne_top_of_integral_locallyOfFiniteType k X p x)

-- The ambient stalk is the already identified actual chain-codimension object.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    ringKrullDim (X.presheaf.stalk (ambientGenericPoint W)) +
        topologicalKrullDim W.val.subscheme = topologicalKrullDim X := by
  rw [← supportCodimension_eq_stalkDim]
  exact supportCodimension_add_dimension_of_integral_locallyOfFiniteType k X p W

example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    (supportCodimension W : WithBot ℕ∞) + topologicalKrullDim W.val.subscheme =
      topologicalKrullDim X :=
  supportCodimension_add_dimension_of_integral_locallyOfFiniteType k X p W

example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W =
        DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ) ↔
      supportCodimension W = (n : ℕ∞) :=
  supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType k X p W n

example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type) [Semiring R] [Nontrivial R] (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ)) ↔
      supportCodimension W = (n : ℕ∞) :=
  fundamentalCycle_mem_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType k X p R W n

-- The full-cycle test does not require nontrivial coefficients.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type) [Semiring R] (c : Cycles X R) (n : ℕ) :
    c ∈ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ)) ↔
      ∀ W : IntegralClosedSubscheme X, c W ≠ 0 → supportCodimension W = (n : ℕ∞) :=
  mem_cyclesOfDegree_sub_iff_supportCodimension_of_integral_locallyOfFiniteType k X p R n c

-- The shifted degree is an integer: n greater than d does not truncate to degree zero.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (R : Type) [Semiring R] [Nontrivial R] (W : IntegralClosedSubscheme X) (n : ℕ)
    (hn : DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) < (n : ℤ)) :
    fundamentalCycle R W ∉ cyclesOfDegree R (DimensionFunction.ofLocallyOfFiniteType k X p)
      (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ)) := by
  intro h
  have hdeg := (fundamentalCycle_mem_cyclesOfDegree_iff R
    (DimensionFunction.ofLocallyOfFiniteType k X p) _ W).mp h
  have hnon := DimensionFunction.ofLocallyOfFiniteType_nonneg k X p (ambientGenericPoint W)
  change DimensionFunction.ofLocallyOfFiniteType k X p (ambientGenericPoint W) = _ at hdeg
  omega

-- Trivial coefficients have zero fundamental cycles at every shifted degree.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle (PUnit : Type) W ∈
      cyclesOfDegree (PUnit : Type) (DimensionFunction.ofLocallyOfFiniteType k X p)
        (DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - (n : ℤ)) := by
  fail_if_success
    have : Nontrivial (PUnit : Type) := inferInstance
  have hz : fundamentalCycle (PUnit : Type) W = 0 := Subsingleton.elim _ _
  rw [hz]
  exact Submodule.zero_mem _

-- The generic support has actual chain codimension zero.
example (X : Scheme) [IsIntegral X] :
    supportCodimension (pointSupport X (genericPoint X)) = 0 := by
  rw [supportCodimension, integralSupport_eq_pointClosure, pointClosure_coheight,
    ambientGenericPoint_pointSupport]
  apply Order.coheight_eq_zero.mpr
  intro y _
  exact Scheme.le_iff_specializes.mpr (genericPoint_specializes y)

-- The old prime-divisor subtype is detected in degree d - 1.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (Z : PrimeDivisor X) :
    supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) Z.val =
      DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) - 1 := by
  simpa only [Nat.cast_one] using
    (supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType k X p Z.val 1).mpr Z.property

-- The actual affine-line origin has codimension one.
example (k : Type) [Field k] :
    supportCodimension (pointSupport (Examples.affineLine k) (Examples.affineLineOrigin k)) = 1 := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))
  letI : LocallyOfFiniteType p :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  apply (supportDegree_eq_sub_iff_supportCodimension_eq_of_integral_locallyOfFiniteType k (Examples.affineLine k) p
    (pointSupport (Examples.affineLine k) (Examples.affineLineOrigin k)) 1).mp
  rw [supportDegree, ambientGenericPoint_pointSupport,
    DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight,
    DimensionFunction.ofLocallyOfFiniteType_eq_pointHeight]
  change Examples.affineLineDimensionFunction k (Examples.affineLineOrigin k) =
    Examples.affineLineDimensionFunction k (genericPoint (Examples.affineLine k)) - (1 : ℤ)
  rw [Examples.affineLineDimensionFunction_origin, Examples.affineLineDimensionFunction_genericPoint]
  norm_num

-- The actual support codimension recovers from its finite value and adds to the existing degree.
example (k : Type) [Field k] (X : Scheme) [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (W : IntegralClosedSubscheme X) :
    ((supportCodimension W).toNat : ℕ∞) = supportCodimension W ∧
      ((supportCodimension W).toNat : ℤ) +
          supportDegree (DimensionFunction.ofLocallyOfFiniteType k X p) W =
        DimensionFunction.ofLocallyOfFiniteType k X p (genericPoint X) :=
  ⟨ENat.coe_toNat (supportCodimension_ne_top_of_integral_locallyOfFiniteType k X p W),
    supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType k X p W⟩

-- Integrality is a genuine premise of the uniform ambient shift, not inferred from locally finite type.
example (k : Type) [Field k] (X : Scheme)
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] : True := by
  fail_if_success
    have h := integral_topologicalKrullDim_eq_ofLocallyOfFiniteType k X p
  trivial

end IntegralCodimensionRegressions
