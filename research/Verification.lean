import HodgeConjecture
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
#check HodgeConjecture.MatrixRestrictionObstruction.no_ringHom_to_commutative
#check HodgeConjecture.MatrixRestrictionObstruction.no_algHom_to_pointwise_sheets

#print axioms HodgeConjecture.SplitPointGeometry.pointProjector_isIdempotent
#print axioms HodgeConjecture.SplitPointCorrespondence.palomarTargetSquare
#print axioms HodgeConjecture.MatrixRestrictionObstruction.no_ringHom_to_commutative

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
