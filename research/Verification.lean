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
