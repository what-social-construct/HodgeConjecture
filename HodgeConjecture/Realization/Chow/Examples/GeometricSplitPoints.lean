import HodgeConjecture.Realization.Chow.Examples.SplitSpanQuotient
import HodgeConjecture.Realization.Chow.Examples.SplitPoints

/-!
# The two-point realization square with a geometric source

The first-point projector now starts in the free rational algebra of actual
finite split scheme-span classes. Its image in the existing finite-étale span
algebra is the previously constructed geometric point projector. The intrinsic
cycle-coefficient realization sends it to the first matrix unit, so the earlier
constant-coordinate calculation supplies its graph-projector action.

The initial source is a free span algebra. The action and its universal
idempotent square also descend to the explicit finite-additivity quotient.
`SplitChowAlgebra` identifies that quotient with the actual finite split
Chow correspondence algebra, and `SplitChowAction` computes its Chow action.
The singular-cohomology comparison is separate.
-/

set_option autoImplicit false

namespace HodgeConjecture.GeometricSplitPoints

noncomputable section

open Classical

variable (K : Type) [Field K]

/-- The actual-source algebra, freely linearized from geometric split classes. -/
abbrev Source := SplitSpanRealization.FreeAlgebra K (Fin 2)

/-- The first-point span chosen geometrically, before taking its coefficients. -/
def projector : Source K :=
  SplitSpanRealization.ofSchemeSpan K (Fin 2)
    (fun _ : PUnit => 0) (fun _ : PUnit => 0)

/-- Forgetting split-presentability recovers exactly the earlier geometric
point projector, not merely an element with the same matrix. -/
theorem projector_toFiniteEtaleFreeAlgebra :
    SplitSpanRealization.toFiniteEtaleFreeAlgebra K (Fin 2) (projector K) =
      SplitPointGeometry.pointProjector K (Fin 2) 0 := by
  rw [projector, SplitSpanRealization.toFiniteEtaleFreeAlgebra_ofSchemeSpan]
  unfold SplitPointGeometry.pointProjector SchemeCorrespondence.finiteEtaleOfScheme
  congr 1
  apply Subtype.ext
  exact SchemeCorrespondence.classOf_eq_of_isom
    (SplitPointGeometry.span_point_iso K (Fin 2) 0)

/-- Source-side idempotence is inherited through the injective geometric
inclusion from the actual point-span pullback calculation. -/
theorem projector_isIdempotent : IsIdempotentElem (projector K) := by
  change projector K * projector K = projector K
  apply SplitSpanRealization.toFiniteEtaleFreeAlgebra_injective K (Fin 2)
  rw [map_mul, projector_toFiniteEtaleFreeAlgebra]
  exact SplitPointGeometry.pointProjector_isIdempotent K (Fin 2) 0

/-- The constructed coefficient map takes the geometric first-point projector
to the first matrix unit. -/
theorem matrixRealization_projector :
    SplitSpanRealization.realization K (Fin 2) (projector K) =
      SplitPointCorrespondence.firstPointProjector := by
  rw [projector, SplitSpanRealization.realization_ofSchemeSpan]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteSpanMatrix.matrix, SplitPointCorrespondence.firstPointProjector]

/-- The geometric source acts on the rational coefficient module in its
constant-unit coordinates. No genuine Betti comparison is asserted. -/
def coefficientRealization : Source K →ₐ[ℚ] Module.End ℚ (ℚ × ℚ) :=
  SplitPointCorrespondence.realization.comp (SplitSpanRealization.realization K (Fin 2))

/-- The source-to-graph-projector action follows from the proved span-to-matrix
map and the earlier explicit change of coordinates. -/
theorem coefficientRealization_projector :
    coefficientRealization K (projector K) =
      ClassGraphProjector.operator (-1 : ℚ) := by
  simp only [coefficientRealization, AlgHom.comp_apply, matrixRealization_projector]
  exact SplitPointCorrespondence.realization_firstPointProjector

/-- The coefficient action with its actual geometric span source. -/
def correspondenceAction : RationalCorrespondenceAction (Source K) (ℚ × ℚ) :=
  ⟨coefficientRealization K⟩

/-- The marked comparison now has a geometric-source projector. Its residual
map is the existing second-coordinate evaluation, and its square is proved. -/
def markedComparison :
    MarkedProjectorActionComparison SplitPointCorrespondence.markedSource
      (correspondenceAction K) (projector K) where
  residualRealization := SplitPointCorrespondence.residualEvaluation
  action_intertwines := by
    change (coefficientRealization K (projector K)).comp
        (SplitPointCorrespondence.markedSource.productRealization
          SplitPointCorrespondence.residualEvaluation) = _
    rw [coefficientRealization_projector]
    simpa [MarkedAugmentedAlgebra.generatedClass] using
      (SplitPointCorrespondence.markedSource.productRealization_intertwines_selectorMultiplication
        SplitPointCorrespondence.residualEvaluation).symm

@[simp]
theorem markedComparison_generatedClass :
    SplitPointCorrespondence.markedSource.generatedClass
      (markedComparison K).residualRealization = -1 :=
  SplitPointCorrespondence.residualEvaluation_residualClass

/-- A projector lift in the actual geometric-source algebra, with coefficient
realization. This is not a claim of Chow/Betti realization. -/
def projectorLift :
    AlgebraicProjectorLift (correspondenceAction K)
      (ClassGraphProjector.operator (-1 : ℚ)) := by
  simpa only [markedComparison_generatedClass] using
    (markedComparison K).toAlgebraicProjectorLift
      (projector_isIdempotent K) SplitPointCorrespondence.residualEvaluation_surjective

/-- The unital algebra-homomorphism square, now starting with the geometric
point-span idempotent rather than a matrix chosen in the target algebra. -/
theorem palomarTargetSquare :
    (coefficientRealization K).comp
        (UniversalIdempotentAlgebra.mapOfIdempotent
          (projector K) (projector_isIdempotent K)) =
      UniversalIdempotentAlgebra.mapOfIdempotent
        (ClassGraphProjector.operator (-1 : ℚ))
        (ClassGraphProjector.operator_isIdempotent (-1 : ℚ)) := by
  simpa only [markedComparison_generatedClass] using
    (markedComparison K).action_comp_idempotentMap_eq_classGraph
      (projector_isIdempotent K) SplitPointCorrespondence.residualEvaluation_surjective

/-- The same coefficient action after imposing the geometric finite-point
decomposition relations. This is not a new marked-comparison assumption. -/
def additiveCoefficientRealization :
    SplitSpanRealization.AdditiveQuotient K (Fin 2) →ₐ[ℚ] Module.End ℚ (ℚ × ℚ) :=
  SplitPointCorrespondence.realization.comp
    (SplitSpanRealization.quotientRealization K (Fin 2))

/-- The descended action agrees with the constructed raw geometric action. -/
theorem additiveCoefficientRealization_comp_classMap :
    (additiveCoefficientRealization K).comp
        (SplitSpanRealization.additivePresentation K (Fin 2)).classMap =
      coefficientRealization K := by
  apply AlgHom.ext
  intro x
  rfl

/-- The Palomar target square survives passage to the additive quotient,
by naturality of the universal idempotent map. No new realization data enter. -/
theorem additivePalomarTargetSquare :
    (additiveCoefficientRealization K).comp
        (UniversalIdempotentAlgebra.mapOfIdempotent
          ((SplitSpanRealization.additivePresentation K (Fin 2)).classMap (projector K))
          ((projector_isIdempotent K).map
            (SplitSpanRealization.additivePresentation K (Fin 2)).classMap)) =
      UniversalIdempotentAlgebra.mapOfIdempotent
        (ClassGraphProjector.operator (-1 : ℚ))
        (ClassGraphProjector.operator_isIdempotent (-1 : ℚ)) := by
  rw [← UniversalIdempotentAlgebra.comp_mapOfIdempotent,
    ← AlgHom.comp_assoc, additiveCoefficientRealization_comp_classMap]
  exact palomarTargetSquare K

end

end HodgeConjecture.GeometricSplitPoints
