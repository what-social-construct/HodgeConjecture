import HodgeConjecture.Realization.Chow.MarkedAugmentedRealization
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Two split points: a finite zero-cycle and correspondence calculation

This calculation uses rational functions on two labels as the
zero-cycle module and matrices as the correspondence algebra. Matrix
multiplication is the finite correspondence convolution. The primitive
correspondence at the first point is chosen before any target class.

The coordinate change from the two point basis to the constant-unit splitting
sends `(a,b)` to `(a,b-a)`. In those coordinates the first point correspondence
realizes the graph projector of the specific residual class `-1`.

This file does not identify these finite models with scheme-theoretic Chow
groups or singular cohomology. It does not construct a cover or establish
coverage of prescribed Hodge classes.
`Examples.GeometricSplitPoints` connects this coefficient calculation to an
actual scheme-span source through the proved split-span matrix realization.
`Examples.SplitChowAlgebra` and `Examples.SplitChowAction` subsequently
identify the additive span quotient and these coefficient operations with
the actual finite split Chow correspondences and their action.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitPointCorrespondence

noncomputable section

abbrev ZeroCycles := Fin 2 → ℚ
abbrev Correspondence := Matrix (Fin 2) (Fin 2) ℚ

/-- The correspondence supported on the ordered pair of first points. -/
def firstPointProjector : Correspondence := !![1, 0; 0, 0]

/-- Idempotence follows from the finite convolution, with no realization
compatibility assumed. -/
theorem firstPointProjector_isIdempotent :
    IsIdempotentElem firstPointProjector := by
  change firstPointProjector * firstPointProjector = firstPointProjector
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstPointProjector, Matrix.mul_apply, Fin.sum_univ_two]

/-- The action of finite correspondences on rational zero-cycles. -/
def pointRealization : Correspondence →ₐ[ℚ] Module.End ℚ ZeroCycles :=
  Matrix.toLinAlgEquiv'.toAlgHom

@[simp]
theorem pointRealization_apply (c : Correspondence) (z : ZeroCycles) :
    pointRealization c z = c.mulVec z := rfl

theorem pointRealization_convolution (c d : Correspondence) :
    pointRealization (c * d) = pointRealization c * pointRealization d :=
  map_mul pointRealization c d

/-- The ordinary two point coordinates. -/
def pointCoordinates : ZeroCycles ≃ₗ[ℚ] ℚ × ℚ where
  toFun z := (z 0, z 1)
  invFun z := ![z.1, z.2]
  left_inv z := by
    funext i
    fin_cases i <;> rfl
  right_inv z := by cases z; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The marked product algebra, augmented at the first point. -/
def markedSource : MarkedAugmentedAlgebra ℚ (ℚ × ℚ) where
  augmentation := AlgHom.fst ℚ ℚ ℚ
  selector := (1, 0)
  augmentation_selector := rfl
  selector_mul a := by
    apply Prod.ext <;> simp

/-- Evaluating the residual ideal at the second point. -/
def residualEvaluation : markedSource.Residual →ₗ[ℚ] ℚ where
  toFun x := (x.val).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem residualEvaluation_residualClass :
    residualEvaluation markedSource.residualClass = -1 := by
  norm_num [residualEvaluation, MarkedAugmentedAlgebra.residualClass,
    markedSource]

theorem residualEvaluation_surjective :
    Function.Surjective residualEvaluation := by
  intro r
  refine ⟨⟨(0, r), ?_⟩, rfl⟩
  rfl

/-- Point coordinates followed by the fixed constant-unit coordinate change. -/
def constantCoordinates : ZeroCycles ≃ₗ[ℚ] ℚ × ℚ :=
  pointCoordinates.trans (ClassGraphProjector.shear (-1 : ℚ))

@[simp]
theorem constantCoordinates_apply (z : ZeroCycles) :
    constantCoordinates z = (z 0, z 1 - z 0) := by
  simp [constantCoordinates, pointCoordinates, sub_eq_add_neg]

/-- These are precisely the coordinates from the marked algebra decomposition,
followed by residual evaluation. -/
theorem constantCoordinates_eq_markedDecomposition (z : ZeroCycles) :
    constantCoordinates z =
      ((markedSource.decomposition (pointCoordinates z)).1,
       residualEvaluation (markedSource.decomposition (pointCoordinates z)).2) := by
  apply Prod.ext <;>
    simp [constantCoordinates, pointCoordinates, residualEvaluation,
      markedSource, MarkedAugmentedAlgebra.decomposition, sub_eq_add_neg]

/-- Conjugation transports the entire finite correspondence algebra into the
constant-unit coordinates. -/
def coordinateChange :
    Module.End ℚ ZeroCycles ≃ₐ[ℚ] Module.End ℚ (ℚ × ℚ) :=
  AlgEquiv.ofLinearEquiv constantCoordinates.conj
    (by exact constantCoordinates.conj_id)
    (fun c d => constantCoordinates.conj_comp d c)

def realization : Correspondence →ₐ[ℚ] Module.End ℚ (ℚ × ℚ) :=
  coordinateChange.toAlgHom.comp pointRealization

/-- The first point correspondence acts diagonally in point coordinates. -/
theorem pointCoordinates_firstPointProjector (z : ZeroCycles) :
    pointCoordinates (pointRealization firstPointProjector z) = (z 0, 0) := by
  simp [pointCoordinates, dotProduct,
    firstPointProjector, Fin.sum_univ_two]

/-- The computed realization square; the class is the fixed residual value
of the first-point selector, rather than an independently prescribed class. -/
theorem realization_firstPointProjector :
    realization firstPointProjector = ClassGraphProjector.operator (-1 : ℚ) := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  change constantCoordinates
      (pointRealization firstPointProjector (constantCoordinates.symm (t, x))) = _
  simp [constantCoordinates, LinearEquiv.trans_apply, pointCoordinates,
    firstPointProjector]

/-- The finite coefficient model as a rational correspondence action. -/
def correspondenceAction : RationalCorrespondenceAction Correspondence (ℚ × ℚ) :=
  ⟨realization⟩

/-- The marked action comparison is constructed from the calculated matrix
action and the naturality of the source decomposition. No compatibility
square is supplied as a hypothesis. -/
def markedComparison :
    MarkedProjectorActionComparison markedSource correspondenceAction
      firstPointProjector where
  residualRealization := residualEvaluation
  action_intertwines := by
    change (realization firstPointProjector).comp
        (markedSource.productRealization residualEvaluation) = _
    rw [realization_firstPointProjector]
    simpa [MarkedAugmentedAlgebra.generatedClass] using
      (markedSource.productRealization_intertwines_selectorMultiplication
        residualEvaluation).symm

@[simp]
theorem markedComparison_generatedClass :
    markedSource.generatedClass markedComparison.residualRealization = -1 :=
  residualEvaluation_residualClass

/-- A constructed projector lift in the finite coefficient model. The
idempotent and its action were proved by matrix computation above. -/
def projectorLift :
    AlgebraicProjectorLift correspondenceAction
      (ClassGraphProjector.operator (-1 : ℚ)) := by
  simpa only [markedComparison_generatedClass] using
    markedComparison.toAlgebraicProjectorLift
      firstPointProjector_isIdempotent residualEvaluation_surjective

/-- The corresponding unital algebra-homomorphism square is proved by
functoriality of the universal one-idempotent algebra. -/
theorem palomarTargetSquare :
    realization.comp
        (UniversalIdempotentAlgebra.mapOfIdempotent
          firstPointProjector firstPointProjector_isIdempotent) =
      UniversalIdempotentAlgebra.mapOfIdempotent
        (ClassGraphProjector.operator (-1 : ℚ))
        (ClassGraphProjector.operator_isIdempotent (-1 : ℚ)) := by
  simpa only [markedComparison_generatedClass] using
    markedComparison.action_comp_idempotentMap_eq_classGraph
      firstPointProjector_isIdempotent residualEvaluation_surjective

end

end HodgeConjecture.SplitPointCorrespondence
