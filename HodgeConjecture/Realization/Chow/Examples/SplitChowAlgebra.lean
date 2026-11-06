module

public import HodgeConjecture.Realization.Chow.Examples.SplitChowComposition
public import HodgeConjecture.Realization.Chow.Examples.SplitSpanQuotient

@[expose] public section

/-!
# The finite split Chow correspondence algebra

The type synonym keeps convolution on pair cycles separate from local
intersection of cycles. Its multiplication is the geometric pull--intersection--
push composition; matrix coordinates prove the ring laws and then give the
algebra equivalence. This identifies the earlier additive span quotient with
the actual finite split Chow correspondence algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

namespace SplitChowCorrespondence

open Classical

variable (K : Type u) [Field K] (I : Type u) [Fintype I] [DecidableEq I]

/-- Endomorphism Chow correspondences, distinguished from the local
intersection ring by their convolution multiplication. -/
def EndAlgebra := Correspondence K I I

instance endAddCommGroup : AddCommGroup (EndAlgebra K I) :=
  inferInstanceAs (AddCommGroup (Correspondence K I I))

instance endModule : Module ℚ (EndAlgebra K I) :=
  inferInstanceAs (Module ℚ (Correspondence K I I))

instance endMul : Mul (EndAlgebra K I) := ⟨comp K⟩
instance endOne : One (EndAlgebra K I) := ⟨diagonal K⟩

/-- Underlying linear coordinates, retaining the actual cycle quotient. -/
def endMatrixCoordinates : EndAlgebra K I ≃ₗ[ℚ] Matrix I I ℚ :=
  matrixCoordinates K I I

omit [DecidableEq I] in
@[simp]
theorem endMatrixCoordinates_mul (a b : EndAlgebra K I) :
    endMatrixCoordinates K I (a * b) =
      endMatrixCoordinates K I a * endMatrixCoordinates K I b :=
  matrixCoordinates_comp K a b

@[simp]
theorem endMatrixCoordinates_one : endMatrixCoordinates K I 1 = 1 :=
  matrixCoordinates_diagonal K

instance endRing : Ring (EndAlgebra K I) where
  __ := endAddCommGroup K I
  __ := endMul K I
  __ := endOne K I
  mul_assoc a b c := comp_assoc K a b c
  one_mul a := diagonal_comp K a
  mul_one a := comp_diagonal K a
  left_distrib a b c := by
    apply (endMatrixCoordinates K I).injective
    simp [mul_add]
  right_distrib a b c := by
    apply (endMatrixCoordinates K I).injective
    simp [add_mul]
  zero_mul a := by
    apply (endMatrixCoordinates K I).injective
    simp
  mul_zero a := by
    apply (endMatrixCoordinates K I).injective
    simp
  natCast n := n • (diagonal K : Correspondence K I I)
  natCast_zero := zero_smul _ _
  natCast_succ n := AddMonoid.nsmul_succ n _
  intCast z := z • (diagonal K : Correspondence K I I)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

instance endAlgebra : Algebra ℚ (EndAlgebra K I) :=
  Algebra.ofModule
    (fun r a b ↦ by
      apply (endMatrixCoordinates K I).injective
      simp [smul_mul_assoc])
    (fun r a b ↦ by
      apply (endMatrixCoordinates K I).injective
      simp [mul_smul_comm])

/-- Matrix coordinates preserve the actual Chow convolution and diagonal. -/
def matrixAlgEquiv : EndAlgebra K I ≃ₐ[ℚ] Matrix I I ℚ :=
  AlgEquiv.ofLinearEquiv (endMatrixCoordinates K I)
    (endMatrixCoordinates_one K I) (endMatrixCoordinates_mul K I)

@[simp]
theorem matrixAlgEquiv_apply (a : EndAlgebra K I) :
    matrixAlgEquiv K I a = matrixCoordinates K I I a := rfl

omit [DecidableEq I] in
/-- The correspondence algebra has precisely the multiplication constructed
by geometric pullback, intersection, and pushforward. -/
theorem mul_eq_comp (a b : EndAlgebra K I) :
    a * b = comp K a b := rfl

omit [DecidableEq I] in
/-- The multiplicative identity is the actual diagonal fundamental class. -/
theorem one_eq_diagonal : (1 : EndAlgebra K I) = diagonal K := rfl

/-- The exact finite-additivity quotient is the rational Chow convolution
algebra of the actual finite split scheme. -/
def spanQuotientEquiv : SplitSpanRealization.AdditiveQuotient K I ≃ₐ[ℚ] EndAlgebra K I :=
  (SplitSpanRealization.quotientRealizationEquiv K I).trans (matrixAlgEquiv K I).symm

@[simp]
theorem matrix_spanQuotientEquiv (a : SplitSpanRealization.AdditiveQuotient K I) :
    matrixAlgEquiv K I (spanQuotientEquiv K I a) =
      SplitSpanRealization.quotientRealizationEquiv K I a := by
  simp [spanQuotientEquiv]

/-- A singleton geometric span maps to the class of its actual point-pair
integral subscheme. -/
@[simp]
theorem spanQuotientEquiv_pointSpanClass (i j : I) :
    spanQuotientEquiv K I
      ((SplitSpanRealization.additivePresentation K I).classMap
        (SplitSpanRealization.pointSpanClass K I i j)) =
      (pointCorrespondence K i j : EndAlgebra K I) := by
  apply (matrixAlgEquiv K I).injective
  rw [matrix_spanQuotientEquiv, SplitSpanRealization.quotientRealizationEquiv_classMap,
    SplitSpanRealization.realization_pointSpanClass, matrixAlgEquiv_apply,
    matrixCoordinates_pointCorrespondence]

variable {S : Type u} [Fintype S]

/-- Push the fundamental cycle of an actual split span's carrier along its
point-pair map into the product. -/
def ofSplitSpan (left right : S → I) : EndAlgebra K I :=
  SplitZeroCycles.chowPushforward K ℚ (fun s ↦ (left s, right s))
    (SplitZeroCycles.classMap K S ℚ (∑ s, SplitZeroCycles.pointCycle K S ℚ s))

omit [DecidableEq I] in
theorem ofSplitSpan_eq_sum (left right : S → I) :
    ofSplitSpan K I left right = ∑ s, (pointCorrespondence K (left s) (right s) : EndAlgebra K I) := by
  change SplitZeroCycles.classMap K (I × I) ℚ
    (SplitZeroCycles.pushforward K ℚ _ (∑ s, SplitZeroCycles.pointCycle K S ℚ s)) = _
  simp only [map_sum, SplitZeroCycles.pushforward_pointCycle]
  rfl

@[simp]
theorem matrixAlgEquiv_ofSplitSpan (left right : S → I) :
    matrixAlgEquiv K I (ofSplitSpan K I left right) = FiniteSpanMatrix.matrix left right := by
  rw [ofSplitSpan_eq_sum]
  simp only [map_sum, matrixAlgEquiv_apply, matrixCoordinates_pointCorrespondence]
  unfold FiniteSpanMatrix.matrix
  apply Finset.sum_congr rfl
  intro s _
  ext j i
  by_cases h : right s = j ∧ left s = i <;> simp [Matrix.single, h]

/-- Every actual split span maps to the proper pushforward of its carrier's
fundamental cycle, not only singleton generators. -/
theorem spanQuotientEquiv_ofSchemeSpan (left right : S → I) :
    spanQuotientEquiv K I
      ((SplitSpanRealization.additivePresentation K I).classMap
        (SplitSpanRealization.ofSchemeSpan K I left right)) = ofSplitSpan K I left right := by
  apply (matrixAlgEquiv K I).injective
  rw [matrix_spanQuotientEquiv, SplitSpanRealization.quotientRealizationEquiv_classMap,
    SplitSpanRealization.realization_ofSchemeSpan, matrixAlgEquiv_ofSplitSpan]

end SplitChowCorrespondence

end

end HodgeConjecture
