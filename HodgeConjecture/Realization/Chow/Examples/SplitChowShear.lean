module

public import HodgeConjecture.Realization.Chow.Examples.SplitTateBlock

@[expose] public section

/-!
# Constant-marked coordinates by an invertible actual Chow correspondence

The lower-left column is proper pushforward of an actual Chow class. Its
square vanishes under geometric correspondence composition. Consequently
the diagonal plus this column is an invertible Chow correspondence, and
conjugating the distinguished point projector produces the existing graph
encoding. This shear is a Chow correspondence, not a scheme automorphism.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitChowShear

noncomputable section

open Classical SplitZeroCycles SplitChowCorrespondence SplitChowTateBlock

variable (I : Type) [Fintype I] [DecidableEq I]

/-- The actual point-pair projector on the distinguished point summand. -/
def pointProjector : EndAlgebra ℂ (Option I) :=
  pointCorrespondence ℂ (none : Option I) none

theorem column_mul_column (z w : Chow ℂ I ℚ) : column I z * column I w = 0 := by
  apply (matrixAlgEquiv ℂ (Option I)).injective
  rw [map_mul, matrix_column, matrix_column, map_zero]
  ext output input
  simp [Matrix.mul_apply]

theorem column_mul_point (z : Chow ℂ I ℚ) : column I z * pointProjector I = column I z := by
  apply (matrixAlgEquiv ℂ (Option I)).injective
  rw [map_mul, matrix_column]
  simp only [pointProjector, matrixAlgEquiv_apply, matrixCoordinates_pointCorrespondence]
  ext output input
  simp [Matrix.mul_apply, Matrix.single, eq_comm]

theorem point_mul_column (z : Chow ℂ I ℚ) : pointProjector I * column I z = 0 := by
  apply (matrixAlgEquiv ℂ (Option I)).injective
  rw [map_mul, matrix_column, map_zero]
  simp only [pointProjector, matrixAlgEquiv_apply, matrixCoordinates_pointCorrespondence]
  ext output input
  simp [Matrix.mul_apply, Matrix.single]

/-- The actual Chow shear, consisting of the diagonal and a column pushforward. -/
def shear (z : Chow ℂ I ℚ) : EndAlgebra ℂ (Option I) := 1 + column I z

@[simp]
theorem shear_mul_shear_neg (z : Chow ℂ I ℚ) : shear I z * shear I (-z) = 1 := by
  simp [shear, add_mul, mul_add, column_mul_column]

@[simp]
theorem shear_neg_mul_shear (z : Chow ℂ I ℚ) : shear I (-z) * shear I z = 1 := by
  simpa only [neg_neg] using shear_mul_shear_neg I (-z)

/-- The inverse is constructed from the negative of the same geometric class. -/
def shearUnit (z : Chow ℂ I ℚ) : (EndAlgebra ℂ (Option I))ˣ where
  val := shear I z
  inv := shear I (-z)
  val_inv := shear_mul_shear_neg I z
  inv_val := shear_neg_mul_shear I z

/-- The graph correspondence is the actual Chow conjugate of the point projector. -/
theorem shear_point_shear_neg (z : Chow ℂ I ℚ) :
    shear I z * pointProjector I * shear I (-z) = encode I z := by
  change shear I z * pointProjector I * shear I (-z) = pointProjector I + column I z
  simp only [shear, add_mul, mul_add, one_mul, mul_one, column_mul_point,
    point_mul_column, column_mul_column, add_zero]

/-- Inner conjugation by the explicitly constructed invertible Chow shear. -/
def conjugation (z : Chow ℂ I ℚ) : EndAlgebra ℂ (Option I) ≃ₐ[ℚ] EndAlgebra ℂ (Option I) where
  toFun c := ↑(shearUnit I z) * c * ↑((shearUnit I z)⁻¹)
  invFun c := ↑((shearUnit I z)⁻¹) * c * ↑(shearUnit I z)
  left_inv c := by
    change shear I (-z) * (shear I z * c * shear I (-z)) * shear I z = c
    calc
      _ = (shear I (-z) * shear I z) * c * (shear I (-z) * shear I z) := by
        simp only [mul_assoc]
      _ = c := by rw [shear_neg_mul_shear]; simp
  right_inv c := by
    change shear I z * (shear I (-z) * c * shear I z) * shear I (-z) = c
    calc
      _ = (shear I z * shear I (-z)) * c * (shear I z * shear I (-z)) := by
        simp only [mul_assoc]
      _ = c := by rw [shear_mul_shear_neg]; simp
  map_add' c d := by
    simp only [mul_add, add_mul]
  map_mul' c d := by
    change shear I z * (c * d) * shear I (-z) =
      (shear I z * c * shear I (-z)) * (shear I z * d * shear I (-z))
    calc
      _ = shear I z * c * (shear I (-z) * shear I z) * d * shear I (-z) := by
        rw [shear_neg_mul_shear]
        simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  commutes' r := by
    change shear I z * algebraMap ℚ (EndAlgebra ℂ (Option I)) r * shear I (-z) = _
    rw [← Algebra.commutes r (shear I z), mul_assoc, shear_mul_shear_neg, mul_one]

@[simp]
theorem conjugation_apply (z : Chow ℂ I ℚ) (c : EndAlgebra ℂ (Option I)) :
    conjugation I z c = shear I z * c * shear I (-z) := rfl

/-- The algebra conjugation sends the distinguished point projector to
the actual geometric graph encoding. -/
@[simp]
theorem conjugation_pointProjector (z : Chow ℂ I ℚ) :
    conjugation I z (pointProjector I) = encode I z :=
  shear_point_shear_neg I z

end

end HodgeConjecture.SplitChowShear
