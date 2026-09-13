import HodgeConjecture.Realization.Chow.Examples.SplitChowAlgebra

/-!
# The geometric diagonal embedding of split point functions

A rational function on a finite split scheme gives a cycle by its actual
point coefficients. Proper pushforward along the actual diagonal puts
that cycle in the Chow correspondence algebra. The computed diagonal
matrix proves that this geometric map is an injective algebra homomorphism.
Its direction is from pointwise functions into Chow convolution, not an
ambient restriction in the opposite direction.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitChowDiagonal

noncomputable section

universe u

open SplitZeroCycles SplitChowCorrespondence
open scoped BigOperators

variable (K : Type u) [Field K] (S : Type u) [Fintype S] [DecidableEq S]

/-- Assemble a cycle from the actual integral point subschemes. -/
def cyclesOfFunction : (S → ℚ) →ₗ[ℚ] Cycles K S ℚ where
  toFun a := ∑ s, a s • pointCycle K S ℚ s
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul,
      RingHom.id_apply]

omit [DecidableEq S] in
@[simp]
theorem coordinates_cyclesOfFunction (a : S → ℚ) (s : S) :
    coordinates K S ℚ (cyclesOfFunction K S a) s = a s := by
  classical
  simp [cyclesOfFunction, -coordinates_apply, Pi.single_apply]

/-- Push the actual point cycle along the actual scheme diagonal. -/
def diagonalLinear : (S → ℚ) →ₗ[ℚ] EndAlgebra K S :=
  (chowPushforward K ℚ (fun s : S ↦ (s, s))).comp
    ((classMap K S ℚ).comp (cyclesOfFunction K S))

/-- The geometric diagonal pushforward has diagonal matrix coordinates. -/
theorem matrix_diagonalLinear (a : S → ℚ) :
    matrixAlgEquiv K S (diagonalLinear K S a) = Matrix.diagonal a := by
  ext j i
  change chowCoordinates K (S × S) ℚ
    (chowPushforward K ℚ (fun s : S ↦ (s, s))
      (classMap K S ℚ (cyclesOfFunction K S a))) (i, j) = _
  rw [chowCoordinates_pushforward]
  simp only [chowCoordinates_classMap, coordinates_cyclesOfFunction]
  by_cases h : i = j
  · subst j
    simp [Prod.mk.injEq]
  · rw [Matrix.diagonal_apply_ne a (Ne.symm h)]
    apply Finset.sum_eq_zero
    intro s _
    have hs : (s, s) ≠ (i, j) := by
      intro hs
      exact h ((congrArg Prod.fst hs).symm.trans (congrArg Prod.snd hs))
    rw [if_neg hs]

/-- The geometric diagonal embedding is a rational algebra homomorphism
from pointwise multiplication to actual Chow convolution. -/
def diagonalAlgHom : (S → ℚ) →ₐ[ℚ] EndAlgebra K S :=
  AlgHom.ofLinearMap (diagonalLinear K S)
    (by
      apply (matrixAlgEquiv K S).injective
      rw [matrix_diagonalLinear, map_one (matrixAlgEquiv K S)]
      exact Matrix.diagonal_one')
    (by
      intro a b
      apply (matrixAlgEquiv K S).injective
      rw [map_mul (matrixAlgEquiv K S), matrix_diagonalLinear,
        matrix_diagonalLinear, matrix_diagonalLinear]
      exact (Matrix.diagonal_mul_diagonal' a b).symm)

@[simp]
theorem diagonalAlgHom_apply (a : S → ℚ) :
    diagonalAlgHom K S a = diagonalLinear K S a := rfl

@[simp]
theorem matrix_diagonalAlgHom (a : S → ℚ) :
    matrixAlgEquiv K S (diagonalAlgHom K S a) = Matrix.diagonal a :=
  matrix_diagonalLinear K S a

/-- Distinct point functions remain distinct in the actual Chow algebra. -/
theorem diagonalAlgHom_injective : Function.Injective (diagonalAlgHom K S) := by
  intro a b h
  apply Matrix.diagonal_injective
  simpa only [matrix_diagonalAlgHom] using congrArg (matrixAlgEquiv K S) h

/-- A characteristic point function becomes its actual point-pair correspondence. -/
@[simp]
theorem diagonalAlgHom_single (s : S) :
    diagonalAlgHom K S (Pi.single s 1) = (pointCorrespondence K s s : EndAlgebra K S) := by
  apply (matrixAlgEquiv K S).injective
  rw [matrix_diagonalAlgHom, matrixAlgEquiv_apply, matrixCoordinates_pointCorrespondence]
  ext j i
  by_cases hj : s = j <;> by_cases hi : s = i <;>
    simp_all [Matrix.diagonal_apply, Matrix.single, eq_comm]

end

end HodgeConjecture.SplitChowDiagonal
