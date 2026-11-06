module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Matrices of finite spans

A finite span `I ← S → J` has a rational incidence matrix with rows indexed by
outputs `J` and columns indexed by inputs `I`. Its entry counts the points of
the carrier lying over the prescribed input-output pair. Disjoint union of
carriers becomes addition, and pullback composition becomes multiplication.

This is a finite-set calculation, not an identification with Chow groups.
-/

set_option autoImplicit false

namespace HodgeConjecture.FiniteSpanMatrix

noncomputable section

open Classical

open scoped BigOperators

variable {I J K S T : Type*}

/-- The incidence matrix of a finite span. Rows are outputs and columns inputs. -/
def matrix [Fintype S] (left : S → I) (right : S → J) : Matrix J I ℚ := by
  classical
  exact ∑ s, Matrix.single (right s) (left s) 1

/-- Each coefficient is the number of points above an input-output pair. -/
theorem matrix_apply [Fintype S] (left : S → I) (right : S → J) (j : J) (i : I) :
    matrix left right j i = ∑ s, if right s = j ∧ left s = i then (1 : ℚ) else 0 := by
  classical
  simp only [matrix, Matrix.sum_apply, Matrix.single]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hr : right s = j <;> by_cases hl : left s = i <;> simp [hr, hl]

/-- Matrix action is the elementary pull-push formula: pull coefficients back
along the left leg, then sum them along the fibers of the right leg. -/
theorem matrix_mulVec [Fintype S] [Fintype I]
    (left : S → I) (right : S → J) (v : I → ℚ) (j : J) :
    (matrix left right).mulVec v j =
      ∑ s, if right s = j then v (left s) else 0 := by
  classical
  simp [matrix, Matrix.sum_mulVec, Matrix.single_mulVec, Function.update_apply, eq_comm]

/-- A singleton carrier gives one matrix unit. -/
@[simp]
theorem matrix_singleton (i : I) (j : J) :
    matrix (fun _ : Unit => i) (fun _ => j) = Matrix.single j i 1 := by
  classical
  simp [matrix]

/-- An empty carrier gives the zero matrix. -/
@[simp]
theorem matrix_empty [Fintype S] [IsEmpty S] (left : S → I) (right : S → J) :
    matrix left right = 0 := by
  classical
  simp [matrix]

/-- Disjoint union of finite spans is additive. -/
theorem matrix_sum [Fintype S] [Fintype T]
    (leftS : S → I) (rightS : S → J) (leftT : T → I) (rightT : T → J) :
    matrix (Sum.elim leftS leftT) (Sum.elim rightS rightT) =
      matrix leftS rightS + matrix leftT rightT := by
  classical
  simp [matrix, Fintype.sum_sum_type]

/-- A finite indexed disjoint union of finite spans realizes as their sum. -/
theorem matrix_sigma {A : Type*} [Fintype A] {S : A → Type*}
    [∀ a, Fintype (S a)] (left : ∀ a, S a → I) (right : ∀ a, S a → J) :
    matrix (fun s : Σ a, S a => left s.1 s.2)
      (fun s => right s.1 s.2) = ∑ a, matrix (left a) (right a) := by
  classical
  exact Fintype.sum_sigma _

/-- Changing labels on the carrier does not change the incidence matrix. -/
theorem matrix_reindex [Fintype S] [Fintype T] (e : S ≃ T)
    (left : T → I) (right : T → J) :
    matrix (left ∘ e) (right ∘ e) = matrix left right := by
  classical
  exact e.sum_comp (fun t => Matrix.single (right t) (left t) (1 : ℚ))

/-- The identity span realizes as the identity matrix. -/
@[simp]
theorem matrix_id [Fintype I] [DecidableEq I] :
    matrix (id : I → I) id = (1 : Matrix I I ℚ) := by
  classical
  ext i j
  by_cases h : i = j
  · subst j
    simp [matrix_apply]
  · simp only [matrix_apply, Matrix.one_apply, if_neg h, id_eq]
    apply Finset.sum_eq_zero
    intro x _
    exact if_neg (fun h' => h (h'.1.symm.trans h'.2))

private theorem sum_subtype_ite {A B : Type*} [Fintype A] [AddCommMonoid B]
    (p : A → Prop) [DecidablePred p] (f : A → B) :
    ∑ a : {a // p a}, f a = ∑ a, if p a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) _).symm

/-- Composition by a finite-set pullback becomes matrix multiplication. -/
theorem matrix_pullback [Fintype S] [Fintype T] [Fintype J]
    (leftS : S → I) (rightS : S → J) (leftT : T → J) (rightT : T → K) :
    matrix (fun p : {p : S × T // rightS p.1 = leftT p.2} => leftS p.val.1)
      (fun p => rightT p.val.2) = matrix leftT rightT * matrix leftS rightS := by
  classical
  unfold matrix
  rw [sum_subtype_ite (fun p : S × T => rightS p.1 = leftT p.2)
    (fun p => Matrix.single (rightT p.2) (leftS p.1) (1 : ℚ)),
    Fintype.sum_prod_type]
  rw [Matrix.sum_mul]
  simp_rw [Matrix.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : rightS s = leftT t
  · simp [h]
  · simp [h, Matrix.single_mul_single_of_ne, Ne.symm h]

end

end HodgeConjecture.FiniteSpanMatrix
