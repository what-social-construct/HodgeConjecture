module

public import HodgeConjecture.Realization.Chow.Examples.SplitCycleOperations
public import HodgeConjecture.Correspondence.Examples.SplitProductGeometry
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Composition of rational Chow correspondences on finite split schemes

Correspondences are the actual rational Chow groups on point-pair products.
Composition is defined by pullback, diagonal intersection, and pushforward
on the triple product. Only afterward do point coordinates identify this
operation with matrix multiplication, with rows as outputs and columns as
inputs. The unit is the pushforward of the fundamental cycle along the
actual diagonal.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

namespace SplitChowCorrespondence

open SplitZeroCycles Classical
open scoped BigOperators

variable (K : Type u) [Field K]
variable (I J : Type u) [Finite I] [Finite J]

/-- Rational Chow correspondences on the point-pair presentation of the
actual product over the field. -/
abbrev Correspondence := Chow K (I × J) ℚ

/-- Point-pair coordinates, with rows indexing outputs and columns inputs. -/
def matrixCoordinates : Correspondence K I J ≃ₗ[ℚ] Matrix J I ℚ where
  toFun c j i := chowCoordinates K (I × J) ℚ c (i, j)
  invFun m := (chowCoordinates K (I × J) ℚ).symm (fun p ↦ m p.2 p.1)
  left_inv c := by
    apply (chowCoordinates K (I × J) ℚ).injective
    simp
  right_inv m := by
    funext j i
    simp
  map_add' c d := by
    funext j i
    simp
  map_smul' r c := by
    funext j i
    simp

@[simp]
theorem matrixCoordinates_apply (c : Correspondence K I J) (j : J) (i : I) :
    matrixCoordinates K I J c j i = chowCoordinates K (I × J) ℚ c (i, j) := rfl

variable {I J}
variable {L M : Type u} [Finite L] [Finite M]

/-- The Chow class of the actual rational point-pair subscheme. -/
def pointCorrespondence (i : I) (j : J) : Correspondence K I J :=
  classMap K (I × J) ℚ (pointCycle K (I × J) ℚ (i, j))

@[simp]
theorem matrixCoordinates_pointCorrespondence [DecidableEq I] [DecidableEq J]
    (i : I) (j : J) :
    matrixCoordinates K I J (pointCorrespondence K i j) = Matrix.single j i 1 := by
  ext y x
  simp [matrixCoordinates_apply, pointCorrespondence, Matrix.single,
    -coordinates_apply, Pi.single_apply, Prod.mk.injEq, ite_and, and_comm, eq_comm]

/-- Pull--intersection--push composition on the triple scheme product. -/
def comp (b : Correspondence K J L) (a : Correspondence K I J) :
    Correspondence K I L :=
  chowPushforward K ℚ (fun t : I × J × L ↦ (t.1, t.2.2))
    (chowIntersection K ℚ
      (chowPullback K ℚ (fun t : I × J × L ↦ (t.1, t.2.1)) a)
      (chowPullback K ℚ (fun t : I × J × L ↦ (t.2.1, t.2.2)) b))

/-- The unit is the fundamental cycle pushed along the actual diagonal. -/
def diagonal [Fintype I] : Correspondence K I I :=
  chowPushforward K ℚ (fun i : I ↦ (i, i))
    (classMap K I ℚ (∑ i : I, pointCycle K I ℚ i))

omit [Finite I] [Finite J] [Finite L] in
/-- The finite triple-product sum contracts its two endpoint conditions. -/
private theorem sum_triple [Fintype I] [Fintype J] [Fintype L]
    (a : I → J → ℚ) (b : J → L → ℚ) (i : I) (l : L) :
    (∑ x : I, ∑ y : J, ∑ z : L,
      if (x, z) = (i, l) then a x y * b y z else 0) =
      ∑ j : J, b j l * a i j := by
  simp only [Prod.mk.injEq, ite_and, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_comm]

/-- Geometric Chow composition has the matrix coefficient formula. -/
theorem matrixCoordinates_comp [Fintype I] [Fintype J] [Fintype L]
    (b : Correspondence K J L) (a : Correspondence K I J) :
    matrixCoordinates K I L (comp K b a) =
      matrixCoordinates K J L b * matrixCoordinates K I J a := by
  ext l i
  simp only [matrixCoordinates_apply, comp, chowCoordinates_pushforward,
    chowCoordinates_intersection, chowCoordinates_pullback, Matrix.mul_apply,
    Fintype.sum_prod_type]
  exact sum_triple
    (fun x y ↦ chowCoordinates K (I × J) ℚ a (x, y))
    (fun y z ↦ chowCoordinates K (J × L) ℚ b (y, z)) i l

@[simp]
theorem matrixCoordinates_diagonal [Fintype I] [DecidableEq I] :
    matrixCoordinates K I I (diagonal K (I := I)) = 1 := by
  ext j i
  simp [matrixCoordinates_apply, diagonal,
    -coordinates_apply, Pi.single_apply, Prod.mk.injEq, Matrix.one_apply,
    ite_and]

/-- Associativity follows from the computed geometric composition law. -/
theorem comp_assoc [Fintype I] [Fintype J] [Fintype L] [Fintype M]
    (c : Correspondence K L M) (b : Correspondence K J L)
    (a : Correspondence K I J) :
    comp K (comp K c b) a = comp K c (comp K b a) := by
  apply (matrixCoordinates K I M).injective
  simp only [matrixCoordinates_comp, Matrix.mul_assoc]

@[simp]
theorem diagonal_comp [Fintype I] [Fintype J]
    (a : Correspondence K I J) :
    comp K (diagonal K (I := J)) a = a := by
  apply (matrixCoordinates K I J).injective
  simp [matrixCoordinates_comp]

@[simp]
theorem comp_diagonal [Fintype I] [Fintype J]
    (a : Correspondence K I J) :
    comp K a (diagonal K (I := I)) = a := by
  apply (matrixCoordinates K I J).injective
  simp [matrixCoordinates_comp]

end SplitChowCorrespondence

end

end HodgeConjecture
