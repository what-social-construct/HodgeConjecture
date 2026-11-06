module

public import HodgeConjecture.LinearAlgebra.MarkedAugmentedAlgebra
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.RingTheory.Idempotents

@[expose] public section

/-!
# Multiplicative decomposition of a marked augmented algebra

For a marked augmented algebra with selector `q`, the augmentation kernel is
the principal ideal `(1 - q)`.  Its inherited multiplication is nonunital as
an `Ideal` subtype, but `1 - q` is an internal unit.  This file packages that
ideal as a unital residual corner and proves the genuine algebra splitting

`A ≃ₐ[R] R × ResidualCorner`.

This is the multiplicative selector-coordinate splitting.  The constant-unit
coordinates in `MarkedAugmentedAlgebra.decomposition` remain only linear:
they are the sheared coordinates in which multiplication by `q` is a graph
projector.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

namespace MarkedAugmentedAlgebra

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (M : MarkedAugmentedAlgebra R A)

/-- The idempotent complementary to the marked selector. -/
def complement : A := 1 - M.selector

theorem complement_isIdempotent : IsIdempotentElem M.complement := by
  simpa [complement] using M.selector_isIdempotent.one_sub

@[simp]
theorem augmentation_complement : M.augmentation M.complement = 0 := by
  simp [complement, M.augmentation_selector]

/-- The augmentation ideal, regarded as a unital corner whose unit is
`1 - selector`. The wrapper keeps this unital structure separate from the
standard nonunital structure on an ideal subtype. -/
structure ResidualCorner where
  toResidual : M.Residual

@[ext]
theorem ResidualCorner.ext {x y : M.ResidualCorner}
    (h : x.toResidual = y.toResidual) : x = y := by
  cases x
  cases y
  congr

/-- The underlying type equivalence between the residual corner and the
augmentation ideal. -/
def residualCornerEquivIdealType : M.ResidualCorner ≃ M.Residual where
  toFun := ResidualCorner.toResidual
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance residualCornerNonUnitalCommRing : NonUnitalCommRing M.ResidualCorner :=
  M.residualCornerEquivIdealType.nonUnitalCommRing

instance residualCornerModule : Module R M.ResidualCorner :=
  (show M.ResidualCorner ≃+ M.Residual from
    { M.residualCornerEquivIdealType with map_add' := fun _ _ ↦ rfl }).module R

theorem residualCorner_property (x : M.ResidualCorner) :
    M.augmentation (x.toResidual : A) = 0 :=
  (M.mem_augmentationIdeal_iff (x.toResidual : A)).mp x.toResidual.property

instance residualCornerOne : One M.ResidualCorner where
  one := ⟨⟨M.complement,
    (M.mem_augmentationIdeal_iff M.complement).mpr M.augmentation_complement⟩⟩

instance residualCornerCommRing : CommRing M.ResidualCorner where
  __ := M.residualCornerNonUnitalCommRing
  __ := M.residualCornerOne
  one_mul x := by
    apply M.residualCornerEquivIdealType.injective
    apply Subtype.ext
    change M.complement * (x.toResidual : A) = x.toResidual
    rw [complement]
    have hx : M.selector * (x.toResidual : A) = 0 :=
      M.selector_mul_residual x.toResidual
    rw [sub_mul, one_mul, hx, sub_zero]
  mul_one x := by
    apply M.residualCornerEquivIdealType.injective
    apply Subtype.ext
    change (x.toResidual : A) * M.complement = x.toResidual
    rw [mul_comm]
    change M.complement * (x.toResidual : A) = x.toResidual
    rw [complement]
    have hx : M.selector * (x.toResidual : A) = 0 :=
      M.selector_mul_residual x.toResidual
    rw [sub_mul, one_mul, hx, sub_zero]

instance residualCornerAlgebra : Algebra R M.ResidualCorner :=
  Algebra.ofModule
    (fun r x y ↦ by
      apply M.residualCornerEquivIdealType.injective
      apply Subtype.ext
      exact Algebra.smul_mul_assoc r (x.toResidual : A) (y.toResidual : A))
    (fun r x y ↦ by
      apply M.residualCornerEquivIdealType.injective
      apply Subtype.ext
      exact Algebra.mul_smul_comm r (x.toResidual : A) (y.toResidual : A))

@[simp]
theorem residualCorner_one_coe :
    ((1 : M.ResidualCorner).toResidual : A) = M.complement :=
  rfl

@[simp]
theorem residualCorner_algebraMap_coe (r : R) :
    ((algebraMap R M.ResidualCorner r : M.ResidualCorner).toResidual : A) =
      r • M.complement := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

/-- Forgetting the corner unit identifies the residual corner with the
original augmentation ideal, multiplicatively and additively. -/
def residualCornerEquivIdeal : M.ResidualCorner ≃+* M.Residual where
  toFun := ResidualCorner.toResidual
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem residualCornerEquivIdeal_apply_coe (x : M.ResidualCorner) :
    ((M.residualCornerEquivIdeal x : M.Residual) : A) =
      (x.toResidual : A) :=
  rfl

/-- The augmentation ideal is exactly the underlying nonunital ring of the
Mathlib corner cut out by `1 - selector`. -/
def residualCornerEquivIdempotentCorner :
    M.ResidualCorner ≃+* M.complement_isIdempotent.Corner where
  toFun x :=
    ⟨x.toResidual, ⟨(x.toResidual : A), by
      have hx : M.complement * (x.toResidual : A) = x.toResidual := by
        rw [complement, sub_mul, one_mul]
        rw [M.selector_mul_residual x.toResidual, sub_zero]
      calc
        M.complement * (x.toResidual : A) * M.complement =
            (x.toResidual : A) * M.complement := by rw [hx]
        _ = M.complement * (x.toResidual : A) := by rw [mul_comm]
        _ = x.toResidual := hx⟩⟩
  invFun x :=
    ⟨⟨x.1, (M.mem_augmentationIdeal_iff x.1).mpr <| by
      obtain ⟨a, ha⟩ := x.property
      rw [← ha]
      simp [M.augmentation_complement]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem residualCornerEquivIdempotentCorner_apply_coe
    (x : M.ResidualCorner) :
    (M.residualCornerEquivIdempotentCorner x).1 =
      (x.toResidual : A) :=
  rfl

/-- Selector coordinates form a genuine product decomposition of algebras.
The residual factor is the augmentation ideal with corner unit
`1 - selector`. -/
def selectorAlgebraDecomposition : A ≃ₐ[R] R × M.ResidualCorner where
  toFun a :=
    (M.augmentation a,
      ⟨⟨M.complement * a, (M.mem_augmentationIdeal_iff _).mpr <| by
        rw [map_mul, M.augmentation_complement, zero_mul]⟩⟩)
  invFun tx := tx.1 • M.selector + (tx.2.toResidual : A)
  left_inv a := by
    change M.augmentation a • M.selector + M.complement * a = a
    rw [complement, sub_mul, one_mul, M.selector_mul]
    abel
  right_inv tx := by
    rcases tx with ⟨r, x⟩
    apply Prod.ext
    · simp [M.augmentation_selector, M.residualCorner_property x]
    · apply ResidualCorner.ext
      apply Subtype.ext
      have hx : M.selector * (x.toResidual : A) = 0 :=
        M.selector_mul_residual x.toResidual
      change M.complement * (r • M.selector + (x.toResidual : A)) = x.toResidual
      rw [complement, Algebra.smul_def, sub_mul, one_mul, mul_add, hx, add_zero]
      rw [← mul_assoc M.selector (algebraMap R A r) M.selector,
        mul_comm M.selector (algebraMap R A r), mul_assoc,
        M.selector_isIdempotent.eq]
      abel
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul M.augmentation a b
    · apply M.residualCornerEquivIdealType.injective
      apply Subtype.ext
      change M.complement * (a * b) =
        (M.complement * a) * (M.complement * b)
      calc
        M.complement * (a * b) =
            (M.complement * M.complement) * (a * b) := by
          rw [M.complement_isIdempotent]
        _ = (M.complement * a) * (M.complement * b) := by ring
  map_add' a b := by
    apply Prod.ext
    · exact map_add M.augmentation a b
    · apply M.residualCornerEquivIdealType.injective
      apply Subtype.ext
      exact mul_add M.complement a b
  commutes' r := by
    apply Prod.ext
    · simp
    · change
        (⟨⟨M.complement * (algebraMap R A r), _⟩⟩ : M.ResidualCorner) =
          algebraMap R M.ResidualCorner r
      apply ResidualCorner.ext
      apply Subtype.ext
      change M.complement * (algebraMap R A r) = r • M.complement
      rw [Algebra.smul_def]
      exact mul_comm M.complement (algebraMap R A r)

@[simp]
theorem selectorAlgebraDecomposition_apply_fst (a : A) :
    (M.selectorAlgebraDecomposition a).1 = M.augmentation a :=
  rfl

@[simp]
theorem selectorAlgebraDecomposition_apply_snd_coe (a : A) :
    ((M.selectorAlgebraDecomposition a).2.toResidual : A) =
      M.complement * a :=
  rfl

/-- The residual coordinate is literally the second coordinate of the
previous selector splitting after forgetting the corner unit. -/
theorem selectorAlgebraDecomposition_apply_snd_eq_selectorCoordinate (a : A) :
    ((M.selectorAlgebraDecomposition a).2.toResidual : A) =
      a - M.augmentation a • M.selector := by
  rw [M.selectorAlgebraDecomposition_apply_snd_coe]
  rw [complement, sub_mul, one_mul, M.selector_mul]

@[simp]
theorem selectorAlgebraDecomposition_symm_apply (r : R) (x : M.ResidualCorner) :
    M.selectorAlgebraDecomposition.symm (r, x) =
      r • M.selector + (x.toResidual : A) :=
  rfl

@[simp]
theorem selectorAlgebraDecomposition_selector :
    M.selectorAlgebraDecomposition M.selector = (1, 0) := by
  apply Prod.ext
  · simp [M.augmentation_selector]
  · apply ResidualCorner.ext
    apply Subtype.ext
    change M.complement * M.selector = 0
    rw [complement, sub_mul, one_mul, M.selector_isIdempotent.eq, sub_self]

@[simp]
theorem selectorAlgebraDecomposition_complement :
    M.selectorAlgebraDecomposition M.complement = (0, 1) := by
  apply Prod.ext
  · exact M.augmentation_complement
  · apply ResidualCorner.ext
    apply Subtype.ext
    change M.complement * M.complement = M.complement
    exact M.complement_isIdempotent.eq

end MarkedAugmentedAlgebra

end

end HodgeConjecture
