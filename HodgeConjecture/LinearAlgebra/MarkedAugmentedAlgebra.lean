import HodgeConjecture.LinearAlgebra.BlockGraphProjector
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Tactic.Ring

/-!
# Marked augmented commutative algebras

This file isolates the commutative algebra carried by a marked generic
selector.  A `MarkedAugmentedAlgebra R A` consists of an augmented
commutative `R`-algebra, a marked element `q`, and the rank-one law

`q * a = augmentation(a) • q`.

The law makes `q` idempotent and identifies multiplication by `q` with a
rank-one projector.  There are two useful splittings of the underlying
`R`-module:

* the constant-unit splitting `A ≃ R × ker(augmentation)`, in which the
  projector has graph form with residual class `q - 1`;
* the selector splitting, in which the projector is diagonal.

This is deliberately only a model of the commutative generic source.  It
places no commutativity assumption on a later Chow-correspondence algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

/--
An augmented commutative algebra with a marked rank-one selector.

The equation `selector_mul` says that left multiplication by the selector
factors through the augmentation.  In particular, the selector cuts out the
copy of the base ring detected by the augmentation.
-/
structure MarkedAugmentedAlgebra
    (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] where
  augmentation : A →ₐ[R] R
  selector : A
  augmentation_selector : augmentation selector = 1
  selector_mul : ∀ a : A, selector * a = augmentation a • selector

namespace MarkedAugmentedAlgebra

variable {R : Type u} {A : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable (M : MarkedAugmentedAlgebra R A)

/-- The marked selector is idempotent. -/
theorem selector_isIdempotent :
    IsIdempotentElem M.selector := by
  change M.selector * M.selector = M.selector
  rw [M.selector_mul]
  rw [M.augmentation_selector, one_smul]

/-- The augmentation ideal.  Unlike a bare linear kernel, this object retains
the multiplicative structure on augmentation-zero elements. -/
def augmentationIdeal : Ideal A :=
  RingHom.ker M.augmentation.toRingHom

@[simp]
theorem mem_augmentationIdeal_iff (a : A) :
    a ∈ M.augmentationIdeal ↔ M.augmentation a = 0 :=
  Iff.rfl

/-- The augmentation ideal is the complementary idempotent summand generated
by `1 - selector`. -/
theorem augmentationIdeal_eq_span_one_sub_selector :
    M.augmentationIdeal = Ideal.span {1 - M.selector} := by
  apply le_antisymm
  · intro a ha
    rw [Ideal.mem_span_singleton']
    refine ⟨a, ?_⟩
    have hε : M.augmentation a = 0 :=
      (M.mem_augmentationIdeal_iff a).mp ha
    calc
      a * (1 - M.selector) = a - a * M.selector := by ring
      _ = a - M.selector * a := by rw [mul_comm a M.selector]
      _ = a := by rw [M.selector_mul, hε, zero_smul, sub_zero]
  · apply Ideal.span_le.2
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact (M.mem_augmentationIdeal_iff (1 - M.selector)).mpr <| by
      simp [M.augmentation_selector]

/-- The residual algebraic object: the augmentation ideal with its inherited
nonunital commutative-ring and module structures. -/
abbrev Residual : Type v :=
  M.augmentationIdeal

@[simp]
theorem residual_mul_coe (x y : M.Residual) :
    ((x * y : M.Residual) : A) = (x : A) * (y : A) :=
  rfl

/-- The older purely linear view of the augmentation kernel. -/
abbrev LinearResidual : Type v :=
  LinearMap.ker M.augmentation.toLinearMap

/-- Forgetting multiplication identifies the augmentation ideal with the
kernel of the augmentation as an `R`-linear map. -/
def residualLinearEquiv : M.Residual ≃ₗ[R] M.LinearResidual where
  toFun x :=
    ⟨x, (M.mem_augmentationIdeal_iff (x : A)).mp x.property⟩
  invFun x :=
    ⟨x, (M.mem_augmentationIdeal_iff (x : A)).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem residualLinearEquiv_apply_coe (x : M.Residual) :
    (M.residualLinearEquiv x : A) = x :=
  rfl

@[simp]
theorem residualLinearEquiv_symm_apply_coe (x : M.LinearResidual) :
    (M.residualLinearEquiv.symm x : A) = x :=
  rfl

/-- The marked selector annihilates every augmentation-zero element. -/
@[simp]
theorem selector_mul_residual (x : M.Residual) :
    M.selector * (x : A) = 0 := by
  rw [M.selector_mul]
  have hx : M.augmentation (x : A) = 0 :=
    (M.mem_augmentationIdeal_iff (x : A)).mp x.property
  rw [hx, zero_smul]

/-- The selector minus the constant unit, regarded as a residual class. -/
def residualClass : M.Residual :=
  ⟨M.selector - 1, by simp [M.augmentation_selector]⟩

@[simp]
theorem residualClass_coe :
    (M.residualClass : A) = M.selector - 1 :=
  rfl

/-!
## Constant-unit coordinates
-/

/--
The augmentation together with the constant section splits the underlying
module as the scalar line plus the augmentation kernel.
-/
def decomposition : A ≃ₗ[R] R × M.Residual where
  toFun a :=
    (M.augmentation a,
      ⟨a - M.augmentation a • (1 : A), by simp⟩)
  invFun tx := tx.1 • (1 : A) + tx.2
  left_inv a := by
    simp
  right_inv tx := by
    rcases tx with ⟨t, x⟩
    have hx := x.property
    change M.augmentation (x : A) = 0 at hx
    apply Prod.ext
    · simp [hx]
    · apply Subtype.ext
      simp [hx]
  map_add' a b := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [Prod.snd_add, Submodule.coe_add, map_add]
      change
        a + b - (M.augmentation a + M.augmentation b) • (1 : A) =
          (a - M.augmentation a • (1 : A)) +
            (b - M.augmentation b • (1 : A))
      rw [add_smul]
      abel
  map_smul' t a := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [Prod.smul_snd, map_smul,
        RingHom.id_apply]
      change
        t • a - (t * M.augmentation a) • (1 : A) =
          t • (a - M.augmentation a • (1 : A))
      simp [smul_sub, smul_smul]

@[simp]
theorem decomposition_apply_fst (a : A) :
    (M.decomposition a).1 = M.augmentation a :=
  rfl

@[simp]
theorem decomposition_apply_snd_coe (a : A) :
    ((M.decomposition a).2 : A) =
      a - M.augmentation a • (1 : A) :=
  rfl

@[simp]
theorem decomposition_symm_apply (t : R) (x : M.Residual) :
    M.decomposition.symm (t, x) = t • (1 : A) + x :=
  rfl

/-!
## Selector coordinates
-/

/--
The selector-marked splitting.  Its scalar summand is the image of
multiplication by the selector.
-/
def selectorDecomposition : A ≃ₗ[R] R × M.Residual where
  toFun a :=
    (M.augmentation a,
      ⟨a - M.augmentation a • M.selector,
        by simp [M.augmentation_selector]⟩)
  invFun tx := tx.1 • M.selector + tx.2
  left_inv a := by
    simp
  right_inv tx := by
    rcases tx with ⟨t, x⟩
    have hx := x.property
    change M.augmentation (x : A) = 0 at hx
    apply Prod.ext
    · simp [hx, M.augmentation_selector]
    · apply Subtype.ext
      simp [hx, M.augmentation_selector]
  map_add' a b := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [Prod.snd_add, Submodule.coe_add, map_add]
      change
        a + b - (M.augmentation a + M.augmentation b) • M.selector =
          (a - M.augmentation a • M.selector) +
            (b - M.augmentation b • M.selector)
      rw [add_smul]
      abel
  map_smul' t a := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      simp only [Prod.smul_snd, map_smul,
        RingHom.id_apply]
      change
        t • a - (t * M.augmentation a) • M.selector =
          t • (a - M.augmentation a • M.selector)
      simp [smul_sub, smul_smul]

@[simp]
theorem selectorDecomposition_apply_fst (a : A) :
    (M.selectorDecomposition a).1 = M.augmentation a :=
  rfl

@[simp]
theorem selectorDecomposition_apply_snd_coe (a : A) :
    ((M.selectorDecomposition a).2 : A) =
      a - M.augmentation a • M.selector :=
  rfl

@[simp]
theorem selectorDecomposition_symm_apply (t : R) (x : M.Residual) :
    M.selectorDecomposition.symm (t, x) =
      t • M.selector + x :=
  rfl

/-!
## Multiplication by the selector
-/

/-- Left multiplication by the marked selector. -/
def multiplication : Module.End R A :=
  LinearMap.mulLeft R M.selector

@[simp]
theorem multiplication_apply (a : A) :
    M.multiplication a = M.selector * a :=
  rfl

/-- The regular representation of the commutative generic source.  This is
the genuinely multiplicative realization map carried by the source algebra.
-/
def regularAction (_M : MarkedAugmentedAlgebra R A) :
    A →ₐ[R] Module.End R A :=
  Algebra.lmul R A

@[simp]
theorem regularAction_apply (a x : A) :
    M.regularAction a x = a * x :=
  rfl

/-- The marked selector acts through the previously defined multiplication
projector. -/
@[simp]
theorem regularAction_selector :
    M.regularAction M.selector = M.multiplication :=
  rfl

/-- Multiplication by the selector is idempotent. -/
theorem multiplication_isIdempotent :
    IsIdempotentElem M.multiplication := by
  change M.multiplication * M.multiplication = M.multiplication
  apply LinearMap.ext
  intro a
  change M.selector * (M.selector * a) = M.selector * a
  rw [← mul_assoc, M.selector_isIdempotent]

/-- The graph projector associated with the residual class `q - 1`. -/
abbrev graphOperator : Module.End R (R × M.Residual) :=
  BlockGraphProjector.operator (R := R) M.residualClass

@[simp]
theorem graphOperator_apply (t : R) (x : M.Residual) :
    M.graphOperator (t, x) = (t, t • M.residualClass) :=
  rfl

/-- The diagonal projector onto the marked scalar coordinate. -/
abbrev diagonalOperator : Module.End R (R × M.Residual) :=
  BlockGraphProjector.diagonalOperator (R := R) (M := M.Residual)

@[simp]
theorem diagonalOperator_apply (t : R) (x : M.Residual) :
    M.diagonalOperator (t, x) = (t, 0) :=
  rfl

/--
In constant-unit coordinates, multiplication by the selector is the graph
projector of the residual class `q - 1`.
-/
theorem decomposition_conj_multiplication :
    M.decomposition.conj M.multiplication = M.graphOperator := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  have hx := x.property
  change M.augmentation (x : A) = 0 at hx
  apply Prod.ext
  · simp [LinearEquiv.conj_apply, hx, M.augmentation_selector]
  · apply Subtype.ext
    simp [LinearEquiv.conj_apply, hx, M.selector_mul,
      M.augmentation_selector, residualClass, sub_eq_add_neg]

/--
In selector coordinates, multiplication by the selector is the diagonal
projector `diag(1, 0)`.
-/
theorem selectorDecomposition_conj_multiplication :
    M.selectorDecomposition.conj M.multiplication =
      M.diagonalOperator := by
  apply LinearMap.ext
  rintro ⟨t, x⟩
  have hx := x.property
  change M.augmentation (x : A) = 0 at hx
  apply Prod.ext
  · simp [LinearEquiv.conj_apply, hx, M.augmentation_selector]
  · apply Subtype.ext
    simp [LinearEquiv.conj_apply, hx, M.selector_mul,
      M.augmentation_selector]

/-- The change from selector coordinates to constant-unit coordinates is the
lower shear with off-diagonal entry `q - 1`. -/
theorem selectorToMarked_eq_shear :
    M.selectorDecomposition.symm.trans M.decomposition =
      BlockGraphProjector.shear (R := R) M.residualClass := by
  apply LinearEquiv.ext
  rintro ⟨t, x⟩
  have hx := x.property
  change M.augmentation (x : A) = 0 at hx
  apply Prod.ext
  · simp [hx, M.augmentation_selector]
  · apply Subtype.ext
    simp [residualClass, hx, M.augmentation_selector,
      sub_eq_add_neg]
    abel

/-- Conjugating the diagonal projector by the marked shear gives the graph
projector. -/
theorem shear_conj_diagonalOperator :
    (BlockGraphProjector.shear (R := R) M.residualClass).conj
        M.diagonalOperator =
      M.graphOperator :=
  BlockGraphProjector.shear_conj_diagonalOperator
    (R := R) M.residualClass

end MarkedAugmentedAlgebra

end

end HodgeConjecture
