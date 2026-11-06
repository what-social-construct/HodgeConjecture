module

public import HodgeConjecture.Boundary.Sheets.GenericProjector
public import HodgeConjecture.LinearAlgebra.MarkedAugmentedAlgebraDecomposition
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The marked-sheet block form of a Galois selector

Let `s₀` be the distinguished sheet in `G / H` and let `q` be its
characteristic function.  Evaluation at `s₀` splits the rational function
space on the sheets as

`(G / H → ℚ) ≃ ℚ × ker(ev_{s₀})`.

The splitting is marked by the constant function `1`, rather than by the
image of multiplication by `q`.  Consequently multiplication by `q`, which
is diagonal in its image/kernel decomposition, has graph form in these
marked coordinates:

`(t, x) ↦ (t, t • (q - 1))`.

This is a pure linear-algebra comparison.  It does not identify the residual
sheet module with cohomology of a variety or assert that every Hodge class is
obtained from Galois-sheet data.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

variable {G : Type u} [Group G]

namespace MarkedSheetProjector

variable (H : Subgroup G)

/-- Evaluation of a rational sheet function at the distinguished base sheet. -/
def baseEvaluation :
    GenericSheetAlgebra ℚ H →ₗ[ℚ] ℚ :=
  LinearMap.proj (baseSheet H)

/-- Evaluation at the marked sheet as an augmentation of the commutative
generic sheet algebra. -/
def baseAugmentation :
    GenericSheetAlgebra ℚ H →ₐ[ℚ] ℚ :=
  Pi.evalAlgHom ℚ (fun _ : CollisionFoundations.GaloisSheets H ↦ ℚ)
    (baseSheet H)

@[simp]
theorem baseAugmentation_apply
    (f : GenericSheetAlgebra ℚ H) :
    baseAugmentation H f = f (baseSheet H) :=
  rfl

/-- The augmentation's underlying linear map is the existing marked-sheet
evaluation map. -/
theorem baseAugmentation_toLinearMap :
    (baseAugmentation H).toLinearMap = baseEvaluation H := by
  apply LinearMap.ext
  intro f
  rfl

/-- The ideal of sheet functions vanishing at the distinguished base sheet.
It retains the inherited nonunital commutative multiplication. -/
abbrev Residual := RingHom.ker (baseAugmentation H).toRingHom

/-- The characteristic function of the distinguished base sheet. -/
def selector : GenericSheetAlgebra ℚ H :=
  genericSheetSelector ℚ H {baseSheet H}

@[simp]
theorem selector_apply_base :
    selector H (baseSheet H) = 1 := by
  simp [selector, genericSheetSelector]

/-- The base-sheet selector as a marked augmented commutative algebra.  This
packages only the generic source algebra; it does not impose commutativity on
any compactified correspondence algebra. -/
def markedAugmentedAlgebra :
    MarkedAugmentedAlgebra ℚ (GenericSheetAlgebra ℚ H) where
  augmentation := baseAugmentation H
  selector := selector H
  augmentation_selector := selector_apply_base H
  selector_mul := by
    intro f
    ext s
    by_cases hs : s = baseSheet H
    · subst s
      simp [selector, genericSheetSelector]
    · simp [selector, genericSheetSelector, hs]

@[simp]
theorem markedAugmentedAlgebra_augmentation_apply
    (f : GenericSheetAlgebra ℚ H) :
    (markedAugmentedAlgebra H).augmentation f =
      f (baseSheet H) :=
  rfl

@[simp]
theorem markedAugmentedAlgebra_selector :
    (markedAugmentedAlgebra H).selector = selector H :=
  rfl

/-- The marked residual class `q - 1`, which vanishes at the base sheet. -/
def residualClass : Residual H :=
  ⟨selector H - 1, by
    simp⟩

@[simp]
theorem residualClass_coe :
    (residualClass H : GenericSheetAlgebra ℚ H) = selector H - 1 :=
  rfl

/--
Evaluation at the marked sheet, together with the constant section, splits
the sheet-function module into the marked line and the residual kernel.
-/
def decomposition :
    GenericSheetAlgebra ℚ H ≃ₗ[ℚ] ℚ × Residual H where
  toFun f :=
    (f (baseSheet H),
      ⟨f - f (baseSheet H) • 1, by
        simp⟩)
  invFun tx := tx.1 • 1 + tx.2
  left_inv f := by
    ext s
    simp
  right_inv tx := by
    rcases tx with ⟨t, x⟩
    have hx := x.property
    change (x : GenericSheetAlgebra ℚ H) (baseSheet H) = 0 at hx
    apply Prod.ext
    · simp [hx]
    · apply Subtype.ext
      ext s
      simp [hx]
  map_add' f g := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change
        f + g - (f + g) (baseSheet H) • 1 =
          (f - f (baseSheet H) • 1) +
            (g - g (baseSheet H) • 1)
      ext s
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
        smul_eq_mul]
      ring
  map_smul' t f := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change
        t • f - (t • f) (baseSheet H) • 1 =
          t • (f - f (baseSheet H) • 1)
      ext s
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
      ring

@[simp]
theorem decomposition_apply_fst
    (f : GenericSheetAlgebra ℚ H) :
    (decomposition H f).1 = f (baseSheet H) :=
  rfl

@[simp]
theorem decomposition_apply_snd_coe
    (f : GenericSheetAlgebra ℚ H) :
    ((decomposition H f).2 : GenericSheetAlgebra ℚ H) =
      f - f (baseSheet H) • 1 :=
  rfl

@[simp]
theorem decomposition_symm_apply
    (t : ℚ) (x : Residual H) :
    (decomposition H).symm (t, x) = t • 1 + x :=
  rfl

/-!
## Selector/CRT coordinates

Using the selector itself, rather than the constant function, as the section
of evaluation gives the image/kernel coordinates in which multiplication by
the selector is diagonal.
-/

/--
The selector-marked splitting.  Its first summand is the image of
multiplication by the base-sheet selector.
-/
def selectorDecomposition :
    GenericSheetAlgebra ℚ H ≃ₗ[ℚ] ℚ × Residual H where
  toFun f :=
    (f (baseSheet H),
      ⟨f - f (baseSheet H) • selector H, by
        simp⟩)
  invFun tx := tx.1 • selector H + tx.2
  left_inv f := by
    ext s
    simp
  right_inv tx := by
    rcases tx with ⟨t, x⟩
    have hx := x.property
    change (x : GenericSheetAlgebra ℚ H) (baseSheet H) = 0 at hx
    apply Prod.ext
    · simp [hx]
    · apply Subtype.ext
      ext s
      simp [hx]
  map_add' f g := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change
        f + g - (f + g) (baseSheet H) • selector H =
          (f - f (baseSheet H) • selector H) +
            (g - g (baseSheet H) • selector H)
      ext s
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  map_smul' t f := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      change
        t • f - (t • f) (baseSheet H) • selector H =
          t • (f - f (baseSheet H) • selector H)
      ext s
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring

@[simp]
theorem selectorDecomposition_apply_fst
    (f : GenericSheetAlgebra ℚ H) :
    (selectorDecomposition H f).1 = f (baseSheet H) :=
  rfl

@[simp]
theorem selectorDecomposition_apply_snd_coe
    (f : GenericSheetAlgebra ℚ H) :
    ((selectorDecomposition H f).2 : GenericSheetAlgebra ℚ H) =
      f - f (baseSheet H) • selector H :=
  rfl

@[simp]
theorem selectorDecomposition_symm_apply
    (t : ℚ) (x : Residual H) :
    (selectorDecomposition H).symm (t, x) =
      t • selector H + x :=
  rfl

/-- Multiplication by the marked base-sheet selector. -/
def multiplication : Module.End ℚ (GenericSheetAlgebra ℚ H) :=
  LinearMap.mulLeft ℚ (selector H)

@[simp]
theorem multiplication_apply
    (f : GenericSheetAlgebra ℚ H) :
    multiplication H f = selector H * f :=
  rfl

/-- The graph operator associated with the canonical residual class. -/
abbrev graphOperator : Module.End ℚ (ℚ × Residual H) :=
  BlockGraphProjector.operator (R := ℚ) (residualClass H)

@[simp]
theorem graphOperator_apply (t : ℚ) (x : Residual H) :
    graphOperator H (t, x) = (t, t • residualClass H) :=
  rfl

/-- The diagonal projector onto the marked scalar coordinate. -/
abbrev diagonalOperator : Module.End ℚ (ℚ × Residual H) :=
  BlockGraphProjector.diagonalOperator (R := ℚ) (M := Residual H)

@[simp]
theorem diagonalOperator_apply (t : ℚ) (x : Residual H) :
    diagonalOperator H (t, x) = (t, 0) :=
  rfl

/-!
## Parity with the generic marked-augmentation API

The following equalities show that the existing Galois-sheet declarations
are precisely the specialization of `MarkedAugmentedAlgebra`.  They keep the
public marked-sheet API stable while exposing the reusable commutative source
algebra underneath it.
-/

@[simp]
theorem markedAugmentedAlgebra_residualClass :
    (markedAugmentedAlgebra H).residualClass = residualClass H :=
  rfl

theorem markedAugmentedAlgebra_decomposition :
    (markedAugmentedAlgebra H).decomposition = decomposition H := by
  apply LinearEquiv.ext
  intro f
  rfl

theorem markedAugmentedAlgebra_selectorDecomposition :
    (markedAugmentedAlgebra H).selectorDecomposition =
      selectorDecomposition H := by
  apply LinearEquiv.ext
  intro f
  rfl

@[simp]
theorem markedAugmentedAlgebra_multiplication :
    (markedAugmentedAlgebra H).multiplication = multiplication H :=
  rfl

@[simp]
theorem markedAugmentedAlgebra_graphOperator :
    (markedAugmentedAlgebra H).graphOperator = graphOperator H :=
  rfl

@[simp]
theorem markedAugmentedAlgebra_diagonalOperator :
    (markedAugmentedAlgebra H).diagonalOperator = diagonalOperator H :=
  rfl

/-!
## Multiplicative selector coordinates

The residual ideal has internal unit `1 - selector H`.  With that corner
unit, the selector-coordinate splitting is an equivalence of algebras, not
merely an equivalence of underlying vector spaces.  The constant-unit
splitting `decomposition H` above is unchanged and remains the graph-form
linear coordinate system.
-/

/-- The marked-sheet augmentation ideal equipped with corner unit
`1 - selector H`. -/
abbrev ResidualCorner :=
  (markedAugmentedAlgebra H).ResidualCorner

/-- The multiplicative selector-coordinate decomposition of the generic
sheet algebra. -/
def selectorAlgebraDecomposition :
    GenericSheetAlgebra ℚ H ≃ₐ[ℚ] ℚ × ResidualCorner H :=
  (markedAugmentedAlgebra H).selectorAlgebraDecomposition

@[simp]
theorem selectorAlgebraDecomposition_apply_fst
    (f : GenericSheetAlgebra ℚ H) :
    (selectorAlgebraDecomposition H f).1 = f (baseSheet H) :=
  rfl

@[simp]
theorem selectorAlgebraDecomposition_selector :
    selectorAlgebraDecomposition H (selector H) = (1, 0) := by
  simpa only [selectorAlgebraDecomposition,
    markedAugmentedAlgebra_selector] using
      (markedAugmentedAlgebra H).selectorAlgebraDecomposition_selector

@[simp]
theorem selectorAlgebraDecomposition_one_sub_selector :
    selectorAlgebraDecomposition H (1 - selector H) = (0, 1) := by
  simpa only [selectorAlgebraDecomposition,
    MarkedAugmentedAlgebra.complement,
    markedAugmentedAlgebra_selector] using
      (markedAugmentedAlgebra H).selectorAlgebraDecomposition_complement

/--
The lower-triangular shear from selector/CRT coordinates to constant-marked
coordinates.  Its off-diagonal entry is the canonical residual class.
-/
abbrev shear : (ℚ × Residual H) ≃ₗ[ℚ] (ℚ × Residual H) :=
  BlockGraphProjector.shear (R := ℚ) (residualClass H)

@[simp]
theorem shear_apply (t : ℚ) (x : Residual H) :
    shear H (t, x) = (t, x + t • residualClass H) :=
  rfl

@[simp]
theorem shear_symm_apply (t : ℚ) (x : Residual H) :
    (shear H).symm (t, x) = (t, x - t • residualClass H) :=
  rfl

/--
In marked evaluation coordinates, multiplication by the base-sheet selector
is exactly the graph projector of `q - 1`.
-/
theorem decomposition_conj_multiplication :
    (decomposition H).conj (multiplication H) = graphOperator H := by
  have h := (markedAugmentedAlgebra H).decomposition_conj_multiplication
  rw [markedAugmentedAlgebra_decomposition, markedAugmentedAlgebra_multiplication, markedAugmentedAlgebra_graphOperator] at h
  exact h

/--
In selector/CRT coordinates, multiplication by the base-sheet selector is
the diagonal projector `diag(1, 0)`.
-/
theorem selectorDecomposition_conj_multiplication :
    (selectorDecomposition H).conj (multiplication H) =
      diagonalOperator H := by
  have h := (markedAugmentedAlgebra H).selectorDecomposition_conj_multiplication
  rw [markedAugmentedAlgebra_selectorDecomposition, markedAugmentedAlgebra_multiplication, markedAugmentedAlgebra_diagonalOperator] at h
  exact h

/-- The two sheet splittings differ by the canonical lower shear. -/
theorem selectorToMarked_eq_shear :
    (selectorDecomposition H).symm.trans (decomposition H) = shear H := by
  simpa only [markedAugmentedAlgebra_selectorDecomposition,
    markedAugmentedAlgebra_decomposition,
    markedAugmentedAlgebra_residualClass] using
      (markedAugmentedAlgebra H).selectorToMarked_eq_shear

/-- Conjugating the diagonal CRT projector by the marked shear gives the graph projector. -/
theorem shear_conj_diagonalOperator :
    (shear H).conj (diagonalOperator H) = graphOperator H :=
  BlockGraphProjector.shear_conj_diagonalOperator
    (R := ℚ) (residualClass H)

/-- Multiplication by the base-sheet selector is idempotent. -/
theorem multiplication_isIdempotent :
    IsIdempotentElem (multiplication H) := by
  simpa only [markedAugmentedAlgebra_multiplication] using
    (markedAugmentedAlgebra H).multiplication_isIdempotent

/-- The transported graph operator is idempotent. -/
theorem graphOperator_isIdempotent :
    IsIdempotentElem (graphOperator H) :=
  BlockGraphProjector.operator_isIdempotent (R := ℚ) (residualClass H)

end MarkedSheetProjector

end

end HodgeConjecture
