import HodgeConjecture.Boundary.Sheets.GenericProjector
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring

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

/-- Sheet functions vanishing at the distinguished base sheet. -/
abbrev Residual := LinearMap.ker (baseEvaluation H)

/-- The characteristic function of the distinguished base sheet. -/
def selector : GenericSheetAlgebra ℚ H :=
  genericSheetSelector ℚ H {baseSheet H}

@[simp]
theorem selector_apply_base :
    selector H (baseSheet H) = 1 := by
  simp [selector, genericSheetSelector]

/-- The marked residual class `q - 1`, which vanishes at the base sheet. -/
def residualClass : Residual H :=
  ⟨selector H - 1, by
    simp [baseEvaluation]⟩

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
        simp [baseEvaluation]⟩)
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
        simp [baseEvaluation]⟩)
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
def graphOperator : Module.End ℚ (ℚ × Residual H) where
  toFun tx := (tx.1, tx.1 • residualClass H)
  map_add' x y := by
    ext <;> simp [add_smul]
  map_smul' t x := by
    ext <;> simp [mul_smul]

@[simp]
theorem graphOperator_apply (t : ℚ) (x : Residual H) :
    graphOperator H (t, x) = (t, t • residualClass H) :=
  rfl

/-- The diagonal projector onto the marked scalar coordinate. -/
def diagonalOperator : Module.End ℚ (ℚ × Residual H) where
  toFun tx := (tx.1, 0)
  map_add' x y := by ext <;> simp
  map_smul' t x := by ext <;> simp

@[simp]
theorem diagonalOperator_apply (t : ℚ) (x : Residual H) :
    diagonalOperator H (t, x) = (t, 0) :=
  rfl

/--
The lower-triangular shear from selector/CRT coordinates to constant-marked
coordinates.  Its off-diagonal entry is the canonical residual class.
-/
def shear : (ℚ × Residual H) ≃ₗ[ℚ] (ℚ × Residual H) where
  toFun tx := (tx.1, tx.2 + tx.1 • residualClass H)
  invFun tx := (tx.1, tx.2 - tx.1 • residualClass H)
  left_inv tx := by
    rcases tx with ⟨t, x⟩
    ext <;> simp
  right_inv tx := by
    rcases tx with ⟨t, x⟩
    ext <;> simp
  map_add' x y := by
    apply Prod.ext
    · simp
    · apply Subtype.ext
      ext s
      simp [add_smul]
      ring
  map_smul' t x := by
    ext <;> simp [mul_smul]

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
  apply LinearMap.ext
  intro tx
  rcases tx with ⟨t, x⟩
  have hx := x.property
  change (x : GenericSheetAlgebra ℚ H) (baseSheet H) = 0 at hx
  apply Prod.ext
  · simp [LinearEquiv.conj_apply, multiplication, selector,
      genericSheetSelector, hx]
  · apply Subtype.ext
    ext s
    by_cases hs : s = baseSheet H
    · subst s
      simp [LinearEquiv.conj_apply, multiplication, selector,
        genericSheetSelector, hx]
    · simp [LinearEquiv.conj_apply, multiplication, selector,
        genericSheetSelector, hs, hx]

/--
In selector/CRT coordinates, multiplication by the base-sheet selector is
the diagonal projector `diag(1, 0)`.
-/
theorem selectorDecomposition_conj_multiplication :
    (selectorDecomposition H).conj (multiplication H) =
      diagonalOperator H := by
  apply LinearMap.ext
  intro tx
  rcases tx with ⟨t, x⟩
  have hx := x.property
  change (x : GenericSheetAlgebra ℚ H) (baseSheet H) = 0 at hx
  apply Prod.ext
  · simp [LinearEquiv.conj_apply, multiplication, selector,
      genericSheetSelector, hx]
  · apply Subtype.ext
    ext s
    by_cases hs : s = baseSheet H
    · subst s
      simp [LinearEquiv.conj_apply, multiplication, selector,
        genericSheetSelector, hx]
    · simp [LinearEquiv.conj_apply, multiplication, selector,
        genericSheetSelector, hs, hx]

/-- The two sheet splittings differ by the canonical lower shear. -/
theorem selectorToMarked_eq_shear :
    (selectorDecomposition H).symm.trans (decomposition H) = shear H := by
  apply LinearEquiv.ext
  intro tx
  rcases tx with ⟨t, x⟩
  have hx := x.property
  change (x : GenericSheetAlgebra ℚ H) (baseSheet H) = 0 at hx
  apply Prod.ext
  · simp [hx]
  · apply Subtype.ext
    ext s
    by_cases hs : s = baseSheet H
    · subst s
      simp [decomposition, selectorDecomposition, shear, selector,
        genericSheetSelector, residualClass, hx]
    · simp [decomposition, selectorDecomposition, shear, selector,
        genericSheetSelector, residualClass, hs, hx, sub_eq_add_neg]

/-- Conjugating the diagonal CRT projector by the marked shear gives the graph projector. -/
theorem shear_conj_diagonalOperator :
    (shear H).conj (diagonalOperator H) = graphOperator H := by
  apply LinearMap.ext
  intro tx
  rcases tx with ⟨t, x⟩
  simp [LinearEquiv.conj_apply]

/-- Multiplication by the base-sheet selector is idempotent. -/
theorem multiplication_isIdempotent :
    IsIdempotentElem (multiplication H) := by
  change multiplication H * multiplication H = multiplication H
  apply LinearMap.ext
  intro f
  ext s
  by_cases hs : s = baseSheet H
  · subst s
    simp [multiplication, selector, genericSheetSelector,
      Module.End.mul_apply]
  · simp [multiplication, selector, genericSheetSelector,
      Module.End.mul_apply, hs]

/-- The transported graph operator is idempotent. -/
theorem graphOperator_isIdempotent :
    IsIdempotentElem (graphOperator H) := by
  change graphOperator H * graphOperator H = graphOperator H
  apply LinearMap.ext
  intro tx
  rcases tx with ⟨t, x⟩
  simp [Module.End.mul_apply]

end MarkedSheetProjector

end

end HodgeConjecture
