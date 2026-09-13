import HodgeConjecture.Boundary.Sheets.MarkedBlockProjector
import HodgeConjecture.Realization.Chow.Examples.SplitCycleOperations
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Option

/-!
# Actual Chow classes of the marked Galois-sheet residual ideal

The residual ideal consists of rational sheet functions vanishing at the
distinguished sheet. Restriction to the complement is an equivalence, and
the Chow map is constructed as the sum of the corresponding actual point
cycles. Its coefficient formula proves bijectivity and compatibility with
geometric intersection. The marked class `q - 1` gives the negative
fundamental cycle of the complement. No Betti inverse defines this map.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitGaloisResidual

noncomputable section

open Classical SplitZeroCycles
open scoped BigOperators

variable {G : Type} [Group G] (D : Subgroup G)

/-- The actual sheet labels other than the distinguished base sheet. -/
abbrev Complement := {s : CollisionFoundations.GaloisSheets D // s ≠ baseSheet D}

/-- The full sheet set is its distinguished point plus the actual complement. -/
def sheetEquiv : Option (Complement D) ≃ CollisionFoundations.GaloisSheets D :=
  Equiv.optionSubtypeNe (baseSheet D)

@[simp]
theorem sheetEquiv_none : sheetEquiv D none = baseSheet D := rfl

@[simp]
theorem sheetEquiv_some (s : Complement D) : sheetEquiv D (some s) = s.val := rfl

/-- Restriction of the residual ideal to the actual complementary sheets,
with inverse given by zero extension at the base sheet. -/
def residualCoordinates : MarkedSheetProjector.Residual D ≃ₗ[ℚ] (Complement D → ℚ) where
  toFun x s := x.val s.val
  invFun a := ⟨fun s ↦ if h : s = baseSheet D then 0 else a ⟨s, h⟩, by
    change (if h : baseSheet D = baseSheet D then (0 : ℚ) else a ⟨baseSheet D, h⟩) = 0
    simp⟩
  left_inv x := by
    apply Subtype.ext
    funext s
    by_cases h : s = baseSheet D
    · subst s
      have hx : x.val (baseSheet D) = 0 := x.property
      simp [hx]
    · simp [h]
  right_inv a := by
    funext s
    simp [s.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem residualCoordinates_apply (x : MarkedSheetProjector.Residual D) (s : Complement D) :
    residualCoordinates D x s = x.val s.val := rfl

@[simp]
theorem residualCoordinates_mul (x y : MarkedSheetProjector.Residual D) :
    residualCoordinates D (x * y) = residualCoordinates D x * residualCoordinates D y := rfl

@[simp]
theorem residualCoordinates_residualClass (s : Complement D) :
    residualCoordinates D (MarkedSheetProjector.residualClass D) s = -1 := by
  simp [MarkedSheetProjector.residualClass, MarkedSheetProjector.selector,
    genericSheetSelector, s.property]

variable [Finite G]

local instance : Fintype (Complement D) := Fintype.ofFinite (Complement D)

/-- The geometric residual cycle, assembled from actual integral point
subschemes with the residual ideal's rational coefficients. -/
def residualCycles : MarkedSheetProjector.Residual D →ₗ[ℚ] Cycles ℂ (Complement D) ℚ where
  toFun x := ∑ s : Complement D, residualCoordinates D x s • pointCycle ℂ (Complement D) ℚ s
  map_add' x y := by
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul,
      smul_eq_mul]

@[simp]
theorem coordinates_residualCycles (x : MarkedSheetProjector.Residual D) (s : Complement D) :
    coordinates ℂ (Complement D) ℚ (residualCycles D x) s = x.val s.val := by
  simp [residualCycles, -coordinates_apply, Pi.single_apply]

/-- The residual Chow map is the class of the explicitly constructed cycle. -/
def residualChow : MarkedSheetProjector.Residual D →ₗ[ℚ] Chow ℂ (Complement D) ℚ :=
  (classMap ℂ (Complement D) ℚ).comp (residualCycles D)

@[simp]
theorem residualChow_apply (x : MarkedSheetProjector.Residual D) :
    residualChow D x = classMap ℂ (Complement D) ℚ
      (∑ s : Complement D, x.val s.val • pointCycle ℂ (Complement D) ℚ s) := rfl

@[simp]
theorem chowCoordinates_residualChow (x : MarkedSheetProjector.Residual D) (s : Complement D) :
    chowCoordinates ℂ (Complement D) ℚ (residualChow D x) s = x.val s.val := by
  exact coordinates_residualCycles D x s

/-- The same geometric residual Chow map, now with its proved inverse. -/
def residualChowEquiv : MarkedSheetProjector.Residual D ≃ₗ[ℚ] Chow ℂ (Complement D) ℚ where
  __ := residualChow D
  invFun z := (residualCoordinates D).symm (chowCoordinates ℂ (Complement D) ℚ z)
  left_inv x := by
    apply (residualCoordinates D).injective
    change residualCoordinates D ((residualCoordinates D).symm
      (chowCoordinates ℂ (Complement D) ℚ (residualChow D x))) = residualCoordinates D x
    rw [LinearEquiv.apply_symm_apply]
    funext s
    exact chowCoordinates_residualChow D x s
  right_inv z := by
    apply (chowCoordinates ℂ (Complement D) ℚ).injective
    change chowCoordinates ℂ (Complement D) ℚ (residualChow D
      ((residualCoordinates D).symm (chowCoordinates ℂ (Complement D) ℚ z))) = _
    funext s
    rw [chowCoordinates_residualChow]
    change residualCoordinates D ((residualCoordinates D).symm
      (chowCoordinates ℂ (Complement D) ℚ z)) s = _
    rw [LinearEquiv.apply_symm_apply]

@[simp]
theorem residualChowEquiv_apply (x : MarkedSheetProjector.Residual D) :
    residualChowEquiv D x = residualChow D x := rfl

/-- The actual fundamental point-sum on the complementary split scheme. -/
def fundamentalClass : Chow ℂ (Complement D) ℚ :=
  classMap ℂ (Complement D) ℚ (∑ s : Complement D, pointCycle ℂ (Complement D) ℚ s)

@[simp]
theorem chowCoordinates_fundamentalClass (s : Complement D) :
    chowCoordinates ℂ (Complement D) ℚ (fundamentalClass D) s = 1 := by
  simp [fundamentalClass, -coordinates_apply, Pi.single_apply]

/-- The marked residual `q - 1` realizes as minus the actual fundamental
cycle of the complementary finite split scheme. -/
theorem residualChow_residualClass :
    residualChow D (MarkedSheetProjector.residualClass D) = -fundamentalClass D := by
  apply (chowCoordinates ℂ (Complement D) ℚ).injective
  ext s
  rw [chowCoordinates_residualChow, map_neg, Pi.neg_apply,
    chowCoordinates_fundamentalClass]
  exact residualCoordinates_residualClass D s

/-- Inherited multiplication in the residual ideal is realized by geometric
Chow intersection, not by correspondence convolution. -/
theorem residualChow_mul (x y : MarkedSheetProjector.Residual D) :
    residualChow D (x * y) = chowIntersection ℂ ℚ (residualChow D x) (residualChow D y) := by
  apply (chowCoordinates ℂ (Complement D) ℚ).injective
  ext s
  rw [chowCoordinates_intersection, chowCoordinates_residualChow,
    chowCoordinates_residualChow, chowCoordinates_residualChow]
  rfl

end

end HodgeConjecture.SplitGaloisResidual
