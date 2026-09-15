import HodgeConjecture.Cycles.DimensionFunction
import HodgeConjecture.Cycles.SupportDimension
import HodgeConjecture.Cycles.CycleDegree

/-!
# The actual dimension function in dimension at most one

If a scheme has topological Krull dimension at most one, its point
height is either zero or one. Every strict increase in the scheme's
closure-inclusion order takes height from zero to one.
Consequently integer-valued point height satisfies both conditions of
the existing dimension-function definition.

The construction uses only the stated bound on actual topological
Krull dimension. It needs no integrality, Noetherianity, catenarity or
independently supplied grading laws, and also applies to the empty
scheme. It does not assert the corresponding unit-step property in
higher dimension.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- The actual topological dimension bound controls every point height. -/
theorem point_height_le_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) (x : X) : Order.height x ≤ 1 := by
  have h : (Order.height x : WithBot ℕ∞) ≤ 1 := by
    calc
      (Order.height x : WithBot ℕ∞) =
          (Order.height (pointClosureOrderIso X x) : WithBot ℕ∞) := by
        rw [Order.height_orderIso]
      _ ≤ topologicalKrullDim X := Order.height_le_krullDim _
      _ ≤ 1 := hdim
  exact WithBot.coe_le_coe.mp h

/-- Under the dimension-one bound, any strict pair has heights zero
and one. This proves more than the immediate-specialization case. -/
theorem point_height_eq_zero_and_eq_one_of_lt (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) {x y : X} (hxy : x < y) :
    Order.height x = 0 ∧ Order.height y = 1 := by
  have hxfin : Order.height x < ⊤ :=
    (point_height_le_one X hdim x).trans_lt (by simp)
  have hlt := Order.height_strictMono hxy hxfin
  have hx : Order.height x = 0 :=
    ENat.lt_one_iff_eq_zero.mp (hlt.trans_le (point_height_le_one X hdim y))
  refine ⟨hx, le_antisymm (point_height_le_one X hdim y) ?_⟩
  exact ENat.one_le_iff_ne_zero.mpr (ne_of_gt (by simpa only [hx] using hlt))

/-- Integer point height is an actual dimension function whenever the
scheme's topological Krull dimension is at most one. -/
def DimensionFunction.ofKrullDimLEOne (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) : DimensionFunction X where
  toFun x := (Order.height x).toNat
  strictMono := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := point_height_eq_zero_and_eq_one_of_lt X hdim hxy
    simp only [hx, hy, ENat.toNat_zero, ENat.toNat_one, Nat.cast_zero, Nat.cast_one]
    exact zero_lt_one
  map_covBy := by
    intro x y hxy
    obtain ⟨hx, hy⟩ := point_height_eq_zero_and_eq_one_of_lt X hdim hxy.lt
    simp only [hx, hy, ENat.toNat_zero, ENat.toNat_one, Nat.cast_zero, Nat.cast_one,
      zero_add]

/-- The constructed function retains the actual point-height formula. -/
@[simp]
theorem DimensionFunction.ofKrullDimLEOne_apply (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ofKrullDimLEOne X hdim x = ((Order.height x).toNat : ℤ) := rfl

/-- No point receives a negative degree in this low-dimensional construction. -/
theorem DimensionFunction.ofKrullDimLEOne_nonneg (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    0 ≤ ofKrullDimLEOne X hdim x := Int.natCast_nonneg _

/-- Its values are exactly among the two permitted geometric dimensions. -/
theorem DimensionFunction.ofKrullDimLEOne_eq_zero_or_eq_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ofKrullDimLEOne X hdim x = 0 ∨ ofKrullDimLEOne X hdim x = 1 := by
  rcases lt_or_eq_of_le (point_height_le_one X hdim x) with hx | hx
  · left
    simp only [ofKrullDimLEOne_apply, ENat.lt_one_iff_eq_zero.mp hx,
      ENat.toNat_zero, Nat.cast_zero]
  · right
    simp only [ofKrullDimLEOne_apply, hx, ENat.toNat_one, Nat.cast_one]

/-- Every strict specialization has the required unit step, not only
those already presented with an immediate-specialization proof. -/
theorem DimensionFunction.ofKrullDimLEOne_values_of_lt (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) {x y : X} (hxy : x < y) :
    ofKrullDimLEOne X hdim x = 0 ∧ ofKrullDimLEOne X hdim y = 1 := by
  obtain ⟨hx, hy⟩ := point_height_eq_zero_and_eq_one_of_lt X hdim hxy
  simp only [ofKrullDimLEOne_apply, hx, hy, ENat.toNat_zero, ENat.toNat_one,
    Nat.cast_zero, Nat.cast_one, and_self]

/-- The constructed degree of an actual carrier agrees exactly with its
topological Krull dimension, expressed without truncation at infinity. -/
theorem supportDegree_ofKrullDimLEOne_eq_iff {X : Scheme.{u}}
    (hdim : topologicalKrullDim X ≤ 1) (W : IntegralClosedSubscheme X) (n : ℕ) :
    supportDegree (DimensionFunction.ofKrullDimLEOne X hdim) W = (n : ℤ) ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  have hfin : topologicalKrullDim X < ⊤ :=
    hdim.trans_lt (WithBot.coe_lt_coe.mpr (by simp))
  have h := point_height_toNat_eq X hfin (ambientGenericPoint W)
  rw [pointSupport_ambientGenericPoint] at h
  rw [← h]
  change ((Order.height (ambientGenericPoint W)).toNat : ℤ) = (n : ℤ) ↔
    ((Order.height (ambientGenericPoint W)).toNat : WithBot ℕ∞) = (n : WithBot ℕ∞)
  norm_cast

/-- In dimension at most one, the existing homogeneous-cycle membership
test for a fundamental carrier cycle is its actual dimension test. -/
theorem fundamentalCycle_mem_ofKrullDimLEOne_iff {X : Scheme.{u}}
    (R : Type*) [Semiring R] [Nontrivial R]
    (hdim : topologicalKrullDim X ≤ 1) (W : IntegralClosedSubscheme X) (n : ℕ) :
    fundamentalCycle R W ∈ cyclesOfDegree R (DimensionFunction.ofKrullDimLEOne X hdim) n ↔
      topologicalKrullDim W.val.subscheme = (n : WithBot ℕ∞) := by
  rw [fundamentalCycle_mem_cyclesOfDegree_iff, supportDegree_ofKrullDimLEOne_eq_iff]

end

end HodgeConjecture.SchemeCycles
