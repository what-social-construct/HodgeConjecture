module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section

/-!
# The actual punctured complex plane retracts onto the circle

Native polar coordinates identify the punctured plane with the actual
unit circle times the positive radius. The positive-radius factor is
contracted explicitly to one, retaining radial projection and the
original unit-circle inclusion as inverse maps.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.PuncturedComplexCircle

open ContinuousMap
open scoped Topology

/-- The original punctured-plane subtype topology. -/
abbrev Plane := ↥({0}ᶜ : Set ℂ)

/-- Positive radii carry their usual real subtype topology. -/
abbrev Radius := ↥(Set.Ioi (0 : ℝ))

/-- Native polar coordinates; no point topology is transported by definition. -/
def polarHomeomorph : Plane ≃ₜ Circle × Radius := homeomorphUnitSphereProd ℂ

/-- The original unit-circle inclusion into the punctured complex plane. -/
def inclusion : C(Circle, Plane) :=
  ⟨fun z ↦ ⟨(z : ℂ), z.coe_ne_zero⟩, by fun_prop⟩

/-- The actual radial map `z ↦ ‖z‖⁻¹ • z`. -/
def radial : C(Plane, Circle) :=
  ContinuousMap.fst.comp ⟨polarHomeomorph, polarHomeomorph.continuous⟩

@[simp]
theorem radial_coe (z : Plane) : (radial z : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) := by
  exact homeomorphUnitSphereProd_apply_fst_coe ℂ z

@[simp]
theorem inclusion_coe (z : Circle) : (inclusion z : ℂ) = (z : ℂ) := rfl

/-- The circle factor is unchanged while the radius moves linearly from one to its original value. -/
def productHomotopy :
    ((ContinuousMap.id Circle).prodMk (ContinuousMap.const Circle (⟨1, zero_lt_one⟩ : Radius))).comp
      ContinuousMap.fst |>.Homotopy (ContinuousMap.id (Circle × Radius)) where
  toFun p := (p.2.1, ⟨1 - p.1.1 + p.1.1 * p.2.2.1, by
    have ht0 : 0 ≤ p.1.1 := p.1.2.1
    have ht1 : p.1.1 ≤ 1 := p.1.2.2
    have hr : 0 < p.2.2.1 := p.2.2.2
    by_cases ht : p.1.1 = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1)
        (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) hr)⟩)
  continuous_toFun := by fun_prop
  map_zero_left p := by ext <;> simp
  map_one_left p := by ext <;> simp

/-- Projection onto the circle and its section at radius one form an actual homotopy equivalence. -/
def productEquiv : Circle × Radius ≃ₕ Circle where
  toFun := ContinuousMap.fst
  invFun := (ContinuousMap.id Circle).prodMk (ContinuousMap.const Circle ⟨1, zero_lt_one⟩)
  left_inv := ⟨productHomotopy⟩
  right_inv := by
    apply Homotopic.refl

/-- The punctured plane and native circle are homotopy equivalent by actual radial normalization. -/
def homotopyEquiv : Plane ≃ₕ Circle :=
  polarHomeomorph.toHomotopyEquiv.trans productEquiv

@[simp]
theorem homotopyEquiv_apply (z : Plane) : homotopyEquiv z = radial z := rfl

@[simp]
theorem homotopyEquiv_symm_apply (z : Circle) : homotopyEquiv.symm z = inclusion z := by
  apply Subtype.ext
  change (1 : ℝ) • (z : ℂ) = (z : ℂ)
  exact one_smul _ _

@[simp]
theorem radial_inclusion (z : Circle) : radial (inclusion z) = z := by
  apply Circle.ext
  simp [radial_coe]

end HodgeConjecture.PuncturedComplexCircle
