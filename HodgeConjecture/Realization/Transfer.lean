module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Rational degree transfer

The linear degree identity gives injectivity and an idempotent normalized
pull–push operator. This common API is independent of schemes, Chow groups,
and Betti realization. Concrete geometric constructions must prove the
identity when they instantiate it.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

/-- The formal normalized pull--push operator is idempotent whenever
`push ∘ pull = d · id` and `d` is positive. -/
theorem normalizedPullPush_isIdempotent
    {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (pull : W →ₗ[ℚ] V) (push : V →ₗ[ℚ] W)
    (d : ℕ) (hd : d ≠ 0)
    (hdeg : push.comp pull = (d : ℚ) • LinearMap.id) :
    IsIdempotentElem
      ((d : ℚ)⁻¹ • pull.comp push) := by
  have hdq : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd
  have hcoeff :
      (d : ℚ)⁻¹ * ((d : ℚ)⁻¹ * (d : ℚ)) =
        (d : ℚ)⁻¹ := by
    field_simp
  rw [IsIdempotentElem]
  ext x
  have hx := LinearMap.congr_fun hdeg (push x)
  simp only [Module.End.mul_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  rw [map_smul, map_smul, hx, map_smul]
  simp only [smul_smul, hcoeff]

/-- Rational pull--push data with a positive integral degree.  A finite
locally free morphism supplies this structure on any rational theory for
which the degree formula has been established. -/
structure RationalDegreeTransfer
    (V : Type u) (W : Type v)
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] where
  pull : W →ₗ[ℚ] V
  push : V →ₗ[ℚ] W
  degree : ℕ
  degree_ne_zero : degree ≠ 0
  push_comp_pull :
    push.comp pull = (degree : ℚ) • LinearMap.id

namespace RationalDegreeTransfer

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- Positive-degree transfer makes rational pullback injective. This uses
the supplied degree law, not a separately assumed injectivity statement. -/
theorem pull_injective (T : RationalDegreeTransfer V W) :
    Function.Injective T.pull := by
  have hd : (T.degree : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr T.degree_ne_zero
  have hleft : Function.LeftInverse
      (fun x ↦ (T.degree : ℚ)⁻¹ • T.push x) T.pull := by
    intro x
    have hx := LinearMap.congr_fun T.push_comp_pull x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hx
    change (T.degree : ℚ)⁻¹ • T.push (T.pull x) = x
    rw [hx, smul_smul, inv_mul_cancel₀ hd, one_smul]
  exact hleft.injective

/-- A finite-cover vanishing can detect only an already zero rational
class when the positive-degree transfer law holds. -/
@[simp]
theorem pull_eq_zero_iff (T : RationalDegreeTransfer V W) (x : W) :
    T.pull x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply T.pull_injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- The normalized pull--push endomorphism on the source theory. -/
def normalizedProjector
    (T : RationalDegreeTransfer V W) :
    Module.End ℚ V :=
  (T.degree : ℚ)⁻¹ • T.pull.comp T.push

/-- The normalized transfer endomorphism is a projector. -/
theorem normalizedProjector_isIdempotent
    (T : RationalDegreeTransfer V W) :
    IsIdempotentElem T.normalizedProjector :=
  normalizedPullPush_isIdempotent
    T.pull T.push T.degree T.degree_ne_zero T.push_comp_pull

end RationalDegreeTransfer

end

end HodgeConjecture
