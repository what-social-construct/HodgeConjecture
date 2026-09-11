import HodgeConjecture.Realization.Chow.Model
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Rational transfer projectors

This file isolates the formal pull--push calculation behind the projector
associated with a finite locally free morphism of positive degree `d`.

In the intended Chow application, `pull` and `push` are flat pullback and
proper pushforward and the relation `push ∘ pull = d · id` is Stacks Project
Tag `02RH`.  Mathlib does not yet construct rational Chow groups and these
operations for the schemes in this repository, so the geometric maps and
degree relation remain explicit data.  The normalized projector and its
idempotence are proved here without any further geometric assumption.
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

/-- Transfer data canonically determines a rational cohomological projector.
The same constructor can be instantiated with rational Chow groups once
their pull--push operations are supplied. -/
def toRationalCohomologicalProjector
    (T : RationalDegreeTransfer V W) :
    RationalCohomologicalProjector V where
  operator := T.normalizedProjector
  operator_isIdempotent := T.normalizedProjector_isIdempotent

@[simp]
theorem toRationalCohomologicalProjector_operator
    (T : RationalDegreeTransfer V W) :
    T.toRationalCohomologicalProjector.operator =
      T.normalizedProjector :=
  rfl

end RationalDegreeTransfer

end

end HodgeConjecture
