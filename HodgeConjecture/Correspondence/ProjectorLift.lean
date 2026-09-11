import HodgeConjecture.Correspondence.Algebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Projection

/-!
# Algebraic lifts of cohomological projectors

This module states the target of the correspondence layer independently of
any particular collision or Galois construction.

An `AlgebraicProjectorLift` consists of an idempotent in a generally
noncommutative rational correspondence algebra whose action is a prescribed
cohomological idempotent.  A `DiagonalDecompositionLift` is a finite family
of mutually orthogonal correspondence idempotents summing to the diagonal
unit.

These are output structures.  Their constructors must come from actual
geometry, for example a group/Hecke calculation in the cover-generated
branch; no existence claim is made here.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

/--
The action of a rational correspondence algebra on a rational cohomology
module.
-/
structure RationalCorrespondenceAction
    (Γ : Type u) (H : Type v)
    [Ring Γ] [Algebra ℚ Γ]
    [AddCommGroup H] [Module ℚ H] where
  action : Γ →ₐ[ℚ] Module.End ℚ H

namespace RationalCorrespondenceAction

variable {Γ : Type u} {H : Type v}
variable [Ring Γ] [Algebra ℚ Γ]
variable [AddCommGroup H] [Module ℚ H]

/-- The cohomological operator induced by a correspondence. -/
abbrev operator
    (ρ : RationalCorrespondenceAction Γ H)
    (γ : Γ) :
    Module.End ℚ H :=
  ρ.action γ

end RationalCorrespondenceAction

/--
An algebraic correspondence lift of a prescribed cohomological projector.
-/
structure AlgebraicProjectorLift
    {Γ : Type u} {H : Type v}
    [Ring Γ] [Algebra ℚ Γ]
    [AddCommGroup H] [Module ℚ H]
    (ρ : RationalCorrespondenceAction Γ H)
    (e : Module.End ℚ H) where
  projector : Γ
  projector_isIdempotent :
    IsIdempotentElem projector
  realizes :
    ρ.action projector = e

namespace AlgebraicProjectorLift

variable {Γ : Type u} {H : Type v}
variable [Ring Γ] [Algebra ℚ Γ]
variable [AddCommGroup H] [Module ℚ H]
variable {ρ : RationalCorrespondenceAction Γ H}
variable {e : Module.End ℚ H}

/-- Any realized operator in an algebraic projector lift is idempotent. -/
theorem cohomological_isIdempotent
    (L : AlgebraicProjectorLift ρ e) :
    IsIdempotentElem e := by
  rw [← L.realizes]
  exact L.projector_isIdempotent.map ρ.action

/-- The complementary correspondence lifts the complementary projector. -/
def complement
    (L : AlgebraicProjectorLift ρ e) :
    AlgebraicProjectorLift ρ (1 - e) where
  projector := 1 - L.projector
  projector_isIdempotent :=
    L.projector_isIdempotent.one_sub
  realizes := by
    rw [map_sub, map_one, L.realizes]

end AlgebraicProjectorLift

/--
A finite algebraic lift of a cohomological decomposition of the diagonal.

Multiplication is correspondence convolution and `1` is the diagonal
class.  Pairwise orthogonality is stated for ordered pairs, hence includes
both directions.
-/
structure DiagonalDecompositionLift
    {Γ : Type u} {H : Type v} {ι : Type*}
    [Ring Γ] [Algebra ℚ Γ]
    [AddCommGroup H] [Module ℚ H]
    [Fintype ι]
    (ρ : RationalCorrespondenceAction Γ H)
    (e : ι → Module.End ℚ H) where
  projector : ι → Γ
  realizes :
    ∀ i, ρ.action (projector i) = e i
  projector_isIdempotent :
    ∀ i, IsIdempotentElem (projector i)
  orthogonal :
    ∀ i j, i ≠ j → projector i * projector j = 0
  sum_eq_diagonal :
    ∑ i, projector i = 1

namespace DiagonalDecompositionLift

variable {Γ : Type u} {H : Type v} {ι : Type*}
variable [Ring Γ] [Algebra ℚ Γ]
variable [AddCommGroup H] [Module ℚ H]
variable [Fintype ι]
variable {ρ : RationalCorrespondenceAction Γ H}
variable {e : ι → Module.End ℚ H}

/-- Every member of a lifted decomposition is a cohomological idempotent. -/
theorem cohomological_isIdempotent
    (L : DiagonalDecompositionLift ρ e)
    (i : ι) :
    IsIdempotentElem (e i) := by
  rw [← L.realizes i]
  exact (L.projector_isIdempotent i).map ρ.action

/-- A lifted diagonal decomposition sums to the identity on cohomology. -/
theorem cohomological_sum_eq_one
    (L : DiagonalDecompositionLift ρ e) :
    ∑ i, e i = 1 := by
  calc
    ∑ i, e i = ∑ i, ρ.action (L.projector i) := by
      simp_rw [L.realizes]
    _ = ρ.action (∑ i, L.projector i) := by
      rw [map_sum]
    _ = ρ.action 1 := by
      rw [L.sum_eq_diagonal]
    _ = 1 := by
      rw [map_one]

/-- Orthogonality descends to the cohomological operators. -/
theorem cohomological_orthogonal
    (L : DiagonalDecompositionLift ρ e)
    (i j : ι) (hij : i ≠ j) :
    e i * e j = 0 := by
  rw [← L.realizes i, ← L.realizes j,
    ← map_mul, L.orthogonal i j hij, map_zero]

end DiagonalDecompositionLift

/-!
## The canonical two-piece diagonal decomposition

One algebraic projector automatically supplies a decomposition of the
diagonal into that projector and its complement.  `Bool` is used only as a
two-element index: `true` denotes the prescribed summand and `false` its
complement.
-/

variable {Γ : Type u} {H : Type v}
variable [Ring Γ] [Algebra ℚ Γ]
variable [AddCommGroup H] [Module ℚ H]
variable {ρ : RationalCorrespondenceAction Γ H}
variable {e : Module.End ℚ H}

/-- A cohomological projector together with its complementary projector. -/
def complementaryCohomologicalProjectors
    (e : Module.End ℚ H) :
    Bool → Module.End ℚ H
  | true => e
  | false => 1 - e

/-- An algebraic projector together with its complementary correspondence. -/
def complementaryAlgebraicProjectors
    (L : AlgebraicProjectorLift ρ e) :
    Bool → Γ
  | true => L.projector
  | false => 1 - L.projector

@[simp]
theorem complementaryCohomologicalProjectors_true :
    complementaryCohomologicalProjectors e true = e :=
  rfl

@[simp]
theorem complementaryCohomologicalProjectors_false :
    complementaryCohomologicalProjectors e false = 1 - e :=
  rfl

@[simp]
theorem complementaryAlgebraicProjectors_true
    (L : AlgebraicProjectorLift ρ e) :
    complementaryAlgebraicProjectors L true = L.projector :=
  rfl

@[simp]
theorem complementaryAlgebraicProjectors_false
    (L : AlgebraicProjectorLift ρ e) :
    complementaryAlgebraicProjectors L false = 1 - L.projector :=
  rfl

namespace AlgebraicProjectorLift

/--
An algebraic projector lift canonically gives the two-piece decomposition of
the diagonal formed by the projector and its complement.
-/
def toBoolDiagonalDecomposition
    (L : AlgebraicProjectorLift ρ e) :
    DiagonalDecompositionLift ρ
      (complementaryCohomologicalProjectors e) where
  projector := complementaryAlgebraicProjectors L
  realizes := by
    intro i
    cases i <;>
      simp [complementaryAlgebraicProjectors,
        complementaryCohomologicalProjectors,
        map_sub, map_one, L.realizes]
  projector_isIdempotent := by
    intro i
    cases i
    · exact L.projector_isIdempotent.one_sub
    · exact L.projector_isIdempotent
  orthogonal := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · change (1 - L.projector) * L.projector = 0
      rw [sub_mul, one_mul, L.projector_isIdempotent, sub_self]
    · change L.projector * (1 - L.projector) = 0
      rw [mul_sub, mul_one, L.projector_isIdempotent, sub_self]
    · exact (hij rfl).elim
  sum_eq_diagonal := by
    rw [Fintype.sum_bool]
    simp [complementaryAlgebraicProjectors]

/-- The selected summand realizes the prescribed cohomological projector. -/
@[simp]
theorem toBoolDiagonalDecomposition_realizes_true
    (L : AlgebraicProjectorLift ρ e) :
    ρ.action
        ((L.toBoolDiagonalDecomposition).projector true) =
      e :=
  L.toBoolDiagonalDecomposition.realizes true

/-- The other summand realizes the complementary projector. -/
@[simp]
theorem toBoolDiagonalDecomposition_realizes_false
    (L : AlgebraicProjectorLift ρ e) :
    ρ.action
        ((L.toBoolDiagonalDecomposition).projector false) =
      1 - e :=
  L.toBoolDiagonalDecomposition.realizes false

end AlgebraicProjectorLift

end

end HodgeConjecture
