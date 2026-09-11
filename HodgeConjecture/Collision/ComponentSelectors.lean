import HodgeConjecture.Collision.SchemeDecomposition

/-!
# Diagonal and off-diagonal component selectors

Let `J` be the ideal cutting out the diagonal inside a collision algebra.  If
an idempotent `q` generates `J`, then

* `q` vanishes on the diagonal quotient and equals one on the residual
  off-diagonal quotient;
* `1 - q` equals one on the diagonal quotient and vanishes on the residual
  off-diagonal quotient.

Thus `q` is the off-diagonal selector, whereas `1 - q` is the diagonal
selector.  Notice that the diagonal selector generates `J.annihilator`, the
ideal whose *zero locus* is the off-diagonal component.

For the product decomposition

`C ≃ (C ⧸ J) × (C ⧸ J.annihilator)`,

whose factors are ordered diagonal first and off-diagonal second, the two
selectors therefore have coordinates

`q ↦ (0, 1)` and `1 - q ↦ (1, 0)`.

These selectors are idempotent for multiplication in the collision
coordinate ring.  Equivalently, they select open-and-closed scheme
components.  No idempotence under composition of algebraic correspondences
is asserted here; that requires a separate cycle-extraction and convolution-
compatibility theorem.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra

noncomputable section

universe u v

variable {C : Type u} [CommRing C]

/--
An element is a diagonal selector for `J` when it is one on `C ⧸ J` and zero
on the residual quotient `C ⧸ J.annihilator`.
-/
def IsDiagonalSelector (J : Ideal C) (e : C) : Prop :=
  IsIdempotentElem e ∧
    Ideal.Quotient.mk J e = 1 ∧
      Ideal.Quotient.mk J.annihilator e = 0

/--
An element is an off-diagonal selector for `J` when it is zero on `C ⧸ J`
and one on the residual quotient `C ⧸ J.annihilator`.
-/
def IsOffDiagonalSelector (J : Ideal C) (e : C) : Prop :=
  IsIdempotentElem e ∧
    Ideal.Quotient.mk J e = 0 ∧
      Ideal.Quotient.mk J.annihilator e = 1

/--
If an idempotent `q` generates `J`, its complement generates the annihilator
of `J`.
-/
theorem annihilator_eq_span_one_sub_of_eq_span
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q}) :
    J.annihilator = Ideal.span {1 - q} := by
  rw [hJ]
  exact CollisionFoundations.annihilator_span_idempotent hq

/-- The generator `q` vanishes on the quotient cut out by `J`. -/
theorem quotient_generator_eq_zero
    (J : Ideal C) (q : C)
    (hJ : J = Ideal.span {q}) :
    Ideal.Quotient.mk J q = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, hJ]
  exact Ideal.mem_span_singleton_self q

/--
An idempotent generator `q` equals one on the quotient by `J.annihilator`.
-/
theorem quotientAnnihilator_generator_eq_one
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q}) :
    Ideal.Quotient.mk J.annihilator q = 1 := by
  have hComplement :
      1 - q ∈ J.annihilator := by
    rw [annihilator_eq_span_one_sub_of_eq_span J q hq hJ]
    exact Ideal.mem_span_singleton_self (1 - q)
  have hZero :
      Ideal.Quotient.mk J.annihilator (1 - q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hComplement
  calc
    Ideal.Quotient.mk J.annihilator q =
        Ideal.Quotient.mk J.annihilator (1 - (1 - q)) := by ring_nf
    _ = 1 - Ideal.Quotient.mk J.annihilator (1 - q) := by
      rw [map_sub, map_one]
    _ = 1 := by rw [hZero, sub_zero]

/-- The complementary idempotent `1 - q` equals one on `C ⧸ J`. -/
theorem quotient_one_sub_generator_eq_one
    (J : Ideal C) (q : C)
    (hJ : J = Ideal.span {q}) :
    Ideal.Quotient.mk J (1 - q) = 1 := by
  rw [map_sub, map_one, quotient_generator_eq_zero J q hJ, sub_zero]

/--
The complementary idempotent `1 - q` vanishes on
`C ⧸ J.annihilator`.
-/
theorem quotientAnnihilator_one_sub_generator_eq_zero
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q}) :
    Ideal.Quotient.mk J.annihilator (1 - q) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem,
    annihilator_eq_span_one_sub_of_eq_span J q hq hJ]
  exact Ideal.mem_span_singleton_self (1 - q)

/-- An idempotent generator of `J` is the off-diagonal selector. -/
theorem generator_isOffDiagonalSelector
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q}) :
    IsOffDiagonalSelector J q :=
  ⟨hq, quotient_generator_eq_zero J q hJ,
    quotientAnnihilator_generator_eq_one J q hq hJ⟩

/-- The complement of an idempotent generator of `J` is the diagonal selector. -/
theorem one_sub_generator_isDiagonalSelector
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q}) :
    IsDiagonalSelector J (1 - q) :=
  ⟨hq.one_sub, quotient_one_sub_generator_eq_one J q hJ,
    quotientAnnihilator_one_sub_generator_eq_zero J q hq hJ⟩

/--
Under the diagonal-first CRT decomposition, an idempotent generator of `J`
has coordinates `(0, 1)`.
-/
theorem idealProductDecomposition_generator
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q})
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤) :
    idealProductDecomposition J hOverlap hContact q = (0, 1) := by
  apply Prod.ext
  · rw [idealProductDecomposition_fst]
    exact quotient_generator_eq_zero J q hJ
  · rw [idealProductDecomposition_snd]
    exact quotientAnnihilator_generator_eq_one J q hq hJ

/--
Under the diagonal-first CRT decomposition, the diagonal selector `1 - q`
has coordinates `(1, 0)`.
-/
theorem idealProductDecomposition_one_sub_generator
    (J : Ideal C) (q : C)
    (hq : IsIdempotentElem q)
    (hJ : J = Ideal.span {q})
    (hOverlap : overlapDefectIdeal J = ⊥)
    (hContact : contactIdeal J = ⊤) :
    idealProductDecomposition J hOverlap hContact (1 - q) = (1, 0) := by
  apply Prod.ext
  · rw [idealProductDecomposition_fst]
    exact quotient_one_sub_generator_eq_one J q hJ
  · rw [idealProductDecomposition_snd]
    exact quotientAnnihilator_one_sub_generator_eq_zero J q hq hJ

section Collision

variable (B : Type u) (A : Type v)
variable [CommRing B] [CommRing A] [Algebra B A]

/--
For a collision obstruction generated by `q`, the diagonal selector `1 - q`
generates the residual off-diagonal ideal.
-/
theorem collisionOffDiagonalIdeal_eq_span_diagonalSelector
    (q : CollisionAlgebra B A)
    (hq : IsIdempotentElem q)
    (hObstruction :
      collisionObstructionIdeal B A = Ideal.span {q}) :
    collisionOffDiagonalIdeal B A = Ideal.span {1 - q} := by
  rw [collisionOffDiagonalIdeal_eq_annihilator]
  exact
    annihilator_eq_span_one_sub_of_eq_span
      (collisionObstructionIdeal B A) q hq hObstruction

/--
An idempotent generator of the collision obstruction is the off-diagonal
selector.
-/
theorem collision_generator_isOffDiagonalSelector
    (q : CollisionAlgebra B A)
    (hq : IsIdempotentElem q)
    (hObstruction :
      collisionObstructionIdeal B A = Ideal.span {q}) :
    IsOffDiagonalSelector (collisionObstructionIdeal B A) q :=
  generator_isOffDiagonalSelector
    (collisionObstructionIdeal B A) q hq hObstruction

/--
The complementary idempotent is the diagonal selector in the collision
algebra.
-/
theorem collision_one_sub_generator_isDiagonalSelector
    (q : CollisionAlgebra B A)
    (hq : IsIdempotentElem q)
    (hObstruction :
      collisionObstructionIdeal B A = Ideal.span {q}) :
    IsDiagonalSelector (collisionObstructionIdeal B A) (1 - q) :=
  one_sub_generator_isDiagonalSelector
    (collisionObstructionIdeal B A) q hq hObstruction

/--
The complementary selector pair attached to a collision decomposition.

The stored generator `q` is the off-diagonal selector.  Its complement
`1 - q` is the diagonal selector, while `q` itself generates the ideal
cutting out the diagonal.
-/
structure CollisionSelectorPair where
  q : CollisionAlgebra B A
  obstruction_eq_span :
    collisionObstructionIdeal B A = Ideal.span {q}
  q_isOffDiagonalSelector :
    IsOffDiagonalSelector (collisionObstructionIdeal B A) q
  one_sub_q_isDiagonalSelector :
    IsDiagonalSelector (collisionObstructionIdeal B A) (1 - q)

/--
An essentially finite-type, formally unramified algebra has a complementary
collision selector pair.

Formal unramifiedness makes the collision contact ideal the unit ideal.  The
resulting idempotent generator of the diagonal obstruction is the
off-diagonal selector, and its complement is the diagonal selector.
-/
theorem collisionSelectorPair_nonempty_of_formallyUnramified
    [EssFiniteType B A] [Algebra.FormallyUnramified B A] :
    Nonempty (CollisionSelectorPair B A) := by
  have hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤ :=
    (collisionContactIdeal_eq_top_iff_formallyUnramified B A).2
      inferInstance
  obtain ⟨q, hq, hObstruction⟩ :=
    exists_idempotent_generator_of_contact_eq_top
      (collisionObstructionIdeal B A) hContact
  exact
    ⟨{
      q := q
      obstruction_eq_span := hObstruction
      q_isOffDiagonalSelector :=
        collision_generator_isOffDiagonalSelector
          B A q hq hObstruction
      one_sub_q_isDiagonalSelector :=
        collision_one_sub_generator_isDiagonalSelector
          B A q hq hObstruction
    }⟩

/--
Elementwise form of the canonical existence result for collision selectors.
-/
theorem exists_collisionSelectors_of_formallyUnramified
    [EssFiniteType B A] [Algebra.FormallyUnramified B A] :
    ∃ q : CollisionAlgebra B A,
      collisionObstructionIdeal B A = Ideal.span {q} ∧
        IsOffDiagonalSelector (collisionObstructionIdeal B A) q ∧
          IsDiagonalSelector
            (collisionObstructionIdeal B A) (1 - q) := by
  obtain ⟨S⟩ :=
    collisionSelectorPair_nonempty_of_formallyUnramified B A
  exact
    ⟨S.q, S.obstruction_eq_span,
      S.q_isOffDiagonalSelector,
      S.one_sub_q_isDiagonalSelector⟩

end Collision

end

end HodgeConjecture
