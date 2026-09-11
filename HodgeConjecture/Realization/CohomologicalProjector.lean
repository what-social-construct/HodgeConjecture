import HodgeConjecture.Collision.SchemeDecomposition
import Mathlib.LinearAlgebra.Projection

/-!
# Correspondence and cohomological projectors

This file formalizes the final implication in the proposed hierarchy:

`scheme/correspondence decomposition ⟹ cohomological projector`.

The geometric input is kept explicit.  A `CorrespondenceRealization` consists
of

1. a multiplicative lift from the scheme-theoretic selector algebra to a
   correspondence algebra;
2. the multiplicative action of correspondences on a cohomology module.

Consequently an idempotent selector gives an idempotent endomorphism.  Its
range and kernel are complementary.  A bigraded realization additionally
requires every correspondence to preserve the chosen pieces; the projector
then splits each piece separately.

This is intentionally an abstract realization layer.  Constructing the
correspondence cycle and identifying it with a Chow or Hodge realization are
the later geometric inputs.  The indexed bigrading below is not a definition
of rational Hodge classes and does not state the Hodge conjecture.  See
`Realization.HodgeClasses` for the literal cycle-class target and
`Realization.Chow.TateGraphProjector` for its projector reformulation.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v w z t

/--
Explicit input lifting scheme-theoretic selectors to correspondences and
letting those correspondences act on a cohomology module.
-/
structure CorrespondenceRealization
    (C : Type u) (Γ : Type v) (K : Type w) (H : Type z)
    [CommRing C] [Ring Γ] [CommRing K]
    [AddCommGroup H] [Module K H] where
  schemeToCorrespondence : C →+* Γ
  action : Γ →+* Module.End K H

namespace CorrespondenceRealization

variable {C : Type u} {Γ : Type v} {K : Type w} {H : Type z}
variable [CommRing C] [Ring Γ] [CommRing K]
variable [AddCommGroup H] [Module K H]

/-- The induced action of scheme-theoretic selectors on cohomology. -/
def cohomologyAction
    (ρ : CorrespondenceRealization C Γ K H) :
    C →+* Module.End K H :=
  ρ.action.comp ρ.schemeToCorrespondence

/-- The cohomological endomorphism realized by a selector. -/
def realizedOperator
    (ρ : CorrespondenceRealization C Γ K H) (q : C) :
    Module.End K H :=
  ρ.cohomologyAction q

/-- Multiplicative realizations carry idempotent selectors to projectors. -/
theorem realizedOperator_isIdempotent
    (ρ : CorrespondenceRealization C Γ K H)
    {q : C} (hq : IsIdempotentElem q) :
    IsIdempotentElem (ρ.realizedOperator q) :=
  hq.map ρ.cohomologyAction

/--
The image and kernel of a realized idempotent selector form a direct-sum
decomposition of the cohomology module.
-/
theorem realizedOperator_isCompl
    (ρ : CorrespondenceRealization C Γ K H)
    {q : C} (hq : IsIdempotentElem q) :
    IsCompl
      (LinearMap.range (ρ.realizedOperator q))
      (LinearMap.ker (ρ.realizedOperator q)) :=
  LinearMap.IsIdempotentElem.isCompl
    (ρ.realizedOperator_isIdempotent hq)

/-- The realized selector acts as an idempotent projector on cohomology. -/
def IsRealizedProjector
    (ρ : CorrespondenceRealization C Γ K H) (q : C) : Prop :=
  IsIdempotentElem (ρ.realizedOperator q) ∧
    IsCompl
      (LinearMap.range (ρ.realizedOperator q))
      (LinearMap.ker (ρ.realizedOperator q))

/-- Every idempotent selector realizes to a cohomological projector. -/
theorem isRealizedProjector
    (ρ : CorrespondenceRealization C Γ K H)
    {q : C} (hq : IsIdempotentElem q) :
    ρ.IsRealizedProjector q :=
  ⟨ρ.realizedOperator_isIdempotent hq,
    ρ.realizedOperator_isCompl hq⟩

end CorrespondenceRealization

/--
A realization equipped with indexed submodules preserved by every
correspondence.  Taking the index type to be `ℤ × ℤ` records the part of a
Hodge bigrading needed for projector arguments.
-/
structure BigradedCorrespondenceRealization
    (C : Type u) (Γ : Type v) (K : Type w) (H : Type z)
    (ι : Type t)
    [CommRing C] [Ring Γ] [CommRing K]
    [AddCommGroup H] [Module K H]
    extends CorrespondenceRealization C Γ K H where
  piece : ι → Submodule K H
  action_preserves_piece :
    ∀ (γ : Γ) (i : ι) (x : H), x ∈ piece i → action γ x ∈ piece i

/--
The minimal bigraded realization interface used for Hodge-theoretic
projectors.  It records `(p,q)`-pieces and their preservation, not the full
definition of a pure Hodge structure.
-/
abbrev HodgeBigradedRealization
    (C : Type u) (Γ : Type v) (K : Type w) (H : Type z)
    [CommRing C] [Ring Γ] [CommRing K]
    [AddCommGroup H] [Module K H] :=
  BigradedCorrespondenceRealization C Γ K H (ℤ × ℤ)

namespace BigradedCorrespondenceRealization

variable {C : Type u} {Γ : Type v} {K : Type w} {H : Type z}
variable {ι : Type t}
variable [CommRing C] [Ring Γ] [CommRing K]
variable [AddCommGroup H] [Module K H]

/-- A realized selector preserves every chosen graded piece. -/
theorem realizedOperator_preserves_piece
    (ρ : BigradedCorrespondenceRealization C Γ K H ι)
    (q : C) (i : ι) (x : H)
    (hx : x ∈ ρ.piece i) :
    ρ.toCorrespondenceRealization.realizedOperator q x ∈ ρ.piece i :=
  ρ.action_preserves_piece (ρ.schemeToCorrespondence q) i x hx

end BigradedCorrespondenceRealization

section InvariantSplitting

variable {K : Type w} {H : Type z}
variable [CommRing K] [AddCommGroup H] [Module K H]

/--
An invariant submodule splits into its intersections with the image and
kernel of an idempotent endomorphism.
-/
theorem invariantSubmodule_inf_range_sup_inf_ker
    {p : Module.End K H}
    (hp : IsIdempotentElem p)
    (U : Submodule K H)
    (hU : ∀ x : H, x ∈ U → p x ∈ U) :
    (U ⊓ LinearMap.range p) ⊔ (U ⊓ LinearMap.ker p) = U := by
  apply le_antisymm
  · exact sup_le inf_le_left inf_le_left
  · intro x hx
    have hpxU : p x ∈ U := hU x hx
    have hpxRange : p x ∈ LinearMap.range p :=
      LinearMap.mem_range_self p x
    have hrestU : x - p x ∈ U :=
      U.sub_mem hx hpxU
    have hrestKer : x - p x ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker]
      calc
        p (x - p x) = p x - p (p x) := by rw [map_sub]
        _ = p x - p x := by
          rw [← Module.End.mul_apply, hp.eq]
        _ = 0 := sub_self _
    exact
      Submodule.mem_sup.mpr
        ⟨p x, ⟨hpxU, hpxRange⟩,
          x - p x, ⟨hrestU, hrestKer⟩, by abel⟩

/--
The two summands in the invariant-submodule decomposition are disjoint.
-/
theorem invariantSubmodule_inf_range_inf_ker_disjoint
    {p : Module.End K H}
    (hp : IsIdempotentElem p)
    (U : Submodule K H) :
    Disjoint
      (U ⊓ LinearMap.range p)
      (U ⊓ LinearMap.ker p) :=
  (LinearMap.IsIdempotentElem.isCompl hp).disjoint.mono
    inf_le_right inf_le_right

end InvariantSplitting

namespace BigradedCorrespondenceRealization

variable {C : Type u} {Γ : Type v} {K : Type w} {H : Type z}
variable {ι : Type t}
variable [CommRing C] [Ring Γ] [CommRing K]
variable [AddCommGroup H] [Module K H]

/--
Each graded piece is the sum of the projector image and kernel lying inside
that same piece.
-/
theorem piece_projector_decomposition
    (ρ : BigradedCorrespondenceRealization C Γ K H ι)
    {q : C} (hq : IsIdempotentElem q)
    (i : ι) :
    (ρ.piece i ⊓
        LinearMap.range
          (ρ.toCorrespondenceRealization.realizedOperator q)) ⊔
      (ρ.piece i ⊓
        LinearMap.ker
          (ρ.toCorrespondenceRealization.realizedOperator q)) =
      ρ.piece i :=
  invariantSubmodule_inf_range_sup_inf_ker
    (ρ.toCorrespondenceRealization.realizedOperator_isIdempotent hq)
    (ρ.piece i)
    (ρ.realizedOperator_preserves_piece q i)

/-- The two projector summands inside each graded piece are disjoint. -/
theorem piece_projector_disjoint
    (ρ : BigradedCorrespondenceRealization C Γ K H ι)
    {q : C} (hq : IsIdempotentElem q)
    (i : ι) :
    Disjoint
      (ρ.piece i ⊓
        LinearMap.range
          (ρ.toCorrespondenceRealization.realizedOperator q))
      (ρ.piece i ⊓
        LinearMap.ker
          (ρ.toCorrespondenceRealization.realizedOperator q)) :=
  invariantSubmodule_inf_range_inf_ker_disjoint
    (ρ.toCorrespondenceRealization.realizedOperator_isIdempotent hq)
    (ρ.piece i)

/--
A projector compatible with all pieces of the chosen bigrading.
-/
def IsBigradedRealizedProjector
    (ρ : BigradedCorrespondenceRealization C Γ K H ι)
    (q : C) : Prop :=
  ρ.toCorrespondenceRealization.IsRealizedProjector q ∧
    ∀ i : ι,
      ((ρ.piece i ⊓
          LinearMap.range
            (ρ.toCorrespondenceRealization.realizedOperator q)) ⊔
        (ρ.piece i ⊓
          LinearMap.ker
            (ρ.toCorrespondenceRealization.realizedOperator q)) =
        ρ.piece i) ∧
      Disjoint
        (ρ.piece i ⊓
          LinearMap.range
            (ρ.toCorrespondenceRealization.realizedOperator q))
        (ρ.piece i ⊓
          LinearMap.ker
            (ρ.toCorrespondenceRealization.realizedOperator q))

/--
An idempotent selector realizes to a projector compatible with every graded
piece.
-/
theorem isBigradedRealizedProjector
    (ρ : BigradedCorrespondenceRealization C Γ K H ι)
    {q : C} (hq : IsIdempotentElem q) :
    ρ.IsBigradedRealizedProjector q :=
  ⟨ρ.toCorrespondenceRealization.isRealizedProjector hq,
    fun i ↦
      ⟨ρ.piece_projector_decomposition hq i,
        ρ.piece_projector_disjoint hq i⟩⟩

end BigradedCorrespondenceRealization

section FromDefects

variable {C : Type u} {Γ : Type v} {K : Type w} {H : Type z}
variable [CommRing C] [Ring Γ] [CommRing K]
variable [AddCommGroup H] [Module K H]

/--
Vanishing ideal-decomposition defects produce both a scheme-theoretic
idempotent selector and its cohomological projector.
-/
theorem exists_realized_projector_of_defects_vanish
    (ρ : CorrespondenceRealization C Γ K H)
    (J : Ideal C)
    (hDefects :
      overlapDefectIdeal J = ⊥ ∧ contactIdeal J = ⊤) :
    ∃ q : C,
      IsIdempotentElem q ∧
      J = Ideal.span {q} ∧
      IsIdempotentElem (ρ.realizedOperator q) ∧
      IsCompl
        (LinearMap.range (ρ.realizedOperator q))
        (LinearMap.ker (ρ.realizedOperator q)) := by
  obtain ⟨q, hq, hJ⟩ :=
    (defects_vanish_iff_exists_idempotent_generator J).mp hDefects
  exact
    ⟨q, hq, hJ,
      ρ.realizedOperator_isIdempotent hq,
      ρ.realizedOperator_isCompl hq⟩

/--
Collision-specific form of the ideal-to-cohomology projector construction.
-/
theorem exists_collision_realized_projector_of_defects_vanish
    (B : Type u) (A : Type u)
    [CommRing B] [CommRing A] [Algebra B A]
    (ρ :
      CorrespondenceRealization
        (CollisionAlgebra B A) Γ K H)
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    ∃ q : CollisionAlgebra B A,
      IsIdempotentElem q ∧
      collisionObstructionIdeal B A = Ideal.span {q} ∧
      IsIdempotentElem (ρ.realizedOperator q) ∧
      IsCompl
        (LinearMap.range (ρ.realizedOperator q))
        (LinearMap.ker (ρ.realizedOperator q)) :=
  exists_realized_projector_of_defects_vanish
    ρ (collisionObstructionIdeal B A) ⟨hOverlap, hContact⟩

end FromDefects

end

end HodgeConjecture
