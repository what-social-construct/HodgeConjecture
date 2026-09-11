import HodgeConjecture.Boundary.GaloisProjectorExtension
import HodgeConjecture.Boundary.NoetherDifferentRamification
import HodgeConjecture.Realization.Chow.Model

/-!
# Prescribed Chow projectors from the Galois boundary bridge

This module is the realization endpoint of the finite-cover branch.  A
boundary extension produces an algebraic idempotent, but identifying its
action with a *prescribed* cohomological or Hodge-theoretic projector is the
hard final geometric step.  Once that equality is supplied, we obtain

* an algebraic lift of the prescribed projector;
* the complementary algebraic projector;
* a two-term algebraic decomposition of the diagonal;
* the collision-different criterion for existence of the prescribed lift.

The target is never defined to be the action of the correspondence being
constructed, so the result does not hide the Hodge algebraicity question in
a tautological definition.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w t q z r e

namespace SchemeCorrespondence

variable {T X : Scheme.{u}}
variable {G : Type v} [Group G]
variable {pX : X ⟶ T}
variable {α : FiniteDeckAction pX G}
variable {β : Type t} {I : β → Subgroup G}
variable {D : Subgroup G} [Fintype D]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
variable {V : Type z} [AddCommGroup V] [Module ℚ V]

/--
A chosen boundary extension whose compactified Chow class realizes a
prescribed cohomological projector.

The equality of restriction maps prevents an unrelated abstract extension
algebra from being silently identified with the Chow model.  The `realizes`
field is the genuine target-identification theorem required in the Hodge
application.
-/
structure PrescribedChowProjectorLift
    (χ :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra V)
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α β I D genericAlgebra
          χ.genericCycleClass compactifiedAlgebra)
    (e : RationalCohomologicalProjector V) where
  extension : E.Extension
  restriction_compatible :
    E.restriction = χ.restriction
  realizes :
    χ.cohomologicalAction.action
        (E.projector extension) =
      e.operator

namespace PrescribedChowProjectorLift

variable
  {χ :
    RationalChowCorrespondenceModel
      pX genericAlgebra compactifiedAlgebra V}
variable
  {E :
    CompactifiedSubgroupProjectorExtension
      pX α β I D genericAlgebra
        χ.genericCycleClass compactifiedAlgebra}
variable {e : RationalCohomologicalProjector V}

/-- The compactified class restricts to the prescribed subgroup average. -/
theorem projector_restricts_to_subgroupAverage
    (L : PrescribedChowProjectorLift χ E e) :
    χ.restriction (E.projector L.extension) =
      χ.genericCycleClass
        (subgroupAveragingProjector pX D α) := by
  rw [← L.restriction_compatible]
  exact E.projector_restricts L.extension

/-- The chosen Chow correspondence is an algebraic lift of the target. -/
def toAlgebraicProjectorLift
    (L : PrescribedChowProjectorLift χ E e) :
    AlgebraicProjectorLift
      χ.cohomologicalAction e.operator :=
  E.toAlgebraProjectorExtension.projectorLiftOfRealizes
    L.extension χ.cohomologicalAction e.operator L.realizes

@[simp]
theorem toAlgebraicProjectorLift_projector
    (L : PrescribedChowProjectorLift χ E e) :
    L.toAlgebraicProjectorLift.projector =
      E.projector L.extension :=
  rfl

/-- The complementary Chow correspondence lifts `1 - e`. -/
def complementAlgebraicProjectorLift
    (L : PrescribedChowProjectorLift χ E e) :
    AlgebraicProjectorLift
      χ.cohomologicalAction e.complement.operator := by
  simpa using L.toAlgebraicProjectorLift.complement

/--
The prescribed projector and its complement give two orthogonal algebraic
idempotents whose sum is the diagonal class.
-/
def toBoolDiagonalDecomposition
    (L : PrescribedChowProjectorLift χ E e) :
    DiagonalDecompositionLift
      χ.cohomologicalAction
      (complementaryCohomologicalProjectors e.operator) :=
  L.toAlgebraicProjectorLift.toBoolDiagonalDecomposition

/--
If every extension has the prescribed action and the geometric restriction
map is the Chow restriction map, a prescribed lift exists exactly when an
algebraic boundary extension exists.
-/
theorem nonempty_iff_extension_nonempty
    (hRestriction : E.restriction = χ.restriction)
    (hRealizes :
      ∀ x : E.Extension,
        χ.cohomologicalAction.action (E.projector x) =
          e.operator) :
    Nonempty (PrescribedChowProjectorLift χ E e) ↔
      Nonempty E.Extension := by
  constructor
  · rintro ⟨L⟩
    exact ⟨L.extension⟩
  · rintro ⟨x⟩
    exact ⟨{
      extension := x
      restriction_compatible := hRestriction
      realizes := hRealizes x
    }⟩

section GlobalCriterion

variable (R A : Type r)
variable [CommRing R] [CommRing A] [Algebra R A]
variable (P : β → Ideal A)
variable [∀ i : β, (P i).IsPrime]

/--
The finite-cover Chow projector realizing the prescribed cohomological
idempotent exists exactly when the collision different avoids every chosen
height-one boundary prime.

The ramification comparisons, Chow restriction comparison, and target
realization equality are all visible hypotheses.
-/
theorem nonempty_iff_forall_different_not_le
    (hRestriction : E.restriction = χ.restriction)
    (hRealizes :
      ∀ x : E.Extension,
        χ.cohomologicalAction.action (E.projector x) =
          e.operator)
    (hDifferent :
      ∀ i : β,
        CollisionDifferentDetectsRamificationAt
          R A (P i))
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization
          R A G (I i) D (P i)) :
    Nonempty (PrescribedChowProjectorLift χ E e) ↔
      ∀ i : β,
        ¬ collisionNoetherDifferentIdeal R A ≤ P i := by
  rw [nonempty_iff_extension_nonempty hRestriction hRealizes]
  exact
    E.extension_nonempty_iff_forall_different_not_le
      R A P hDifferent hInertia

end GlobalCriterion

end PrescribedChowProjectorLift

section ExplicitBoundaryUnramifiedCorollary

variable (R A : Type r)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.EssFiniteType R A]
variable (P : β → Ideal A)
variable [∀ i : β, (P i).IsPrime]
variable {Extension : Type e}

/--
Different avoidance produces an explicit compactified correspondence
realizing the prescribed operator, conditional on separately visible
cycle-extraction, compactified convolution-idempotence, purity, inertia,
restriction, and realization inputs.

The generic convolution-idempotence of the subgroup average itself is the
formal theorem `subgroupAveragingProjector_isIdempotent`.  The hypothesis
`hConvolutionIdempotent` is the distinct compactified Chow-level input.
-/
theorem exists_prescribed_subgroupAverage_chowProjector_of_different_away
    (deck : FiniteDeckAction pX G)
    (χ :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra V)
    (target : RationalCohomologicalProjector V)
    (chowClassOfExtension :
      Extension → compactifiedAlgebra)
    (hConvolutionIdempotent :
      ∀ x : Extension,
        IsIdempotentElem (chowClassOfExtension x))
    (hRestricts :
      ∀ x : Extension,
        χ.restriction (chowClassOfExtension x) =
          χ.genericCycleClass
            (subgroupAveragingProjector pX D deck))
    (hPurity :
      (∀ i : β,
        InertiaSaturated (I i) D {baseSheet D}) →
          Nonempty Extension)
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization
          R A G (I i) D (P i))
    (hRealizes :
      ∀ x : Extension,
        χ.cohomologicalAction.action
            (chowClassOfExtension x) =
          target.operator)
    (hDifferentAway :
      ∀ i : β,
        ¬ collisionNoetherDifferentIdeal R A ≤ P i) :
    ∃ projector : compactifiedAlgebra,
      IsIdempotentElem projector ∧
      χ.restriction projector =
        χ.genericCycleClass
          (subgroupAveragingProjector pX D deck) ∧
      χ.cohomologicalAction.action projector =
        target.operator := by
  have hSaturated :
      ∀ i : β,
        InertiaSaturated (I i) D {baseSheet D} := by
    intro i
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R A G (I i) D (P i)
        (collisionDifferentDetectsRamificationAt_of_essFiniteType
          R A (P i))
        (hInertia i)).mpr
        (hDifferentAway i)
  obtain ⟨x⟩ := hPurity hSaturated
  exact
    ⟨chowClassOfExtension x,
      hConvolutionIdempotent x,
      hRestricts x,
      hRealizes x⟩

end ExplicitBoundaryUnramifiedCorollary

end SchemeCorrespondence

end

end HodgeConjecture
