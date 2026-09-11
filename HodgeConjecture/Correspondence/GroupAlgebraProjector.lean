import HodgeConjecture.Correspondence.FiniteGroupProjector

/-!
# Projectors transported from rational group algebras

An action by deck transformations gives an algebra map from the rational
group algebra to the finite-etale correspondence algebra.  This module
records the formal consequence needed by the projector layer: every
idempotent of `ℚ[G]`, not only a subgroup average, transports to an
idempotent correspondence and hence to an algebraic lift of any prescribed
operator that it realizes.

The same construction transports a finite ordered family of orthogonal
group-algebra idempotents summing to one to a decomposition of the diagonal.
No semisimplicity or existence theorem for such group-algebra idempotents is
asserted here.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w x

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)
variable {G : Type v} [Group G]

/--
The finite-etale correspondence represented by an arbitrary element of the
rational group algebra of a deck action.
-/
noncomputable def groupAlgebraCorrespondence
    (α : FiniteDeckAction pX G)
    (q : MonoidAlgebra ℚ G) :
    FiniteEtaleFreeAlgebra pX :=
  α.toFiniteEtaleAlgebra pX q

/-- A group basis element transports to the corresponding graph class. -/
@[simp]
theorem groupAlgebraCorrespondence_single
    (α : FiniteDeckAction pX G) (g : G) :
    groupAlgebraCorrespondence pX α
        (MonoidAlgebra.single g 1) =
      finiteEtaleOfScheme
        (graph pX (α g))
        (graph_hasFiniteEtaleLegs pX (α g)) :=
  α.toFiniteEtaleAlgebra_single pX g

/-- Idempotence is preserved by the graph-correspondence algebra map. -/
theorem groupAlgebraCorrespondence_isIdempotent
    (α : FiniteDeckAction pX G)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q) :
    IsIdempotentElem
      (groupAlgebraCorrespondence pX α q) :=
  hq.map (α.toFiniteEtaleAlgebra pX)

section Realization

variable {H : Type w} [AddCommGroup H] [Module ℚ H]

/--
An idempotent of `ℚ[G]` gives an algebraic lift of its induced operator under
any rational action of the finite-etale correspondence algebra.
-/
noncomputable def groupAlgebraProjectorLift
    (α : FiniteDeckAction pX G)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H) :
    AlgebraicProjectorLift ρ
      (ρ.action (groupAlgebraCorrespondence pX α q)) where
  projector := groupAlgebraCorrespondence pX α q
  projector_isIdempotent :=
    groupAlgebraCorrespondence_isIdempotent pX α q hq
  realizes := rfl

/--
Transport an idempotent group-algebra element to a lift of a separately
prescribed cohomological projector.  The realization equality is an explicit
input; the target is not defined circularly from the correspondence.
-/
noncomputable def prescribedGroupAlgebraProjectorLift
    (α : FiniteDeckAction pX G)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H)
    (e : Module.End ℚ H)
    (hrealizes :
      ρ.action (groupAlgebraCorrespondence pX α q) = e) :
    AlgebraicProjectorLift ρ e where
  projector := groupAlgebraCorrespondence pX α q
  projector_isIdempotent :=
    groupAlgebraCorrespondence_isIdempotent pX α q hq
  realizes := hrealizes

@[simp]
theorem prescribedGroupAlgebraProjectorLift_projector
    (α : FiniteDeckAction pX G)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H)
    (e : Module.End ℚ H)
    (hrealizes :
      ρ.action (groupAlgebraCorrespondence pX α q) = e) :
    (prescribedGroupAlgebraProjectorLift
        pX α q hq ρ e hrealizes).projector =
      groupAlgebraCorrespondence pX α q :=
  rfl

/-- The prescribed lift realizes exactly the supplied target operator. -/
theorem prescribedGroupAlgebraProjectorLift_realizes
    (α : FiniteDeckAction pX G)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H)
    (e : Module.End ℚ H)
    (hrealizes :
      ρ.action (groupAlgebraCorrespondence pX α q) = e) :
    ρ.action
        ((prescribedGroupAlgebraProjectorLift
          pX α q hq ρ e hrealizes).projector) =
      e :=
  hrealizes

end Realization

/-!
## Finite decompositions in the group algebra
-/

/--
A finite family of ordered orthogonal idempotents in `ℚ[G]` whose sum is the
unit.  Ordered orthogonality records both multiplication directions in the
possibly noncommutative group algebra.
-/
structure GroupAlgebraDiagonalDecomposition
    (G : Type v) [Group G]
    (ι : Type x) [Fintype ι] where
  projector : ι → MonoidAlgebra ℚ G
  projector_isIdempotent :
    ∀ i, IsIdempotentElem (projector i)
  orthogonal :
    ∀ i j, i ≠ j → projector i * projector j = 0
  sum_eq_one :
    ∑ i, projector i = 1

namespace GroupAlgebraDiagonalDecomposition

variable {ι : Type x} [Fintype ι]

/-- Transport every member of a group-algebra decomposition to a correspondence. -/
noncomputable def correspondence
    (Q : GroupAlgebraDiagonalDecomposition G ι)
    (α : FiniteDeckAction pX G)
    (i : ι) :
    FiniteEtaleFreeAlgebra pX :=
  groupAlgebraCorrespondence pX α (Q.projector i)

/-- Every transported member remains idempotent. -/
theorem correspondence_isIdempotent
    (Q : GroupAlgebraDiagonalDecomposition G ι)
    (α : FiniteDeckAction pX G)
    (i : ι) :
    IsIdempotentElem (Q.correspondence pX α i) :=
  groupAlgebraCorrespondence_isIdempotent
    pX α (Q.projector i) (Q.projector_isIdempotent i)

/-- Ordered orthogonality is preserved by transport. -/
theorem correspondence_orthogonal
    (Q : GroupAlgebraDiagonalDecomposition G ι)
    (α : FiniteDeckAction pX G)
    (i j : ι) (hij : i ≠ j) :
    Q.correspondence pX α i * Q.correspondence pX α j = 0 := by
  change
    α.toFiniteEtaleAlgebra pX (Q.projector i) *
        α.toFiniteEtaleAlgebra pX (Q.projector j) = 0
  rw [← map_mul, Q.orthogonal i j hij, map_zero]

/-- The transported family sums to the diagonal unit. -/
theorem correspondence_sum_eq_diagonal
    (Q : GroupAlgebraDiagonalDecomposition G ι)
    (α : FiniteDeckAction pX G) :
    ∑ i, Q.correspondence pX α i = 1 := by
  change
    ∑ i, α.toFiniteEtaleAlgebra pX (Q.projector i) = 1
  rw [← map_sum, Q.sum_eq_one, map_one]

section Realization

variable {H : Type w} [AddCommGroup H] [Module ℚ H]

/--
The transported family gives a decomposition of the diagonal, with its
cohomological operators defined by the given correspondence action.
-/
noncomputable def toDiagonalDecompositionLift
    (Q : GroupAlgebraDiagonalDecomposition G ι)
    (α : FiniteDeckAction pX G)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H) :
    DiagonalDecompositionLift ρ
      (fun i => ρ.action (Q.correspondence pX α i)) where
  projector := Q.correspondence pX α
  realizes := fun _ => rfl
  projector_isIdempotent :=
    Q.correspondence_isIdempotent pX α
  orthogonal := Q.correspondence_orthogonal pX α
  sum_eq_diagonal := Q.correspondence_sum_eq_diagonal pX α

/--
The same transported family lifts a separately prescribed cohomological
decomposition once each realization equality has been supplied explicitly.
-/
noncomputable def toPrescribedDiagonalDecompositionLift
    (Q : GroupAlgebraDiagonalDecomposition G ι)
    (α : FiniteDeckAction pX G)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H)
    (e : ι → Module.End ℚ H)
    (hrealizes :
      ∀ i, ρ.action (Q.correspondence pX α i) = e i) :
    DiagonalDecompositionLift ρ e where
  projector := Q.correspondence pX α
  realizes := hrealizes
  projector_isIdempotent :=
    Q.correspondence_isIdempotent pX α
  orthogonal := Q.correspondence_orthogonal pX α
  sum_eq_diagonal := Q.correspondence_sum_eq_diagonal pX α

end Realization

end GroupAlgebraDiagonalDecomposition

end SchemeCorrespondence

end

end HodgeConjecture
