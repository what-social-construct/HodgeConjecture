import HodgeConjecture.Correspondence.Graph
import HodgeConjecture.Correspondence.ProjectorLift

/-!
# Finite-group averaging projectors

A finite group acting by deck transformations on `X/S` gives graph
correspondences with finite étale legs.  The normalized sum of the elements
of the group algebra is an idempotent, and the graph algebra map transports
it to a genuine convolution idempotent in the finite-étale correspondence
algebra.

This is the first concrete source of `AlgebraicProjectorLift`s in the
correspondence layer.  It applies to the structured, finite-monodromy branch
of the project; it does not assert that every Hodge projector is generated
by a finite group action.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- An action of a group by automorphisms of `X` over `S`. -/
abbrev FiniteDeckAction
    (G : Type v) [Group G] :=
  G →* DeckTransformation pX

namespace FiniteDeckAction

variable {G : Type v} [Group G]

/-- Restrict a deck action to a subgroup. -/
def restrict
    (α : FiniteDeckAction pX G)
    (H : Subgroup G) :
    FiniteDeckAction pX H :=
  α.comp H.subtype

@[simp]
theorem restrict_apply
    (α : FiniteDeckAction pX G)
    (H : Subgroup G) (h : H) :
    α.restrict pX H h = α h :=
  rfl

/--
The multiplicative map from an acting group to finite-étale graph
correspondence classes.
-/
noncomputable def toClassMonoidHom
    (α : FiniteDeckAction pX G) :
    G →* FiniteEtaleClass pX :=
  (graphClassMonoidHom pX).comp α

/-- The algebra map induced by the action on rational group algebras. -/
noncomputable def toDeckGroupAlgebra
    (α : FiniteDeckAction pX G) :
    MonoidAlgebra ℚ G →ₐ[ℚ] DeckGroupAlgebra pX :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ α

/--
The graph-correspondence algebra map induced by the action.

It factors through the group algebra of all deck transformations.
-/
noncomputable def toFiniteEtaleAlgebra
    (α : FiniteDeckAction pX G) :
    MonoidAlgebra ℚ G →ₐ[ℚ] FiniteEtaleFreeAlgebra pX :=
  (graphAlgebraMap pX).comp (α.toDeckGroupAlgebra pX)

@[simp]
theorem toDeckGroupAlgebra_single
    (α : FiniteDeckAction pX G) (g : G) :
    α.toDeckGroupAlgebra pX
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (α g) 1 := by
  simp [toDeckGroupAlgebra]

@[simp]
theorem toFiniteEtaleAlgebra_single
    (α : FiniteDeckAction pX G) (g : G) :
    α.toFiniteEtaleAlgebra pX
        (MonoidAlgebra.single g 1) =
      finiteEtaleOfScheme
        (graph pX (α g))
        (graph_hasFiniteEtaleLegs pX (α g)) := by
  simp [toFiniteEtaleAlgebra]

end FiniteDeckAction

section Average

variable (G : Type v) [Group G] [Fintype G]

/-- The unnormalized sum of all basis elements in the rational group algebra. -/
noncomputable def finiteGroupSum :
    MonoidAlgebra ℚ G :=
  ∑ g : G, MonoidAlgebra.single g 1

/-- The normalized averaging element `|G|⁻¹ ∑ g` in `ℚ[G]`. -/
noncomputable def finiteGroupAverage :
    MonoidAlgebra ℚ G :=
  (Fintype.card G : ℚ)⁻¹ • finiteGroupSum G

/-- The group sum is invariant under left multiplication by a basis element. -/
@[simp]
theorem single_mul_finiteGroupSum
    (g : G) :
    MonoidAlgebra.single g 1 * finiteGroupSum G =
      finiteGroupSum G := by
  simp only [finiteGroupSum, Finset.mul_sum,
    MonoidAlgebra.single_mul_single, one_mul]
  set f : G → MonoidAlgebra ℚ G :=
    fun x => MonoidAlgebra.single x 1
  change (∑ x : G, f (g * x)) = ∑ x : G, f x
  rw [Function.Bijective.sum_comp
    (Group.mulLeft_bijective g) _]

/-- The group sum is invariant under right multiplication by a basis element. -/
@[simp]
theorem finiteGroupSum_mul_single
    (g : G) :
    finiteGroupSum G * MonoidAlgebra.single g 1 =
      finiteGroupSum G := by
  simp only [finiteGroupSum, Finset.sum_mul,
    MonoidAlgebra.single_mul_single, one_mul]
  set f : G → MonoidAlgebra ℚ G :=
    fun x => MonoidAlgebra.single x 1
  change (∑ x : G, f (x * g)) = ∑ x : G, f x
  rw [Function.Bijective.sum_comp
    (Group.mulRight_bijective g) _]

/-- The normalized average is left invariant. -/
@[simp]
theorem single_mul_finiteGroupAverage
    (g : G) :
    MonoidAlgebra.single g 1 * finiteGroupAverage G =
      finiteGroupAverage G := by
  rw [finiteGroupAverage, Algebra.mul_smul_comm,
    single_mul_finiteGroupSum]

/-- The normalized average is right invariant. -/
@[simp]
theorem finiteGroupAverage_mul_single
    (g : G) :
    finiteGroupAverage G * MonoidAlgebra.single g 1 =
      finiteGroupAverage G := by
  rw [finiteGroupAverage, Algebra.smul_mul_assoc,
    finiteGroupSum_mul_single]

/-- The normalized finite-group average is an idempotent of `ℚ[G]`. -/
@[simp]
theorem finiteGroupAverage_mul_self :
    finiteGroupAverage G * finiteGroupAverage G =
      finiteGroupAverage G := by
  change
    ((Fintype.card G : ℚ)⁻¹ • finiteGroupSum G) *
        finiteGroupAverage G =
      finiteGroupAverage G
  rw [Algebra.smul_mul_assoc]
  simp only [finiteGroupSum, Finset.sum_mul,
    single_mul_finiteGroupAverage,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  simp

/-- Predicate form of idempotence of the normalized average. -/
theorem finiteGroupAverage_isIdempotent :
    IsIdempotentElem (finiteGroupAverage G) :=
  finiteGroupAverage_mul_self G

end Average

section CorrespondenceProjector

variable {G : Type v} [Group G] [Fintype G]

/--
The image of the rational group-algebra average in the finite-étale
correspondence algebra.
-/
noncomputable def averagingProjector
    (α : FiniteDeckAction pX G) :
    FiniteEtaleFreeAlgebra pX :=
  α.toFiniteEtaleAlgebra pX (finiteGroupAverage G)

/-- The averaging projector is the normalized sum of the graph classes. -/
theorem averagingProjector_eq_sum
    (α : FiniteDeckAction pX G) :
    averagingProjector pX α =
      (Fintype.card G : ℚ)⁻¹ •
        ∑ g : G,
          finiteEtaleOfScheme
            (graph pX (α g))
            (graph_hasFiniteEtaleLegs pX (α g)) := by
  simp [averagingProjector, finiteGroupAverage,
    finiteGroupSum]

/-- The graph-correspondence average is a convolution idempotent. -/
theorem averagingProjector_isIdempotent
    (α : FiniteDeckAction pX G) :
    IsIdempotentElem (averagingProjector pX α) :=
  (finiteGroupAverage_isIdempotent G).map
    (α.toFiniteEtaleAlgebra pX)

/-- Every acting graph fixes the averaging projector on the left. -/
@[simp]
theorem action_single_mul_averagingProjector
    (α : FiniteDeckAction pX G) (g : G) :
    α.toFiniteEtaleAlgebra pX
          (MonoidAlgebra.single g 1) *
        averagingProjector pX α =
      averagingProjector pX α := by
  rw [averagingProjector, ← map_mul,
    single_mul_finiteGroupAverage]

/-- Every acting graph fixes the averaging projector on the right. -/
@[simp]
theorem averagingProjector_mul_action_single
    (α : FiniteDeckAction pX G) (g : G) :
    averagingProjector pX α *
        α.toFiniteEtaleAlgebra pX
          (MonoidAlgebra.single g 1) =
      averagingProjector pX α := by
  rw [averagingProjector, ← map_mul,
    finiteGroupAverage_mul_single]

/-- The complementary finite-group correspondence projector. -/
noncomputable def complementaryAveragingProjector
    (α : FiniteDeckAction pX G) :
    FiniteEtaleFreeAlgebra pX :=
  1 - averagingProjector pX α

/-- The complement of the averaging projector is idempotent. -/
theorem complementaryAveragingProjector_isIdempotent
    (α : FiniteDeckAction pX G) :
    IsIdempotentElem
      (complementaryAveragingProjector pX α) := by
  exact (averagingProjector_isIdempotent pX α).one_sub

end CorrespondenceProjector

section SubgroupProjector

variable {G : Type v} [Group G]
variable (H : Subgroup G) [Fintype H]

/--
The averaging projector of a finite subgroup of deck transformations.

For a Galois action this is the correspondence projector onto the
`H`-invariant part.  Keeping the subgroup explicit is what later allows
boundary inertia to test the containment `I ≤ H`.
-/
noncomputable def subgroupAveragingProjector
    (α : FiniteDeckAction pX G) :
    FiniteEtaleFreeAlgebra pX :=
  averagingProjector pX (α.restrict pX H)

/-- A finite-subgroup graph average is a convolution idempotent. -/
theorem subgroupAveragingProjector_isIdempotent
    (α : FiniteDeckAction pX G) :
    IsIdempotentElem
      (subgroupAveragingProjector pX H α) :=
  averagingProjector_isIdempotent
    pX (α.restrict pX H)

/-- The subgroup projector is the normalized sum of its graph sheets. -/
theorem subgroupAveragingProjector_eq_sum
    (α : FiniteDeckAction pX G) :
    subgroupAveragingProjector pX H α =
      (Fintype.card H : ℚ)⁻¹ •
        ∑ h : H,
          finiteEtaleOfScheme
            (graph pX (α h))
            (graph_hasFiniteEtaleLegs pX (α h)) := by
  simpa [subgroupAveragingProjector] using
    averagingProjector_eq_sum
      pX (α.restrict pX H)

end SubgroupProjector

section Realization

variable {G : Type v} [Group G] [Fintype G]
variable {H : Type w} [AddCommGroup H] [Module ℚ H]

/--
The finite-group averaging correspondence as an algebraic lift of its
operator under any rational correspondence action.
-/
noncomputable def averagingProjectorLift
    (α : FiniteDeckAction pX G)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H) :
    AlgebraicProjectorLift ρ
      (ρ.action (averagingProjector pX α)) where
  projector := averagingProjector pX α
  projector_isIdempotent :=
    averagingProjector_isIdempotent pX α
  realizes := rfl

/-- The complementary averaging correspondence also gives a projector lift. -/
noncomputable def complementaryAveragingProjectorLift
    (α : FiniteDeckAction pX G)
    (ρ :
      RationalCorrespondenceAction
        (FiniteEtaleFreeAlgebra pX) H) :
    AlgebraicProjectorLift ρ
      (1 - ρ.action (averagingProjector pX α)) :=
  (averagingProjectorLift pX α ρ).complement

end Realization

end SchemeCorrespondence

end

end HodgeConjecture
