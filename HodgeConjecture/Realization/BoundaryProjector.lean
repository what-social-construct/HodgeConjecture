import HodgeConjecture.Boundary.ExtensionCriterion
import HodgeConjecture.Realization.CohomologicalProjector

/-!
# Boundary inertia and realized projectors

This file packages the final boundary-to-realization bridge.

`BoundarySelectorExtension` is the geometric input still required after the
height-one inertia calculation.  Its extension witnesses carry actual
idempotent selectors, and such witnesses exist exactly when the selected
generic sheets are a union of inertia orbits.

Combining this input with a local criterion identifying the collision
different with ramification gives:

`a realized boundary projector exists`

if and only if

`the collision different is not contained in the boundary prime`.

The bigraded form says the same projector splits every preserved `(p,q)`-piece.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v w z t s

/--
Geometric extension data for a generic sheet selector at a boundary inertia
group.

The equivalence in the final field is the precise input expressing that an
idempotent selector extends exactly when its selected sheets form a union of
inertia orbits.
-/
structure BoundarySelectorExtension
    (C : Type u) [CommRing C]
    (G : Type v) [Group G]
    (I D : Subgroup G) where
  Extension : Type t
  selector : Extension → C
  selector_isIdempotent :
    ∀ e : Extension, IsIdempotentElem (selector e)
  extension_nonempty_iff_inertiaSaturated :
    Nonempty Extension ↔ InertiaSaturated I D {baseSheet D}

section Criterion

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

variable (G : Type v) [Group G]
variable (I D : Subgroup G)
variable (P : Ideal S) [P.IsPrime]

variable {C : Type w} {Γ : Type z} {K : Type s} {V : Type t}
variable [CommRing C] [Ring Γ] [CommRing K]
variable [AddCommGroup V] [Module K V]

/--
Boundary inertia controls existence of the realized cohomological projector:
it exists exactly when the collision different avoids the boundary prime.
-/
theorem exists_boundary_realizedProjector_iff_different_not_le
    (hDifferent : CollisionDifferentDetectsRamificationAt R S P)
    (hInertia : HeightOneInertiaRealization R S G I D P)
    (E : BoundarySelectorExtension C G I D)
    (ρ : CorrespondenceRealization C Γ K V) :
    (∃ e : E.Extension,
      ρ.IsRealizedProjector (E.selector e)) ↔
      ¬ collisionNoetherDifferentIdeal R S ≤ P := by
  constructor
  · rintro ⟨e, _⟩
    have hSaturated : InertiaSaturated I D {baseSheet D} :=
      E.extension_nonempty_iff_inertiaSaturated.mp ⟨e⟩
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R S G I D P hDifferent hInertia).mp hSaturated
  · intro hDifferentAway
    have hSaturated : InertiaSaturated I D {baseSheet D} :=
      (baseSheet_projector_extends_iff_different_not_le
        R S G I D P hDifferent hInertia).mpr hDifferentAway
    obtain ⟨e⟩ :=
      E.extension_nonempty_iff_inertiaSaturated.mpr hSaturated
    exact
      ⟨e, ρ.isRealizedProjector (E.selector_isIdempotent e)⟩

variable {ι : Type*}

/--
Hodge-style bigraded form: an inertia-compatible boundary extension produces
a projector that preserves and splits every chosen `(p,q)`-piece, and such a
projector exists exactly away from the collision different.  This statement
does not quantify over rational Hodge classes and is not the rational Hodge
conjecture target.
-/
theorem exists_boundary_bigradedProjector_iff_different_not_le
    (hDifferent : CollisionDifferentDetectsRamificationAt R S P)
    (hInertia : HeightOneInertiaRealization R S G I D P)
    (E : BoundarySelectorExtension C G I D)
    (ρ : BigradedCorrespondenceRealization C Γ K V ι) :
    (∃ e : E.Extension,
      ρ.IsBigradedRealizedProjector (E.selector e)) ↔
      ¬ collisionNoetherDifferentIdeal R S ≤ P := by
  constructor
  · rintro ⟨e, _⟩
    have hSaturated : InertiaSaturated I D {baseSheet D} :=
      E.extension_nonempty_iff_inertiaSaturated.mp ⟨e⟩
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R S G I D P hDifferent hInertia).mp hSaturated
  · intro hDifferentAway
    have hSaturated : InertiaSaturated I D {baseSheet D} :=
      (baseSheet_projector_extends_iff_different_not_le
        R S G I D P hDifferent hInertia).mpr hDifferentAway
    obtain ⟨e⟩ :=
      E.extension_nonempty_iff_inertiaSaturated.mpr hSaturated
    exact
      ⟨e,
        ρ.isBigradedRealizedProjector
          (E.selector_isIdempotent e)⟩

end Criterion

end

end HodgeConjecture
