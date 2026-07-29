import HodgeConjecture.BoundaryProjector

/-!
# Compactification, purity, and all boundary components

The one-prime theorem in `BoundaryProjector` describes extension across a
single height-one boundary component.  A normal compactification generally
has a family of such components.

`CompactificationSelectorExtension` packages the purity input:

* a global extension witness carries an idempotent selector;
* a global extension exists exactly when the generic selector extends across
  every height-one boundary component;
* height-one extension is expressed by inertia saturation.

Under the local comparison of differents and the inertia realization at every
boundary prime, this gives a global realized projector exactly when the
collision different avoids every boundary prime.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v w z t s b

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/--
Purity/compactification input for a family of height-one boundary inertia
groups.

In applications, `Extension` is the type of global extensions of the generic
sheet selector to the chosen normal compactification.
-/
structure CompactificationSelectorExtension
    (C : Type u) [CommRing C]
    (G : Type v) [Group G]
    (β : Type b)
    (I : β → Subgroup G)
    (D : Subgroup G) where
  Extension : Type t
  selector : Extension → C
  selector_isIdempotent :
    ∀ e : Extension, IsIdempotentElem (selector e)
  extension_nonempty_iff_forall_inertiaSaturated :
    Nonempty Extension ↔
      ∀ i : β, InertiaSaturated (I i) D {baseSheet D}

section Criterion

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsDedekindDomain R] [IsDedekindDomain S]
variable [NoZeroSMulDivisors R S] [Module.Finite R S]
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

variable (G : Type v) [Group G]
variable (β : Type b)
variable (I : β → Subgroup G)
variable (D : Subgroup G)
variable (P : β → Ideal S)
variable [∀ i : β, (P i).IsPrime]

/--
The generic selector is invariant under every boundary inertia group exactly
when the collision different avoids every boundary prime.
-/
theorem forall_inertiaSaturated_iff_forall_different_not_le
    (hDifferent : CollisionDifferentComparison R S)
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization R S G (I i) D (P i)) :
    (∀ i : β, InertiaSaturated (I i) D {baseSheet D}) ↔
      ∀ i : β, ¬ collisionNoetherDifferentIdeal R S ≤ P i := by
  constructor
  · intro hSaturated i
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R S G (I i) D (P i) hDifferent (hInertia i)).mp
        (hSaturated i)
  · intro hDifferentAway i
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R S G (I i) D (P i) hDifferent (hInertia i)).mpr
        (hDifferentAway i)

variable {C : Type w} {Γ : Type z} {K : Type s} {V : Type t}
variable [CommRing C] [Ring Γ] [CommRing K]
variable [AddCommGroup V] [Module K V]

/--
Global compactification criterion for a realized cohomological projector.
-/
theorem exists_compactification_realizedProjector_iff_forall_different_not_le
    (hDifferent : CollisionDifferentComparison R S)
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization R S G (I i) D (P i))
    (E : CompactificationSelectorExtension C G β I D)
    (ρ : CorrespondenceRealization C Γ K V) :
    (∃ e : E.Extension,
      ρ.IsRealizedProjector (E.selector e)) ↔
      ∀ i : β, ¬ collisionNoetherDifferentIdeal R S ≤ P i := by
  constructor
  · rintro ⟨e, _⟩
    have hSaturated :
        ∀ i : β, InertiaSaturated (I i) D {baseSheet D} :=
      E.extension_nonempty_iff_forall_inertiaSaturated.mp ⟨e⟩
    exact
      (forall_inertiaSaturated_iff_forall_different_not_le
        R S G β I D P hDifferent hInertia).mp hSaturated
  · intro hDifferentAway
    have hSaturated :
        ∀ i : β, InertiaSaturated (I i) D {baseSheet D} :=
      (forall_inertiaSaturated_iff_forall_different_not_le
        R S G β I D P hDifferent hInertia).mpr hDifferentAway
    obtain ⟨e⟩ :=
      E.extension_nonempty_iff_forall_inertiaSaturated.mpr hSaturated
    exact
      ⟨e, ρ.isRealizedProjector (E.selector_isIdempotent e)⟩

variable {ι : Type*}

/--
Global Hodge-style criterion: the compactified selector realizes to a
projector splitting every preserved bigraded piece exactly when the collision
different avoids all height-one boundary primes.
-/
theorem exists_compactification_bigradedProjector_iff_forall_different_not_le
    (hDifferent : CollisionDifferentComparison R S)
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization R S G (I i) D (P i))
    (E : CompactificationSelectorExtension C G β I D)
    (ρ : BigradedCorrespondenceRealization C Γ K V ι) :
    (∃ e : E.Extension,
      ρ.IsBigradedRealizedProjector (E.selector e)) ↔
      ∀ i : β, ¬ collisionNoetherDifferentIdeal R S ≤ P i := by
  constructor
  · rintro ⟨e, _⟩
    have hSaturated :
        ∀ i : β, InertiaSaturated (I i) D {baseSheet D} :=
      E.extension_nonempty_iff_forall_inertiaSaturated.mp ⟨e⟩
    exact
      (forall_inertiaSaturated_iff_forall_different_not_le
        R S G β I D P hDifferent hInertia).mp hSaturated
  · intro hDifferentAway
    have hSaturated :
        ∀ i : β, InertiaSaturated (I i) D {baseSheet D} :=
      (forall_inertiaSaturated_iff_forall_different_not_le
        R S G β I D P hDifferent hInertia).mpr hDifferentAway
    obtain ⟨e⟩ :=
      E.extension_nonempty_iff_forall_inertiaSaturated.mpr hSaturated
    exact
      ⟨e,
        ρ.isBigradedRealizedProjector
          (E.selector_isIdempotent e)⟩

end Criterion

end

end HodgeConjecture
