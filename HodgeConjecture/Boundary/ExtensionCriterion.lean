import HodgeConjecture.Boundary.HeightOneDifferent
import HodgeConjecture.Boundary.Sheets.InertiaSaturation

/-!
# Boundary inertia as the projector-extension obstruction

This file joins the two algebraically different ends of the construction:

1. the collision contact quotient and its height-one different;
2. the Galois-closure sheet action and its inertia saturation condition.

The bridge is deliberately packaged as `HeightOneInertiaRealization`.  It is
the valuation-theoretic input asserting that ramification at the chosen prime
is detected by nontrivial relative inertia on the distinguished sheet.  Under
that input and the local comparison of differents, containment of the
collision different in the boundary prime is exactly failure of the generic
singleton selector to extend across inertia.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

section Criterion

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

variable (G : Type v) [Group G]
variable (I H : Subgroup G)
variable (P : Ideal S) [P.IsPrime]

/--
The valuation/Galois-closure input identifying ramification at `P` with
nontrivial relative inertia on the distinguished `G/H` sheet.

In concrete normalization diagrams this is supplied by the inertia and
geometric-ramification-index realization, together with the appropriate
residue-separability hypotheses.
-/
structure HeightOneInertiaRealization : Prop where
  ramified_iff_inertiaIndex_ne_one :
    (¬ Algebra.IsUnramifiedAt R P) ↔
      CollisionFoundations.inertiaIndexAtSheet I H (baseSheet H) ≠ 1

/--
The collision different meets the boundary prime exactly when inertia
prevents extension of the distinguished singleton sheet selector.
-/
theorem collisionDifferent_le_prime_iff_not_inertiaSaturated
    (hDifferent : CollisionDifferentDetectsRamificationAt R S P)
    (hInertia : HeightOneInertiaRealization R S G I H P) :
    collisionNoetherDifferentIdeal R S ≤ P ↔
      ¬ InertiaSaturated I H {baseSheet H} := by
  calc
    collisionNoetherDifferentIdeal R S ≤ P ↔
        ¬ Algebra.IsUnramifiedAt R P :=
      hDifferent
    _ ↔ CollisionFoundations.inertiaIndexAtSheet I H (baseSheet H) ≠ 1 :=
      hInertia.ramified_iff_inertiaIndex_ne_one
    _ ↔ ¬ InertiaSaturated I H {baseSheet H} :=
      not_congr (inertiaIndexAtBaseSheet_eq_one_iff_saturated I H)

/--
Boxed projector-extension form: the distinguished generic selector extends
across the chosen boundary inertia exactly when the collision different is
not contained in the boundary prime.
-/
theorem baseSheet_projector_extends_iff_different_not_le
    (hDifferent : CollisionDifferentDetectsRamificationAt R S P)
    (hInertia : HeightOneInertiaRealization R S G I H P) :
    InertiaSaturated I H {baseSheet H} ↔
      ¬ collisionNoetherDifferentIdeal R S ≤ P := by
  constructor
  · intro hSaturated hDifferentAtP
    exact
      (collisionDifferent_le_prime_iff_not_inertiaSaturated
        R S G I H P hDifferent hInertia).mp hDifferentAtP hSaturated
  · intro hDifferentAway
    by_contra hSaturated
    exact hDifferentAway
      ((collisionDifferent_le_prime_iff_not_inertiaSaturated
        R S G I H P hDifferent hInertia).mpr hSaturated)

end Criterion

end

end HodgeConjecture
