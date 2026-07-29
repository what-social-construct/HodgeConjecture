import HodgeConjecture.Foundations.DecompositionSheets

/-!
# Inertia-saturated sheet selections

The generic idempotent associated with a set of collision sheets is the
characteristic function of that set.  At a boundary valuation, the elementary
extension condition is that the selected sheets are closed under the inertia
action—equivalently, that they form a union of inertia orbits.

This file packages that condition independently of any particular
compactification.  The valuation-theoretic and geometric realization remains
in the reusable `CollisionIdeals` normalization-diagram modules.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- A selected set of `G/H`-sheets is closed under the inertia action. -/
def InertiaSaturated
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) : Prop :=
  ∀ i : I, ∀ s, s ∈ selected → (i : G) • s ∈ selected

/-- Inertia crosses the partition when it moves a selected sheet outside. -/
def InertiaCrosses
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) : Prop :=
  ∃ i : I, ∃ s, s ∈ selected ∧ (i : G) • s ∉ selected

/-- Saturation is exactly the absence of an inertia crossing. -/
theorem inertiaSaturated_iff_not_crosses
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    InertiaSaturated I H selected ↔
      ¬ InertiaCrosses I H selected := by
  constructor
  · intro h ⟨i, s, hs, his⟩
    exact his (h i s hs)
  · intro h i s hs
    by_contra his
    exact h ⟨i, s, hs, his⟩

/-- The distinguished sheet of the intermediate extension. -/
abbrev baseSheet (H : Subgroup G) :
    CollisionFoundations.GaloisSheets H :=
  ((1 : G) : CollisionFoundations.GaloisSheets H)

/--
The distinguished singleton sheet is inertia-saturated exactly when inertia
is contained in its stabilizer `H`.
-/
theorem inertiaSaturated_singleton_baseSheet_iff
    (I H : Subgroup G) :
    InertiaSaturated I H {baseSheet H} ↔ I ≤ H := by
  rw [← CollisionFoundations.inertiaInvisibleAt_baseSheet_iff I H]
  constructor
  · intro h i
    have hi :=
      h i (baseSheet H) (Set.mem_singleton (baseSheet H))
    simpa using hi
  · intro h i s hs
    rw [Set.mem_singleton_iff] at hs ⊢
    subst s
    exact h i

/--
Index one on the base sheet is equivalent to extension of its singleton
selector across the corresponding inertia action.
-/
theorem inertiaIndexAtBaseSheet_eq_one_iff_saturated
    (I H : Subgroup G) :
    CollisionFoundations.inertiaIndexAtSheet I H (baseSheet H) = 1 ↔
      InertiaSaturated I H {baseSheet H} := by
  rw [CollisionFoundations.inertiaIndexAtSheet_eq_one_iff,
    CollisionFoundations.inertiaInvisibleAt_baseSheet_iff,
    inertiaSaturated_singleton_baseSheet_iff]

end

end HodgeConjecture
