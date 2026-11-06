module

public import HodgeConjecture.Boundary.Sheets.DecompositionSheets
public import Mathlib.Algebra.Pointwise.Stabilizer

@[expose] public section

/-!
# Inertia-saturated sheet selections

The generic idempotent associated with a set of collision sheets is the
characteristic function of that set.  At a boundary valuation, the elementary
extension condition is that the selected sheets are closed under the inertia
action—equivalently, that they form a union of inertia orbits.

This file packages that condition independently of any particular
compactification.  The valuation-theoretic groups are locally owned in
`HodgeConjecture.Boundary.Normalization.ValuationInertia`; realizing their
centers on a compactification is the geometric normalization-diagram layer.
-/

set_option autoImplicit false

namespace HodgeConjecture

open scoped Pointwise

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

/--
The complement of an inertia-saturated sheet selection is again
inertia-saturated.  Thus saturation is a condition on the associated
partition, not only on one of its two parts.
-/
theorem inertiaSaturated_compl
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H))
    (hSelected : InertiaSaturated I H selected) :
    InertiaSaturated I H selectedᶜ := by
  intro i s hs his
  have hBack :
      ((i⁻¹ : I) : G) • ((i : G) • s) ∈ selected :=
    hSelected i⁻¹ ((i : G) • s) his
  exact hs (by simpa using hBack)

/--
An inertia-saturated selection is literally a union of inertia orbits.

The union is indexed by the selected sheets themselves.  The reverse
inclusion is automatic, while saturation says that the full orbit of each
selected sheet remains selected.
-/
theorem inertiaSaturated_iff_eq_iUnion_orbits
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    InertiaSaturated I H selected ↔
      selected =
        ⋃ s : selected,
          MulAction.orbit I
            (s : CollisionFoundations.GaloisSheets H) := by
  constructor
  · intro hSelected
    apply Set.Subset.antisymm
    · intro s hs
      exact Set.mem_iUnion.mpr
        ⟨⟨s, hs⟩, MulAction.mem_orbit_self s⟩
    · intro s hs
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hs
      obtain ⟨i, rfl⟩ := MulAction.mem_orbit_iff.mp ht
      exact hSelected i t t.property
  · intro hUnion i s hs
    rw [hUnion]
    exact Set.mem_iUnion.mpr
      ⟨⟨s, hs⟩, MulAction.mem_orbit s i⟩

/--
Equivalently, the inertia subgroup lies in the setwise stabilizer of the
selected sheets.  This identifies the precise subgroup obstruction for an
arbitrary sheet projector.
-/
theorem inertiaSaturated_iff_le_setwiseStabilizer
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    InertiaSaturated I H selected ↔
      I ≤ MulAction.stabilizer G selected := by
  constructor
  · intro hSelected g hg
    rw [MulAction.mem_stabilizer_set]
    intro s
    constructor
    · intro hgs
      have hBack :=
        hSelected
          (⟨g⁻¹, I.inv_mem hg⟩ : I)
          (g • s) hgs
      simpa [smul_smul] using hBack
    · intro hs
      exact hSelected ⟨g, hg⟩ s hs
  · intro hStabilizer i s hs
    have hi := hStabilizer i.property
    rw [MulAction.mem_stabilizer_set] at hi
    exact (hi s).mpr hs

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
