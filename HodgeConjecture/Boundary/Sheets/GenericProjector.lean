module

public import HodgeConjecture.Boundary.Sheets.InertiaSaturation

@[expose] public section

/-!
# Generic sheet projectors

After passage to a Galois closure, a generically finite collision
correspondence splits into sheets indexed by `G/H`.  A selection of sheets
therefore has a concrete characteristic-function idempotent in the split
generic algebra

`(G/H → K)`.

This file makes that generic projector explicit.  Its invariance under a
boundary inertia subgroup is equivalent to the selected sheets being
inertia-saturated, hence equivalent to their being a union of inertia
orbits.  This is the algebraic generic-fibre half of the extension principle;
the boundary and compactification modules package the geometric extension
of this idempotent.
-/

set_option autoImplicit false

namespace HodgeConjecture

open scoped Pointwise

noncomputable section

universe u v

variable {G : Type u} [Group G]

/-- The split generic algebra of functions on the `G/H` collision sheets. -/
abbrev GenericSheetAlgebra
    (K : Type v) (H : Subgroup G) :=
  CollisionFoundations.GaloisSheets H → K

/-- The characteristic-function selector of a collection of generic sheets. -/
def genericSheetSelector
    (K : Type v) [Zero K] [One K]
    (H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    GenericSheetAlgebra K H := by
  classical
  exact fun s ↦ if s ∈ selected then 1 else 0

/-- Every characteristic-function sheet selector is an idempotent. -/
theorem genericSheetSelector_isIdempotent
    (K : Type v) [CommRing K]
    (H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    IsIdempotentElem (genericSheetSelector K H selected) := by
  ext s
  by_cases hs : s ∈ selected
  · simp [genericSheetSelector, hs]
  · simp [genericSheetSelector, hs]

/-- Intersecting sheet selections multiplies their generic projectors. -/
theorem genericSheetSelector_inter
    (K : Type v) [CommRing K]
    (H : Subgroup G)
    (selected₁ selected₂ :
      Set (CollisionFoundations.GaloisSheets H)) :
    genericSheetSelector K H (selected₁ ∩ selected₂) =
      genericSheetSelector K H selected₁ *
        genericSheetSelector K H selected₂ := by
  ext s
  by_cases hs₁ : s ∈ selected₁ <;>
    by_cases hs₂ : s ∈ selected₂ <;>
      simp [genericSheetSelector, hs₁, hs₂]

/-- Complementary sheet selections give complementary generic projectors. -/
theorem genericSheetSelector_compl
    (K : Type v) [CommRing K]
    (H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    genericSheetSelector K H selectedᶜ =
      1 - genericSheetSelector K H selected := by
  ext s
  by_cases hs : s ∈ selected
  · simp [genericSheetSelector, hs]
  · simp [genericSheetSelector, hs]

/-- A generic sheet function is invariant under the boundary inertia action. -/
def InertiaInvariantSelector
    (K : Type v)
    (I H : Subgroup G)
    (q : GenericSheetAlgebra K H) : Prop :=
  ∀ i : I, ∀ s, q ((i : G) • s) = q s

/--
Over a nonzero coefficient ring, the characteristic-function projector is
inertia-invariant exactly when its selected sheets are inertia-saturated.
-/
theorem genericSheetSelector_invariant_iff_saturated
    (K : Type v) [CommRing K] [Nontrivial K]
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    InertiaInvariantSelector K I H
        (genericSheetSelector K H selected) ↔
      InertiaSaturated I H selected := by
  classical
  constructor
  · intro hInvariant i s hs
    by_contra his
    have hValue := hInvariant i s
    change
      (if (i : G) • s ∈ selected then (1 : K) else 0) =
        (if s ∈ selected then 1 else 0) at hValue
    rw [if_neg his, if_pos hs] at hValue
    exact zero_ne_one hValue
  · intro hSelected i s
    by_cases hs : s ∈ selected
    · have his : (i : G) • s ∈ selected :=
        hSelected i s hs
      simp [genericSheetSelector, hs, his]
    · have hComplement :
          InertiaSaturated I H selectedᶜ :=
        inertiaSaturated_compl I H selected hSelected
      have his : (i : G) • s ∈ selectedᶜ :=
        hComplement i s hs
      have his' : (i : G) • s ∉ selected := by
        simpa only [Set.mem_compl_iff] using his
      simp [genericSheetSelector, hs, his']

/--
Concrete generic-projector form of the guiding principle:

`the sheet projector is inertia-invariant`

if and only if

`its selected sheets form a union of inertia orbits`.
-/
theorem genericSheetSelector_invariant_iff_union_of_orbits
    (K : Type v) [CommRing K] [Nontrivial K]
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    InertiaInvariantSelector K I H
        (genericSheetSelector K H selected) ↔
      selected =
        ⋃ s : selected,
          MulAction.orbit I
            (s : CollisionFoundations.GaloisSheets H) := by
  rw [genericSheetSelector_invariant_iff_saturated,
    inertiaSaturated_iff_eq_iUnion_orbits]

/--
Subgroup form: the generic projector is inertia-invariant exactly when
inertia is contained in the setwise stabilizer of its selected sheets.
-/
theorem genericSheetSelector_invariant_iff_le_setwiseStabilizer
    (K : Type v) [CommRing K] [Nontrivial K]
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H)) :
    InertiaInvariantSelector K I H
        (genericSheetSelector K H selected) ↔
      I ≤ MulAction.stabilizer G selected := by
  rw [genericSheetSelector_invariant_iff_saturated,
    inertiaSaturated_iff_le_setwiseStabilizer]

/--
For the distinguished diagonal/base sheet, inertia invariance of the concrete
generic projector reduces to the familiar subgroup containment `I ≤ H`.
This is the generic-algebra statement consumed by the height-one boundary
criterion.
-/
theorem genericBaseSheetSelector_invariant_iff_le
    (K : Type v) [CommRing K] [Nontrivial K]
    (I H : Subgroup G) :
    InertiaInvariantSelector K I H
        (genericSheetSelector K H {baseSheet H}) ↔
      I ≤ H := by
  rw [genericSheetSelector_invariant_iff_saturated,
    inertiaSaturated_singleton_baseSheet_iff]

end

end HodgeConjecture
