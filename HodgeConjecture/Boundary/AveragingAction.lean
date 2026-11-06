module

public import HodgeConjecture.Boundary.ExtensionCriterion
public import HodgeConjecture.Boundary.Sheets.GenericProjector
public import HodgeConjecture.Correspondence.FiniteGroupProjector

@[expose] public section

/-!
# Boundary inertia acting through averaging correspondences

The generic sheet selector and the inertia-averaging correspondence are two
different kinds of idempotent:

* `genericSheetSelector` belongs to the pointwise function algebra on the
  generic sheets `G / D`;
* `subgroupAveragingProjector` belongs to the convolution algebra of
  finite-étale graph correspondences.

They should therefore not be identified as elements of one algebra.  This
module relates them through a correspondence action.  The required
compatibility says that the graph of an inertia element acts on functions on
the generic sheets by the contragredient permutation action.

Under that compatibility, the inertia average fixes a selector exactly when
its selected sheets form a union of inertia orbits.  For the distinguished
base sheet, the existing height-one inertia realization and collision
different then identify this fixed-point condition with unramifiedness at the
boundary prime.  A family theorem records the criterion simultaneously over
all height-one boundary components.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w b

namespace BoundaryAveraging

variable {S X : Scheme.{u}} (pX : X ⟶ S)
variable {G : Type v} [Group G]

/--
Compatibility between finite-étale graph correspondences and the
contragredient permutation action on the generic sheets.

The inverse is essential: it makes the left action of the convolution
algebra agree with the usual action on functions.
-/
structure SheetActionCompatibility
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I D : Subgroup G)
    (ρ :
      RationalCorrespondenceAction
        (SchemeCorrespondence.FiniteEtaleFreeAlgebra pX)
        (GenericSheetAlgebra ℚ D)) : Prop where
  basis_action :
    ∀ (i : I) (q : GenericSheetAlgebra ℚ D)
      (s : CollisionFoundations.GaloisSheets D),
      ρ.action
          ((α.restrict pX I).toFiniteEtaleAlgebra pX
            (MonoidAlgebra.single i 1)) q s =
        q (((i : G)⁻¹) • s)

/--
The normalized graph average of a finite boundary inertia subgroup.

Normalization and Galois-closure data naturally provide `Finite I`; the
underlying finite sum uses the noncomputable `Fintype.ofFinite I`.
-/
noncomputable def inertiaAveragingProjector
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I : Subgroup G) [Finite I] :
    SchemeCorrespondence.FiniteEtaleFreeAlgebra pX := by
  letI : Fintype I := Fintype.ofFinite I
  exact
    SchemeCorrespondence.subgroupAveragingProjector
      pX I α

/-- The inertia-averaging correspondence is a convolution idempotent. -/
theorem inertiaAveragingProjector_isIdempotent
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I : Subgroup G) [Finite I] :
    IsIdempotentElem (inertiaAveragingProjector pX α I) := by
  letI : Fintype I := Fintype.ofFinite I
  simpa [inertiaAveragingProjector] using
    SchemeCorrespondence.subgroupAveragingProjector_isIdempotent
      pX I α

/--
The inertia average fixes a generic sheet function exactly when that function
is invariant under inertia.
-/
theorem inertiaAveragingProjector_fixes_iff_invariant
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I D : Subgroup G) [Finite I]
    (ρ :
      RationalCorrespondenceAction
        (SchemeCorrespondence.FiniteEtaleFreeAlgebra pX)
        (GenericSheetAlgebra ℚ D))
    (C : SheetActionCompatibility pX α I D ρ)
    (q : GenericSheetAlgebra ℚ D) :
    ρ.action (inertiaAveragingProjector pX α I) q = q ↔
      InertiaInvariantSelector ℚ I D q := by
  letI : Fintype I := Fintype.ofFinite I
  let φ :=
    (α.restrict pX I).toFiniteEtaleAlgebra pX
  let e := SchemeCorrespondence.finiteGroupAverage I
  change ρ.action (φ e) q = q ↔ _
  constructor
  · intro hfix i s
    have hoperator (j : I) :
        ρ.action (φ (MonoidAlgebra.single j 1))
            (ρ.action (φ e) q) =
          ρ.action (φ e) q := by
      calc
        ρ.action (φ (MonoidAlgebra.single j 1))
              (ρ.action (φ e) q) =
            (ρ.action (φ (MonoidAlgebra.single j 1)) *
              ρ.action (φ e)) q := by
                rw [Module.End.mul_apply]
        _ = ρ.action
              (φ (MonoidAlgebra.single j 1) * φ e) q := by
                rw [map_mul]
        _ = ρ.action
              (φ (MonoidAlgebra.single j 1 * e)) q := by
                rw [map_mul φ]
        _ = ρ.action (φ e) q := by
              rw [SchemeCorrespondence.single_mul_finiteGroupAverage]
    have h := hoperator i⁻¹
    rw [hfix] at h
    have hs := congrFun h s
    rw [C.basis_action] at hs
    simpa using hs
  · intro hInvariant
    ext s
    change
      ρ.action
          (φ
            ((Fintype.card I : ℚ)⁻¹ •
              ∑ i : I, MonoidAlgebra.single i 1)) q s =
        q s
    simp only [map_smul, map_sum, LinearMap.smul_apply,
      LinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply, φ]
    rw [Finset.sum_congr rfl fun i _ ↦ C.basis_action i q s]
    have hEach :
        ∀ i : I, q (((i : G)⁻¹) • s) = q s := by
      intro i
      simpa using hInvariant i⁻¹ s
    simp_rw [hEach]
    simp

/--
The boundary-inertia form of the orbit criterion: an averaging
correspondence fixes a characteristic-function selector exactly when the
selected sheets form a union of inertia orbits.
-/
theorem inertiaAveragingProjector_fixes_selector_iff_union_of_orbits
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I D : Subgroup G) [Finite I]
    (ρ :
      RationalCorrespondenceAction
        (SchemeCorrespondence.FiniteEtaleFreeAlgebra pX)
        (GenericSheetAlgebra ℚ D))
    (C : SheetActionCompatibility pX α I D ρ)
    (selected : Set (CollisionFoundations.GaloisSheets D)) :
    ρ.action (inertiaAveragingProjector pX α I)
        (genericSheetSelector ℚ D selected) =
          genericSheetSelector ℚ D selected ↔
      selected =
        ⋃ s : selected,
          MulAction.orbit I
            (s : CollisionFoundations.GaloisSheets D) := by
  rw [inertiaAveragingProjector_fixes_iff_invariant
    pX α I D ρ C]
  exact
    genericSheetSelector_invariant_iff_union_of_orbits
      ℚ I D selected

/--
At a height-one boundary prime, the inertia average fixes the distinguished
base-sheet selector exactly when the collision different avoids that prime.

The hypotheses `hDifferent` and `hInertia` are the local étaleness bridge:
they identify containment of the collision different with ramification, and
ramification with nontrivial relative inertia on the base sheet.
-/
theorem inertiaAveragingProjector_fixes_baseSelector_iff_different_not_le
    {R T : Type w}
    [CommRing R] [CommRing T] [Algebra R T]
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I D : Subgroup G) [Finite I]
    (P : Ideal T) [P.IsPrime]
    (ρ :
      RationalCorrespondenceAction
        (SchemeCorrespondence.FiniteEtaleFreeAlgebra pX)
        (GenericSheetAlgebra ℚ D))
    (C : SheetActionCompatibility pX α I D ρ)
    (hDifferent :
      CollisionDifferentDetectsRamificationAt R T P)
    (hInertia :
      HeightOneInertiaRealization R T G I D P) :
    ρ.action (inertiaAveragingProjector pX α I)
        (genericSheetSelector ℚ D {baseSheet D}) =
      genericSheetSelector ℚ D {baseSheet D} ↔
        ¬ collisionNoetherDifferentIdeal R T ≤ P := by
  rw [inertiaAveragingProjector_fixes_iff_invariant
    pX α I D ρ C]
  rw [genericSheetSelector_invariant_iff_saturated]
  exact
    baseSheet_projector_extends_iff_different_not_le
      R T G I D P hDifferent hInertia

/--
The height-one criterion simultaneously over every indexed boundary
component.  A separate purity or gluing theorem can consume its left-hand
side to construct a global extension.
-/
theorem forall_inertiaAveragingProjectors_fix_baseSelector_iff
    {R T : Type w}
    [CommRing R] [CommRing T] [Algebra R T]
    {β : Type b}
    (α : SchemeCorrespondence.FiniteDeckAction pX G)
    (I : β → Subgroup G) [∀ i : β, Finite (I i)]
    (D : Subgroup G)
    (P : β → Ideal T) [∀ i : β, (P i).IsPrime]
    (ρ :
      RationalCorrespondenceAction
        (SchemeCorrespondence.FiniteEtaleFreeAlgebra pX)
        (GenericSheetAlgebra ℚ D))
    (C : ∀ i : β, SheetActionCompatibility pX α (I i) D ρ)
    (hDifferent :
      ∀ i : β,
        CollisionDifferentDetectsRamificationAt R T (P i))
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization R T G (I i) D (P i)) :
    (∀ i : β,
      ρ.action (inertiaAveragingProjector pX α (I i))
          (genericSheetSelector ℚ D {baseSheet D}) =
        genericSheetSelector ℚ D {baseSheet D}) ↔
      ∀ i : β,
        ¬ collisionNoetherDifferentIdeal R T ≤ P i := by
  constructor
  · intro hFix i
    exact
      (inertiaAveragingProjector_fixes_baseSelector_iff_different_not_le
        pX α (I i) D (P i) ρ (C i)
        (hDifferent i) (hInertia i)).mp
          (hFix i)
  · intro hDifferentAway i
    exact
      (inertiaAveragingProjector_fixes_baseSelector_iff_different_not_le
        pX α (I i) D (P i) ρ (C i)
        (hDifferent i) (hInertia i)).mpr
          (hDifferentAway i)

end BoundaryAveraging

end

end HodgeConjecture
