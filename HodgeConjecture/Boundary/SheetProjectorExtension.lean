import HodgeConjecture.Boundary.Normalization.ExtensionBridge
import HodgeConjecture.Boundary.Normalization.ConjugateBoundary

/-!
# Extension of selected-sheet projectors

This module separates the three inputs in the extension problem for a
generic characteristic-function projector:

* inertia saturation is the general local condition on a selected set of
  sheets;
* a selection-dependent height-one realization is required before that
  condition can be identified with avoidance of the collision different;
* a purity/gluing hypothesis promotes all height-one conditions to an actual
  global idempotent whose generic restriction is the prescribed selector.

For the distinguished singleton sheet, the existing height-one inertia
realization supplies the selection-dependent input automatically.  For an
arbitrary selected set, ramification need not destroy saturation: inertia
may permute sheets entirely within the selected set.  Consequently the
different criteria below retain the required local realization explicitly.

The final normalization wrappers connect this interface both to the existing
formal-unramifiedness/no-hidden-inertia machinery and to the canonical
fixed--moving conjugate-boundary separation route.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w t b

variable {G : Type u} [Group G]

/--
The local input identifying ramification at one height-one prime with
failure of inertia saturation for a specified set of sheets.

This is deliberately an explicit, selection-dependent hypothesis.  For a
general selection, ramification can coexist with saturation when inertia
only permutes sheets inside the selected part and its complement.
-/
structure SelectedSheetHeightOneInertiaRealization
    (R S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (I H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H))
    (P : Ideal S) [P.IsPrime] : Prop where
  ramified_iff_not_saturated :
    (¬ Algebra.IsUnramifiedAt R P) ↔
      ¬ InertiaSaturated I H selected

namespace SelectedSheetHeightOneInertiaRealization

variable
  {R S : Type v}
  [CommRing R] [CommRing S] [Algebra R S]
  {I H : Subgroup G}
  {P : Ideal S} [P.IsPrime]

/--
The existing base-sheet inertia realization supplies the selected-set
realization for the distinguished singleton.
-/
def ofBaseSheet
    (h : HeightOneInertiaRealization R S G I H P) :
    SelectedSheetHeightOneInertiaRealization
      R S I H {baseSheet H} P where
  ramified_iff_not_saturated := by
    exact h.ramified_iff_inertiaIndex_ne_one.trans
      (not_congr
        (inertiaIndexAtBaseSheet_eq_one_iff_saturated I H))

end SelectedSheetHeightOneInertiaRealization

section LocalCriterion

variable
  (R S : Type v)
  [CommRing R] [CommRing S] [Algebra R S]
  (I H : Subgroup G)
  (selected : Set (CollisionFoundations.GaloisSheets H))
  (P : Ideal S) [P.IsPrime]

/--
At one height-one prime, saturation of the selected partition is equivalent
to avoidance of the collision different, under the two explicit local
realization hypotheses.
-/
theorem selectedSheets_extend_iff_different_not_le
    (hDifferent : CollisionDifferentDetectsRamificationAt R S P)
    (hInertia :
      SelectedSheetHeightOneInertiaRealization
        R S I H selected P) :
    InertiaSaturated I H selected ↔
      ¬ collisionNoetherDifferentIdeal R S ≤ P := by
  constructor
  · intro hSaturated hDifferentAtP
    exact
      hInertia.ramified_iff_not_saturated.mp
        (hDifferent.mp hDifferentAtP) hSaturated
  · intro hDifferentAway
    by_contra hSaturated
    exact hDifferentAway
      (hDifferent.mpr
        (hInertia.ramified_iff_not_saturated.mpr
          hSaturated))

/--
The concrete generic characteristic-function selector is invariant at the
height-one prime exactly when the collision different avoids that prime,
provided the local different and selected-sheet realizations are available.
-/
theorem genericSheetSelector_invariant_iff_different_not_le
    (K : Type w) [CommRing K] [Nontrivial K]
    (hDifferent : CollisionDifferentDetectsRamificationAt R S P)
    (hInertia :
      SelectedSheetHeightOneInertiaRealization
        R S I H selected P) :
    InertiaInvariantSelector K I H
        (genericSheetSelector K H selected) ↔
      ¬ collisionNoetherDifferentIdeal R S ≤ P := by
  rw [genericSheetSelector_invariant_iff_saturated]
  exact selectedSheets_extend_iff_different_not_le
    R S I H selected P hDifferent hInertia

end LocalCriterion

section FamilyCriterion

variable
  (R S : Type v)
  [CommRing R] [CommRing S] [Algebra R S]
  (β : Type b)
  (I : β → Subgroup G)
  (H : Subgroup G)
  (selected : Set (CollisionFoundations.GaloisSheets H))
  (P : β → Ideal S)
  [∀ i, (P i).IsPrime]

/-- Local invariance at every indexed height-one boundary component. -/
def InvariantAtEveryBoundary
    (K : Type w) [CommRing K] : Prop :=
  ∀ i : β,
    InertiaInvariantSelector K (I i) H
      (genericSheetSelector K H selected)

/--
The family form of the conditional collision-different criterion.
-/
theorem invariantAtEveryBoundary_iff_forall_different_not_le
    (K : Type w) [CommRing K] [Nontrivial K]
    (hDifferent :
      ∀ i, CollisionDifferentDetectsRamificationAt R S (P i))
    (hInertia :
      ∀ i,
        SelectedSheetHeightOneInertiaRealization
          R S (I i) H selected (P i)) :
    InvariantAtEveryBoundary β I H selected K ↔
      ∀ i, ¬ collisionNoetherDifferentIdeal R S ≤ P i := by
  constructor
  · intro hInvariant i
    exact
      (genericSheetSelector_invariant_iff_different_not_le
        R S (I i) H selected (P i) K
        (hDifferent i) (hInertia i)).mp
        (hInvariant i)
  · intro hAway i
    exact
      (genericSheetSelector_invariant_iff_different_not_le
        R S (I i) H selected (P i) K
        (hDifferent i) (hInertia i)).mpr
        (hAway i)

end FamilyCriterion

/--
Actual global idempotents whose generic restriction is the prescribed
characteristic-function selector.
-/
def GlobalSheetSelectorExtension
    (C : Type t) [CommRing C]
    (K : Type w) [CommRing K]
    (H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H))
    (genericRestriction :
      C →+* GenericSheetAlgebra K H) :=
  {q : C //
    IsIdempotentElem q ∧
      genericRestriction q =
        genericSheetSelector K H selected}

/--
The compactification/purity input: an actual global idempotent extension
exists exactly when the selector is saturated for every height-one boundary
inertia group.

This structure records the Hartogs/purity/gluing step rather than deriving it
from the local inertia calculation.
-/
structure GaloisProjectorExtensionPurity
    (C : Type t) [CommRing C]
    (K : Type w) [CommRing K]
    (β : Type b)
    (I : β → Subgroup G)
    (H : Subgroup G)
    (selected : Set (CollisionFoundations.GaloisSheets H))
    (genericRestriction :
      C →+* GenericSheetAlgebra K H) : Prop where
  extension_nonempty_iff_forall_inertiaSaturated :
    Nonempty
        (GlobalSheetSelectorExtension
          C K H selected genericRestriction) ↔
      ∀ i : β, InertiaSaturated (I i) H selected

section GlobalCriterion

variable
  (R S : Type v)
  [CommRing R] [CommRing S] [Algebra R S]
  (β : Type b)
  (I : β → Subgroup G)
  (H : Subgroup G)
  (selected : Set (CollisionFoundations.GaloisSheets H))
  (P : β → Ideal S)
  [∀ i, (P i).IsPrime]
  (C : Type t) [CommRing C]
  (K : Type w) [CommRing K] [Nontrivial K]
  (genericRestriction :
    C →+* GenericSheetAlgebra K H)

/--
Under the explicit purity/gluing input, actual global extension is equivalent
to inertia invariance at every height-one boundary component.  This is the
general selected-set statement and does not require a collision-different
realization.
-/
theorem globalSheetSelectorExtension_nonempty_iff_invariantAtEveryBoundary
    (hPurity :
      GaloisProjectorExtensionPurity
        C K β I H selected genericRestriction) :
    Nonempty
        (GlobalSheetSelectorExtension
          C K H selected genericRestriction) ↔
      InvariantAtEveryBoundary β I H selected K := by
  rw [hPurity.extension_nonempty_iff_forall_inertiaSaturated]
  constructor
  · intro hSaturated i
    exact
      (genericSheetSelector_invariant_iff_saturated
        K (I i) H selected).mpr
        (hSaturated i)
  · intro hInvariant i
    exact
      (genericSheetSelector_invariant_iff_saturated
        K (I i) H selected).mp
        (hInvariant i)

omit [Nontrivial K] in
/--
Under the explicit local realizations and the purity/gluing input, an actual
global selector extension exists exactly when the collision different avoids
every indexed boundary prime.
-/
theorem globalSheetSelectorExtension_nonempty_iff_forall_different_not_le
    (hDifferent :
      ∀ i, CollisionDifferentDetectsRamificationAt R S (P i))
    (hInertia :
      ∀ i,
        SelectedSheetHeightOneInertiaRealization
          R S (I i) H selected (P i))
    (hPurity :
      GaloisProjectorExtensionPurity
        C K β I H selected genericRestriction) :
    Nonempty
        (GlobalSheetSelectorExtension
          C K H selected genericRestriction) ↔
      ∀ i, ¬ collisionNoetherDifferentIdeal R S ≤ P i := by
  rw [hPurity.extension_nonempty_iff_forall_inertiaSaturated]
  constructor
  · intro hSaturated i
    exact
      (selectedSheets_extend_iff_different_not_le
        R S (I i) H selected (P i)
        (hDifferent i) (hInertia i)).mp
        (hSaturated i)
  · intro hAway i
    exact
      (selectedSheets_extend_iff_different_not_le
        R S (I i) H selected (P i)
        (hDifferent i) (hInertia i)).mpr
        (hAway i)

end GlobalCriterion

end

end HodgeConjecture

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u w t

namespace NormalizationInertia

section DiagramBridge

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable
  {C : NormalizedCover
    (B := B) (K := K) (L := L) (N := N) U j}

namespace Diagram

omit [IsFractionRing B K] in
/--
The existing normalization bridge, uniformly over all packaged ramified
height-one points.
-/
theorem forall_genericBaseSheetProjector_invariant_iff_forall_different_not_le
    (A : Type w) [CommRing A] [Nontrivial A]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (hUnramified :
      ∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
        Algebra.IsUnramifiedAt B
            (D.centerPrime E (D.baseClass E)) ↔
          D.geometricRamificationIndex E (D.baseClass E) = 1)
    (hDifferent :
      ∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
        CollisionDifferentDetectsRamificationAt
          B (IntermediateNormalizationRing (B := B) (L := L))
          (D.centerPrime E (D.baseClass E))) :
    (∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
      InertiaInvariantSelector A
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        (genericSheetSelector A
          C.normalClosure.intermediateFixingSubgroup
          {baseSheet
            C.normalClosure.intermediateFixingSubgroup})) ↔
      ∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
        ¬ collisionNoetherDifferentIdeal
            B (IntermediateNormalizationRing (B := B) (L := L)) ≤
          D.centerPrime E (D.baseClass E) := by
  constructor
  · intro hInvariant E
    exact
      (D.genericBaseSheetProjector_invariant_iff_different_not_le
        A R E (hUnramified E) (hDifferent E)).mp
        (hInvariant E)
  · intro hAway E
    exact
      (D.genericBaseSheetProjector_invariant_iff_different_not_le
        A R E (hUnramified E) (hDifferent E)).mpr
        (hAway E)

omit [IsFractionRing B K] in
/--
Formal unramifiedness plus no hidden inertia eliminates the entire index
type of ramified height-one points; therefore every selected partition
satisfies the codimension-one saturation condition.
-/
theorem forall_inertiaSaturated_of_formallyUnramified
    [PerfectField K] [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (hFormal :
      FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia)
    (selected :
      Set
        (CollisionFoundations.GaloisSheets
          C.normalClosure.intermediateFixingSubgroup)) :
    ∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
      InertiaSaturated
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        selected := by
  have hBoundary : D.RamifiedConjugateCentersInBoundary :=
    D.ramifiedConjugateCentersInBoundary R hFormal
  have hEmpty :
      IsEmpty
        (RamifiedCodimensionOnePoint (B := B) (N := N)) :=
    D.ramifiedCodimensionOnePoint_isEmpty
      hBoundary hNoHidden
  intro E
  exact isEmptyElim E

omit [IsFractionRing B K] in
/--
The canonical fixed--moving boundary separation route eliminates the same
ramified height-one index type, without passing through the separate
`NoHiddenInertia` predicate.  The center and ramification comparisons remain
visible in `ConjugateBoundaryData`, while separation itself is an explicit
geometric hypothesis.
-/
theorem forall_inertiaSaturated_of_conjugateBoundarySeparation
    [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateBoundaryData)
    (hFormal :
      FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hSeparation : ConjugateBoundarySeparation C)
    (selected :
      Set
        (CollisionFoundations.GaloisSheets
          C.normalClosure.intermediateFixingSubgroup)) :
    ∀ E : RamifiedCodimensionOnePoint (B := B) (N := N),
      InertiaSaturated
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        selected := by
  have hEmpty :
      IsEmpty
        (RamifiedCodimensionOnePoint (B := B) (N := N)) :=
    D.ramifiedCodimensionOnePoint_isEmpty_of_conjugateBoundarySeparation
      R hFormal hSeparation
  intro E
  exact isEmptyElim E

omit [IsFractionRing B K] in
/--
Combining the normalization theorem with the explicit selector-purity input
produces an actual global idempotent extension.
-/
theorem globalSheetSelectorExtension_of_formallyUnramified
    [PerfectField K] [IsNoetherianRing B]
    (A : Type t) [CommRing A]
    (Λ : Type w) [CommRing Λ]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (hFormal :
      FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia)
    (selected :
      Set
        (CollisionFoundations.GaloisSheets
          C.normalClosure.intermediateFixingSubgroup))
    (genericRestriction :
      A →+*
        GenericSheetAlgebra Λ
          C.normalClosure.intermediateFixingSubgroup)
    (hPurity :
      GaloisProjectorExtensionPurity
        A Λ
        (RamifiedCodimensionOnePoint (B := B) (N := N))
        (fun E =>
          CollisionFoundations.inertiaGroupAt K
            (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        selected genericRestriction) :
    Nonempty
      (GlobalSheetSelectorExtension
        A Λ C.normalClosure.intermediateFixingSubgroup
        selected genericRestriction) := by
  apply
    hPurity.extension_nonempty_iff_forall_inertiaSaturated.mpr
  exact
    D.forall_inertiaSaturated_of_formallyUnramified
      R hFormal hNoHidden selected

omit [IsFractionRing B K] in
/--
Fixed--moving boundary separation supplies the local side of the global
selector-extension criterion.  The actual gluing step remains precisely the
supplied `GaloisProjectorExtensionPurity` input.
-/
theorem globalSheetSelectorExtension_of_conjugateBoundarySeparation
    [IsNoetherianRing B]
    (A : Type t) [CommRing A]
    (Λ : Type w) [CommRing Λ]
    (D : Diagram C)
    (R : D.ConjugateBoundaryData)
    (hFormal :
      FormallyUnramified
        (j ≫ intermediateNormalizationToBase (B := B) (L := L)))
    (hSeparation : ConjugateBoundarySeparation C)
    (selected :
      Set
        (CollisionFoundations.GaloisSheets
          C.normalClosure.intermediateFixingSubgroup))
    (genericRestriction :
      A →+*
        GenericSheetAlgebra Λ
          C.normalClosure.intermediateFixingSubgroup)
    (hPurity :
      GaloisProjectorExtensionPurity
        A Λ
        (RamifiedCodimensionOnePoint (B := B) (N := N))
        (fun E =>
          CollisionFoundations.inertiaGroupAt K
            (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        selected genericRestriction) :
    Nonempty
      (GlobalSheetSelectorExtension
        A Λ C.normalClosure.intermediateFixingSubgroup
        selected genericRestriction) := by
  apply hPurity.extension_nonempty_iff_forall_inertiaSaturated.mpr
  exact
    D.forall_inertiaSaturated_of_conjugateBoundarySeparation
      R hFormal hSeparation selected

end Diagram

end DiagramBridge

end NormalizationInertia

end

end HodgeConjecture
