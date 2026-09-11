import HodgeConjecture.Boundary.ExtensionCriterion
import HodgeConjecture.Boundary.NoetherDifferentRamification
import HodgeConjecture.Boundary.Normalization.InertiaDiagram
import HodgeConjecture.Boundary.Sheets.GenericProjector

/-!
# From normalization inertia to projector extension

This module is the junction between the geometric normalization diagram and
the abstract boundary-extension criterion.

At the distinguished double-coset center, the diagram identifies the
double-coset inertia index with the stabilizer index of the base `G/H` sheet.
After supplying the local equivalence between unramifiedness and geometric
ramification index one, this produces `HeightOneInertiaRealization`.

For the extension-existence direction, the full equivalence is unnecessary.
Finite normalization and the collision Noether-different theorem give
different avoidance implies unramifiedness; Mathlib then gives ramification
index one, and the diagram's explicit index comparison gives inertia
saturation.  The reverse direction is deliberately not asserted here.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v

namespace NormalizationInertia

section Bridge

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
The normalization diagram realizes ramification by relative inertia at its
distinguished center once the local `unramified ↔ index one` theorem is
supplied.
-/
theorem heightOneInertiaRealizationAtBaseClass
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hUnramified :
      Algebra.IsUnramifiedAt B
          (D.centerPrime E (D.baseClass E)) ↔
        D.geometricRamificationIndex E (D.baseClass E) = 1) :
    HeightOneInertiaRealization
      B (IntermediateNormalizationRing (B := B) (L := L))
      C.normalClosure.galoisGroup
      (CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing)
      C.normalClosure.intermediateFixingSubgroup
      (D.centerPrime E (D.baseClass E)) := by
  constructor
  rw [not_congr hUnramified,
    ← R.inertiaIndex_eq_geometricRamificationIndex,
    D.inertiaIndex_baseClass_eq_inertiaIndexAtSheet]

omit [IsFractionRing B K] in
/--
Different avoidance implies saturation of the distinguished sheet without a
full `unramified ↔ ramification index one` hypothesis.

This is the one-way normalization argument used in the Jacobian-collision
development: unramifiedness implies geometric ramification index one, while
`ConjugateRamificationRealization` supplies the explicit comparison with the
group-theoretic inertia index.  No converse is used or claimed.
-/
theorem baseClass_inertiaSaturated_of_different_not_le
    [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hAway :
      ¬ collisionNoetherDifferentIdeal
          B (IntermediateNormalizationRing (B := B) (L := L)) ≤
        D.centerPrime E (D.baseClass E)) :
    InertiaSaturated
      (CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing)
      C.normalClosure.intermediateFixingSubgroup
      {baseSheet C.normalClosure.intermediateFixingSubgroup} := by
  letI :
      Module.Finite B
        (IntermediateNormalizationRing (B := B) (L := L)) :=
    C.finiteIntermediateModel
  letI :
      IsNoetherianRing
        (IntermediateNormalizationRing (B := B) (L := L)) :=
    IsNoetherianRing.of_finite B
      (IntermediateNormalizationRing (B := B) (L := L))
  have hUnramified :
      Algebra.IsUnramifiedAt B
        (D.centerPrime E (D.baseClass E)) := by
    by_contra hRamified
    exact hAway
      ((collisionDifferentDetectsRamificationAt_of_essFiniteType
        B (IntermediateNormalizationRing (B := B) (L := L))
        (D.centerPrime E (D.baseClass E))).mpr hRamified)
  letI :
      Algebra.IsUnramifiedAt B
        (D.centerPrime E (D.baseClass E)) :=
    hUnramified
  have hGeometric :
      D.geometricRamificationIndex E (D.baseClass E) = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
      (R.center_ne_bot E (D.baseClass E))
  apply
    (inertiaIndexAtBaseSheet_eq_one_iff_saturated
      (CollisionFoundations.inertiaGroupAt K
        (D.valuationAt E).valuationRing)
      C.normalClosure.intermediateFixingSubgroup).mp
  rw [← D.inertiaIndex_baseClass_eq_inertiaIndexAtSheet,
    R.inertiaIndex_eq_geometricRamificationIndex]
  exact hGeometric

omit [IsFractionRing B K] in
/--
Normalization-diagram form of the boundary extension principle: the
distinguished generic sheet is inertia-saturated exactly when the collision
different avoids its center.
-/
theorem baseClass_projector_extends_iff_different_not_le
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hUnramified :
      Algebra.IsUnramifiedAt B
          (D.centerPrime E (D.baseClass E)) ↔
        D.geometricRamificationIndex E (D.baseClass E) = 1)
    (hDifferent :
      CollisionDifferentDetectsRamificationAt
        B (IntermediateNormalizationRing (B := B) (L := L))
        (D.centerPrime E (D.baseClass E))) :
    InertiaSaturated
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        {baseSheet C.normalClosure.intermediateFixingSubgroup} ↔
      ¬ collisionNoetherDifferentIdeal
          B (IntermediateNormalizationRing (B := B) (L := L)) ≤
        D.centerPrime E (D.baseClass E) :=
  baseSheet_projector_extends_iff_different_not_le
    B (IntermediateNormalizationRing (B := B) (L := L))
    C.normalClosure.galoisGroup
    (CollisionFoundations.inertiaGroupAt K
      (D.valuationAt E).valuationRing)
    C.normalClosure.intermediateFixingSubgroup
    (D.centerPrime E (D.baseClass E))
    hDifferent
    (D.heightOneInertiaRealizationAtBaseClass R E hUnramified)

omit [IsFractionRing B K] in
/--
Concrete generic-algebra form: the characteristic-function projector selecting
the base sheet is inertia-invariant exactly when the collision different
avoids the corresponding center.
-/
theorem genericBaseSheetProjector_invariant_iff_different_not_le
    (A : Type v) [CommRing A] [Nontrivial A]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (E : RamifiedCodimensionOnePoint (B := B) (N := N))
    (hUnramified :
      Algebra.IsUnramifiedAt B
          (D.centerPrime E (D.baseClass E)) ↔
        D.geometricRamificationIndex E (D.baseClass E) = 1)
    (hDifferent :
      CollisionDifferentDetectsRamificationAt
        B (IntermediateNormalizationRing (B := B) (L := L))
        (D.centerPrime E (D.baseClass E))) :
    InertiaInvariantSelector A
        (CollisionFoundations.inertiaGroupAt K
          (D.valuationAt E).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        (genericSheetSelector A
          C.normalClosure.intermediateFixingSubgroup
          {baseSheet C.normalClosure.intermediateFixingSubgroup}) ↔
      ¬ collisionNoetherDifferentIdeal
          B (IntermediateNormalizationRing (B := B) (L := L)) ≤
        D.centerPrime E (D.baseClass E) := by
  rw [genericSheetSelector_invariant_iff_saturated]
  exact
    D.baseClass_projector_extends_iff_different_not_le
      R E hUnramified hDifferent

end Diagram

end Bridge

end NormalizationInertia

end

end HodgeConjecture
