import HodgeConjecture.Boundary.ExtensionCriterion
import HodgeConjecture.Boundary.SheetProjectorExtension
import HodgeConjecture.Correspondence.GaloisCollision
import HodgeConjecture.LinearAlgebra.UniversalIdempotentAlgebra

/-!
# Boundary extension of Galois subgroup projectors

A finite subgroup `H` of a deck group produces the convolution idempotent

`e_H = |H|⁻¹ ∑ h : H, Γ_h`.

The associated intermediate sheet is the base coset in `G/H`.  At a
height-one boundary component with inertia group `I`, that sheet is stable
exactly when `I ≤ H`.  Equivalently, its singleton is inertia-saturated.

This file connects those two statements without identifying a generic
correspondence algebra with its compactified counterpart.  The geometric
input is an explicit extension package containing

* a compactified correspondence algebra;
* a restriction map to the generic finite-étale correspondence algebra;
* compactified idempotents restricting to `e_H`;
* the purity statement that such extensions exist exactly when the base
  sheet is saturated under the relevant boundary inertia groups.

The resulting extended element gives an `AlgebraicProjectorLift` under any
rational correspondence action.  The collision-different criterion then
turns the inertia condition into a height-one, or global codimension-one,
existence theorem.

The full-group average is the special case `H = ⊤`.  More generally,
subgroup averages model the cover-generated projectors attached to
intermediate quotients.  No claim is made that arbitrary Hodge projectors
arise in this way.

The equivalence between inertia saturation and extension of the
*correspondence* projector is an explicit purity/comparison input below.
Inertia saturation alone directly controls the clopen sheet selector; it
does not by itself prove that a graph average extends idempotently in a Chow
correspondence algebra.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v w t r z q

/--
Algebraic extension data for one generic rational correspondence projector.

`genericAlgebra` is the algebra on the generic locus and
`compactifiedAlgebra` is the algebra in which an extension is sought.
-/
structure AlgebraProjectorExtension
    (genericAlgebra : Type u)
    (compactifiedAlgebra : Type v)
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
    (genericProjector : genericAlgebra) where
  genericProjector_isIdempotent :
    IsIdempotentElem genericProjector
  restriction :
    compactifiedAlgebra →ₐ[ℚ] genericAlgebra
  Extension : Type w
  projector : Extension → compactifiedAlgebra
  projector_isIdempotent :
    ∀ e, IsIdempotentElem (projector e)
  projector_restricts :
    ∀ e, restriction (projector e) = genericProjector

namespace AlgebraProjectorExtension

variable
  {genericAlgebra : Type u}
  {compactifiedAlgebra : Type v}
  [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
  [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
  {genericProjector : genericAlgebra}

/-- The canonical map from the universal one-idempotent algebra to the
generic algebra, carrying `(1, 0)` to the generic projector. -/
noncomputable def genericIdempotentMap
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector) :
    UniversalIdempotentAlgebra ℚ →ₐ[ℚ] genericAlgebra :=
  UniversalIdempotentAlgebra.mapOfIdempotent
    genericProjector E.genericProjector_isIdempotent

/-- The canonical map from the universal one-idempotent algebra to the
compactified algebra, carrying `(1, 0)` to the chosen extension projector. -/
noncomputable def compactifiedIdempotentMap
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    (e : E.Extension) :
    UniversalIdempotentAlgebra ℚ →ₐ[ℚ] compactifiedAlgebra :=
  UniversalIdempotentAlgebra.mapOfIdempotent
    (E.projector e) (E.projector_isIdempotent e)

@[simp]
theorem genericIdempotentMap_selector
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector) :
    E.genericIdempotentMap
        (UniversalIdempotentAlgebra.selector (R := ℚ)) =
      genericProjector :=
  UniversalIdempotentAlgebra.mapOfIdempotent_selector _ _

@[simp]
theorem compactifiedIdempotentMap_selector
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    (e : E.Extension) :
    E.compactifiedIdempotentMap e
        (UniversalIdempotentAlgebra.selector (R := ℚ)) =
      E.projector e :=
  UniversalIdempotentAlgebra.mapOfIdempotent_selector _ _

/-- Restriction commutes with the canonical one-idempotent presentations.
This is the compactification square at the smallest algebra that records the
projector and its complement. -/
theorem restriction_comp_compactifiedIdempotentMap
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    (e : E.Extension) :
    E.restriction.comp (E.compactifiedIdempotentMap e) =
      E.genericIdempotentMap := by
  unfold compactifiedIdempotentMap genericIdempotentMap
  rw [UniversalIdempotentAlgebra.comp_mapOfIdempotent]
  simp only [E.projector_restricts e]

/--
The complementary compactified projector extends the complementary generic
projector through the same restriction map.
-/
noncomputable def complement
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector) :
    AlgebraProjectorExtension
      genericAlgebra compactifiedAlgebra
      (1 - genericProjector) where
  genericProjector_isIdempotent :=
    E.genericProjector_isIdempotent.one_sub
  restriction := E.restriction
  Extension := E.Extension
  projector := fun e ↦ 1 - E.projector e
  projector_isIdempotent := fun e ↦
    (E.projector_isIdempotent e).one_sub
  projector_restricts := by
    intro e
    rw [map_sub, map_one, E.projector_restricts]

/--
An extended correspondence idempotent gives an algebraic lift of its action
on rational cohomology.
-/
noncomputable def projectorLift
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    (e : E.Extension)
    {V : Type t} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V) :
    AlgebraicProjectorLift ρ
      (ρ.action (E.projector e)) where
  projector := E.projector e
  projector_isIdempotent :=
    E.projector_isIdempotent e
  realizes := rfl

/--
If the extended correspondence is known to act as a prescribed
cohomological projector, it gives a lift of that specific target.

Unlike `projectorLift`, the realization equality here is genuine geometric
input rather than definitional.
-/
noncomputable def projectorLiftOfRealizes
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    (e : E.Extension)
    {V : Type t} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V)
    (target : Module.End ℚ V)
    (hRealizes :
      ρ.action (E.projector e) = target) :
    AlgebraicProjectorLift ρ target where
  projector := E.projector e
  projector_isIdempotent :=
    E.projector_isIdempotent e
  realizes := hRealizes

/-- The type of an extension witness together with its projector lift. -/
abbrev LiftWitness
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    {V : Type t} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V) :=
  Σ e : E.Extension,
    AlgebraicProjectorLift ρ
      (ρ.action (E.projector e))

/-- A projector lift exists exactly when an algebraic extension exists. -/
theorem liftWitness_nonempty_iff
    (E :
      AlgebraProjectorExtension
        genericAlgebra compactifiedAlgebra genericProjector)
    {V : Type t} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V) :
    Nonempty (E.LiftWitness ρ) ↔
      Nonempty E.Extension := by
  constructor
  · rintro ⟨⟨e, _⟩⟩
    exact ⟨e⟩
  · rintro ⟨e⟩
    exact ⟨⟨e, E.projectorLift e ρ⟩⟩

end AlgebraProjectorExtension

namespace SchemeCorrespondence

variable {T X : Scheme.{u}} (pX : X ⟶ T)
variable {G : Type v} [Group G]

/--
Local boundary-extension data for the subgroup averaging projector `e_H`.

The final field is the geometric height-one extension theorem.  It is not
deduced merely from group theory: a concrete normalization or
compactification must supply it.
-/
structure BoundarySubgroupProjectorExtension
    (α : FiniteDeckAction pX G)
    (I H : Subgroup G) [Fintype H]
    (genericAlgebra : Type q)
    [Ring genericAlgebra]
    [Algebra ℚ genericAlgebra]
    (genericRealization :
      FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
        genericAlgebra)
    (compactifiedAlgebra : Type w)
    [Ring compactifiedAlgebra]
    [Algebra ℚ compactifiedAlgebra]
    extends
      AlgebraProjectorExtension
        genericAlgebra
        compactifiedAlgebra
        (genericRealization
          (subgroupAveragingProjector pX H α)) where
  extension_nonempty_iff_inertiaSaturated :
    Nonempty Extension ↔
      InertiaSaturated I H {baseSheet H}

/--
Global compactification data for a subgroup averaging projector.

An extension exists exactly when the base `G/H` sheet is saturated for every
height-one boundary inertia group in the family `I`.
-/
structure CompactifiedSubgroupProjectorExtension
    (α : FiniteDeckAction pX G)
    (β : Type t)
    (I : β → Subgroup G)
    (H : Subgroup G) [Fintype H]
    (genericAlgebra : Type q)
    [Ring genericAlgebra]
    [Algebra ℚ genericAlgebra]
    (genericRealization :
      FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
        genericAlgebra)
    (compactifiedAlgebra : Type w)
    [Ring compactifiedAlgebra]
    [Algebra ℚ compactifiedAlgebra]
    extends
      AlgebraProjectorExtension
        genericAlgebra
        compactifiedAlgebra
        (genericRealization
          (subgroupAveragingProjector pX H α)) where
  extension_nonempty_iff_forall_inertiaSaturated :
    Nonempty Extension ↔
      ∀ i : β,
        InertiaSaturated (I i) H {baseSheet H}

namespace CompactifiedSubgroupProjectorExtension

variable {pX : X ⟶ T}
variable {α : FiniteDeckAction pX G}
variable {β : Type t} {I : β → Subgroup G}
variable {H : Subgroup G} [Fintype H]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra]
variable [Algebra ℚ genericAlgebra]
variable
  {genericRealization :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
      genericAlgebra}
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra]
variable [Algebra ℚ compactifiedAlgebra]

/--
The global subgroup projector extends exactly when every boundary inertia
group is contained in `H`.
-/
theorem extension_nonempty_iff_forall_inertia_le
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α β I H genericAlgebra
          genericRealization compactifiedAlgebra) :
    Nonempty E.Extension ↔
      ∀ i : β, I i ≤ H := by
  rw [E.extension_nonempty_iff_forall_inertiaSaturated]
  apply forall_congr'
  intro i
  exact inertiaSaturated_singleton_baseSheet_iff (I i) H

section GlobalCriterion

variable (R A : Type r)
variable [CommRing R] [CommRing A] [Algebra R A]
variable (P : β → Ideal A)
variable [∀ i : β, (P i).IsPrime]

/--
Global codimension-one bridge: the subgroup averaging projector extends to
the compactification exactly when the collision different avoids every
height-one boundary prime.
-/
theorem extension_nonempty_iff_forall_different_not_le
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α β I H genericAlgebra
          genericRealization compactifiedAlgebra)
    (hDifferent :
      ∀ i : β,
        CollisionDifferentDetectsRamificationAt
          R A (P i))
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization
          R A G (I i) H (P i)) :
    Nonempty E.Extension ↔
      ∀ i : β,
        ¬ collisionNoetherDifferentIdeal R A ≤ P i := by
  rw [E.extension_nonempty_iff_forall_inertiaSaturated]
  constructor
  · intro hSaturated i
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R A G (I i) H (P i)
        (hDifferent i) (hInertia i)).mp
        (hSaturated i)
  · intro hDifferentAway i
    exact
      (baseSheet_projector_extends_iff_different_not_le
        R A G (I i) H (P i)
        (hDifferent i) (hInertia i)).mpr
        (hDifferentAway i)

/--
Global cohomological form: a compactified algebraic projector lift exists
exactly when the collision different avoids every boundary prime.
-/
theorem liftWitness_nonempty_iff_forall_different_not_le
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α β I H genericAlgebra
          genericRealization compactifiedAlgebra)
    (hDifferent :
      ∀ i : β,
        CollisionDifferentDetectsRamificationAt
          R A (P i))
    (hInertia :
      ∀ i : β,
        HeightOneInertiaRealization
          R A G (I i) H (P i))
    {V : Type z} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V) :
    Nonempty
        (E.toAlgebraProjectorExtension.LiftWitness ρ) ↔
      ∀ i : β,
        ¬ collisionNoetherDifferentIdeal R A ≤ P i := by
  rw [
    E.toAlgebraProjectorExtension.liftWitness_nonempty_iff,
    E.extension_nonempty_iff_forall_different_not_le
      R A P hDifferent hInertia]

end GlobalCriterion

end CompactifiedSubgroupProjectorExtension

/-!
## Compatibility with the one-boundary presentation

The family extension package is canonical. A one-boundary package carries
the same data as its specialization to the constant family indexed by
`PUnit`; these adapters retain the earlier local API without adding or
removing a boundary condition.
-/

namespace BoundarySubgroupProjectorExtension

variable {pX : X ⟶ T}
variable {α : FiniteDeckAction pX G}
variable {I H : Subgroup G} [Fintype H]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra]
variable [Algebra ℚ genericAlgebra]
variable
  {genericRealization :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
      genericAlgebra}
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra]
variable [Algebra ℚ compactifiedAlgebra]

/-- Regard a one-boundary extension package as a singleton family. -/
def toCompactifiedPUnit
    (E :
      BoundarySubgroupProjectorExtension
        pX α I H genericAlgebra
          genericRealization compactifiedAlgebra) :
    CompactifiedSubgroupProjectorExtension
      pX α PUnit.{1} (fun _ ↦ I) H genericAlgebra
        genericRealization compactifiedAlgebra where
  toAlgebraProjectorExtension :=
    E.toAlgebraProjectorExtension
  extension_nonempty_iff_forall_inertiaSaturated := by
    constructor
    · intro h _
      exact E.extension_nonempty_iff_inertiaSaturated.mp h
    · intro h
      exact
        E.extension_nonempty_iff_inertiaSaturated.mpr
          (h PUnit.unit)

@[simp]
theorem toCompactifiedPUnit_toAlgebraProjectorExtension
    (E :
      BoundarySubgroupProjectorExtension
        pX α I H genericAlgebra
          genericRealization compactifiedAlgebra) :
    E.toCompactifiedPUnit.toAlgebraProjectorExtension =
      E.toAlgebraProjectorExtension :=
  rfl

/-- Boundary extension of `e_H` is equivalent to the containment `I ≤ H`. -/
theorem extension_nonempty_iff_inertia_le
    (E :
      BoundarySubgroupProjectorExtension
        pX α I H genericAlgebra
          genericRealization compactifiedAlgebra) :
    Nonempty E.Extension ↔ I ≤ H := by
  have h :=
    E.toCompactifiedPUnit.extension_nonempty_iff_forall_inertia_le
  exact h.trans ⟨fun hI ↦ hI PUnit.unit, fun hI _ ↦ hI⟩

section HeightOne

variable (R A : Type r)
variable [CommRing R] [CommRing A] [Algebra R A]
variable (P : Ideal A) [P.IsPrime]

/--
Height-one boundary bridge, retained as the singleton-family compatibility
form of the global criterion.
-/
theorem extension_nonempty_iff_different_not_le
    (E :
      BoundarySubgroupProjectorExtension
        pX α I H genericAlgebra
          genericRealization compactifiedAlgebra)
    (hDifferent :
      CollisionDifferentDetectsRamificationAt R A P)
    (hInertia :
      HeightOneInertiaRealization R A G I H P) :
    Nonempty E.Extension ↔
      ¬ collisionNoetherDifferentIdeal R A ≤ P := by
  let boundaryPrime : PUnit.{1} → Ideal A := fun _ ↦ P
  letI : ∀ i, (boundaryPrime i).IsPrime := fun _ ↦ inferInstance
  have h :=
    E.toCompactifiedPUnit.extension_nonempty_iff_forall_different_not_le
      R A boundaryPrime (fun _ ↦ hDifferent) (fun _ ↦ hInertia)
  exact h.trans ⟨fun hP ↦ hP PUnit.unit, fun hP _ ↦ hP⟩

/--
Height-one cohomological form, retained as the singleton-family compatibility
form of the global lift criterion.
-/
theorem liftWitness_nonempty_iff_different_not_le
    (E :
      BoundarySubgroupProjectorExtension
        pX α I H genericAlgebra
          genericRealization compactifiedAlgebra)
    (hDifferent :
      CollisionDifferentDetectsRamificationAt R A P)
    (hInertia :
      HeightOneInertiaRealization R A G I H P)
    {V : Type z} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V) :
    Nonempty (E.toAlgebraProjectorExtension.LiftWitness ρ) ↔
      ¬ collisionNoetherDifferentIdeal R A ≤ P := by
  rw [
    E.toAlgebraProjectorExtension.liftWitness_nonempty_iff,
    E.extension_nonempty_iff_different_not_le
      R A P hDifferent hInertia]

end HeightOne

end BoundarySubgroupProjectorExtension

namespace CompactifiedSubgroupProjectorExtension

variable {pX : X ⟶ T}
variable {α : FiniteDeckAction pX G}
variable {I H : Subgroup G} [Fintype H]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra]
variable [Algebra ℚ genericAlgebra]
variable
  {genericRealization :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
      genericAlgebra}
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra]
variable [Algebra ℚ compactifiedAlgebra]

/-- Recover the one-boundary compatibility package from a singleton family. -/
def toBoundary
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α PUnit.{1} (fun _ ↦ I) H genericAlgebra
          genericRealization compactifiedAlgebra) :
    BoundarySubgroupProjectorExtension
      pX α I H genericAlgebra
        genericRealization compactifiedAlgebra where
  toAlgebraProjectorExtension :=
    E.toAlgebraProjectorExtension
  extension_nonempty_iff_inertiaSaturated := by
    constructor
    · intro h
      exact
        E.extension_nonempty_iff_forall_inertiaSaturated.mp h
          PUnit.unit
    · intro h
      apply
        E.extension_nonempty_iff_forall_inertiaSaturated.mpr
      intro _
      exact h

@[simp]
theorem toBoundary_toAlgebraProjectorExtension
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α PUnit.{1} (fun _ ↦ I) H genericAlgebra
          genericRealization compactifiedAlgebra) :
    E.toBoundary.toAlgebraProjectorExtension =
      E.toAlgebraProjectorExtension :=
  rfl

end CompactifiedSubgroupProjectorExtension

namespace BoundarySubgroupProjectorExtension

variable {pX : X ⟶ T}
variable {α : FiniteDeckAction pX G}
variable {I H : Subgroup G} [Fintype H]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra]
variable [Algebra ℚ genericAlgebra]
variable
  {genericRealization :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
      genericAlgebra}
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra]
variable [Algebra ℚ compactifiedAlgebra]

/-- The two singleton-family adapters lose no one-boundary package data. -/
@[simp]
theorem toCompactifiedPUnit_toBoundary
    (E :
      BoundarySubgroupProjectorExtension
        pX α I H genericAlgebra
          genericRealization compactifiedAlgebra) :
    E.toCompactifiedPUnit.toBoundary = E := by
  cases E
  rfl

end BoundarySubgroupProjectorExtension

namespace CompactifiedSubgroupProjectorExtension

variable {pX : X ⟶ T}
variable {α : FiniteDeckAction pX G}
variable {I H : Subgroup G} [Fintype H]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra]
variable [Algebra ℚ genericAlgebra]
variable
  {genericRealization :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
      genericAlgebra}
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra]
variable [Algebra ℚ compactifiedAlgebra]

/-- The two one-boundary adapters lose no singleton-family package data. -/
@[simp]
theorem toBoundary_toCompactifiedPUnit
    (E :
      CompactifiedSubgroupProjectorExtension
        pX α PUnit.{1} (fun _ ↦ I) H genericAlgebra
          genericRealization compactifiedAlgebra) :
    E.toBoundary.toCompactifiedPUnit = E := by
  cases E
  rfl

end CompactifiedSubgroupProjectorExtension

end SchemeCorrespondence

section GaloisSpecialization

variable {T X Y : Scheme.{u}}
variable {G : Type u} [Group G]
variable {f : X ⟶ Y}

/--
The subgroup averaging projector attached to an explicit Galois collision
decomposition, viewed over a further base `T`.
-/
abbrev GaloisCollisionDecomposition.subgroupProjector
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ T)
    (H : Subgroup G) [Fintype H] :
    SchemeCorrespondence.FiniteEtaleFreeAlgebra
      (f ≫ g) :=
  SchemeCorrespondence.subgroupAveragingProjector
    (f ≫ g) H (D.actionOverBase g)

/-- Every Galois subgroup projector is convolution-idempotent. -/
theorem GaloisCollisionDecomposition.subgroupProjector_isIdempotent
    (D : GaloisCollisionDecomposition G f)
    (g : Y ⟶ T)
    (H : Subgroup G) [Fintype H] :
    IsIdempotentElem (D.subgroupProjector g H) :=
  SchemeCorrespondence.subgroupAveragingProjector_isIdempotent
    (f ≫ g) H (D.actionOverBase g)

end GaloisSpecialization

namespace NormalizationInertia

section DiagramProjectorExtension

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable
  {j :
    U ⟶
      intermediateNormalization
        (B := B) (L := L)}
variable
  {C :
    NormalizedCover
      (B := B) (K := K) (L := L) (N := N)
      U j}

namespace Diagram

omit [IsFractionRing B K] in
/--
Formal unramifiedness on the visible locus and absence of hidden inertia
supply the codimension-one condition required by a compactified subgroup
projector extension.

The extension package still contains the separate purity/comparison input
turning that condition into an actual compactified correspondence
idempotent.
-/
theorem compactifiedSubgroupProjectorExtension_nonempty_of_formallyUnramified
    [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (hFormal :
      FormallyUnramified
        (j ≫
          intermediateNormalizationToBase
            (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia)
    {T X : Scheme.{u}} {pX : X ⟶ T}
    (α :
      SchemeCorrespondence.FiniteDeckAction
        pX C.normalClosure.galoisGroup)
    [Fintype
      C.normalClosure.intermediateFixingSubgroup]
    {genericAlgebra : Type q}
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    (genericRealization :
      SchemeCorrespondence.FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
        genericAlgebra)
    {compactifiedAlgebra : Type w}
    [Ring compactifiedAlgebra]
    [Algebra ℚ compactifiedAlgebra]
    (E :
      SchemeCorrespondence.CompactifiedSubgroupProjectorExtension
        pX α
        (RamifiedCodimensionOnePoint
          (B := B) (N := N))
        (fun Q ↦
          CollisionFoundations.inertiaGroupAt K
            (D.valuationAt Q).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        genericAlgebra genericRealization
        compactifiedAlgebra) :
    Nonempty E.Extension := by
  apply
    E.extension_nonempty_iff_forall_inertiaSaturated.mpr
  exact
    D.forall_inertiaSaturated_of_formallyUnramified
      R hFormal hNoHidden
      {baseSheet
        C.normalClosure.intermediateFixingSubgroup}

omit [IsFractionRing B K] in
/--
The same normalization hypotheses produce an extended algebraic projector
lift under every rational action of the compactified correspondence algebra.
-/
theorem compactifiedSubgroupProjectorLift_nonempty_of_formallyUnramified
    [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateRamificationRealization)
    (hFormal :
      FormallyUnramified
        (j ≫
          intermediateNormalizationToBase
            (B := B) (L := L)))
    (hNoHidden : D.NoHiddenInertia)
    {T X : Scheme.{u}} {pX : X ⟶ T}
    (α :
      SchemeCorrespondence.FiniteDeckAction
        pX C.normalClosure.galoisGroup)
    [Fintype
      C.normalClosure.intermediateFixingSubgroup]
    {genericAlgebra : Type q}
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    (genericRealization :
      SchemeCorrespondence.FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
        genericAlgebra)
    {compactifiedAlgebra : Type w}
    [Ring compactifiedAlgebra]
    [Algebra ℚ compactifiedAlgebra]
    (E :
      SchemeCorrespondence.CompactifiedSubgroupProjectorExtension
        pX α
        (RamifiedCodimensionOnePoint
          (B := B) (N := N))
        (fun Q ↦
          CollisionFoundations.inertiaGroupAt K
            (D.valuationAt Q).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        genericAlgebra genericRealization
        compactifiedAlgebra)
    {V : Type z} [AddCommGroup V] [Module ℚ V]
    (ρ :
      RationalCorrespondenceAction
        compactifiedAlgebra V) :
    Nonempty
      (E.toAlgebraProjectorExtension.LiftWitness ρ) := by
  rw [E.toAlgebraProjectorExtension.liftWitness_nonempty_iff]
  exact
    D.compactifiedSubgroupProjectorExtension_nonempty_of_formallyUnramified
      R hFormal hNoHidden α genericRealization E

omit [IsFractionRing B K] in
/--
Fixed--moving conjugate-boundary separation supplies all local inertia
conditions needed by the compactified subgroup-projector extension package.
The package's extension/purity equivalence remains a visible hypothesis.
-/
theorem compactifiedSubgroupProjectorExtension_nonempty_of_conjugateBoundarySeparation
    [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateBoundaryData)
    (hFormal :
      FormallyUnramified
        (j ≫
          intermediateNormalizationToBase
            (B := B) (L := L)))
    (hSeparation : ConjugateBoundarySeparation C)
    {T X : Scheme.{u}} {pX : X ⟶ T}
    (α :
      SchemeCorrespondence.FiniteDeckAction
        pX C.normalClosure.galoisGroup)
    [Fintype C.normalClosure.intermediateFixingSubgroup]
    {genericAlgebra : Type q}
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    (genericRealization :
      SchemeCorrespondence.FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
        genericAlgebra)
    {compactifiedAlgebra : Type w}
    [Ring compactifiedAlgebra]
    [Algebra ℚ compactifiedAlgebra]
    (E :
      SchemeCorrespondence.CompactifiedSubgroupProjectorExtension
        pX α
        (RamifiedCodimensionOnePoint (B := B) (N := N))
        (fun Q ↦
          CollisionFoundations.inertiaGroupAt K
            (D.valuationAt Q).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        genericAlgebra genericRealization
        compactifiedAlgebra) :
    Nonempty E.Extension := by
  apply E.extension_nonempty_iff_forall_inertiaSaturated.mpr
  exact
    D.forall_inertiaSaturated_of_conjugateBoundarySeparation
      R hFormal hSeparation
      {baseSheet C.normalClosure.intermediateFixingSubgroup}

omit [IsFractionRing B K] in
/--
The same separation route produces the corresponding algebraic-projector
lift for every supplied rational action of the compactified algebra.
-/
theorem compactifiedSubgroupProjectorLift_nonempty_of_conjugateBoundarySeparation
    [IsNoetherianRing B]
    (D : Diagram C)
    (R : D.ConjugateBoundaryData)
    (hFormal :
      FormallyUnramified
        (j ≫
          intermediateNormalizationToBase
            (B := B) (L := L)))
    (hSeparation : ConjugateBoundarySeparation C)
    {T X : Scheme.{u}} {pX : X ⟶ T}
    (α :
      SchemeCorrespondence.FiniteDeckAction
        pX C.normalClosure.galoisGroup)
    [Fintype C.normalClosure.intermediateFixingSubgroup]
    {genericAlgebra : Type q}
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    (genericRealization :
      SchemeCorrespondence.FiniteEtaleFreeAlgebra pX →ₐ[ℚ]
        genericAlgebra)
    {compactifiedAlgebra : Type w}
    [Ring compactifiedAlgebra]
    [Algebra ℚ compactifiedAlgebra]
    (E :
      SchemeCorrespondence.CompactifiedSubgroupProjectorExtension
        pX α
        (RamifiedCodimensionOnePoint (B := B) (N := N))
        (fun Q ↦
          CollisionFoundations.inertiaGroupAt K
            (D.valuationAt Q).valuationRing)
        C.normalClosure.intermediateFixingSubgroup
        genericAlgebra genericRealization
        compactifiedAlgebra)
    {V : Type z} [AddCommGroup V] [Module ℚ V]
    (ρ : RationalCorrespondenceAction compactifiedAlgebra V) :
    Nonempty (E.toAlgebraProjectorExtension.LiftWitness ρ) := by
  rw [E.toAlgebraProjectorExtension.liftWitness_nonempty_iff]
  exact
    D.compactifiedSubgroupProjectorExtension_nonempty_of_conjugateBoundarySeparation
      R hFormal hSeparation α genericRealization E

end Diagram

end DiagramProjectorExtension

end NormalizationInertia

end

end HodgeConjecture
