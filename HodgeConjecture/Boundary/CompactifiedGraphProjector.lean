import HodgeConjecture.Boundary.GaloisProjectorExtension
import HodgeConjecture.Correspondence.GroupAlgebraProjector
import HodgeConjecture.Correspondence.ProjectorDefect

/-!
# Supplied compactified graph projectors

This module isolates the algebraic comparison needed after a deck action has
been extended to some supplied compactified correspondence model.  The two
scheme morphisms below need not be related by data in this structure: all of
the geometric work is concentrated in the commutative square of algebra
homomorphisms.

In particular, `compactifiedAlgebra` is only a supplied rational algebra.  It
is not identified here with a Chow-correspondence algebra, and this file does
not construct a compactification, extend a cover, or invoke purity.

Once the comparison square is available, every idempotent of `ℚ[G]` has a
compactified idempotent image with the prescribed generic restriction.  Thus
its idempotence defect is literally zero; no separate boundary-support
argument is hidden in the construction.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v a c

namespace SchemeCorrespondence

variable {TGeneric XGeneric TCompactified XCompactified : Scheme.{u}}

/--
A supplied comparison between generic and compactified graph realizations of
the same abstract deck group.

The field `graph_square` is the exact compatibility used below.  Constructing
it from open restriction, graph-cycle classes, or a concrete Chow theory is a
separate geometric task.
-/
structure CompactifiedDeckGraphComparison
    (pGeneric : XGeneric ⟶ TGeneric)
    (pCompactified : XCompactified ⟶ TCompactified)
    (G : Type v) [Group G]
    (genericAlgebra : Type a)
    (compactifiedAlgebra : Type c)
    [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
    [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
    (genericAction : FiniteDeckAction pGeneric G)
    (compactifiedAction : FiniteDeckAction pCompactified G) where
  genericCycleClass :
    FiniteEtaleFreeAlgebra pGeneric →ₐ[ℚ] genericAlgebra
  compactifiedCycleClass :
    FiniteEtaleFreeAlgebra pCompactified →ₐ[ℚ] compactifiedAlgebra
  restriction : compactifiedAlgebra →ₐ[ℚ] genericAlgebra
  graph_square :
    restriction.comp
          (compactifiedCycleClass.comp
            (compactifiedAction.toFiniteEtaleAlgebra pCompactified)) =
      genericCycleClass.comp
        (genericAction.toFiniteEtaleAlgebra pGeneric)

namespace CompactifiedDeckGraphComparison

variable {pGeneric : XGeneric ⟶ TGeneric}
variable {pCompactified : XCompactified ⟶ TCompactified}
variable {G : Type v} [Group G]
variable {genericAlgebra : Type a}
variable {compactifiedAlgebra : Type c}
variable [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
variable [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
variable {genericAction : FiniteDeckAction pGeneric G}
variable {compactifiedAction : FiniteDeckAction pCompactified G}

/-- The generic image of an element of the rational group algebra. -/
noncomputable def genericGroupAlgebraProjector
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G) :
    genericAlgebra :=
  C.genericCycleClass
    (groupAlgebraCorrespondence pGeneric genericAction q)

/-- The supplied compactified image of an element of the rational group algebra. -/
noncomputable def compactifiedGroupAlgebraProjector
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G) :
    compactifiedAlgebra :=
  C.compactifiedCycleClass
    (groupAlgebraCorrespondence pCompactified compactifiedAction q)

/-- The compactified group-algebra image has the prescribed generic restriction. -/
theorem compactifiedGroupAlgebraProjector_restricts
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G) :
    C.restriction (C.compactifiedGroupAlgebraProjector q) =
      C.genericGroupAlgebraProjector q := by
  simpa [genericGroupAlgebraProjector,
    compactifiedGroupAlgebraProjector, groupAlgebraCorrespondence] using
    DFunLike.congr_fun C.graph_square q

/-- An idempotent group-algebra element remains idempotent after compactified realization. -/
theorem compactifiedGroupAlgebraProjector_isIdempotent
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q) :
    IsIdempotentElem (C.compactifiedGroupAlgebraProjector q) :=
  (groupAlgebraCorrespondence_isIdempotent
      pCompactified compactifiedAction q hq).map
    C.compactifiedCycleClass

/-- Restriction carries the compactified defect to the corresponding generic defect. -/
theorem compactifiedGroupAlgebraProjector_defect_restricts
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G) :
    C.restriction
        (projectorIdempotenceDefect
          (C.compactifiedGroupAlgebraProjector q)) =
      projectorIdempotenceDefect
        (C.genericGroupAlgebraProjector q) := by
  calc
    C.restriction
          (projectorIdempotenceDefect
            (C.compactifiedGroupAlgebraProjector q)) =
        projectorIdempotenceDefect
          (C.restriction
            (C.compactifiedGroupAlgebraProjector q)) := by
      exact
        map_projectorIdempotenceDefect C.restriction.toRingHom
          (C.compactifiedGroupAlgebraProjector q)
    _ = projectorIdempotenceDefect
          (C.genericGroupAlgebraProjector q) := by
      rw [C.compactifiedGroupAlgebraProjector_restricts]

/-- A transported group-algebra idempotent has zero compactified defect. -/
theorem compactifiedGroupAlgebraProjector_defect_eq_zero
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q) :
    projectorIdempotenceDefect
        (C.compactifiedGroupAlgebraProjector q) = 0 :=
  projectorIdempotenceDefect_eq_zero
    (C.compactifiedGroupAlgebraProjector_isIdempotent q hq)

/--
The comparison square turns any supplied group-algebra idempotent into an
`AlgebraProjectorExtension`.  The singleton witness type records that the
compactified projector has already been constructed by the supplied graph
realization.
-/
noncomputable def groupAlgebraProjectorExtension
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified G genericAlgebra compactifiedAlgebra
        genericAction compactifiedAction)
    (q : MonoidAlgebra ℚ G)
    (hq : IsIdempotentElem q) :
    AlgebraProjectorExtension
      genericAlgebra compactifiedAlgebra
      (C.genericGroupAlgebraProjector q) where
  genericProjector_isIdempotent :=
    (groupAlgebraCorrespondence_isIdempotent
        pGeneric genericAction q hq).map
      C.genericCycleClass
  restriction := C.restriction
  Extension := PUnit
  projector := fun _ ↦ C.compactifiedGroupAlgebraProjector q
  projector_isIdempotent := fun _ ↦
    C.compactifiedGroupAlgebraProjector_isIdempotent q hq
  projector_restricts := fun _ ↦
    C.compactifiedGroupAlgebraProjector_restricts q

section SubgroupAverage

variable {G₀ : Type v} [Group G₀]
variable (H : Subgroup G₀) [Fintype H]
variable {genericAction₀ : FiniteDeckAction pGeneric G₀}
variable {compactifiedAction₀ : FiniteDeckAction pCompactified G₀}

/--
The subgroup-average specialization.  The comparison is required only for
the two restricted `H`-actions; no assertion is made that it follows from
inertia saturation.
-/
noncomputable def subgroupAveragingProjectorExtension
    (C :
      CompactifiedDeckGraphComparison
        pGeneric pCompactified H genericAlgebra compactifiedAlgebra
        (genericAction₀.restrict pGeneric H)
        (compactifiedAction₀.restrict pCompactified H)) :
    AlgebraProjectorExtension
      genericAlgebra compactifiedAlgebra
      (C.genericCycleClass
        (subgroupAveragingProjector pGeneric H genericAction₀)) := by
  simpa [genericGroupAlgebraProjector, groupAlgebraCorrespondence,
    subgroupAveragingProjector, averagingProjector] using
    C.groupAlgebraProjectorExtension
      (finiteGroupAverage H)
      (finiteGroupAverage_isIdempotent H)

end SubgroupAverage

end CompactifiedDeckGraphComparison

end SchemeCorrespondence

end

end HodgeConjecture
