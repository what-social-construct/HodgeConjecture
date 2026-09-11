import HodgeConjecture.Realization.Chow.GaloisProjector
import HodgeConjecture.Realization.Chow.TateGraphProjector

/-!
# From prescribed deck-action projectors to Hodge classes

This module connects the existing cover-intended deck-action realization
endpoint to the modeled fixed-variety rational Hodge-conjecture target.  Its
formal context assumes a `FiniteDeckAction` and a finite subgroup `D`; despite
the historical API name, it does not itself assert that `pX` is finite or
étale.  Those properties belong to a concrete finite-cover instance.

A `PrescribedChowProjectorLift` of the canonical graph projector of `α`
already gives an `AlgebraicProjectorLift`.  If the compactified algebra also
has the lower-left Chow-block detection map from
`ClassGraphProjectorDetection`, that lift yields a Chow class whose cycle
class is `α`.

`ClassIndexedFiniteCoverGraphCoverage` lets the boundary-extension package
vary with the rational Hodge class while keeping the deck-action data,
subgroup, and Chow model fixed.  It maps one way to ordinary graph-projector
liftability and, after lower-left detection, to `RationalHodgeConjectureAt`.
The converse is
not automatic.  `GraphProjectorLiftFactorizationThroughFixedDeckData` names the
extra assertion that an arbitrary algebraic graph lift can be replaced by one
factoring through the prescribed extension/restriction data.  Under that
explicit assertion and the Chow-level graph comparison, the module proves a
conditional equivalence with finite-cover coverage.

This coverage condition is a strong geometric hypothesis, not a consequence
of deck averaging alone.  In particular, the usual subgroup average acts on
the cover geometry, whereas the canonical graph projector has block form
`[[1, 0], [alpha, 0]]` on a Tate-augmented object.  Idempotence of the average
does not identify these two operators; the `realizes` field of
`PrescribedChowProjectorLift` records precisely that missing comparison.

The conventional compactified algebra `CH^d(X × X)_ℚ` described in
`Realization.Chow.Model` has no Tate-to-`X` lower-left block by itself.  A
geometric use of this module must first construct the Tate-augmented block
algebra `End(ℚ(-p) ⊕ h(X))` and compare the finite-cover action with it.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w t q c h e

namespace SchemeCorrespondence

variable {T X : Scheme.{u}}
variable {G : Type v} [Group G]
variable {pX : X ⟶ T}
variable {deck : FiniteDeckAction pX G}
variable {β : Type t} {I : β → Subgroup G}
variable {D : Subgroup G} [Fintype D]
variable {genericAlgebra : Type q}
variable [Ring genericAlgebra] [Algebra ℚ genericAlgebra]
variable {compactifiedAlgebra : Type w}
variable [Ring compactifiedAlgebra] [Algebra ℚ compactifiedAlgebra]
variable {Chow : Type c} {H : Type h}
variable [AddCommGroup Chow] [Module ℚ Chow]
variable [AddCommGroup H] [Module ℚ H]

namespace PrescribedChowProjectorLift

variable {M : RationalHodgeCycleClassModel Chow H}
variable
  {χ :
    RationalChowCorrespondenceModel
      pX genericAlgebra compactifiedAlgebra (ℚ × H)}
variable
  {E :
    CompactifiedSubgroupProjectorExtension
      pX deck β I D genericAlgebra
        χ.genericCycleClass compactifiedAlgebra}
variable {α : H}

/--
A prescribed lift of the canonical graph projector, together with lower-left
Chow-block detection, produces an algebraic representative of its class.
-/
theorem isAlgebraicHodgeClass_of_classGraphProjector
    (detect :
      ClassGraphProjectorDetection M χ.cohomologicalAction)
    (L :
      PrescribedChowProjectorLift χ E
        (ClassGraphProjector.projector α)) :
    IsAlgebraicHodgeClass M α := by
  apply isAlgebraicHodgeClass_of_graphProjectorLift detect
  exact ⟨L.toAlgebraicProjectorLift⟩

/--
Class-indexed prescribed-projector coverage over fixed deck-action data,
subgroup, and Chow model.  The name records the intended finite-cover
application, but finiteness and étaleness of `pX` are not hypotheses of this
abstract layer.  Each rational Hodge class may choose its own boundary-
extension package, which must produce the independently defined canonical
graph projector of the class.

The prescribed-action equality inside `PrescribedChowProjectorLift` makes
this a stronger requirement than merely producing an idempotent by subgroup
averaging.  No such coverage is constructed in this definition.
-/
def ClassIndexedFiniteCoverGraphCoverage
    (M : RationalHodgeCycleClassModel Chow H)
    (χ :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra (ℚ × H)) : Prop :=
  ∀ α : H, IsRationalHodgeClass M α →
    ∃ Eα :
      CompactifiedSubgroupProjectorExtension.{u, v, w, t, q, e}
        pX deck β I D genericAlgebra
          χ.genericCycleClass compactifiedAlgebra,
      Nonempty
        (PrescribedChowProjectorLift χ Eα
          (ClassGraphProjector.projector α))

/--
The missing factorization from an algebraic graph-projector lift in a chosen
target class to one generated by the fixed deck-action data and subgroup.

The predicate `target` can select all graph classes, rational Hodge classes,
or a smaller named subspace.  The assertion does not contain a surjectivity or
algebraicity conclusion, but it is nevertheless a strong motivic-generation
hypothesis: an arbitrary algebraic lift need not have the prescribed generic
restriction or factor through any `E.Extension`.  No instance is constructed
here.
-/
def GraphProjectorLiftFactorizationThroughFixedDeckData
    (target : H → Prop)
    (χ :
      RationalChowCorrespondenceModel
        pX genericAlgebra compactifiedAlgebra (ℚ × H)) : Prop :=
  ∀ α : H,
    target α →
      Nonempty
        (AlgebraicProjectorLift χ.cohomologicalAction
          (ClassGraphProjector.operator α)) →
      ∃ Eα :
        CompactifiedSubgroupProjectorExtension.{u, v, w, t, q, e}
          pX deck β I D genericAlgebra
            χ.genericCycleClass compactifiedAlgebra,
        Nonempty
          (PrescribedChowProjectorLift χ Eα
            (ClassGraphProjector.projector α))

/--
Prescribed deck-action coverage forgets to ordinary algebraic liftability of
every canonical graph projector.  This is only a one-way implication: an
arbitrary algebraic graph-projector lift need not factor through boundary-
extension data for the chosen deck action.
-/
theorem everyHodgeClassHasGraphProjectorLift_of_classIndexedFiniteCoverCoverage
    (coverage :
      ClassIndexedFiniteCoverGraphCoverage
        (deck := deck) (I := I) (D := D) M χ) :
    EveryHodgeClassHasGraphProjectorLift M χ.cohomologicalAction := by
  intro α hα
  obtain ⟨Eα, ⟨L⟩⟩ := coverage α hα
  exact ⟨L.toAlgebraicProjectorLift⟩

/--
The named factorization condition turns ordinary Hodge-class graph lifts into
class-indexed prescribed deck-action coverage.
-/
theorem classIndexedFiniteCoverGraphCoverage_of_everyHodgeClassHasGraphProjectorLift
    (factorization :
      GraphProjectorLiftFactorizationThroughFixedDeckData.{u, v, w, t, q, h, e}
        (deck := deck) (I := I) (D := D)
        (IsRationalHodgeClass M) χ)
    (h : EveryHodgeClassHasGraphProjectorLift M χ.cohomologicalAction) :
    ClassIndexedFiniteCoverGraphCoverage.{u, v, w, t, q, c, h, e}
      (deck := deck) (I := I) (D := D) M χ := by
  intro α hα
  exact factorization α hα (h α hα)

/--
Class-indexed prescribed deck-action coverage proves the modeled rational
Hodge target once the Tate-block correspondence algebra has lower-left Chow
detection.

This theorem does not prove the coverage or detection hypotheses; those are
the remaining geometric inputs.
-/
theorem rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage
    (detect :
      ClassGraphProjectorDetection M χ.cohomologicalAction)
    (coverage :
      ClassIndexedFiniteCoverGraphCoverage
        (deck := deck) (I := I) (D := D) M χ) :
    RationalHodgeConjectureAt M :=
  rationalHodgeConjectureAt_of_everyHodgeClassHasGraphProjectorLift
    detect
    (everyHodgeClassHasGraphProjectorLift_of_classIndexedFiniteCoverCoverage
      coverage)

/--
Conditional prescribed deck-action coverage reformulation of the modeled
Hodge target.

The direction from the Hodge target to coverage uses the separately named
factorization hypothesis; that hypothesis is not a consequence of the Hodge
conjecture or of deck averaging.  This theorem therefore exposes the exact
extra generation statement rather than folding it into the realization map.
-/
theorem rationalHodgeConjectureAt_iff_classIndexedFiniteCoverGraphCoverage
    (construct :
      ClassGraphProjectorConstruction M χ.cohomologicalAction)
    (detect :
      ClassGraphProjectorDetection M χ.cohomologicalAction)
    (factorization :
      GraphProjectorLiftFactorizationThroughFixedDeckData.{u, v, w, t, q, h, e}
        (deck := deck) (I := I) (D := D)
        (IsRationalHodgeClass M) χ) :
    RationalHodgeConjectureAt M ↔
      ClassIndexedFiniteCoverGraphCoverage.{u, v, w, t, q, c, h, e}
        (deck := deck) (I := I) (D := D) M χ := by
  constructor
  · intro h
    apply
      classIndexedFiniteCoverGraphCoverage_of_everyHodgeClassHasGraphProjectorLift
        factorization
    exact
      everyHodgeClassHasGraphProjectorLift_of_rationalHodgeConjectureAt
        construct h
  · exact
      rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage
        detect

/--
If the cover-intended realization supplies the canonical graph projector of
every rational Hodge class, then the rational Hodge conjecture holds in the
modeled codimension.  This version fixes one extension-data package for every
class and is therefore a stronger fixed-package hypothesis than class-indexed
coverage.
-/
theorem rationalHodgeConjectureAt_of_every_classGraphProjector_for_fixed_extensionData
    (detect :
      ClassGraphProjectorDetection M χ.cohomologicalAction)
    (hLifts :
      ∀ α : H, IsRationalHodgeClass M α →
        Nonempty
          (PrescribedChowProjectorLift χ E
            (ClassGraphProjector.projector α))) :
    RationalHodgeConjectureAt M := by
  apply
    rationalHodgeConjectureAt_of_classIndexedFiniteCoverGraphCoverage
      (deck := deck) (I := I) (D := D)
      detect
  intro α hα
  exact ⟨E, hLifts α hα⟩

end PrescribedChowProjectorLift

end SchemeCorrespondence

end

end HodgeConjecture
