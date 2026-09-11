import HodgeConjecture.Realization.Chow.Model
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Noncommutative presentations of rational Chow-correspondence algebras

This file is the algebraic adapter between supplied raw correspondence
algebras and the abstract Chow model in `Realization.Chow.Model`.

The input `Z` is already a noncommutative rational algebra with an
everywhere-defined convolution product.  A two-sided ideal records the
relations imposed on that algebra; these may include rational equivalence,
coproduct additivity, moving/refined-intersection relations, and any
proper-support restrictions needed to make convolution meaningful.  The
quotient is an honest noncommutative algebra in Lean.

Crucially, ordinary raw codimension-`d` cycles are not claimed to carry this
product automatically.  On a nonproper generic locus, plain
`CH^d(U × U)_ℚ` is likewise not automatically a correspondence algebra,
because the pushforward in convolution may fail to be proper.  Constructing
the supplied raw algebras and identifying these quotients with the desired
Chow or bivariant theory remain geometric theorems.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v w z

/--
A presentation of a rational, generally noncommutative correspondence
algebra by a two-sided ideal of relations.
-/
structure CorrespondenceAlgebraPresentation
    (Z : Type u) [Ring Z] [Algebra ℚ Z] where
  relations : TwoSidedIdeal Z

namespace CorrespondenceAlgebraPresentation

variable {Z : Type u} [Ring Z] [Algebra ℚ Z]

/-- The presented noncommutative rational correspondence algebra. -/
abbrev QuotientAlgebra
    (P : CorrespondenceAlgebraPresentation Z) :=
  P.relations.ringCon.Quotient

/-- The class of a raw correspondence modulo the supplied relations. -/
def classMap
    (P : CorrespondenceAlgebraPresentation Z) :
    Z →ₐ[ℚ] P.QuotientAlgebra :=
  { P.relations.ringCon.mk' with
    commutes' := fun _ ↦ rfl }

/-- Every quotient class has a raw representative. -/
theorem classMap_surjective
    (P : CorrespondenceAlgebraPresentation Z) :
    Function.Surjective P.classMap :=
  Quotient.mk''_surjective

/-- A raw correspondence has zero class exactly when it is a relation. -/
@[simp]
theorem classMap_eq_zero_iff
    (P : CorrespondenceAlgebraPresentation Z)
    (z : Z) :
    P.classMap z = 0 ↔ z ∈ P.relations := by
  change (Quotient.mk'' z : P.QuotientAlgebra) =
      Quotient.mk'' 0 ↔ _
  rw [Quotient.eq'']
  exact P.relations.mem_iff z

/-- The kernel of the quotient class map is precisely the relation ideal. -/
theorem ker_classMap
    (P : CorrespondenceAlgebraPresentation Z) :
    TwoSidedIdeal.ker P.classMap = P.relations := by
  ext z
  rw [TwoSidedIdeal.mem_ker, P.classMap_eq_zero_iff]

variable {A : Type v} [Ring A] [Algebra ℚ A]

/--
An algebra homomorphism annihilating the supplied relations descends to the
presented quotient algebra.
-/
def lift
    (P : CorrespondenceAlgebraPresentation Z)
    (f : Z →ₐ[ℚ] A)
    (hf : ∀ z : Z, z ∈ P.relations → f z = 0) :
    P.QuotientAlgebra →ₐ[ℚ] A where
  toFun := _root_.Quotient.lift f fun x y hxy ↦ by
    have hzero : f (x - y) = 0 :=
      hf (x - y) ((P.relations.rel_iff x y).mp hxy)
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero
  map_zero' := f.map_zero
  map_one' := f.map_one
  map_add' := _root_.Quotient.ind₂' fun x y ↦ f.map_add x y
  map_mul' := _root_.Quotient.ind₂' fun x y ↦ f.map_mul x y
  commutes' := fun r ↦ f.commutes r

/-- The descended homomorphism agrees with the raw map on representatives. -/
@[simp]
theorem lift_classMap_apply
    (P : CorrespondenceAlgebraPresentation Z)
    (f : Z →ₐ[ℚ] A)
    (hf : ∀ z : Z, z ∈ P.relations → f z = 0)
    (z : Z) :
    P.lift f hf (P.classMap z) = f z :=
  rfl

/-- The descended algebra homomorphism is uniquely determined by representatives. -/
theorem lift_unique
    (P : CorrespondenceAlgebraPresentation Z)
    (f : Z →ₐ[ℚ] A)
    (hf : ∀ z : Z, z ∈ P.relations → f z = 0)
    (g : P.QuotientAlgebra →ₐ[ℚ] A)
    (hg : g.comp P.classMap = f) :
    g = P.lift f hf := by
  apply AlgHom.ext
  intro q
  obtain ⟨z, rfl⟩ := P.classMap_surjective q
  rw [P.lift_classMap_apply]
  exact AlgHom.congr_fun hg z

variable {W : Type w} [Ring W] [Algebra ℚ W]

/--
A raw algebra map respecting both relation ideals descends to a map between
the presented quotient algebras.
-/
def map
    (P : CorrespondenceAlgebraPresentation Z)
    (Q : CorrespondenceAlgebraPresentation W)
    (f : Z →ₐ[ℚ] W)
    (hf : P.relations ≤ Q.relations.comap f) :
    P.QuotientAlgebra →ₐ[ℚ] Q.QuotientAlgebra :=
  P.lift (Q.classMap.comp f) fun z hz ↦ by
    change Q.classMap (f z) = 0
    rw [Q.classMap_eq_zero_iff]
    exact (TwoSidedIdeal.mem_comap f).mp (hf hz)

/-- The induced quotient map has the expected value on representatives. -/
@[simp]
theorem map_classMap_apply
    (P : CorrespondenceAlgebraPresentation Z)
    (Q : CorrespondenceAlgebraPresentation W)
    (f : Z →ₐ[ℚ] W)
    (hf : P.relations ≤ Q.relations.comap f)
    (z : Z) :
    P.map Q f hf (P.classMap z) =
      Q.classMap (f z) :=
  rfl

end CorrespondenceAlgebraPresentation

namespace SchemeCorrespondence

variable {T X : Scheme.{u}} (pX : X ⟶ T)

/--
Raw generic and compactified correspondence algebras whose relation
quotients form a `RationalChowCorrespondenceModel`.

The generic algebra should be an admissible/proper-support or
finite-cover-generated algebra on which convolution is defined.  The
restriction and action compatibility fields are explicit because neither is
automatic for arbitrary cycles on an open locus.
-/
structure PresentedRationalChowCorrespondenceModel
    (genericRaw : Type v)
    (compactifiedRaw : Type w)
    (V : Type z)
    [Ring genericRaw] [Algebra ℚ genericRaw]
    [Ring compactifiedRaw] [Algebra ℚ compactifiedRaw]
    [AddCommGroup V] [Module ℚ V] where
  genericPresentation :
    CorrespondenceAlgebraPresentation genericRaw
  compactifiedPresentation :
    CorrespondenceAlgebraPresentation compactifiedRaw
  genericCycleRaw :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ] genericRaw
  rawRestriction :
    compactifiedRaw →ₐ[ℚ] genericRaw
  restriction_respects :
    compactifiedPresentation.relations ≤
      genericPresentation.relations.comap rawRestriction
  rawCohomologicalAction :
    compactifiedRaw →ₐ[ℚ] Module.End ℚ V
  action_kills_relations :
    ∀ z : compactifiedRaw,
      z ∈ compactifiedPresentation.relations →
        rawCohomologicalAction z = 0

namespace PresentedRationalChowCorrespondenceModel

variable {pX : X ⟶ T}
variable {genericRaw : Type v}
variable {compactifiedRaw : Type w}
variable {V : Type z}
variable [Ring genericRaw] [Algebra ℚ genericRaw]
variable [Ring compactifiedRaw] [Algebra ℚ compactifiedRaw]
variable [AddCommGroup V] [Module ℚ V]

/-- The generic relation quotient. -/
abbrev GenericAlgebra
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V) :=
  M.genericPresentation.QuotientAlgebra

/-- The compactified relation quotient. -/
abbrev CompactifiedAlgebra
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V) :=
  M.compactifiedPresentation.QuotientAlgebra

/-- Finite-étale spans acquire their generic quotient classes. -/
def genericCycleClass
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V) :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ] M.GenericAlgebra :=
  M.genericPresentation.classMap.comp M.genericCycleRaw

/-- Raw restriction descends to the two relation quotients. -/
def restriction
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V) :
    M.CompactifiedAlgebra →ₐ[ℚ] M.GenericAlgebra :=
  M.compactifiedPresentation.map
    M.genericPresentation M.rawRestriction M.restriction_respects

/-- The raw cohomological action descends through the compactified relations. -/
def cohomologicalAction
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V) :
    RationalCorrespondenceAction M.CompactifiedAlgebra V where
  action :=
    M.compactifiedPresentation.lift
      M.rawCohomologicalAction M.action_kills_relations

/-- The relation presentation canonically supplies the abstract Chow model. -/
def toRationalChowCorrespondenceModel
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V) :
    RationalChowCorrespondenceModel
      pX M.GenericAlgebra M.CompactifiedAlgebra V where
  genericCycleClass := M.genericCycleClass
  restriction := M.restriction
  cohomologicalAction := M.cohomologicalAction

@[simp]
theorem genericCycleClass_apply
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V)
    (c : FiniteEtaleFreeAlgebra pX) :
    M.genericCycleClass c =
      M.genericPresentation.classMap (M.genericCycleRaw c) :=
  rfl

@[simp]
theorem restriction_classMap_apply
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V)
    (z : compactifiedRaw) :
    M.restriction (M.compactifiedPresentation.classMap z) =
      M.genericPresentation.classMap (M.rawRestriction z) :=
  rfl

@[simp]
theorem cohomologicalAction_classMap_apply
    (M :
      PresentedRationalChowCorrespondenceModel
        pX genericRaw compactifiedRaw V)
    (z : compactifiedRaw) :
    M.cohomologicalAction.action
        (M.compactifiedPresentation.classMap z) =
      M.rawCohomologicalAction z :=
  rfl

end PresentedRationalChowCorrespondenceModel

end SchemeCorrespondence

end

end HodgeConjecture
