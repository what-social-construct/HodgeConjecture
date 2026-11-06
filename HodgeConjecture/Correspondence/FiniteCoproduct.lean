module

public import HodgeConjecture.Correspondence.Algebra

@[expose] public section

/-!
# Finite coproducts of scheme correspondences

A finite family of spans with the same source and target has a literal
scheme-theoretic coproduct.  This is the geometric object used below to
express a split collision relation as the disjoint union of its graph
sheets.

Binary coproduct additivity is already part of `AdditiveClassMap`.  For an
indexed coproduct it is convenient to record the corresponding finite-sum
law as a separate compatibility property.  This remains an interface for a
cycle theory: it does not assert that the free span algebra itself identifies
disjoint unions with sums.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

noncomputable section

universe u v

namespace SchemeCorrespondence

variable {S X Y : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S}

/--
The indexed disjoint union of a family of scheme correspondences.

Its carrier is the categorical coproduct of the carriers, and its two legs
are induced componentwise.
-/
def indexedCoprod
    {ι : Type u}
    (P : ι → SchemeCorrespondence pX pY) :
    SchemeCorrespondence pX pY where
  carrier := ∐ fun i ↦ (P i).carrier
  left := Sigma.desc fun i ↦ (P i).left
  right := Sigma.desc fun i ↦ (P i).right
  over_base := by
    apply Sigma.hom_ext
    intro i
    simp [(P i).over_base]

@[simp]
theorem indexedCoprod_carrier
    {ι : Type u}
    (P : ι → SchemeCorrespondence pX pY) :
    (indexedCoprod P).carrier =
      ∐ fun i ↦ (P i).carrier :=
  rfl

/-- The inclusion of one component into an indexed coproduct span. -/
def indexedCoprodIn
    {ι : Type u}
    (P : ι → SchemeCorrespondence pX pY)
    (i : ι) :
    (P i).carrier ⟶ (indexedCoprod P).carrier :=
  Sigma.ι (fun j ↦ (P j).carrier) i

@[reassoc (attr := simp)]
theorem indexedCoprodIn_left
    {ι : Type u}
    (P : ι → SchemeCorrespondence pX pY)
    (i : ι) :
    indexedCoprodIn P i ≫ (indexedCoprod P).left =
      (P i).left := by
  simp [indexedCoprodIn, indexedCoprod]

@[reassoc (attr := simp)]
theorem indexedCoprodIn_right
    {ι : Type u}
    (P : ι → SchemeCorrespondence pX pY)
    (i : ι) :
    indexedCoprodIn P i ≫ (indexedCoprod P).right =
      (P i).right := by
  simp [indexedCoprodIn, indexedCoprod]

namespace AdditiveClassMap

variable {Γ : Type v} [AddCommMonoid Γ] [One Γ]

/--
Compatibility of an additive class assignment with finite indexed
coproducts.

This is stated separately from `AdditiveClassMap`, whose primitive geometric
operation is binary coproduct.  A concrete cycle model can supply the
property without being repackaged as a new algebra model.
-/
structure PreservesFiniteIndexedCoproducts
    (χ : AdditiveClassMap pX Γ) : Prop where
  classOf_indexedCoprod :
    ∀ {ι : Type u} [Fintype ι]
      (P : ι → SchemeCorrespondence pX pX),
      χ.classOf (indexedCoprod P) =
        ∑ i, χ.classOf (P i)

/-- An isomorphic finite sheet decomposition becomes a finite sum of classes. -/
theorem classOf_eq_sum_of_isom_indexedCoprod
    (χ : AdditiveClassMap pX Γ)
    (hχ : χ.PreservesFiniteIndexedCoproducts)
    {ι : Type u} [Fintype ι]
    {R : SchemeCorrespondence pX pX}
    (P : ι → SchemeCorrespondence pX pX)
    (e : Isom R (indexedCoprod P)) :
    χ.classOf R = ∑ i, χ.classOf (P i) := by
  rw [χ.classOf_isom e, hχ.classOf_indexedCoprod]

end AdditiveClassMap

end SchemeCorrespondence

end

end HodgeConjecture
