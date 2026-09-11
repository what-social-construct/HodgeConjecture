import HodgeConjecture.Correspondence.Etale
import HodgeConjecture.Correspondence.Linearized

/-!
# Isomorphism classes and algebra of finite étale correspondences

Finite-étale admissibility is invariant under correspondence isomorphism and
closed under the diagonal identity and fiber-product composition.  It
therefore descends from raw scheme spans to a submonoid of strict
correspondence classes.

The monoid algebra of that submonoid is the free rational algebra on finite
étale scheme correspondences.  As with the ambient free span algebra, it
does not yet impose disjoint-union additivity or rational equivalence.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X Y : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S}

/-- Finite-étale admissibility as a well-defined predicate on span classes. -/
def classHasFiniteEtaleLegs :
    Class pX pY → Prop :=
  Quotient.lift
    (fun P => HasFiniteEtaleLegs P)
    (by
      intro P Q h
      apply propext
      obtain ⟨e⟩ := h
      exact HasFiniteEtaleLegs.isom_iff e)

@[simp]
theorem classHasFiniteEtaleLegs_classOf
    (P : SchemeCorrespondence pX pY) :
    classHasFiniteEtaleLegs (classOf P) ↔
      HasFiniteEtaleLegs P :=
  Iff.rfl

/-- Finite étale endocorrespondence classes form a convolution submonoid. -/
noncomputable def finiteEtaleClassSubmonoid
    (pX : X ⟶ S) :
    Submonoid (Class pX pX) where
  carrier := { c | classHasFiniteEtaleLegs c }
  one_mem' := by
    change
      classHasFiniteEtaleLegs
        (classOf (identity pX))
    exact HasFiniteEtaleLegs.identity pX
  mul_mem' := by
    intro a b ha hb
    revert ha hb
    refine Quotient.inductionOn₂ a b ?_
    intro Q P hQ hP
    exact hQ.comp hP

/-- The type of finite étale endocorrespondence classes. -/
abbrev FiniteEtaleClass
    (pX : X ⟶ S) :=
  finiteEtaleClassSubmonoid pX

/-- A literal finite étale correspondence as an admissible class. -/
def finiteEtaleClassOf
    (P : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P) :
    FiniteEtaleClass pX :=
  ⟨classOf P, hP⟩

/--
The free rational algebra on finite étale endocorrespondence classes.
-/
abbrev FiniteEtaleFreeAlgebra
    (pX : X ⟶ S) :=
  MonoidAlgebra ℚ (FiniteEtaleClass pX)

/-- A literal finite étale correspondence as a basis vector. -/
def finiteEtaleOfScheme
    (P : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P) :
    FiniteEtaleFreeAlgebra pX :=
  MonoidAlgebra.single (finiteEtaleClassOf P hP) 1

/--
The finite étale free algebra maps naturally to the unrestricted free span
algebra by forgetting admissibility evidence.
-/
def finiteEtaleFreeAlgebraMap
    (pX : X ⟶ S) :
    FiniteEtaleFreeAlgebra pX →ₐ[ℚ] FreeAlgebra pX :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ
    (finiteEtaleClassSubmonoid pX).subtype

@[simp]
theorem finiteEtaleFreeAlgebraMap_ofScheme
    (P : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P) :
    finiteEtaleFreeAlgebraMap pX
        (finiteEtaleOfScheme P hP) =
      ofScheme pX P := by
  simp [finiteEtaleFreeAlgebraMap,
    finiteEtaleOfScheme, finiteEtaleClassOf,
    ofScheme, ofClass]

end SchemeCorrespondence

end

end HodgeConjecture
