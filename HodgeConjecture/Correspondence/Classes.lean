module

public import HodgeConjecture.Correspondence.Scheme

@[expose] public section

/-!
# Isomorphism classes of scheme correspondences

Raw scheme spans compose only up to canonical isomorphism.  This module
passes to carrier-isomorphism classes, where the diagonal span becomes a
strict unit and pullback composition becomes strictly associative.

For a fixed `X/S`, the resulting type of endocorrespondence classes is a
generally noncommutative monoid.  This is the multiplicative basis for the
free rational scheme-correspondence algebra constructed in the next module.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X Y Z : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}

/-- Two scheme correspondences are isomorphic when their carriers are
isomorphic compatibly with both legs. -/
def Isomorphic
    (P Q : SchemeCorrespondence pX pY) : Prop :=
  Nonempty (Isom P Q)

/-- Carrier-compatible isomorphism is an equivalence relation. -/
instance isomorphicSetoid :
    Setoid (SchemeCorrespondence pX pY) where
  r := Isomorphic
  iseqv := {
    refl := fun P => ⟨Isom.refl P⟩
    symm := fun {_ _} h => by
      obtain ⟨e⟩ := h
      exact ⟨e.symm⟩
    trans := fun {_ _ _} h h' => by
      obtain ⟨e⟩ := h
      obtain ⟨e'⟩ := h'
      exact ⟨e.trans e'⟩
  }

/-- Isomorphism classes of scheme correspondences from `X` to `Y` over `S`. -/
abbrev Class (pX : X ⟶ S) (pY : Y ⟶ S) :=
  Quotient (isomorphicSetoid (pX := pX) (pY := pY))

/-- The isomorphism class represented by a scheme correspondence. -/
def classOf
    (P : SchemeCorrespondence pX pY) :
    Class pX pY :=
  Quotient.mk' P

/-- Isomorphic correspondences define the same class. -/
theorem classOf_eq_of_isom
    {P Q : SchemeCorrespondence pX pY}
    (e : Isom P Q) :
    classOf P = classOf Q :=
  Quotient.sound ⟨e⟩

/--
Composition on isomorphism classes.  The first argument acts after the
second, matching multiplication of endomorphisms.
-/
noncomputable def classComp :
    Class pY pZ → Class pX pY → Class pX pZ :=
  Quotient.lift₂
    (fun Q P => classOf (Q.comp P))
    (by
      intro Q P Q' P' hQ hP
      apply Quotient.sound
      obtain ⟨eQ⟩ := hQ
      obtain ⟨eP⟩ := hP
      exact ⟨Isom.comp eQ eP⟩)

@[simp]
theorem classComp_classOf
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    classComp (classOf Q) (classOf P) =
      classOf (Q.comp P) :=
  rfl

section Endocorrespondences

variable (pX)

/-- The diagonal/identity correspondence class. -/
noncomputable def classOne :
    Class pX pX :=
  classOf (identity pX)

/--
The monoid of scheme endocorrespondence classes under pullback
composition.  Multiplication is generally noncommutative.
-/
noncomputable instance classMonoid :
    Monoid (Class pX pX) where
  one := classOne pX
  mul := classComp
  one_mul a := by
    refine Quotient.inductionOn a ?_
    intro P
    exact
      classOf_eq_of_isom
        (identityCompIsom P)
  mul_one a := by
    refine Quotient.inductionOn a ?_
    intro P
    exact
      classOf_eq_of_isom
        (compIdentityIsom P)
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro P Q R
    exact
      classOf_eq_of_isom
        (assocIsom P Q R).symm

@[simp]
theorem classOf_identity :
    classOf (identity pX) = (1 : Class pX pX) :=
  rfl

@[simp]
theorem classOf_comp
    (Q P : SchemeCorrespondence pX pX) :
    classOf (Q.comp P) =
      classOf Q * classOf P :=
  rfl

end Endocorrespondences

end SchemeCorrespondence

end

end HodgeConjecture
