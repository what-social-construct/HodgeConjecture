module

public import HodgeConjecture.Correspondence.Classes
public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section

/-!
# Free rational algebra on scheme correspondences

For a fixed `X/S`, isomorphism classes of scheme endocorrespondences form a
generally noncommutative monoid under pullback composition.  Its monoid
algebra over `ℚ` is the free rational scheme-correspondence algebra.

This construction is intentionally *free*.  In particular, it does not
identify the class of a disjoint union with the sum of the classes of its
components:

`[P ⨿ Q] = [P] + [Q]`

is an additional cycle-additivity relation.  Likewise, no rational
equivalence or refined-intersection relation is imposed here.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/--
The free rational algebra on isomorphism classes of scheme
endocorrespondences of `X/S`.
-/
abbrev FreeAlgebra :=
  MonoidAlgebra ℚ (Class pX pX)

/-- A correspondence class as a basis element of the free rational algebra. -/
def ofClass
    (c : Class pX pX) :
    FreeAlgebra pX :=
  MonoidAlgebra.single c 1

/-- A literal scheme correspondence as a basis element. -/
def ofScheme
    (P : SchemeCorrespondence pX pX) :
    FreeAlgebra pX :=
  ofClass pX (classOf P)

@[simp]
theorem ofClass_one :
    ofClass pX 1 = 1 := by
  rw [MonoidAlgebra.one_def]
  rfl

@[simp]
theorem ofClass_mul
    (a b : Class pX pX) :
    ofClass pX (a * b) =
      ofClass pX a * ofClass pX b := by
  simp [ofClass, MonoidAlgebra.single_mul_single]

@[simp]
theorem ofScheme_identity :
    ofScheme pX (identity pX) = 1 := by
  simp [ofScheme]

@[simp]
theorem ofScheme_comp
    (Q P : SchemeCorrespondence pX pX) :
    ofScheme pX (Q.comp P) =
      ofScheme pX Q * ofScheme pX P := by
  simp [ofScheme]

/--
The formal defect of disjoint-union additivity.  A Chow or additive
correspondence realization must send this element to zero.
-/
def coprodAdditivityDefect
    (P Q : SchemeCorrespondence pX pX) :
    FreeAlgebra pX :=
  ofScheme pX (coprod P Q) -
    ofScheme pX P -
      ofScheme pX Q

end SchemeCorrespondence

end

end HodgeConjecture
