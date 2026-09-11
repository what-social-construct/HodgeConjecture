import HodgeConjecture.Correspondence.Linearized

/-!
# Additive and convolution-compatible correspondence classes

The free rational scheme-correspondence algebra is formal.  Passing from
scheme spans to cycles requires additional geometry:

* isomorphic spans must have the same class;
* disjoint union must become addition;
* the diagonal must become the unit;
* pullback composition must agree with convolution.

This module records those requirements explicitly on the unrestricted span
type.  It does not construct Chow groups or claim that every raw span
satisfies the dimensional, properness, or refined-intersection hypotheses
needed to define such a class.  In particular, this broad interface is only
an exploratory theorem target: arbitrary spans include infinite coproducts,
so unrestricted additivity can collapse a ring-valued model.  The
finite-cover branch uses `FiniteEtaleAlgebraModel`, whose source is the
finite-étale admissible convolution algebra and whose additivity law is
restricted to finite coproducts.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry

noncomputable section

universe u v

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)
variable (Γ : Type v)

/--
An additive class assignment for scheme endocorrespondences.

This is the exact interface needed to turn a literal clopen decomposition
of schemes into an additive decomposition of correspondence classes.
-/
structure AdditiveClassMap
    [AddMonoid Γ] [One Γ] where
  classOf : SchemeCorrespondence pX pX → Γ
  classOf_isom :
    ∀ {P Q : SchemeCorrespondence pX pX},
      Isom P Q → classOf P = classOf Q
  classOf_identity :
    classOf (identity pX) = 1
  classOf_coprod :
    ∀ P Q : SchemeCorrespondence pX pX,
      classOf (coprod P Q) = classOf P + classOf Q

/--
A rational correspondence-algebra model on all scheme spans.

The final field is the nontrivial bridge from ordinary fiber products of
schemes to convolution.  Supplying this structure is a geometric input, not
an automatic consequence of a clopen selector in a coordinate ring.  For a
nontrivial cycle realization, prefer an admissible interface such as
`FiniteEtaleAlgebraModel` rather than this unrestricted structure.
-/
structure AlgebraModel
    [Ring Γ] [Algebra ℚ Γ]
    extends AdditiveClassMap pX Γ where
  classOf_comp :
    ∀ Q P : SchemeCorrespondence pX pX,
      classOf (Q.comp P) = classOf Q * classOf P

namespace AdditiveClassMap

variable [AddMonoid Γ] [One Γ]

/-- The additive decomposition induced by an isomorphism with a coproduct. -/
theorem classOf_eq_add_of_isom_coprod
    (χ : AdditiveClassMap pX Γ)
    {R P Q : SchemeCorrespondence pX pX}
    (e : Isom R (coprod P Q)) :
    χ.classOf R = χ.classOf P + χ.classOf Q := by
  rw [χ.classOf_isom e, χ.classOf_coprod]

end AdditiveClassMap

namespace AlgebraModel

variable [Ring Γ] [Algebra ℚ Γ]

/-- The value of an algebra model on an isomorphism class. -/
def classValue
    (χ : AlgebraModel pX Γ) :
    Class pX pX → Γ :=
  Quotient.lift χ.classOf
    (by
      intro P Q h
      obtain ⟨e⟩ := h
      exact χ.classOf_isom e)

@[simp]
theorem classValue_classOf
    (χ : AlgebraModel pX Γ)
    (P : SchemeCorrespondence pX pX) :
    classValue pX Γ χ (SchemeCorrespondence.classOf P) =
      χ.classOf P :=
  rfl

/-- The class assignment as a monoid homomorphism under convolution. -/
def classMonoidHom
    (χ : AlgebraModel pX Γ) :
    Class pX pX →* Γ where
  toFun := classValue pX Γ χ
  map_one' := by
    simpa [classOne] using χ.classOf_identity
  map_mul' := by
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro Q P
    exact χ.classOf_comp Q P

/--
The induced algebra homomorphism from the free rational
scheme-correspondence algebra.
-/
def freeAlgebraMap
    (χ : AlgebraModel pX Γ) :
    FreeAlgebra pX →ₐ[ℚ] Γ :=
  MonoidAlgebra.lift ℚ (Class pX pX) Γ
    (classMonoidHom pX Γ χ)

@[simp]
theorem freeAlgebraMap_ofScheme
    (χ : AlgebraModel pX Γ)
    (P : SchemeCorrespondence pX pX) :
    freeAlgebraMap pX Γ χ (ofScheme pX P) =
      χ.classOf P := by
  simp [freeAlgebraMap, ofScheme, ofClass, classMonoidHom]

/--
Disjoint-union additivity is exactly the assertion that every coproduct
defect dies under the cycle/convolution realization.
-/
@[simp]
theorem freeAlgebraMap_coprodAdditivityDefect
    (χ : AlgebraModel pX Γ)
    (P Q : SchemeCorrespondence pX pX) :
    freeAlgebraMap pX Γ χ
      (coprodAdditivityDefect pX P Q) = 0 := by
  simp [coprodAdditivityDefect, χ.classOf_coprod]

end AlgebraModel

end SchemeCorrespondence

end

end HodgeConjecture
