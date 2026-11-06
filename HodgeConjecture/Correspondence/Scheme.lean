module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

@[expose] public section

/-!
# Scheme correspondences over a base

A scheme correspondence from `X` to `Y`, relative to a base scheme `S`, is
a span

`X ← Z → Y`

whose two structure maps agree after composition to `S`.  Equivalently, its
carrier maps to `X ×[S] Y`.

Correspondences compose by pullback over the middle scheme.  The identity
correspondence is the diagonal span `X ← X → X`, and disjoint union is the
scheme-level precursor of addition of cycle classes.

Composition of raw spans is associative and unital only up to canonical
isomorphism.  This module therefore does not force these spans into a strict
ring.  A later algebraic layer records passage to isomorphism-invariant
classes, where disjoint union becomes addition and pullback composition
becomes convolution.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S X Y T : Scheme.{u}}

/--
A scheme correspondence from `X` to `Y` over `S`.

The equality `over_base` is precisely the condition needed for the carrier
to map to the relative product `X ×[S] Y`.
-/
structure SchemeCorrespondence (pX : X ⟶ S) (pY : Y ⟶ S) where
  carrier : Scheme.{u}
  left : carrier ⟶ X
  right : carrier ⟶ Y
  over_base : left ≫ pX = right ≫ pY

namespace SchemeCorrespondence

variable {pX : X ⟶ S} {pY : Y ⟶ S}

/-- The support map of a scheme correspondence into `X ×[S] Y`. -/
def toAmbientProduct
    (Z : SchemeCorrespondence pX pY) :
    Z.carrier ⟶ pullback pX pY :=
  pullback.lift Z.left Z.right Z.over_base

@[reassoc (attr := simp)]
theorem toAmbientProduct_fst
    (Z : SchemeCorrespondence pX pY) :
    Z.toAmbientProduct ≫ pullback.fst pX pY = Z.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem toAmbientProduct_snd
    (Z : SchemeCorrespondence pX pY) :
    Z.toAmbientProduct ≫ pullback.snd pX pY = Z.right :=
  pullback.lift_snd _ _ _

/--
The identity correspondence of `X/S`.  Its support map to `X ×[S] X` is
the relative diagonal.
-/
def identity (pX : X ⟶ S) :
    SchemeCorrespondence pX pX where
  carrier := X
  left := 𝟙 X
  right := 𝟙 X
  over_base := rfl

@[simp]
theorem identity_carrier (pX : X ⟶ S) :
    (identity pX).carrier = X :=
  rfl

@[simp]
theorem identity_left (pX : X ⟶ S) :
    (identity pX).left = 𝟙 X :=
  rfl

@[simp]
theorem identity_right (pX : X ⟶ S) :
    (identity pX).right = 𝟙 X :=
  rfl

/-- The identity support map is the relative diagonal. -/
theorem identity_toAmbientProduct (pX : X ⟶ S) :
    (identity pX).toAmbientProduct = pullback.diagonal pX := by
  apply pullback.hom_ext <;> simp

/-- Reverse the two legs of a scheme correspondence. -/
def transpose
    (Z : SchemeCorrespondence pX pY) :
    SchemeCorrespondence pY pX where
  carrier := Z.carrier
  left := Z.right
  right := Z.left
  over_base := Z.over_base.symm

@[simp]
theorem transpose_transpose
    (Z : SchemeCorrespondence pX pY) :
    Z.transpose.transpose = Z := by
  cases Z
  rfl

section Composition

variable {Z : Scheme.{u}} {pZ : Z ⟶ S}

/--
Composition of scheme correspondences.

If `P : X ← P.carrier → Y` and `Q : Y ← Q.carrier → Z`, then
`Q.comp P` has carrier `P.carrier ×[Y] Q.carrier`.  This ordering matches
ring and endomorphism conventions: after passage to correspondence classes,
the intended formula is `[Q.comp P] = [Q] * [P]`.
-/
def comp
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    SchemeCorrespondence pX pZ where
  carrier := pullback P.right Q.left
  left := pullback.fst P.right Q.left ≫ P.left
  right := pullback.snd P.right Q.left ≫ Q.right
  over_base := by
    simp only [Category.assoc]
    rw [P.over_base, ← Category.assoc, pullback.condition]
    rw [Category.assoc, Q.over_base]

@[simp]
theorem comp_carrier
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    (Q.comp P).carrier = pullback P.right Q.left :=
  rfl

@[simp]
theorem comp_left
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    (Q.comp P).left =
      pullback.fst P.right Q.left ≫ P.left :=
  rfl

@[simp]
theorem comp_right
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    (Q.comp P).right =
      pullback.snd P.right Q.left ≫ Q.right :=
  rfl

end Composition

/--
An isomorphism of scheme correspondences: an isomorphism of carriers that
commutes with both legs.
-/
structure Isom
    (P Q : SchemeCorrespondence pX pY) where
  carrierIso : P.carrier ≅ Q.carrier
  hom_left : carrierIso.hom ≫ Q.left = P.left
  hom_right : carrierIso.hom ≫ Q.right = P.right

namespace Isom

/-- Identity isomorphism of a scheme correspondence. -/
def refl (P : SchemeCorrespondence pX pY) :
    Isom P P where
  carrierIso := Iso.refl _
  hom_left := by simp
  hom_right := by simp

/-- Reverse an isomorphism of scheme correspondences. -/
def symm {P Q : SchemeCorrespondence pX pY}
    (e : Isom P Q) :
    Isom Q P where
  carrierIso := e.carrierIso.symm
  hom_left := by
    rw [← e.hom_left]
    simp
  hom_right := by
    rw [← e.hom_right]
    simp

/-- Compose isomorphisms of scheme correspondences. -/
def trans {P Q R : SchemeCorrespondence pX pY}
    (e : Isom P Q) (e' : Isom Q R) :
    Isom P R where
  carrierIso := e.carrierIso ≪≫ e'.carrierIso
  hom_left := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [e'.hom_left, e.hom_left]
  hom_right := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [e'.hom_right, e.hom_right]

section Composition

variable {Z : Scheme.{u}} {pZ : Z ⟶ S}

/-- Composition of scheme correspondences respects carrier isomorphisms. -/
noncomputable def comp
    {Q Q' : SchemeCorrespondence pY pZ}
    {P P' : SchemeCorrespondence pX pY}
    (eQ : Isom Q Q') (eP : Isom P P') :
    Isom (Q.comp P) (Q'.comp P') where
  carrierIso :=
    asIso
      (pullback.map
        P.right Q.left P'.right Q'.left
        eP.carrierIso.hom eQ.carrierIso.hom (𝟙 Y)
        (by simpa using eP.hom_right.symm)
        (by simpa using eQ.hom_left.symm))
  hom_left := by
    simp [SchemeCorrespondence.comp, eP.hom_left]
  hom_right := by
    simp [SchemeCorrespondence.comp, eQ.hom_right]

end Composition

end Isom

section UnitIsomorphisms

/-- Composing the identity of the target after `P` is canonically `P`. -/
noncomputable def identityCompIsom
    (P : SchemeCorrespondence pX pY) :
    Isom ((identity pY).comp P) P where
  carrierIso := asIso (pullback.fst P.right (𝟙 Y))
  hom_left := rfl
  hom_right := by
    simpa using pullback.condition (f := P.right) (g := 𝟙 Y)

/-- Composing `P` after the identity of the source is canonically `P`. -/
noncomputable def compIdentityIsom
    (P : SchemeCorrespondence pX pY) :
    Isom (P.comp (identity pX)) P where
  carrierIso := asIso (pullback.snd (𝟙 X) P.left)
  hom_left := by
    simpa using
      (pullback.condition (f := 𝟙 X) (g := P.left)).symm
  hom_right := rfl

end UnitIsomorphisms

section Associativity

variable {Z W : Scheme.{u}} {pZ : Z ⟶ S} {pW : W ⟶ S}

/--
Pullback composition is associative up to its canonical carrier
isomorphism.

After passage to isomorphism classes this becomes the strict associativity
law for convolution.
-/
noncomputable def assocIsom
    (R : SchemeCorrespondence pZ pW)
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    Isom (R.comp (Q.comp P)) ((R.comp Q).comp P) where
  carrierIso :=
    pullbackAssoc P.right Q.left Q.right R.left
  hom_left := by
    simp [comp]
  hom_right := by
    simp [comp]

end Associativity

section Coproduct

/--
Disjoint union of two scheme correspondences with the same source and
target.  This is the scheme-level operation that later maps to addition of
cycle or correspondence classes.
-/
def coprod
    (P Q : SchemeCorrespondence pX pY) :
    SchemeCorrespondence pX pY where
  carrier := P.carrier ⨿ Q.carrier
  left := coprod.desc P.left Q.left
  right := coprod.desc P.right Q.right
  over_base := by
    apply coprod.hom_ext
    · simp [P.over_base]
    · simp [Q.over_base]

@[simp]
theorem coprod_carrier
    (P Q : SchemeCorrespondence pX pY) :
    (coprod P Q).carrier = (P.carrier ⨿ Q.carrier) :=
  rfl

/-- The first summand maps to the coproduct correspondence. -/
def inl
    (P Q : SchemeCorrespondence pX pY) :
    P.carrier ⟶ (coprod P Q).carrier :=
  coprod.inl

/-- The second summand maps to the coproduct correspondence. -/
def inr
    (P Q : SchemeCorrespondence pX pY) :
    Q.carrier ⟶ (coprod P Q).carrier :=
  coprod.inr

@[reassoc (attr := simp)]
theorem inl_left
    (P Q : SchemeCorrespondence pX pY) :
    inl P Q ≫ (coprod P Q).left = P.left := by
  simp [inl, coprod]

@[reassoc (attr := simp)]
theorem inl_right
    (P Q : SchemeCorrespondence pX pY) :
    inl P Q ≫ (coprod P Q).right = P.right := by
  simp [inl, coprod]

@[reassoc (attr := simp)]
theorem inr_left
    (P Q : SchemeCorrespondence pX pY) :
    inr P Q ≫ (coprod P Q).left = Q.left := by
  simp [inr, coprod]

@[reassoc (attr := simp)]
theorem inr_right
    (P Q : SchemeCorrespondence pX pY) :
    inr P Q ≫ (coprod P Q).right = Q.right := by
  simp [inr, coprod]

end Coproduct

/--
The support map is proper.  This is a basic admissibility condition for
pushing the carrier's fundamental cycle to the ambient product.
-/
abbrev IsProperSupport
    (Z : SchemeCorrespondence pX pY) : Prop :=
  IsProper Z.toAmbientProduct

end SchemeCorrespondence

end

end HodgeConjecture
