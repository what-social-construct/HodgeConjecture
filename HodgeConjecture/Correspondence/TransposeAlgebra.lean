import HodgeConjecture.Correspondence.Graph
import Mathlib.Algebra.MonoidAlgebra.Opposite
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RingTheory.RingInvo

/-!
# Transpose on the correspondence algebra

Transposing a span reverses its two legs.  Pullback symmetry therefore
identifies the transpose of a composite with the composite of the
transposes in reverse order:

`(Q.comp P)ᵗ ≅ Pᵗ.comp Qᵗ`.

This module descends that construction to isomorphism classes and then
extends it linearly to both the unrestricted and finite-etale free rational
correspondence algebras.  The resulting operations are genuine ring
involutions.  For graph correspondences transpose sends the graph of a deck
transformation to the graph of its inverse.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X Y Z : Scheme.{u}}
variable {pX : X ⟶ S} {pY : Y ⟶ S} {pZ : Z ⟶ S}

/-! ## Raw spans -/

/-- Transposing an isomorphism of correspondences transposes its source
and target correspondences. -/
def Isom.transpose
    {P Q : SchemeCorrespondence pX pY}
    (e : Isom P Q) :
    Isom P.transpose Q.transpose where
  carrierIso := e.carrierIso
  hom_left := e.hom_right
  hom_right := e.hom_left

/-- Transpose reverses pullback composition, up to the canonical symmetry
isomorphism of the two pullback factors. -/
noncomputable def transposeCompIsom
    (Q : SchemeCorrespondence pY pZ)
    (P : SchemeCorrespondence pX pY) :
    Isom (Q.comp P).transpose
      (P.transpose.comp Q.transpose) where
  carrierIso := pullbackSymmetry P.right Q.left
  hom_left := by
    simp [SchemeCorrespondence.comp, transpose]
  hom_right := by
    simp [SchemeCorrespondence.comp, transpose]

/-- The diagonal correspondence is fixed by transpose. -/
def transposeIdentityIsom (pX : X ⟶ S) :
    Isom (identity pX).transpose (identity pX) where
  carrierIso := Iso.refl X
  hom_left := by simp [transpose, identity]
  hom_right := by simp [transpose, identity]

/-! ## Isomorphism classes -/

/-- Transpose on isomorphism classes of correspondences. -/
noncomputable def classTranspose :
    Class pX pY → Class pY pX :=
  Quotient.lift
    (fun P ↦ classOf P.transpose)
    (by
      intro P Q h
      obtain ⟨e⟩ := h
      exact classOf_eq_of_isom e.transpose)

@[simp]
theorem classTranspose_classOf
    (P : SchemeCorrespondence pX pY) :
    classTranspose (classOf P) = classOf P.transpose :=
  rfl

@[simp]
theorem classTranspose_involutive
    (c : Class pX pY) :
    classTranspose (classTranspose c) = c := by
  refine Quotient.inductionOn c ?_
  intro P
  change classOf P.transpose.transpose = classOf P
  rw [transpose_transpose]

/-- Transpose is an equivalence between the two directions of
correspondence classes. -/
noncomputable def classTransposeEquiv :
    Class pX pY ≃ Class pY pX where
  toFun := classTranspose
  invFun := classTranspose
  left_inv := classTranspose_involutive
  right_inv := classTranspose_involutive

/-- Finite-etale admissibility is invariant under transpose at the level of
isomorphism classes. -/
@[simp]
theorem classHasFiniteEtaleLegs_transpose
    (c : Class pX pY) :
    classHasFiniteEtaleLegs (classTranspose c) ↔
      classHasFiniteEtaleLegs c := by
  refine Quotient.inductionOn c ?_
  intro P
  change HasFiniteEtaleLegs P.transpose ↔
    HasFiniteEtaleLegs P
  constructor
  · intro hP
    simpa only [transpose_transpose] using hP.transpose
  · exact HasFiniteEtaleLegs.transpose

@[simp]
theorem classTranspose_classComp
    (q : Class pY pZ) (p : Class pX pY) :
    classTranspose (classComp q p) =
      classComp (classTranspose p) (classTranspose q) := by
  refine Quotient.inductionOn₂ q p ?_
  intro Q P
  exact classOf_eq_of_isom (transposeCompIsom Q P)

section Endocorrespondences

variable (pX)

@[simp]
theorem classTranspose_one :
    classTranspose (1 : Class pX pX) = 1 :=
  classOf_eq_of_isom (transposeIdentityIsom pX)

@[simp]
theorem classTranspose_mul
    (a b : Class pX pX) :
    classTranspose (a * b) =
      classTranspose b * classTranspose a :=
  classTranspose_classComp a b

/-- Transpose as a multiplicative equivalence from correspondence classes
to their opposite monoid. -/
noncomputable def classTransposeMulEquiv :
    Class pX pX ≃* (Class pX pX)ᵐᵒᵖ where
  toFun c := MulOpposite.op (classTranspose c)
  invFun c := classTranspose c.unop
  left_inv := classTranspose_involutive
  right_inv c := by
    apply MulOpposite.unop_injective
    exact classTranspose_involutive c.unop
  map_mul' a b := by
    apply MulOpposite.unop_injective
    exact classTranspose_mul pX a b

/-! ## Finite-etale classes -/

/-- Transpose on finite-etale correspondence classes. -/
noncomputable def finiteEtaleClassTranspose
    (c : FiniteEtaleClass pX) :
    FiniteEtaleClass pX :=
  ⟨classTranspose c.1,
    (classHasFiniteEtaleLegs_transpose c.1).2 c.2⟩

@[simp]
theorem finiteEtaleClassTranspose_val
    (c : FiniteEtaleClass pX) :
    (finiteEtaleClassTranspose pX c).1 =
      classTranspose c.1 :=
  rfl

@[simp]
theorem finiteEtaleClassTranspose_involutive
    (c : FiniteEtaleClass pX) :
    finiteEtaleClassTranspose pX
        (finiteEtaleClassTranspose pX c) = c := by
  apply Subtype.ext
  exact classTranspose_involutive c.1

/-- Transpose as an involutive equivalence of finite-etale classes. -/
noncomputable def finiteEtaleClassTransposeEquiv :
    FiniteEtaleClass pX ≃ FiniteEtaleClass pX where
  toFun := finiteEtaleClassTranspose pX
  invFun := finiteEtaleClassTranspose pX
  left_inv := finiteEtaleClassTranspose_involutive pX
  right_inv := finiteEtaleClassTranspose_involutive pX

@[simp]
theorem finiteEtaleClassTranspose_one :
    finiteEtaleClassTranspose pX
        (1 : FiniteEtaleClass pX) = 1 := by
  apply Subtype.ext
  exact classTranspose_one pX

@[simp]
theorem finiteEtaleClassTranspose_mul
    (a b : FiniteEtaleClass pX) :
    finiteEtaleClassTranspose pX (a * b) =
      finiteEtaleClassTranspose pX b *
        finiteEtaleClassTranspose pX a := by
  apply Subtype.ext
  exact classTranspose_mul pX a.1 b.1

/-- Transpose as a multiplicative equivalence from finite-etale classes to
their opposite monoid. -/
noncomputable def finiteEtaleClassTransposeMulEquiv :
    FiniteEtaleClass pX ≃* (FiniteEtaleClass pX)ᵐᵒᵖ where
  toFun c := MulOpposite.op
    (finiteEtaleClassTranspose pX c)
  invFun c := finiteEtaleClassTranspose pX c.unop
  left_inv := finiteEtaleClassTranspose_involutive pX
  right_inv c := by
    apply MulOpposite.unop_injective
    exact finiteEtaleClassTranspose_involutive pX c.unop
  map_mul' a b := by
    apply MulOpposite.unop_injective
    exact finiteEtaleClassTranspose_mul pX a b

@[simp]
theorem finiteEtaleClassTranspose_ofScheme
    (P : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P) :
    finiteEtaleClassTranspose pX
        (finiteEtaleClassOf P hP) =
      finiteEtaleClassOf P.transpose hP.transpose := by
  apply Subtype.ext
  rfl

/-! ## Free rational algebra -/

/-- The linear extension of transpose to the free rational
correspondence algebra. -/
noncomputable def freeTransposeLinearEquiv :
    FreeAlgebra pX ≃ₗ[ℚ] FreeAlgebra pX :=
  Finsupp.domLCongr
    (classTransposeEquiv (pX := pX) (pY := pX))

@[simp]
theorem freeTranspose_ofClass
    (c : Class pX pX) :
    freeTransposeLinearEquiv pX (ofClass pX c) =
      ofClass pX (classTranspose c) := by
  change
    Finsupp.equivMapDomain
        (classTransposeEquiv (pX := pX) (pY := pX))
        (MonoidAlgebra.single c 1) =
      MonoidAlgebra.single (classTranspose c) 1
  exact Finsupp.equivMapDomain_single _ _ _

@[simp]
theorem freeTranspose_single
    (c : Class pX pX) (r : ℚ) :
    freeTransposeLinearEquiv pX
        (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (classTranspose c) r := by
  change
    Finsupp.equivMapDomain
        (classTransposeEquiv (pX := pX) (pY := pX))
        (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (classTranspose c) r
  exact Finsupp.equivMapDomain_single _ _ _

@[simp]
theorem freeTranspose_ofScheme
    (P : SchemeCorrespondence pX pX) :
    freeTransposeLinearEquiv pX (ofScheme pX P) =
      ofScheme pX P.transpose := by
  simp [ofScheme]

@[simp]
theorem freeTranspose_one :
    freeTransposeLinearEquiv pX 1 = 1 := by
  calc
    freeTransposeLinearEquiv pX 1 =
        freeTransposeLinearEquiv pX
          (ofClass pX (1 : Class pX pX)) := by
            rw [ofClass_one]
    _ = ofClass pX (classTranspose (1 : Class pX pX)) :=
      freeTranspose_ofClass pX 1
    _ = ofClass pX (1 : Class pX pX) := by
      rw [classTranspose_one]
    _ = 1 := ofClass_one pX

/-- The linear transpose reverses convolution. -/
theorem freeTranspose_mul
    (a b : FreeAlgebra pX) :
    freeTransposeLinearEquiv pX (a * b) =
      freeTransposeLinearEquiv pX b *
        freeTransposeLinearEquiv pX a := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ ha₁ ha₂
    simp only [add_mul, map_add, ha₁, ha₂, mul_add]
  · intro c r
    refine MonoidAlgebra.induction_linear b ?_ ?_ ?_
    · simp
    · intro b₁ b₂ hb₁ hb₂
      simp only [mul_add, map_add, hb₁, hb₂, add_mul]
    · intro d s
      simp only [MonoidAlgebra.single_mul_single,
        freeTranspose_single, classTranspose_mul]
      rw [mul_comm r s]

@[simp]
theorem freeTranspose_involutive
    (a : FreeAlgebra pX) :
    freeTransposeLinearEquiv pX
        (freeTransposeLinearEquiv pX a) = a := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ ha₁ ha₂
    simp only [map_add, ha₁, ha₂]
  · intro c r
    simp only [freeTranspose_single,
      classTranspose_involutive]

/-- Transpose on the free rational correspondence algebra, packaged as a
ring involution into the opposite ring. -/
noncomputable def freeTransposeRingInvo :
    RingInvo (FreeAlgebra pX) where
  toFun a := MulOpposite.op (freeTransposeLinearEquiv pX a)
  invFun a := freeTransposeLinearEquiv pX a.unop
  left_inv := freeTranspose_involutive pX
  right_inv a := by
    apply MulOpposite.unop_injective
    exact freeTranspose_involutive pX a.unop
  map_add' a b := by
    apply MulOpposite.unop_injective
    exact (freeTransposeLinearEquiv pX).map_add a b
  map_mul' a b := by
    apply MulOpposite.unop_injective
    exact freeTranspose_mul pX a b
  involution' := freeTranspose_involutive pX

/-! ## Finite-etale free rational algebra -/

/-- The linear extension of transpose to the finite-etale free
correspondence algebra. -/
noncomputable def finiteEtaleFreeTransposeLinearEquiv :
    FiniteEtaleFreeAlgebra pX ≃ₗ[ℚ]
      FiniteEtaleFreeAlgebra pX :=
  Finsupp.domLCongr (finiteEtaleClassTransposeEquiv pX)

@[simp]
theorem finiteEtaleFreeTranspose_single
    (c : FiniteEtaleClass pX) (r : ℚ) :
    finiteEtaleFreeTransposeLinearEquiv pX
        (MonoidAlgebra.single c r) =
      MonoidAlgebra.single
        (finiteEtaleClassTranspose pX c) r := by
  change
    Finsupp.equivMapDomain
        (finiteEtaleClassTransposeEquiv pX)
        (MonoidAlgebra.single c r) =
      MonoidAlgebra.single
        (finiteEtaleClassTranspose pX c) r
  exact Finsupp.equivMapDomain_single _ _ _

@[simp]
theorem finiteEtaleFreeTranspose_ofScheme
    (P : SchemeCorrespondence pX pX)
    (hP : HasFiniteEtaleLegs P) :
    finiteEtaleFreeTransposeLinearEquiv pX
        (finiteEtaleOfScheme P hP) =
      finiteEtaleOfScheme P.transpose hP.transpose := by
  simp [finiteEtaleOfScheme]

@[simp]
theorem finiteEtaleFreeTranspose_one :
    finiteEtaleFreeTransposeLinearEquiv pX 1 = 1 := by
  change
    finiteEtaleFreeTransposeLinearEquiv pX
        (MonoidAlgebra.single 1 1) =
      MonoidAlgebra.single 1 1
  rw [finiteEtaleFreeTranspose_single,
    finiteEtaleClassTranspose_one]

/-- The finite-etale linear transpose reverses convolution. -/
theorem finiteEtaleFreeTranspose_mul
    (a b : FiniteEtaleFreeAlgebra pX) :
    finiteEtaleFreeTransposeLinearEquiv pX (a * b) =
      finiteEtaleFreeTransposeLinearEquiv pX b *
        finiteEtaleFreeTransposeLinearEquiv pX a := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ ha₁ ha₂
    simp only [add_mul, map_add, ha₁, ha₂, mul_add]
  · intro c r
    refine MonoidAlgebra.induction_linear b ?_ ?_ ?_
    · simp
    · intro b₁ b₂ hb₁ hb₂
      simp only [mul_add, map_add, hb₁, hb₂, add_mul]
    · intro d s
      simp only [MonoidAlgebra.single_mul_single,
        finiteEtaleFreeTranspose_single,
        finiteEtaleClassTranspose_mul]
      rw [mul_comm r s]

@[simp]
theorem finiteEtaleFreeTranspose_involutive
    (a : FiniteEtaleFreeAlgebra pX) :
    finiteEtaleFreeTransposeLinearEquiv pX
        (finiteEtaleFreeTransposeLinearEquiv pX a) = a := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp
  · intro a₁ a₂ ha₁ ha₂
    simp only [map_add, ha₁, ha₂]
  · intro c r
    simp only [finiteEtaleFreeTranspose_single,
      finiteEtaleClassTranspose_involutive]

/-- Transpose on the finite-etale free algebra, packaged as a ring
involution into the opposite ring. -/
noncomputable def finiteEtaleFreeTransposeRingInvo :
    RingInvo (FiniteEtaleFreeAlgebra pX) where
  toFun a := MulOpposite.op
    (finiteEtaleFreeTransposeLinearEquiv pX a)
  invFun a := finiteEtaleFreeTransposeLinearEquiv pX a.unop
  left_inv := finiteEtaleFreeTranspose_involutive pX
  right_inv a := by
    apply MulOpposite.unop_injective
    exact finiteEtaleFreeTranspose_involutive pX a.unop
  map_add' a b := by
    apply MulOpposite.unop_injective
    exact
      (finiteEtaleFreeTransposeLinearEquiv pX).map_add a b
  map_mul' a b := by
    apply MulOpposite.unop_injective
    exact finiteEtaleFreeTranspose_mul pX a b
  involution' := finiteEtaleFreeTranspose_involutive pX

end Endocorrespondences

/-! ## Graph correspondences -/

/-- The transpose of a graph is isomorphic to the graph of the inverse
deck transformation. -/
def graphTransposeIsom
    (pX : X ⟶ S) (sigma : DeckTransformation pX) :
    Isom (graph pX sigma).transpose (graph pX sigma⁻¹) where
  carrierIso := Comma.leftIso sigma
  hom_left := by
    simp [graph, transpose]
  hom_right := by
    change sigma.hom.left ≫ sigma.inv.left = 𝟙 X
    exact Over.hom_left_inv_left sigma

@[simp]
theorem classTranspose_graph
    (pX : X ⟶ S) (sigma : DeckTransformation pX) :
    classTranspose (classOf (graph pX sigma)) =
      classOf (graph pX sigma⁻¹) :=
  classOf_eq_of_isom (graphTransposeIsom pX sigma)

@[simp]
theorem freeTranspose_graph
    (pX : X ⟶ S) (sigma : DeckTransformation pX) :
    freeTransposeLinearEquiv pX (ofScheme pX (graph pX sigma)) =
      ofScheme pX (graph pX sigma⁻¹) := by
  rw [freeTranspose_ofScheme]
  change
    ofClass pX (classOf (graph pX sigma).transpose) =
      ofClass pX (classOf (graph pX sigma⁻¹))
  rw [classOf_eq_of_isom (graphTransposeIsom pX sigma)]

@[simp]
theorem finiteEtaleClassTranspose_graph
    (pX : X ⟶ S) (sigma : DeckTransformation pX) :
    finiteEtaleClassTranspose pX
        (graphFiniteEtaleClass pX sigma) =
      graphFiniteEtaleClass pX sigma⁻¹ := by
  apply Subtype.ext
  exact classTranspose_graph pX sigma

@[simp]
theorem finiteEtaleFreeTranspose_graph
    (pX : X ⟶ S) (sigma : DeckTransformation pX) :
    finiteEtaleFreeTransposeLinearEquiv pX
        (finiteEtaleOfScheme
          (graph pX sigma)
          (graph_hasFiniteEtaleLegs pX sigma)) =
      finiteEtaleOfScheme
        (graph pX sigma⁻¹)
        (graph_hasFiniteEtaleLegs pX sigma⁻¹) := by
  change
    finiteEtaleFreeTransposeLinearEquiv pX
        (MonoidAlgebra.single
          (graphFiniteEtaleClass pX sigma) 1) =
      MonoidAlgebra.single
        (graphFiniteEtaleClass pX sigma⁻¹) 1
  rw [finiteEtaleFreeTranspose_single,
    finiteEtaleClassTranspose_graph]

end SchemeCorrespondence

end

end HodgeConjecture
