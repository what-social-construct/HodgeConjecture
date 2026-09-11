import HodgeConjecture.Collision.ComponentSelectors
import HodgeConjecture.Collision.GlobalGeometry

/-!
# Literal clopen collision decompositions

This module packages the scheme-level endpoint of the collision stage.
For `f : X ⟶ Y`, a `CollisionSchemeDecomposition f` is a literal
decomposition

`X ×[Y] X ≅ X ⨿ Rᵒᶠᶠ`

whose first component is the actual relative diagonal.

The associated component morphisms into `X × X`, or into `X ×[S] X` after
choosing a base `S`, are geometric inputs for a later cycle construction.
This file does not extract Chow classes and does not assert idempotence under
composition of correspondences.  Those statements use the convolution
algebra of correspondences on the ambient product, whose unit is the
diagonal class.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A literal decomposition of the self-collision scheme into the relative
diagonal and a complementary off-diagonal scheme.

The complement is recorded as a scheme because this is the precise output
of a clopen coordinate-ring idempotent.  No cycle or correspondence-ring
structure is included.
-/
structure CollisionSchemeDecomposition where
  offDiagonal : Scheme.{u}
  decomposition :
    collisionSpace f ≅ X ⨿ offDiagonal
  diagonal_hom :
    collisionDiagonal f ≫ decomposition.hom = coprod.inl

namespace CollisionSchemeDecomposition

variable {f}

/-- The diagonal component inclusion back into the collision space. -/
abbrev diagonalInclusion
    (_D : CollisionSchemeDecomposition f) :
    X ⟶ collisionSpace f :=
  collisionDiagonal f

/-- The complementary component inclusion back into the collision space. -/
def offDiagonalInclusion
    (D : CollisionSchemeDecomposition f) :
    D.offDiagonal ⟶ collisionSpace f :=
  coprod.inr ≫ D.decomposition.inv

/-- In decomposition coordinates, the off-diagonal inclusion is `coprod.inr`. -/
@[reassoc (attr := simp)]
theorem offDiagonalInclusion_decomposition_hom
    (D : CollisionSchemeDecomposition f) :
    D.offDiagonalInclusion ≫ D.decomposition.hom = coprod.inr := by
  simp [offDiagonalInclusion]

/-- The inverse decomposition map restricts to the actual relative diagonal. -/
@[reassoc]
theorem inl_decomposition_inv
    (D : CollisionSchemeDecomposition f) :
    coprod.inl ≫ D.decomposition.inv = collisionDiagonal f := by
  rw [← D.diagonal_hom]
  simp

private theorem coprodInl_isClosedImmersion
    (X Z : Scheme.{u}) :
    IsClosedImmersion (coprod.inl : X ⟶ X ⨿ Z) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [← (isCompl_range_inl_inr X Z).symm.compl_eq]
  exact
    (coprod.inr : Z ⟶ X ⨿ Z).isOpenEmbedding.isOpen_range.isClosed_compl

private theorem coprodInr_isClosedImmersion
    (X Z : Scheme.{u}) :
    IsClosedImmersion (coprod.inr : Z ⟶ X ⨿ Z) := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [← (isCompl_range_inl_inr X Z).compl_eq]
  exact
    (coprod.inl : X ⟶ X ⨿ Z).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The diagonal component of a collision decomposition is open. -/
instance diagonalInclusion_isOpenImmersion
    (D : CollisionSchemeDecomposition f) :
    IsOpenImmersion D.diagonalInclusion := by
  change IsOpenImmersion (collisionDiagonal f)
  rw [← D.inl_decomposition_inv]
  infer_instance

/-- The diagonal component of a collision decomposition is closed. -/
instance diagonalInclusion_isClosedImmersion
    (D : CollisionSchemeDecomposition f) :
    IsClosedImmersion D.diagonalInclusion := by
  change IsClosedImmersion (collisionDiagonal f)
  rw [← D.inl_decomposition_inv]
  letI : IsClosedImmersion
      (coprod.inl : X ⟶ X ⨿ D.offDiagonal) :=
    coprodInl_isClosedImmersion X D.offDiagonal
  infer_instance

/-- The off-diagonal component of a collision decomposition is open. -/
instance offDiagonalInclusion_isOpenImmersion
    (D : CollisionSchemeDecomposition f) :
    IsOpenImmersion D.offDiagonalInclusion := by
  dsimp [offDiagonalInclusion]
  infer_instance

/-- The off-diagonal component of a collision decomposition is closed. -/
instance offDiagonalInclusion_isClosedImmersion
    (D : CollisionSchemeDecomposition f) :
    IsClosedImmersion D.offDiagonalInclusion := by
  dsimp [offDiagonalInclusion]
  letI : IsClosedImmersion
      (coprod.inr :
        D.offDiagonal ⟶ X ⨿ D.offDiagonal) :=
    coprodInr_isClosedImmersion X D.offDiagonal
  infer_instance

/--
The off-diagonal component mapped to the absolute ambient product.

For varieties over a field, `offDiagonalToAmbientProduct` below is normally
the relevant map, since correspondence cycles live on the product over that
field.
-/
def offDiagonalToProduct
    (D : CollisionSchemeDecomposition f) :
    D.offDiagonal ⟶ X ⨯ X :=
  D.offDiagonalInclusion ≫ collisionToProduct f

/--
For `X ⟶ Y ⟶ S`, the off-diagonal component mapped to the ambient product
`X ×[S] X`.  This is the scheme-level support map from which a later
correspondence-cycle class may be extracted.
-/
def offDiagonalToAmbientProduct
    {S : Scheme.{u}}
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    D.offDiagonal ⟶ pullback (f ≫ g) (f ≫ g) :=
  D.offDiagonalInclusion ≫ collisionToAmbientProduct f g

/-- The diagonal component maps to the absolute diagonal in `X × X`. -/
@[reassoc (attr := simp)]
theorem diagonalInclusion_comp_collisionToProduct
    (D : CollisionSchemeDecomposition f) :
    D.diagonalInclusion ≫ collisionToProduct f =
      absoluteDiagonal X :=
  collisionDiagonal_comp_collisionToProduct f

/--
Over a base `S`, the diagonal component maps to the relative diagonal of
`X ⟶ S`.
-/
@[reassoc (attr := simp)]
theorem diagonalInclusion_comp_collisionToAmbientProduct
    {S : Scheme.{u}}
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    D.diagonalInclusion ≫ collisionToAmbientProduct f g =
      pullback.diagonal (f ≫ g) :=
  collisionDiagonal_comp_collisionToAmbientProduct f g

end CollisionSchemeDecomposition

section Affine

variable (B A : Type u)
variable [CommRing B] [CommRing A] [Algebra B A]

/--
The literal affine collision decomposition obtained from vanishing overlap
and contact defects.
-/
noncomputable def affineCollisionSchemeDecomposition
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    CollisionSchemeDecomposition (affineCollisionMap B A) where
  offDiagonal :=
    Spec
      (.of
        (CollisionAlgebra B A ⧸
          collisionOffDiagonalIdeal B A))
  decomposition :=
    affineSelfCollisionDecomposition B A hOverlap hContact
  diagonal_hom :=
    affineCollisionDiagonal_decomposition_hom
      B A hOverlap hContact

/--
A collision selector pair canonically supplies the defect vanishings and
hence a literal affine scheme decomposition.
-/
noncomputable def CollisionSelectorPair.affineSchemeDecomposition
    (S : CollisionSelectorPair B A) :
    CollisionSchemeDecomposition (affineCollisionMap B A) :=
  affineCollisionSchemeDecomposition B A
    (overlapDefectIdeal_eq_bot_of_idempotent_generator
      (collisionObstructionIdeal B A)
      S.q S.q_isOffDiagonalSelector.1 S.obstruction_eq_span)
    (contactIdeal_eq_top_of_idempotent_generator
      (collisionObstructionIdeal B A)
      S.q S.q_isOffDiagonalSelector.1 S.obstruction_eq_span)

/--
An essentially finite-type formally unramified affine morphism has a
literal diagonal/off-diagonal collision decomposition.
-/
noncomputable def
    affineCollisionSchemeDecompositionOfFormallyUnramified
    [EssFiniteType B A] [Algebra.FormallyUnramified B A] :
    CollisionSchemeDecomposition (affineCollisionMap B A) :=
  affineCollisionSchemeDecomposition B A
    (affineCollisionDefects_vanish_of_formallyUnramified B A).1
    (affineCollisionDefects_vanish_of_formallyUnramified B A).2

end Affine

end

end HodgeConjecture
