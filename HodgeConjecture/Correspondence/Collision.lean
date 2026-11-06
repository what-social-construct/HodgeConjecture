module

public import HodgeConjecture.Collision.ClopenDecomposition
public import HodgeConjecture.Correspondence.Algebra

@[expose] public section

/-!
# Collision schemes as scheme correspondences

For a factorization `X ⟶ Y ⟶ S`, the self-collision scheme
`R_f = X ×[Y] X` is a scheme correspondence from `X` to itself over `S`,
with legs the two pullback projections.

A literal clopen collision decomposition

`R_f ≅ X ⨿ R_fᵒᶠᶠ`

then becomes an isomorphism of scheme correspondences between the collision
relation and the coproduct of

* the identity/diagonal correspondence, and
* the off-diagonal correspondence.

This is still a statement about schemes and spans.  It does not yet assert
an equality of Chow classes or idempotence for convolution.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S X Y : Scheme.{u}}

/--
The collision scheme `X ×[Y] X`, regarded as a self-correspondence of `X`
over `S`.
-/
def collisionSchemeCorrespondence
    (f : X ⟶ Y) (g : Y ⟶ S) :
    SchemeCorrespondence (f ≫ g) (f ≫ g) where
  carrier := collisionSpace f
  left := collisionFst f
  right := collisionSnd f
  over_base := by
    simpa [Category.assoc] using
      congrArg (fun h => h ≫ g)
        (pullback.condition (f := f) (g := f))

/--
The support map of the collision correspondence is the canonical closed
map `R_f ⟶ X ×[S] X`.
-/
theorem collisionSchemeCorrespondence_toAmbientProduct
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (collisionSchemeCorrespondence f g).toAmbientProduct =
      collisionToAmbientProduct f g := by
  apply pullback.hom_ext <;>
    simp [collisionSchemeCorrespondence,
      collisionToAmbientProduct]

namespace CollisionSchemeDecomposition

variable {f : X ⟶ Y}

/--
The off-diagonal component of a clopen collision decomposition, regarded
as a self-correspondence of `X` over `S`.
-/
def offDiagonalSchemeCorrespondence
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    SchemeCorrespondence (f ≫ g) (f ≫ g) where
  carrier := D.offDiagonal
  left := D.offDiagonalInclusion ≫ collisionFst f
  right := D.offDiagonalInclusion ≫ collisionSnd f
  over_base := by
    simpa [Category.assoc] using
      congrArg
        (fun h => D.offDiagonalInclusion ≫ h ≫ g)
        (pullback.condition (f := f) (g := f))

/--
The off-diagonal correspondence support map agrees with the component map
to `X ×[S] X` already constructed in the collision layer.
-/
theorem offDiagonalSchemeCorrespondence_toAmbientProduct
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    (D.offDiagonalSchemeCorrespondence g).toAmbientProduct =
      D.offDiagonalToAmbientProduct g := by
  apply pullback.hom_ext <;>
    simp [offDiagonalSchemeCorrespondence,
      offDiagonalToAmbientProduct,
      collisionToAmbientProduct]

/--
The diagonal component inclusion identifies its support with the actual
diagonal correspondence in the ambient self-product.
-/
@[simp]
theorem diagonalInclusion_comp_correspondenceSupport
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    D.diagonalInclusion ≫
        (collisionSchemeCorrespondence f g).toAmbientProduct =
      (SchemeCorrespondence.identity (f ≫ g)).toAmbientProduct := by
  rw [collisionSchemeCorrespondence_toAmbientProduct,
    SchemeCorrespondence.identity_toAmbientProduct]
  exact D.diagonalInclusion_comp_collisionToAmbientProduct g

/--
The off-diagonal component inclusion identifies its support with the
off-diagonal correspondence in the ambient self-product.
-/
@[simp]
theorem offDiagonalInclusion_comp_correspondenceSupport
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    D.offDiagonalInclusion ≫
        (collisionSchemeCorrespondence f g).toAmbientProduct =
      (D.offDiagonalSchemeCorrespondence g).toAmbientProduct := by
  rw [collisionSchemeCorrespondence_toAmbientProduct,
    D.offDiagonalSchemeCorrespondence_toAmbientProduct]
  rfl

/--
The clopen decomposition of the collision scheme is an isomorphism of
scheme correspondences

`R_f ≅ 1_X ⨿ R_fᵒᶠᶠ`.

Thus the actual diagonal span, rather than merely an abstract quotient, is
the first summand.
-/
noncomputable def correspondenceDecompositionIsom
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S) :
    SchemeCorrespondence.Isom
      (collisionSchemeCorrespondence f g)
      (SchemeCorrespondence.coprod
        (SchemeCorrespondence.identity (f ≫ g))
        (D.offDiagonalSchemeCorrespondence g)) where
  carrierIso := D.decomposition
  hom_left := by
    rw [← D.decomposition.eq_inv_comp]
    apply coprod.hom_ext
    · simp only [SchemeCorrespondence.coprod,
        SchemeCorrespondence.identity_left,
        coprod.inl_desc]
      change
        𝟙 X =
          (coprod.inl ≫ D.decomposition.inv) ≫
            collisionFst f
      rw [D.inl_decomposition_inv]
      simp
    · simp [SchemeCorrespondence.coprod,
        offDiagonalSchemeCorrespondence,
        offDiagonalInclusion,
        collisionSchemeCorrespondence]
  hom_right := by
    rw [← D.decomposition.eq_inv_comp]
    apply coprod.hom_ext
    · simp only [SchemeCorrespondence.coprod,
        SchemeCorrespondence.identity_right,
        coprod.inl_desc]
      change
        𝟙 X =
          (coprod.inl ≫ D.decomposition.inv) ≫
            collisionSnd f
      rw [D.inl_decomposition_inv]
      simp
    · simp [SchemeCorrespondence.coprod,
        offDiagonalSchemeCorrespondence,
        offDiagonalInclusion,
        collisionSchemeCorrespondence]

/--
Every additive class assignment sends the literal collision decomposition
to

`[R_f] = [Δ_X] + [R_fᵒᶠᶠ] = 1 + [R_fᵒᶠᶠ]`.

This is the precise passage from the scheme decomposition to an additive
correspondence decomposition.  It does not assert that the off-diagonal
class is idempotent for convolution.
-/
theorem additiveClassMap_collisionDecomposition
    (D : CollisionSchemeDecomposition f)
    (g : Y ⟶ S)
    {Γ : Type*} [AddMonoid Γ] [One Γ]
    (χ :
      SchemeCorrespondence.AdditiveClassMap
        (f ≫ g) Γ) :
    χ.classOf (collisionSchemeCorrespondence f g) =
      1 +
        χ.classOf
          (D.offDiagonalSchemeCorrespondence g) := by
  calc
    χ.classOf (collisionSchemeCorrespondence f g) =
        χ.classOf
          (SchemeCorrespondence.coprod
            (SchemeCorrespondence.identity (f ≫ g))
            (D.offDiagonalSchemeCorrespondence g)) :=
      χ.classOf_isom (D.correspondenceDecompositionIsom g)
    _ =
        χ.classOf (SchemeCorrespondence.identity (f ≫ g)) +
          χ.classOf (D.offDiagonalSchemeCorrespondence g) :=
      χ.classOf_coprod _ _
    _ =
        1 +
          χ.classOf (D.offDiagonalSchemeCorrespondence g) := by
      rw [χ.classOf_identity]

end CollisionSchemeDecomposition

end

end HodgeConjecture
