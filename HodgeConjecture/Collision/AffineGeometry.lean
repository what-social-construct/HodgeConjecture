import HodgeConjecture.Collision.SchemeDecomposition
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Unramified.Finite

/-!
# Affine collision geometry

For an affine morphism

`Spec A ⟶ Spec B`,

the self-collision scheme is its self-fiber product.  Mathlib identifies this
pullback with `Spec (A ⊗[B] A)`.  Under that identification the relative
diagonal is dual to tensor multiplication.

This file connects those scheme-theoretic constructions to the collision
algebra and its diagonal/off-diagonal decomposition.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

variable (B A : Type u)
variable [CommRing B] [CommRing A] [Algebra B A]

/-- The affine morphism associated to the algebra structure `B → A`. -/
def affineCollisionMap :
    Spec (.of A) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B A))

/-- The affine self-collision scheme `Spec A ×_{Spec B} Spec A`. -/
def affineSelfCollisionScheme : Scheme :=
  pullback (affineCollisionMap B A) (affineCollisionMap B A)

/--
The canonical identification of the affine self-collision scheme with the
spectrum of the tensor-product collision algebra.
-/
noncomputable def affineSelfCollisionSpecIso :
    affineSelfCollisionScheme B A ≅
      Spec (.of (CollisionAlgebra B A)) :=
  pullbackSpecIso B A A

/-- The relative diagonal into the affine self-collision scheme. -/
def affineCollisionDiagonal :
    Spec (.of A) ⟶ affineSelfCollisionScheme B A :=
  pullback.diagonal (affineCollisionMap B A)

/--
Under the tensor-product description of the self-collision scheme, the
relative diagonal is the spectrum map dual to collision multiplication.
-/
theorem affineCollisionDiagonal_eq :
    affineCollisionDiagonal B A =
      Spec.map
          (CommRingCat.ofHom
            (collisionMultiplication B A).toRingHom) ≫
        (affineSelfCollisionSpecIso B A).inv := by
  exact diagonal_Spec_map B A

/-- Tensor multiplication is surjective, with section `a ↦ 1 ⊗ a`. -/
theorem affineCollisionMultiplication_surjective :
    Function.Surjective
      (collisionMultiplication B A).toRingHom := by
  intro a
  refine ⟨(1 : A) ⊗ₜ[B] a, ?_⟩
  simp [collisionMultiplication]

/--
The quotient of the collision algebra by the diagonal obstruction ideal is
canonically the diagonal algebra `A`.
-/
noncomputable def collisionDiagonalQuotientEquiv :
    (CollisionAlgebra B A ⧸ collisionObstructionIdeal B A) ≃+* A :=
  (collisionMultiplication B A).toRingHom.quotientKerEquivOfSurjective
    (affineCollisionMultiplication_surjective B A)

@[simp]
theorem collisionDiagonalQuotientEquiv_mk
    (x : CollisionAlgebra B A) :
    collisionDiagonalQuotientEquiv B A
        (Ideal.Quotient.mk (collisionObstructionIdeal B A) x) =
      collisionMultiplication B A x := by
  exact
    RingHom.quotientKerEquivOfSurjective_apply_mk
      (affineCollisionMultiplication_surjective B A) x

/--
For an essentially finite-type formally unramified algebra, both collision
decomposition defects vanish.
-/
theorem affineCollisionDefects_vanish_of_formallyUnramified
    [EssFiniteType B A] [Algebra.FormallyUnramified B A] :
    collisionOverlapDefectIdeal B A = ⊥ ∧
      contactIdeal (collisionObstructionIdeal B A) = ⊤ := by
  have hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤ :=
    (collisionContactIdeal_eq_top_iff_formallyUnramified B A).2
      (inferInstance : Algebra.FormallyUnramified B A)
  obtain ⟨q, hq, hqJ⟩ :=
    exists_idempotent_generator_of_contact_eq_top
      (collisionObstructionIdeal B A) hContact
  exact
    ⟨overlapDefectIdeal_eq_bot_of_idempotent_generator
        (collisionObstructionIdeal B A) q hq hqJ,
      hContact⟩

/--
An explicit diagonal/off-diagonal ideal decomposition gives a decomposition
of the actual affine self-fiber product.  The first component has been
identified canonically with `Spec A`, rather than left as the quotient by the
diagonal obstruction ideal.
-/
noncomputable def affineSelfCollisionDecomposition
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    affineSelfCollisionScheme B A ≅
      (Spec (.of A) ⨿
        Spec
          (.of
            (CollisionAlgebra B A ⧸
              collisionOffDiagonalIdeal B A))) :=
  affineSelfCollisionSpecIso B A ≪≫
    collisionAffineSchemeDecomposition B A hOverlap hContact ≪≫
      coprod.mapIso
        (Scheme.Spec.mapIso
          (collisionDiagonalQuotientEquiv B A).toCommRingCatIso.op).symm
        (Iso.refl _)

/--
The first component in the affine collision decomposition is the actual
relative diagonal.
-/
@[reassoc]
theorem affineCollisionDiagonal_decomposition_hom
    (hOverlap : collisionOverlapDefectIdeal B A = ⊥)
    (hContact :
      contactIdeal (collisionObstructionIdeal B A) = ⊤) :
    affineCollisionDiagonal B A ≫
        (affineSelfCollisionDecomposition
          B A hOverlap hContact).hom =
      coprod.inl := by
  rw [← cancel_mono
    (affineSelfCollisionDecomposition B A hOverlap hContact).inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [affineCollisionDiagonal_eq]
  simp [
    affineSelfCollisionDecomposition,
    collisionAffineSchemeDecomposition,
    idealAffineSchemeDecomposition]
  simp only [← Category.assoc]
  rw [cancel_mono (affineSelfCollisionSpecIso B A).inv]
  simp only [collisionOffDiagonalIdeal]
  slice_rhs 2 3 => rw [coprodSpec_inl]
  rw [← Spec.map_comp, ← Spec.map_comp]
  rw [Spec.map_inj]
  ext x
  simp [idealProductDecomposition_fst]

/--
For an essentially finite-type formally unramified affine morphism, the
self-collision scheme splits canonically into its diagonal and residual
off-diagonal components.
-/
noncomputable def affineSelfCollisionDecompositionOfFormallyUnramified
    [EssFiniteType B A] [Algebra.FormallyUnramified B A] :
    affineSelfCollisionScheme B A ≅
      (Spec (.of A) ⨿
        Spec
          (.of
            (CollisionAlgebra B A ⧸
              collisionOffDiagonalIdeal B A))) :=
  affineSelfCollisionDecomposition B A
    (affineCollisionDefects_vanish_of_formallyUnramified B A).1
    (affineCollisionDefects_vanish_of_formallyUnramified B A).2

end

end HodgeConjecture
