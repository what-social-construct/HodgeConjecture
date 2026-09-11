import HodgeConjecture.Collision.AffineGeometry
import HodgeConjecture.Collision.SheafColon
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The relative diagonal ideal sheaf

This module globalizes the collision obstruction from an ideal in an affine
self-fiber-product algebra to the kernel ideal sheaf of a relative diagonal.

For a scheme morphism `f : X ⟶ Y`, the relative diagonal

`X ⟶ X ×[Y] X`

defines an ideal sheaf on the self-fiber product.  In the affine case, after
transport across `pullbackSpecIso`, this is the kernel sheaf of tensor
multiplication.  The comparison with `collisionObstructionIdeal` below keeps
the global-sections equivalence explicit.  The residual off-diagonal uses
`CollisionIdealSheaf.annihilator`, whose sheaf-colon construction first
takes the largest ideal-sheaf datum contained in the componentwise colon;
thus no unproved componentwise gluing assertion is needed.
-/

set_option autoImplicit false

namespace HodgeConjecture

open Algebra
open AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct

noncomputable section

universe u

/--
The ideal sheaf of the relative diagonal of a scheme morphism.

`Scheme.Hom.ker` is Mathlib's quasi-coherent ideal-sheaf data associated to a
morphism.  For quasi-compact diagonals its affine-open components are the
literal kernels of the corresponding maps on sections.  When `f` is
separated—hence in particular for the affine and finite cases—the diagonal is
a closed immersion and this is its defining ideal sheaf.
-/
def relativeDiagonalIdealSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback f f).IdealSheafData :=
  (pullback.diagonal f).ker

/--
The intrinsic residual off-diagonal ideal sheaf: the sheaf annihilator of
the relative diagonal ideal sheaf.
-/
def relativeOffDiagonalIdealSheaf
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback f f).IdealSheafData :=
  CollisionIdealSheaf.annihilator
    (relativeDiagonalIdealSheaf f)

private theorem annihilator_comap_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal S) (e : R ≃+* S) :
    (I.comap e.toRingHom).annihilator =
      I.annihilator.comap e.toRingHom := by
  ext x
  change
    (x ∈ (I.comap e.toRingHom).annihilator) ↔
      (e x ∈ I.annihilator)
  constructor
  · intro hx
    rw [Submodule.mem_annihilator] at hx ⊢
    intro y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    have hz : z ∈ I.comap e.toRingHom := hy
    simpa [smul_eq_mul] using congrArg e (hx z hz)
  · intro hx
    rw [Submodule.mem_annihilator] at hx ⊢
    intro z hz
    apply e.injective
    simpa [smul_eq_mul] using hx (e z) hz

section Affine

variable (B A : Type u)
variable [CommRing B] [CommRing A] [Algebra B A]

/--
Transport the relative diagonal ideal sheaf across
`pullbackSpecIso B A A`.
-/
def affineRelativeDiagonalIdealSheaf :
    (Spec (.of (CollisionAlgebra B A))).IdealSheafData :=
  (relativeDiagonalIdealSheaf (affineCollisionMap B A)).map
    (pullbackSpecIso B A A).hom

/--
The affine off-diagonal ideal sheaf, formed intrinsically as the annihilator
of the transported relative diagonal ideal sheaf.
-/
def affineRelativeOffDiagonalIdealSheaf :
    (Spec (.of (CollisionAlgebra B A))).IdealSheafData :=
  CollisionIdealSheaf.annihilator
    (affineRelativeDiagonalIdealSheaf B A)

/--
After transport by `pullbackSpecIso`, the relative diagonal ideal sheaf is
the kernel sheaf of tensor multiplication.
-/
theorem affineRelativeDiagonalIdealSheaf_eq_ker :
    affineRelativeDiagonalIdealSheaf B A =
      (Spec.map
        (CommRingCat.ofHom
          (collisionMultiplication B A).toRingHom)).ker := by
  rw [affineRelativeDiagonalIdealSheaf, relativeDiagonalIdealSheaf,
    Scheme.IdealSheafData.map_ker]
  congr 1
  unfold affineCollisionMap collisionMultiplication
  rw [AlgebraicGeometry.diagonal_Spec_map, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/--
On the top affine open, the transported diagonal ideal sheaf is the existing
collision obstruction ideal, with the canonical global-sections equivalence
kept explicit.
-/
theorem affineRelativeDiagonalIdealSheaf_top :
    (affineRelativeDiagonalIdealSheaf B A).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      (collisionObstructionIdeal B A).comap
        (Scheme.ΓSpecIso (.of (CollisionAlgebra B A))).hom.hom := by
  rw [affineRelativeDiagonalIdealSheaf_eq_ker,
    Scheme.ker_of_isAffine]
  change
    (Scheme.IdealSheafData.equivOfIsAffine
      (X := Spec (.of (CollisionAlgebra B A))))
        ((Scheme.IdealSheafData.equivOfIsAffine
          (X := Spec (.of (CollisionAlgebra B A)))).symm
            (RingHom.ker
              (Spec.map
                (CommRingCat.ofHom
                  (collisionMultiplication B A).toRingHom)).appTop.hom)) =
      _
  rw [OrderIso.apply_symm_apply]
  unfold collisionObstructionIdeal collisionMultiplication
    CollisionFoundations.diagonalMultiplication KaehlerDifferential.ideal
  change
    RingHom.ker
        (Spec.map
          (CommRingCat.ofHom
            (TensorProduct.lmul' B :
              CollisionAlgebra B A →ₐ[B] A).toRingHom)).appTop.hom =
      (RingHom.ker
        (TensorProduct.lmul' B :
          CollisionAlgebra B A →ₐ[B] A).toRingHom).comap
        (Scheme.ΓSpecIso (.of (CollisionAlgebra B A))).hom.hom
  rw [← RingHom.ker_equiv_comp _
      (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv,
    RingHom.comap_ker, RingEquiv.toRingHom_eq_coe,
    Iso.commRingCatIsoToRingEquiv_toRingHom,
    ← CommRingCat.hom_comp]
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/--
On the top affine open, the intrinsic off-diagonal sheaf is the existing
off-diagonal collision ideal, transported through the canonical
global-sections equivalence.
-/
theorem affineRelativeOffDiagonalIdealSheaf_top :
    (affineRelativeOffDiagonalIdealSheaf B A).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      (collisionOffDiagonalIdeal B A).comap
        (Scheme.ΓSpecIso (.of (CollisionAlgebra B A))).hom.hom := by
  rw [affineRelativeOffDiagonalIdealSheaf,
    CollisionIdealSheaf.annihilator_ideal_top,
    affineRelativeDiagonalIdealSheaf_top,
    collisionOffDiagonalIdeal_eq_annihilator]
  exact
    annihilator_comap_ringEquiv
      (collisionObstructionIdeal B A)
      (Scheme.ΓSpecIso
        (.of (CollisionAlgebra B A))).commRingCatIsoToRingEquiv

end Affine

end

end HodgeConjecture
