import HodgeConjecture.Boundary.Normalization.InertiaDiagram
import HodgeConjecture.Correspondence.FiniteGroupProjector

/-!
# The normal-closure deck action

The Galois group of a marked normal closure preserves the integral closure
of the affine base ring.  Contravariance of `Spec` therefore gives a
canonical action by automorphisms of the normal-closure normalization over
the base.

This packages, at scheme level, the integral-closure action used in the
sibling Jacobian-collision development.  No purity or étaleness hypothesis
is needed to construct the action: those hypotheses concern the structure
map of the normalization, whereas each graph leg is an isomorphism.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace NormalizationInertia

section RingAction

variable {B K N : Type u}
variable [CommRing B] [Field K] [Field N]
variable [Algebra B K] [Algebra K N] [Algebra B N]
variable [IsScalarTower B K N]

/-- A `K`-automorphism of the normal closure, regarded over the affine base
ring `B`. -/
def normalClosureEquivOverBase
    (σ : N ≃ₐ[K] N) : N ≃ₐ[B] N :=
  σ.restrictScalars B

/-- The induced automorphism of the integral closure of `B` in `N`. -/
def normalClosureNormalizationRingEquiv
    (σ : N ≃ₐ[K] N) :
    NormalClosureNormalizationRing (B := B) (N := N) ≃ₐ[B]
      NormalClosureNormalizationRing (B := B) (N := N) :=
  (normalClosureEquivOverBase (B := B) σ).mapIntegralClosure

@[simp]
theorem normalClosureNormalizationRingEquiv_coe
    (σ : N ≃ₐ[K] N)
    (x : NormalClosureNormalizationRing (B := B) (N := N)) :
    ((normalClosureNormalizationRingEquiv (B := B) σ x :
        NormalClosureNormalizationRing (B := B) (N := N)) : N) =
      σ (x : N) :=
  rfl

end RingAction

section SchemeAction

variable {B K N : Type u}
variable [CommRing B] [Field K] [Field N]
variable [Algebra B K] [Algebra K N] [Algebra B N]
variable [IsScalarTower B K N]

/-- The scheme automorphism induced by a normal-closure Galois
automorphism.  The inverse ring automorphism appears because `Spec` is
contravariant; with this convention the construction is multiplicative in
`σ`. -/
def normalClosureNormalizationSchemeIso
    (σ : N ≃ₐ[K] N) :
    normalClosureNormalization (B := B) (N := N) ≅
      normalClosureNormalization (B := B) (N := N) :=
  Scheme.Spec.mapIso
    (normalClosureNormalizationRingEquiv (B := B) σ).toRingEquiv.toCommRingCatIso.symm.op

/-- The normal-closure scheme automorphism commutes with the map to the
affine base. -/
@[reassoc (attr := simp)]
theorem normalClosureNormalizationSchemeIso_hom_comp_toBase
    (σ : N ≃ₐ[K] N) :
    (normalClosureNormalizationSchemeIso (B := B) σ).hom ≫
        normalClosureNormalizationToBase (B := B) (N := N) =
      normalClosureNormalizationToBase (B := B) (N := N) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext b
  change (((normalClosureNormalizationRingEquiv (B := B) σ).symm
      (algebraMap B (NormalClosureNormalizationRing (B := B) (N := N)) b) :
        NormalClosureNormalizationRing (B := B) (N := N)) : N) =
    algebraMap B N b
  rw [(normalClosureNormalizationRingEquiv (B := B) σ).symm.commutes]
  rfl

/-- A Galois automorphism as a deck transformation of the affine
normal-closure normalization. -/
def normalClosureDeckTransformation
    (σ : N ≃ₐ[K] N) :
    SchemeCorrespondence.DeckTransformation
      (normalClosureNormalizationToBase (B := B) (N := N)) :=
  Over.isoMk
    (normalClosureNormalizationSchemeIso (B := B) σ)
    (normalClosureNormalizationSchemeIso_hom_comp_toBase
      (B := B) σ)

end SchemeAction

section FiniteDeckAction

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B N] [IsScalarTower B K N]

/-- The canonical Galois deck action on the normal-closure normalization. -/
def normalClosureFiniteDeckAction
    (D : CollisionFoundations.NormalClosureData K L N) :
    SchemeCorrespondence.FiniteDeckAction
      (normalClosureNormalizationToBase (B := B) (N := N))
      D.galoisGroup where
  toFun := normalClosureDeckTransformation (B := B)
  map_one' := by
    apply CategoryTheory.Aut.ext
    apply Over.OverMorphism.ext
    change (normalClosureNormalizationSchemeIso
      (B := B) (1 : D.galoisGroup)).hom = 𝟙 _
    simp only [normalClosureNormalizationSchemeIso, Functor.mapIso_hom,
      Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    unfold normalClosureNormalization
      HodgeConjecture.CollisionFoundations.normalizedAffineModel
    rw [← Spec.map_id]
    congr 1
  map_mul' := by
    intro σ τ
    apply CategoryTheory.Aut.ext
    apply Over.OverMorphism.ext
    change (normalClosureNormalizationSchemeIso (B := B) (σ * τ)).hom =
      (normalClosureDeckTransformation (B := B) τ).hom.left ≫
        (normalClosureDeckTransformation (B := B) σ).hom.left
    change (normalClosureNormalizationSchemeIso (B := B) (σ * τ)).hom =
      (normalClosureNormalizationSchemeIso (B := B) τ).hom ≫
        (normalClosureNormalizationSchemeIso (B := B) σ).hom
    simp only [normalClosureNormalizationSchemeIso, Functor.mapIso_hom,
      Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [← Spec.map_comp]
    congr 1

end FiniteDeckAction

end NormalizationInertia

end

end HodgeConjecture
