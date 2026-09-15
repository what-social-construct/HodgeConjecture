import HodgeConjecture.Correspondence.Graph

/-!
# Forgetting a deck transformation's base

Postcomposition of structural morphisms gives a functor on slice categories.
Its map on automorphism groups retains the actual scheme automorphism and
is injective. This changes only the base over which the automorphism is
regarded; it is not a pullback or an extension of an automorphism.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory

universe u

variable {X S B C : Scheme.{u}} (p : X ⟶ S) (b : S ⟶ B)

/-- Regard an automorphism over `S` as an automorphism over `B`, retaining
its actual underlying scheme map. -/
def forgetDeckBase : DeckTransformation p →* DeckTransformation (p ≫ b) :=
  Functor.mapAut (Over.mk p) (Over.map b)

@[simp]
theorem forgetDeckBase_toSchemeHom (σ : DeckTransformation p) :
    (forgetDeckBase p b σ).toSchemeHom = σ.toSchemeHom := rfl

@[simp]
theorem forgetDeckBase_one : forgetDeckBase p b 1 = 1 :=
  (forgetDeckBase p b).map_one

@[simp]
theorem forgetDeckBase_mul (σ τ : DeckTransformation p) :
    forgetDeckBase p b (σ * τ) = forgetDeckBase p b σ * forgetDeckBase p b τ :=
  (forgetDeckBase p b).map_mul σ τ

/-- The group multiplication keeps the convention that `σ` acts after `τ`. -/
theorem forgetDeckBase_mul_toSchemeHom (σ τ : DeckTransformation p) :
    (forgetDeckBase p b (σ * τ)).toSchemeHom = τ.toSchemeHom ≫ σ.toSchemeHom := rfl

/-- Forgetting the base does not identify distinct deck transformations. -/
theorem forgetDeckBase_injective : Function.Injective (forgetDeckBase p b) := by
  intro σ τ h
  apply Iso.ext
  apply Over.OverMorphism.ext
  exact congrArg (fun γ : DeckTransformation (p ≫ b) ↦ γ.toSchemeHom) h

/-- Successive changes of base retain the same scheme map as their composite.
The two structural arrows differ only by categorical reassociation. -/
theorem forgetDeckBase_comp_toSchemeHom (c : B ⟶ C) (σ : DeckTransformation p) :
    (forgetDeckBase (p ≫ b) c (forgetDeckBase p b σ)).toSchemeHom =
      (forgetDeckBase p (b ≫ c) σ).toSchemeHom := rfl

end HodgeConjecture.SchemeCorrespondence
