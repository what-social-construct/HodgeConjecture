module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Morphism projections of the bundled categorical automorphism

Lean 4.35's Mathlib bundles an automorphism around `asIso`. These projections
retain the existing geometric deck-map API while using that native type.
-/

@[expose] public section

namespace CategoryTheory.Aut

universe u v
variable {C : Type u} [Category.{v} C] {X : C}

abbrev hom (a : Aut X) : X ⟶ X := a.asIso.hom
abbrev inv (a : Aut X) : X ⟶ X := a.asIso.inv

@[ext]
theorem hom_ext {a b : Aut X} (h : a.hom = b.hom) : a = b := by
  apply Aut.ext
  exact Iso.ext h

instance (a : Aut X) : IsIso a.hom := inferInstanceAs (IsIso a.asIso.hom)

@[simp] theorem hom_one : (1 : Aut X).hom = 𝟙 X := rfl
@[simp] theorem hom_mul (a b : Aut X) : (a * b).hom = b.hom ≫ a.hom := rfl
@[simp] theorem hom_inv (a : Aut X) : (a⁻¹).hom = a.inv := rfl
@[simp] theorem hom_inv_id (a : Aut X) : a.hom ≫ a.inv = 𝟙 X := a.asIso.hom_inv_id
@[simp] theorem inv_hom_id (a : Aut X) : a.inv ≫ a.hom = 𝟙 X := a.asIso.inv_hom_id

end CategoryTheory.Aut
