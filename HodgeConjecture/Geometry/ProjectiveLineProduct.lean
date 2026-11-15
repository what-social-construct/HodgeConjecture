module

public import HodgeConjecture.Geometry.ProjectiveLine
public import HodgeConjecture.Geometry.ComplexPointsFunctoriality
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The product of two actual projective lines

The product is the scheme fiber product over `Spec k`, using the structure
morphism of the two-chart projective line. Its projections satisfy the
cartesian square by construction. Over `ℂ`, its complex points are in
bijection with ordered pairs of complex points of the projective line;
the projection maps on complex points are continuous.

This is the geometric object on which the two fiber cycles and their Betti
classes will be compared. The point equivalence here is a set equivalence;
identifying the analytic topology with the product topology requires a
separate argument.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The actual scheme `P¹_k ×_{Spec k} P¹_k`. -/
abbrev projectiveLineProduct : Scheme.{u} :=
  pullback (projectiveLine k ↘ Spec (.of k))
    (projectiveLine k ↘ Spec (.of k))

/-- First projection of the projective-line product. -/
abbrev projectiveLineProductFst : projectiveLineProduct k ⟶ projectiveLine k :=
  pullback.fst _ _

/-- Second projection of the projective-line product. -/
abbrev projectiveLineProductSnd : projectiveLineProduct k ⟶ projectiveLine k :=
  pullback.snd _ _

/-- The structural map of the product, obtained from the first projection. -/
abbrev projectiveLineProductStructureMorphism :
    projectiveLineProduct k ⟶ Spec (.of k) :=
  projectiveLineProductFst k ≫ (projectiveLine k ↘ Spec (.of k))

@[simp] theorem projectiveLineProductFst_comp_structureMorphism :
    projectiveLineProductFst k ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineProductStructureMorphism k := rfl

@[simp] theorem projectiveLineProductSnd_comp_structureMorphism :
    projectiveLineProductSnd k ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLineProductStructureMorphism k :=
  (pullback.condition).symm

/-- The product is itself a scheme over `Spec k`. -/
instance : (projectiveLineProduct k).Over (Spec (.of k)) where
  hom := projectiveLineProductStructureMorphism k

/-- The pullback's universal property in the category of schemes. -/
theorem projectiveLineProduct_hom_ext {T : Scheme.{u}}
    {f g : T ⟶ projectiveLineProduct k}
    (h₁ : f ≫ projectiveLineProductFst k = g ≫ projectiveLineProductFst k)
    (h₂ : f ≫ projectiveLineProductSnd k = g ≫ projectiveLineProductSnd k) :
    f = g := pullback.hom_ext h₁ h₂

end AlgebraicGeometry

end
