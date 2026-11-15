module

public import HodgeConjecture.Geometry.ComplexPointsFunctoriality
public import HodgeConjecture.Realization.Betti.SingularCochains
public import Mathlib.CategoryTheory.Comma.Over.Basic

@[expose] public section

/-!
# Rational singular Betti cohomology of the canonical complex point space

The topological space is constructed from actual scheme sections and
regular-function evaluations. Morphisms over Spec ℂ induce the original
continuous maps and hence the existing singular pullbacks in every degree.
No topological space, comparison isomorphism or purity datum is supplied.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.SchemeBetti

open AlgebraicGeometry CategoryTheory

variable {X Y Z : Scheme.{0}}
variable {x : X ⟶ Spec (.of ℂ)} {y : Y ⟶ Spec (.of ℂ)} {z : Z ⟶ Spec (.of ℂ)}

/-- The actual scheme-valued complex points with the proved analytic topology. -/
abbrev space (f : X ⟶ Spec (.of ℂ)) : TopCat.{0} :=
  TopCat.of (Scheme.ComplexPoints f)

/-- The original map on complex points, bundled as a continuous map. -/
def map (f : X ⟶ Y) (hf : f ≫ y = x) : space x ⟶ space y :=
  TopCat.ofHom ⟨Scheme.ComplexPoints.map f hf, Scheme.ComplexPoints.continuous_map f hf⟩

@[simp]
theorem map_id : map (𝟙 X) (Category.id_comp x) = 𝟙 (space x) := by
  ext p : 1
  exact Scheme.ComplexPoints.map_id p

theorem map_comp (f : X ⟶ Y) (hf : f ≫ y = x)
    (g : Y ⟶ Z) (hg : g ≫ z = y) :
    map (f ≫ g) (by rw [Category.assoc, hg, hf]) = map f hf ≫ map g hg := by
  ext p : 1
  exact Scheme.ComplexPoints.map_comp f hf g hg p

/-- A genuine functor from schemes over the complex base to their analytic point spaces. -/
def complexPointsFunctor : CategoryTheory.Over (Spec (.of ℂ)) ⥤ TopCat.{0} where
  obj X := space X.hom
  map f := map f.left f.w
  map_id X := by ext p : 1; exact Scheme.ComplexPoints.map_id p
  map_comp f g := by
    ext p : 1
    exact Scheme.ComplexPoints.map_comp f.left f.w g.left g.w p

/-- The existing singular group on the canonical scheme point space, without a new cochain carrier. -/
abbrev Cohomology (f : X ⟶ Spec (.of ℂ)) (n : ℕ) :=
  SingularCochains.Cohomology (space f) n

/-- Scheme-morphism pullback is the original continuous singular-cohomology pullback. -/
def pullback (f : X ⟶ Y) (hf : f ≫ y = x) (n : ℕ) :
    Cohomology y n ⟶ Cohomology x n :=
  SingularCochains.cohomologyPullback (map f hf) n

@[simp]
theorem pullback_id (n : ℕ) :
    pullback (𝟙 X) (Category.id_comp x) n = 𝟙 (Cohomology x n) := by
  simp [pullback]

theorem pullback_comp (f : X ⟶ Y) (hf : f ≫ y = x)
    (g : Y ⟶ Z) (hg : g ≫ z = y) (n : ℕ) :
    pullback (f ≫ g) (by rw [Category.assoc, hg, hf]) n =
      pullback g hg n ≫ pullback f hf n := by
  rw [pullback, map_comp, SingularCochains.cohomologyPullback_comp]
  rfl

/-- Rational singular Betti cohomology is contravariant on the actual complex schemes. -/
def cohomologyFunctor (n : ℕ) :
    (CategoryTheory.Over (Spec (.of ℂ)))ᵒᵖ ⥤ ModuleCat.{0} ℚ where
  obj X := Cohomology X.unop.hom n
  map f := pullback f.unop.left f.unop.w n
  map_id _X := pullback_id n
  map_comp f g := pullback_comp g.unop.left g.unop.w f.unop.left f.unop.w n

end HodgeConjecture.SchemeBetti
