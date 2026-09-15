import HodgeConjecture.Correspondence.RelativeProductComparison
import HodgeConjecture.Correspondence.DeckBaseChange
import HodgeConjecture.Correspondence.GraphSlice

/-!
# Graph geometry under a change of structural base

The actual pair and triple comparison morphisms commute with graph maps,
graph-composition parametrizations, and graph slices. Their scheme-theoretic
images identify the relative graph and graph intersection with those of the
same automorphisms regarded over the structural base.

The morphism equations and the graph-kernel image equality require no
separatedness. Identifying the graph-intersection ideal with its kernel uses
separatedness of both structural morphisms. This module makes no cycle or
Chow construction.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {X S B : Scheme.{u}} (p : X ⟶ S) (b : S ⟶ B)

/-- The pair comparison preserves the actual graph morphism. -/
@[reassoc (attr := simp)]
theorem graphMorphism_pairBaseComparison (σ : DeckTransformation p) :
    graphMorphism p σ ≫ pairBaseComparison p b =
      graphMorphism (p ≫ b) (forgetDeckBase p b σ) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The triple comparison preserves the graph-composition parametrization,
with `σ` acting after `τ`. -/
@[reassoc (attr := simp)]
theorem graphCompositionMorphism_tripleBaseComparison (σ τ : DeckTransformation p) :
    graphCompositionMorphism p σ τ ≫ tripleBaseComparison p b =
      graphCompositionMorphism (p ≫ b)
        (forgetDeckBase p b σ) (forgetDeckBase p b τ) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Changing the input coordinate by a deck transformation commutes with
the actual pair comparison. -/
@[reassoc (attr := simp)]
theorem graphSlicePairMap_baseComparison (τ : DeckTransformation p) :
    graphSlicePairMap p τ ≫ pairBaseComparison p b =
      pairBaseComparison p b ≫
        graphSlicePairMap (p ≫ b) (forgetDeckBase p b τ) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The graph slice commutes with the actual pair and triple comparisons. -/
@[reassoc (attr := simp)]
theorem graphSliceMorphism_baseComparison (τ : DeckTransformation p) :
    graphSliceMorphism p τ ≫ tripleBaseComparison p b =
      pairBaseComparison p b ≫
        graphSliceMorphism (p ≫ b) (forgetDeckBase p b τ) := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The actual image of the graph kernel ideal is the graph kernel ideal
over the structural base; this equality does not require separatedness. -/
theorem graphIdeal_map_pairBaseComparison (σ : DeckTransformation p) :
    (graphIdeal p σ).map (pairBaseComparison p b) =
      graphIdeal (p ≫ b) (forgetDeckBase p b σ) := by
  rw [graphIdeal, Scheme.IdealSheafData.map_ker, graphMorphism_pairBaseComparison]
  rfl

/-- The actual graph intersection maps scheme-theoretically to the graph
intersection over the structural base. -/
theorem graphIntersectionIdeal_map_tripleBaseComparison
    [IsSeparated p] [IsSeparated b] (σ τ : DeckTransformation p) :
    (graphIntersectionIdeal p σ τ).map (tripleBaseComparison p b) =
      graphIntersectionIdeal (p ≫ b)
        (forgetDeckBase p b σ) (forgetDeckBase p b τ) := by
  rw [graphIntersectionIdeal_eq_ker, Scheme.IdealSheafData.map_ker,
    graphCompositionMorphism_tripleBaseComparison, graphIntersectionIdeal_eq_ker]

end

end HodgeConjecture.SchemeCorrespondence
