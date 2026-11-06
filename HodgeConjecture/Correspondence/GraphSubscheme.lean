module

public import HodgeConjecture.Correspondence.Graph
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

@[expose] public section

/-!
# Closed graph subschemes of deck transformations

The graph span has an actual morphism into the relative product. When the
structural morphism is separated, this graph morphism is a closed immersion.
Its kernel ideal sheaf defines a closed subscheme canonically isomorphic to
the source, with the prescribed two projections.

These are scheme-theoretic constructions. They do not assign Chow classes or
prove compatibility with a Chow product or cohomological realization.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- The actual graph morphism, with identity first projection and deck
transformation second projection. -/
def graphMorphism (σ : DeckTransformation pX) : X ⟶ pullback pX pX :=
  pullback.lift (𝟙 X) σ.toSchemeHom (by simp)

@[reassoc (attr := simp)]
theorem graphMorphism_fst (σ : DeckTransformation pX) :
    graphMorphism pX σ ≫ pullback.fst pX pX = 𝟙 X := by
  simp [graphMorphism]

@[reassoc (attr := simp)]
theorem graphMorphism_snd (σ : DeckTransformation pX) :
    graphMorphism pX σ ≫ pullback.snd pX pX = σ.toSchemeHom := by
  simp [graphMorphism]

/-- Separatedness makes the graph an actual closed immersion into the
relative product. -/
instance graphMorphism_isClosedImmersion [IsSeparated pX]
    (σ : DeckTransformation pX) : IsClosedImmersion (graphMorphism pX σ) := by
  letI : IsSeparated (pullback.fst pX pX) :=
    MorphismProperty.pullback_fst pX pX (inferInstance : IsSeparated pX)
  letI : IsClosedImmersion (graphMorphism pX σ ≫ pullback.fst pX pX) := by
    rw [graphMorphism_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (graphMorphism pX σ) (pullback.fst pX pX)

/-- The kernel ideal of the graph morphism. Under separatedness it cuts out
the actual closed graph, as witnessed by `graphSubschemeIso`. -/
def graphIdeal (σ : DeckTransformation pX) : (pullback pX pX).IdealSheafData :=
  (graphMorphism pX σ).ker

/-- The source identifies with the closed subscheme defined by its graph ideal. -/
def graphSubschemeIso [IsSeparated pX] (σ : DeckTransformation pX) :
    X ≅ (graphIdeal pX σ).subscheme :=
  asIso (graphMorphism pX σ).toImage

@[reassoc (attr := simp)]
theorem graphSubschemeIso_hom_subschemeι [IsSeparated pX]
    (σ : DeckTransformation pX) :
    (graphSubschemeIso pX σ).hom ≫ (graphIdeal pX σ).subschemeι =
      graphMorphism pX σ :=
  (graphMorphism pX σ).toImage_imageι

/-- The closed graph morphism is proper, with no assumption beyond separatedness. -/
theorem graphMorphism_isProper [IsSeparated pX] (σ : DeckTransformation pX) :
    IsProper (graphMorphism pX σ) := by
  infer_instance

end SchemeCorrespondence

end

end HodgeConjecture
