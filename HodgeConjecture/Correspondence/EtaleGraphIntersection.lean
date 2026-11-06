module

public import HodgeConjecture.Correspondence.GraphComposition
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

/-!
# Open graph intersections for an étale structural morphism

A section of an étale morphism is an open immersion. Applied to the
relative pair and triple projections, this proves that the graph and its
composition parametrization are open immersions. Under separatedness their
actual kernel-defined closed subscheme inclusions are therefore also open.

These are geometric open-immersion results. No cycle intersection or Chow
product is defined or assumed here.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/-- If postcomposition by an étale map is an open immersion, then the
original map is an open immersion. This applies in particular to sections. -/
theorem isOpenImmersion_of_comp_isEtale {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) [Etale g] [IsOpenImmersion (f ≫ g)] :
    IsOpenImmersion f := by
  letI : MorphismProperty.HasOfPostcompProperty
      @IsOpenImmersion @Etale := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y h hh
    letI := hh
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal h))
  exact MorphismProperty.of_postcomp @IsOpenImmersion f g
    (inferInstance : Etale g) (inferInstance : IsOpenImmersion (f ≫ g))

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- The first pair projection of the triple is étale by base change. -/
instance tripleProductP12_isEtale [Etale pX] : Etale (tripleProductP12 pX) :=
  MorphismProperty.pullback_fst _ _
    (MorphismProperty.pullback_fst pX pX (inferInstance : Etale pX))

/-- The last pair projection of the triple is étale by base change. -/
instance tripleProductP23_isEtale [Etale pX] : Etale (tripleProductP23 pX) :=
  MorphismProperty.pullback_snd _ _
    (MorphismProperty.pullback_snd pX pX (inferInstance : Etale pX))

/-- A deck graph is open when its structural morphism is étale.
Separatedness is not needed for this open-immersion statement. -/
instance graphMorphism_isOpenImmersion [Etale pX]
    (σ : DeckTransformation pX) : IsOpenImmersion (graphMorphism pX σ) := by
  letI : Etale (pullback.fst pX pX) :=
    MorphismProperty.pullback_fst pX pX (inferInstance : Etale pX)
  haveI : IsOpenImmersion (graphMorphism pX σ ≫ pullback.fst pX pX) := by
    rw [graphMorphism_fst]
    infer_instance
  exact isOpenImmersion_of_comp_isEtale (graphMorphism pX σ) (pullback.fst pX pX)

/-- The canonical closed graph subscheme is also open in the relative pair. -/
instance graphIdeal_subschemeι_isOpenImmersion [Etale pX] [IsSeparated pX]
    (σ : DeckTransformation pX) : IsOpenImmersion (graphIdeal pX σ).subschemeι := by
  have h : (graphIdeal pX σ).subschemeι =
      (graphSubschemeIso pX σ).inv ≫ graphMorphism pX σ := by
    rw [← graphSubschemeIso_hom_subschemeι, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- The graph-composition parametrization is a section of an étale
first-coordinate projection, and is therefore an open immersion. -/
instance graphCompositionMorphism_isOpenImmersion [Etale pX]
    (σ τ : DeckTransformation pX) :
    IsOpenImmersion (graphCompositionMorphism pX σ τ) := by
  letI : Etale (pullback.fst pX pX) :=
    MorphismProperty.pullback_fst pX pX (inferInstance : Etale pX)
  letI : Etale (tripleProductP12 pX ≫ pullback.fst pX pX) :=
    MorphismProperty.comp_mem @Etale _ _ inferInstance inferInstance
  haveI : IsOpenImmersion (graphCompositionMorphism pX σ τ ≫
      tripleProductP12 pX ≫ pullback.fst pX pX) := by
    simp only [← Category.assoc, graphCompositionMorphism_p12, graphMorphism_fst]
    infer_instance
  exact isOpenImmersion_of_comp_isEtale (graphCompositionMorphism pX σ τ)
    (tripleProductP12 pX ≫ pullback.fst pX pX)

/-- The actual closed graph intersection is open in the relative triple. -/
instance graphIntersectionIdeal_subschemeι_isOpenImmersion
    [Etale pX] [IsSeparated pX] (σ τ : DeckTransformation pX) :
    IsOpenImmersion (graphIntersectionIdeal pX σ τ).subschemeι := by
  have h : (graphIntersectionIdeal pX σ τ).subschemeι =
      (graphIntersectionIso pX σ τ).inv ≫ graphCompositionMorphism pX σ τ := by
    rw [← graphIntersectionIso_hom_subschemeι, Iso.inv_hom_id_assoc]
  rw [h]
  infer_instance

/-- The inverse-image graph on the first two coordinates is open in the triple. -/
instance graphIdeal_comap_p12_subschemeι_isOpenImmersion
    [Etale pX] [IsSeparated pX] (τ : DeckTransformation pX) :
    IsOpenImmersion ((graphIdeal pX τ).comap (tripleProductP12 pX)).subschemeι := by
  rw [← Scheme.IdealSheafData.comapIso_hom_fst]
  infer_instance

/-- The inverse-image graph on the last two coordinates is open in the triple. -/
instance graphIdeal_comap_p23_subschemeι_isOpenImmersion
    [Etale pX] [IsSeparated pX] (σ : DeckTransformation pX) :
    IsOpenImmersion ((graphIdeal pX σ).comap (tripleProductP23 pX)).subschemeι := by
  rw [← Scheme.IdealSheafData.comapIso_hom_fst]
  infer_instance

end

end HodgeConjecture.SchemeCorrespondence
