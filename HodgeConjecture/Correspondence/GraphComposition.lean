import HodgeConjecture.Correspondence.GraphSubscheme

/-!
# Scheme-theoretic composition of closed graphs

In the relative triple product, intersecting the inverse images of the graphs
of `τ` and `σ` cuts out the actual closed subscheme parametrized by
`x ↦ (x, τ x, σ (τ x))`. Its outer projection identifies it isomorphically
with the closed graph of `σ * τ`. The intersection is the sum of ideal
sheaves, so the assertions retain the scheme structure, not just the support.

Only separatedness of the structure morphism is used. No cycle intersection,
Chow product, or cohomological realization is defined in this module.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- The relative triple product, formed by matching the middle projections. -/
abbrev tripleProduct : Scheme.{u} :=
  pullback (pullback.snd pX pX) (pullback.fst pX pX)

/-- Projection onto the first two coordinates. -/
abbrev tripleProductP12 : tripleProduct pX ⟶ pullback pX pX :=
  pullback.fst (pullback.snd pX pX) (pullback.fst pX pX)

/-- Projection onto the last two coordinates. -/
abbrev tripleProductP23 : tripleProduct pX ⟶ pullback pX pX :=
  pullback.snd (pullback.snd pX pX) (pullback.fst pX pX)

/-- Projection onto the first and last coordinates. -/
def tripleProductP13 : tripleProduct pX ⟶ pullback pX pX :=
  pullback.lift
    (tripleProductP12 pX ≫ pullback.fst pX pX)
    (tripleProductP23 pX ≫ pullback.snd pX pX) (by
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc, pullback.condition]
      simp only [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem tripleProductP13_fst :
    tripleProductP13 pX ≫ pullback.fst pX pX =
      tripleProductP12 pX ≫ pullback.fst pX pX := by
  simp [tripleProductP13]

@[reassoc (attr := simp)]
theorem tripleProductP13_snd :
    tripleProductP13 pX ≫ pullback.snd pX pX =
      tripleProductP23 pX ≫ pullback.snd pX pX := by
  simp [tripleProductP13]

/-- The graph-composition parametrization; `σ` acts after `τ`. -/
def graphCompositionMorphism (σ τ : DeckTransformation pX) :
    X ⟶ tripleProduct pX :=
  pullback.lift (graphMorphism pX τ)
    (τ.toSchemeHom ≫ graphMorphism pX σ) (by simp)

@[reassoc (attr := simp)]
theorem graphCompositionMorphism_p12 (σ τ : DeckTransformation pX) :
    graphCompositionMorphism pX σ τ ≫ tripleProductP12 pX =
      graphMorphism pX τ := by
  simp [graphCompositionMorphism]

@[reassoc (attr := simp)]
theorem graphCompositionMorphism_p23 (σ τ : DeckTransformation pX) :
    graphCompositionMorphism pX σ τ ≫ tripleProductP23 pX =
      τ.toSchemeHom ≫ graphMorphism pX σ := by
  simp [graphCompositionMorphism]

@[reassoc (attr := simp)]
theorem graphCompositionMorphism_p13 (σ τ : DeckTransformation pX) :
    graphCompositionMorphism pX σ τ ≫ tripleProductP13 pX =
      graphMorphism pX (σ * τ) := by
  apply pullback.hom_ext <;> simp [Category.assoc]
  rfl

/-- The scheme-theoretic intersection of the two inverse-image graph ideals. -/
def graphIntersectionIdeal (σ τ : DeckTransformation pX) :
    (tripleProduct pX).IdealSheafData :=
  (graphIdeal pX τ).comap (tripleProductP12 pX) ⊔
    (graphIdeal pX σ).comap (tripleProductP23 pX)

private theorem graphIntersectionIdeal_le_ker (σ τ : DeckTransformation pX) :
    graphIntersectionIdeal pX σ τ ≤ (graphCompositionMorphism pX σ τ).ker := by
  apply sup_le
  · rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_ker, graphCompositionMorphism_p12]
    exact le_rfl
  · rw [← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_ker, graphCompositionMorphism_p23]
    exact τ.toSchemeHom.le_ker_comp (graphMorphism pX σ)

private theorem graphIntersection_firstCoordinate_factor [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphIntersectionIdeal pX σ τ).subschemeι ≫
        tripleProductP12 pX ≫ pullback.fst pX pX ≫
          graphCompositionMorphism pX σ τ =
      (graphIntersectionIdeal pX σ τ).subschemeι := by
  let J := graphIntersectionIdeal pX σ τ
  have h12 : (graphMorphism pX τ).ker ≤
      (J.subschemeι ≫ tripleProductP12 pX).ker := by
    rw [← Scheme.IdealSheafData.map_ker,
      Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_sup_left
  have h23 : (graphMorphism pX σ).ker ≤
      (J.subschemeι ≫ tripleProductP23 pX).ker := by
    rw [← Scheme.IdealSheafData.map_ker,
      Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_sup_right
  let a := IsClosedImmersion.lift (graphMorphism pX τ)
    (J.subschemeι ≫ tripleProductP12 pX) h12
  let b := IsClosedImmersion.lift (graphMorphism pX σ)
    (J.subschemeι ≫ tripleProductP23 pX) h23
  have ha : a ≫ graphMorphism pX τ = J.subschemeι ≫ tripleProductP12 pX := by
    simp [a]
  have hb : b ≫ graphMorphism pX σ = J.subschemeι ≫ tripleProductP23 pX := by
    simp [b]
  have ha_first : a = J.subschemeι ≫ tripleProductP12 pX ≫ pullback.fst pX pX := by
    simpa only [Category.assoc, graphMorphism_fst, Category.comp_id] using
      congrArg (fun f ↦ f ≫ pullback.fst pX pX) ha
  have hb_first : b = J.subschemeι ≫ tripleProductP23 pX ≫ pullback.fst pX pX := by
    simpa only [Category.assoc, graphMorphism_fst, Category.comp_id] using
      congrArg (fun f ↦ f ≫ pullback.fst pX pX) hb
  have hab : a ≫ τ.toSchemeHom = b := by
    rw [hb_first]
    have h := congrArg (fun f ↦ f ≫ pullback.snd pX pX) ha
    simpa only [Category.assoc, graphMorphism_snd, pullback.condition] using h
  change (J.subschemeι ≫ tripleProductP12 pX ≫ pullback.fst pX pX) ≫
    graphCompositionMorphism pX σ τ = J.subschemeι
  rw [← ha_first]
  apply pullback.hom_ext
  · simpa only [Category.assoc, graphCompositionMorphism_p12] using ha
  · change (a ≫ graphCompositionMorphism pX σ τ) ≫ tripleProductP23 pX = _
    rw [Category.assoc, graphCompositionMorphism_p23, ← Category.assoc, hab]
    exact hb

/-- The intersection has exactly the kernel ideal of its parametrization. -/
theorem graphIntersectionIdeal_eq_ker [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    graphIntersectionIdeal pX σ τ = (graphCompositionMorphism pX σ τ).ker := by
  apply le_antisymm (graphIntersectionIdeal_le_ker pX σ τ)
  calc
    (graphCompositionMorphism pX σ τ).ker ≤
        ((graphIntersectionIdeal pX σ τ).subschemeι ≫
          tripleProductP12 pX ≫ pullback.fst pX pX ≫
            graphCompositionMorphism pX σ τ).ker :=
      ( (graphIntersectionIdeal pX σ τ).subschemeι ≫
          tripleProductP12 pX ≫ pullback.fst pX pX).le_ker_comp _
    _ = graphIntersectionIdeal pX σ τ := by
      rw [graphIntersection_firstCoordinate_factor, Scheme.IdealSheafData.ker_subschemeι]

/-- The actual graph intersection is parametrized isomorphically by `X`. -/
def graphIntersectionIso [IsSeparated pX] (σ τ : DeckTransformation pX) :
    X ≅ (graphIntersectionIdeal pX σ τ).subscheme where
  hom := IsClosedImmersion.lift (graphIntersectionIdeal pX σ τ).subschemeι
    (graphCompositionMorphism pX σ τ) (by
      simpa using graphIntersectionIdeal_le_ker pX σ τ)
  inv := (graphIntersectionIdeal pX σ τ).subschemeι ≫
    tripleProductP12 pX ≫ pullback.fst pX pX
  hom_inv_id := by simp [← Category.assoc]
  inv_hom_id := by
    apply (cancel_mono (graphIntersectionIdeal pX σ τ).subschemeι).mp
    simp only [Category.assoc, IsClosedImmersion.lift_fac, Category.id_comp]
    exact graphIntersection_firstCoordinate_factor pX σ τ

@[reassoc (attr := simp)]
theorem graphIntersectionIso_hom_subschemeι [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphIntersectionIso pX σ τ).hom ≫
        (graphIntersectionIdeal pX σ τ).subschemeι =
      graphCompositionMorphism pX σ τ := by
  simp [graphIntersectionIso]

/-- The outer projection is an isomorphism from the intersection onto the
closed graph of the composed automorphism. -/
def graphCompositionIso [IsSeparated pX] (σ τ : DeckTransformation pX) :
    (graphIntersectionIdeal pX σ τ).subscheme ≅
      (graphIdeal pX (σ * τ)).subscheme :=
  (graphIntersectionIso pX σ τ).symm ≪≫ graphSubschemeIso pX (σ * τ)

@[reassoc (attr := simp)]
theorem graphCompositionIso_hom_subschemeι [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphCompositionIso pX σ τ).hom ≫
        (graphIdeal pX (σ * τ)).subschemeι =
      (graphIntersectionIdeal pX σ τ).subschemeι ≫ tripleProductP13 pX := by
  apply (cancel_epi (graphIntersectionIso pX σ τ).hom).mp
  simp [graphCompositionIso, ← Category.assoc]

/-- The scheme-theoretic image of the graph intersection under the outer
projection is exactly the composed graph, as an equality of ideal sheaves. -/
theorem graphIntersectionIdeal_map_p13 [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphIntersectionIdeal pX σ τ).map (tripleProductP13 pX) =
      graphIdeal pX (σ * τ) := by
  change ((graphIntersectionIdeal pX σ τ).subschemeι ≫ tripleProductP13 pX).ker = _
  rw [← graphCompositionIso_hom_subschemeι, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]

end SchemeCorrespondence

end

end HodgeConjecture
