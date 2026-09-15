import HodgeConjecture.Correspondence.EtaleGraphIntersection

/-!
# Graph slices in the relative triple product

The slice `(x,z) ↦ (x,τ x,z)` is a closed immersion under separatedness.
Its last-pair map is the actual pair isomorphism `(x,z) ↦ (τ x,z)`.
It is the actual inverse image of the graph of `τ` under the first-pair
projection, and is an open immersion when the structural morphism is étale.
Inverse image through that isomorphism, followed by the slice inclusion,
gives exactly the previously constructed graph-intersection ideal.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- Change only the input coordinate by a deck transformation. -/
def graphSlicePairMap (τ : DeckTransformation pX) :
    pullback pX pX ⟶ pullback pX pX :=
  pullback.map pX pX pX pX τ.toSchemeHom (𝟙 X) (𝟙 S) (by simp) (by simp)

instance graphSlicePairMap_isIso (τ : DeckTransformation pX) :
    IsIso (graphSlicePairMap pX τ) := by
  unfold graphSlicePairMap
  infer_instance

@[reassoc (attr := simp)]
theorem graphSlicePairMap_fst (τ : DeckTransformation pX) :
    graphSlicePairMap pX τ ≫ pullback.fst pX pX =
      pullback.fst pX pX ≫ τ.toSchemeHom := by simp [graphSlicePairMap]

@[reassoc (attr := simp)]
theorem graphSlicePairMap_snd (τ : DeckTransformation pX) :
    graphSlicePairMap pX τ ≫ pullback.snd pX pX = pullback.snd pX pX := by
  simp [graphSlicePairMap]

/-- The actual graph slice, with free first and last coordinates. -/
def graphSliceMorphism (τ : DeckTransformation pX) :
    pullback pX pX ⟶ tripleProduct pX :=
  pullback.lift (pullback.fst pX pX ≫ graphMorphism pX τ)
    (graphSlicePairMap pX τ) (by simp)

@[reassoc (attr := simp)]
theorem graphSliceMorphism_p12 (τ : DeckTransformation pX) :
    graphSliceMorphism pX τ ≫ tripleProductP12 pX =
      pullback.fst pX pX ≫ graphMorphism pX τ := by simp [graphSliceMorphism]

@[reassoc (attr := simp)]
theorem graphSliceMorphism_p23 (τ : DeckTransformation pX) :
    graphSliceMorphism pX τ ≫ tripleProductP23 pX = graphSlicePairMap pX τ := by
  simp [graphSliceMorphism]

@[reassoc (attr := simp)]
theorem graphSliceMorphism_p13 (τ : DeckTransformation pX) :
    graphSliceMorphism pX τ ≫ tripleProductP13 pX = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- The slice is open when the structural morphism is étale. -/
instance graphSliceMorphism_isOpenImmersion [IsEtale pX]
    (τ : DeckTransformation pX) : IsOpenImmersion (graphSliceMorphism pX τ) := by
  letI : IsOpenImmersion (graphSliceMorphism pX τ ≫ tripleProductP23 pX) := by
    rw [graphSliceMorphism_p23]
    infer_instance
  exact isOpenImmersion_of_comp_isEtale (graphSliceMorphism pX τ) (tripleProductP23 pX)

/-- The slice is the scheme-theoretic inverse image of the first-pair graph. -/
theorem graphSlice_isPullback (τ : DeckTransformation pX) :
    IsPullback (graphSliceMorphism pX τ) (pullback.fst pX pX)
      (tripleProductP12 pX) (graphMorphism pX τ) := by
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk _ _ (graphSliceMorphism_p12 pX τ))
  refine PullbackCone.isLimitAux'
    (PullbackCone.mk _ _ (graphSliceMorphism_p12 pX τ)) (fun s ↦ ?_)
  have hf : s.fst ≫ tripleProductP12 pX ≫ pullback.fst pX pX = s.snd := by
    have h := congrArg (fun f ↦ f ≫ pullback.fst pX pX) s.condition
    simpa only [Category.assoc, graphMorphism_fst, Category.comp_id] using h
  have hs : s.fst ≫ tripleProductP12 pX ≫ pullback.snd pX pX =
      s.snd ≫ τ.toSchemeHom := by
    have h := congrArg (fun f ↦ f ≫ pullback.snd pX pX) s.condition
    simpa only [Category.assoc, graphMorphism_snd] using h
  refine ⟨s.fst ≫ tripleProductP13 pX, ?_, ?_, ?_⟩
  · change (s.fst ≫ tripleProductP13 pX) ≫ graphSliceMorphism pX τ = s.fst
    apply pullback.hom_ext
    · change ((s.fst ≫ tripleProductP13 pX) ≫ graphSliceMorphism pX τ) ≫
        tripleProductP12 pX = s.fst ≫ tripleProductP12 pX
      calc
        _ = (s.fst ≫ tripleProductP12 pX ≫ pullback.fst pX pX) ≫
            graphMorphism pX τ := by
          simp only [Category.assoc, graphSliceMorphism_p12, tripleProductP13_fst_assoc]
        _ = _ := by rw [hf]; exact s.condition.symm
    · change ((s.fst ≫ tripleProductP13 pX) ≫ graphSliceMorphism pX τ) ≫
        tripleProductP23 pX = s.fst ≫ tripleProductP23 pX
      rw [Category.assoc, graphSliceMorphism_p23]
      apply pullback.hom_ext
      · simp only [Category.assoc, graphSlicePairMap_fst, tripleProductP13_fst_assoc]
        calc
          _ = s.snd ≫ τ.toSchemeHom := by
            simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ τ.toSchemeHom) hf
          _ = _ := by simpa only [pullback.condition] using hs.symm
      · simp only [Category.assoc, graphSlicePairMap_snd, tripleProductP13_snd]
  · change (s.fst ≫ tripleProductP13 pX) ≫ pullback.fst pX pX = s.snd
    simpa only [Category.assoc, tripleProductP13_fst] using hf
  · intro m hm _
    change m ≫ graphSliceMorphism pX τ = s.fst at hm
    have h := congrArg (fun f ↦ f ≫ tripleProductP13 pX) hm
    simpa only [Category.assoc, graphSliceMorphism_p13, Category.comp_id] using h

instance graphSliceMorphism_isClosedImmersion [IsSeparated pX]
    (τ : DeckTransformation pX) : IsClosedImmersion (graphSliceMorphism pX τ) := by
  letI : IsSeparated (pullback.snd pX pX) :=
    MorphismProperty.pullback_snd pX pX (inferInstance : IsSeparated pX)
  letI : IsSeparated (tripleProductP23 pX) :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsSeparated (pullback.snd pX pX))
  letI : IsClosedImmersion (graphSliceMorphism pX τ ≫ tripleProductP23 pX) := by
    rw [graphSliceMorphism_p23]
    infer_instance
  exact IsClosedImmersion.of_comp (graphSliceMorphism pX τ) (tripleProductP23 pX)

/-- The first-pair graph ideal pulls back to the actual kernel ideal of the slice. -/
theorem graphIdeal_comap_p12_eq_graphSlice_ker [IsSeparated pX]
    (τ : DeckTransformation pX) :
    (graphIdeal pX τ).comap (tripleProductP12 pX) = (graphSliceMorphism pX τ).ker := by
  rw [← (graphSlice_isPullback pX τ).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rfl

@[reassoc (attr := simp)]
theorem graphMorphism_graphSlicePairMap (σ τ : DeckTransformation pX) :
    graphMorphism pX (σ * τ) ≫ graphSlicePairMap pX τ =
      τ.toSchemeHom ≫ graphMorphism pX σ := by
  apply pullback.hom_ext <;> simp [Category.assoc]
  rfl

/-- The pair change has the actual graph pullback square. -/
theorem graphSlicePair_isPullback (σ τ : DeckTransformation pX) :
    IsPullback (graphMorphism pX (σ * τ)) τ.toSchemeHom
      (graphSlicePairMap pX τ) (graphMorphism pX σ) :=
  IsPullback.of_vert_isIso ⟨graphMorphism_graphSlicePairMap pX σ τ⟩

/-- Actual inverse image of a graph under the pair isomorphism. -/
theorem graphIdeal_comap_graphSlicePairMap [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphIdeal pX σ).comap (graphSlicePairMap pX τ) = graphIdeal pX (σ * τ) := by
  have h := graphSlicePair_isPullback pX σ τ
  change _ = (graphMorphism pX (σ * τ)).ker
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rfl

@[reassoc (attr := simp)]
theorem graphMorphism_graphSliceMorphism (σ τ : DeckTransformation pX) :
    graphMorphism pX (σ * τ) ≫ graphSliceMorphism pX τ =
      graphCompositionMorphism pX σ τ := by
  apply pullback.hom_ext <;> simp [Category.assoc]

/-- Closed image of the pulled-back graph in the slice is the actual intersection. -/
theorem graphIdeal_map_graphSliceMorphism [IsSeparated pX]
    (σ τ : DeckTransformation pX) :
    (graphIdeal pX (σ * τ)).map (graphSliceMorphism pX τ) =
      graphIntersectionIdeal pX σ τ := by
  rw [graphIdeal, Scheme.IdealSheafData.map_ker, graphMorphism_graphSliceMorphism,
    graphIntersectionIdeal_eq_ker]

end

end HodgeConjecture.SchemeCorrespondence
