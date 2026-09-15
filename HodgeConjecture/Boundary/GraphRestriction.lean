import HodgeConjecture.Correspondence.GraphSubscheme
import HodgeConjecture.Inputs.FiniteEtaleExtension

/-!
# Scheme-theoretic restriction of extended deck graphs

For a chosen finite étale extension over an open immersion, the graph of
every extended deck automorphism pulls back to the graph of its restriction.
This is a Cartesian square of actual schemes and an equality of the defining
ideal sheaves. Restricting an already supplied automorphism does not require
the separate deck-extension hypothesis.

The result supplies the closed-subscheme restriction step; passage to Chow
classes and compatibility with convolution remain separate constructions.
-/

set_option autoImplicit false

namespace HodgeConjecture.LiteratureInputs.FiniteEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence

noncomputable section

universe u v

variable {X U Y : Scheme.{u}} {j : U ⟶ X} {p : Y ⟶ U}

/-- The map of relative products induced by the actual cover inclusion. -/
def pairInclusion (E : FiniteEtaleExtension j p) :
    pullback p p ⟶ pullback E.toBase E.toBase :=
  pullback.map p p E.toBase E.toBase E.inclusion E.inclusion j
    E.inclusion_toBase.symm E.inclusion_toBase.symm

@[reassoc (attr := simp)]
theorem pairInclusion_fst (E : FiniteEtaleExtension j p) :
    E.pairInclusion ≫ pullback.fst E.toBase E.toBase =
      pullback.fst p p ≫ E.inclusion := by
  simp [pairInclusion]

@[reassoc (attr := simp)]
theorem pairInclusion_snd (E : FiniteEtaleExtension j p) :
    E.pairInclusion ≫ pullback.snd E.toBase E.toBase =
      pullback.snd p p ≫ E.inclusion := by
  simp [pairInclusion]

/-- An open base inclusion induces an actual open immersion of relative products. -/
theorem pairInclusion_isOpenImmersion (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] : IsOpenImmersion E.pairInclusion := by
  letI := E.inclusion_isOpenImmersion
  unfold pairInclusion
  infer_instance

/-- Restriction of an extended automorphism gives a commuting graph square. -/
@[reassoc]
theorem graph_restriction_commutes (E : FiniteEtaleExtension j p)
    (σ : DeckTransformation E.toBase) :
    graphMorphism p (E.restriction σ) ≫ E.pairInclusion =
      E.inclusion ≫ graphMorphism E.toBase σ := by
  apply pullback.hom_ext
  · simp
  · simp only [Category.assoc, pairInclusion_snd,
      graphMorphism_snd_assoc, graphMorphism_snd]
    exact E.restriction_inclusion σ

/-- The restricted graph is the actual pullback of the extended graph,
not merely a commuting span. Monicity of the open cover inclusion provides
the second projection in the universal property. -/
theorem graphRestriction_isPullback (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] (σ : DeckTransformation E.toBase) :
    IsPullback (graphMorphism p (E.restriction σ)) E.inclusion
      E.pairInclusion (graphMorphism E.toBase σ) := by
  letI := E.inclusion_isOpenImmersion
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk _ _ (E.graph_restriction_commutes σ))
  refine PullbackCone.isLimitAux'
    (PullbackCone.mk _ _ (E.graph_restriction_commutes σ)) (fun s ↦ ?_)
  have hf : s.fst ≫ pullback.fst p p ≫ E.inclusion = s.snd := by
    have h := congrArg
      (fun f ↦ f ≫ pullback.fst E.toBase E.toBase) s.condition
    simpa [Category.assoc] using h
  have hs : s.fst ≫ pullback.snd p p ≫ E.inclusion =
      s.snd ≫ σ.toSchemeHom := by
    have h := congrArg
      (fun f ↦ f ≫ pullback.snd E.toBase E.toBase) s.condition
    simpa [Category.assoc] using h
  refine ⟨s.fst ≫ pullback.fst p p, ?_, ?_, ?_⟩
  · change (s.fst ≫ pullback.fst p p) ≫
        graphMorphism p (E.restriction σ) = s.fst
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, graphMorphism_snd]
      apply (cancel_mono E.inclusion).mp
      calc
        (s.fst ≫ pullback.fst p p ≫ (E.restriction σ).toSchemeHom) ≫
            E.inclusion =
            (s.fst ≫ pullback.fst p p ≫ E.inclusion) ≫ σ.toSchemeHom := by
              simp only [Category.assoc, E.restriction_inclusion σ]
        _ = s.snd ≫ σ.toSchemeHom := by rw [hf]
        _ = (s.fst ≫ pullback.snd p p) ≫ E.inclusion := by
          simpa only [Category.assoc] using hs.symm
  · simpa only [Category.assoc] using hf
  · intro m hm _
    have h := congrArg (fun f ↦ f ≫ pullback.fst p p) hm
    simpa [Category.assoc] using h

/-- Equality of the graph ideal sheaves under actual scheme-theoretic
inverse image. Finiteness of the extended cover supplies separatedness. -/
theorem graphIdeal_restriction (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] (σ : DeckTransformation E.toBase) :
    graphIdeal p (E.restriction σ) =
      (graphIdeal E.toBase σ).comap E.pairInclusion := by
  letI := E.finite
  change (graphMorphism p (E.restriction σ)).ker =
    (graphMorphism E.toBase σ).ker.comap E.pairInclusion
  rw [← (E.graphRestriction_isPullback σ).isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- For a prescribed original action, the same restriction theorem applies
to its lift under the explicitly stated deck-extension hypothesis. -/
theorem graphIdeal_liftDeckAction (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] [DeckExtensionHypothesis E]
    {G : Type v} [Group G] (α : FiniteDeckAction p G) (g : G) :
    graphIdeal p (α g) =
      (graphIdeal E.toBase (E.liftDeckAction α g)).comap E.pairInclusion := by
  simpa only [restriction_liftDeckAction] using
    E.graphIdeal_restriction (E.liftDeckAction α g)

end

end HodgeConjecture.LiteratureInputs.FiniteEtaleExtension
