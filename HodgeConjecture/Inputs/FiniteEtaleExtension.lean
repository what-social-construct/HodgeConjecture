import HodgeConjecture.Correspondence.FiniteGroupProjector
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Selected finite-étale extension and deck-extension inputs

These are explicit selected-conclusion interfaces, not formalizations or
proofs of the full cited Stacks theorems. A cover extension and unique deck
extension are separate inputs. Every consumer of an input class states that
class in its own declaration; neither input has a default instance.

For an open immersion `j : U ⟶ X` and finite étale `p : Y ⟶ U`, Stacks
Project Lemma 58.31.2, Tag `0H2W`, supplies the cover-extension conclusion
after verifying that `X` is locally Noetherian, `U` is dense, the cover is
unramified over `X` in codimension one, and the boundary local rings are
regular. These source-matching obligations are not proved or replaced by
opaque stand-in predicates here.

For a chosen extension, Lemma 58.10.3, Tag `0BQF`, supplies full faithfulness
of restriction on finite étale covers when `U` is dense open, the underlying
space of `X` is Noetherian, and the punctured spectrum of the strict
henselization at each boundary point is connected. Bijectivity on the
automorphism groups of the chosen cover is its selected consequence below.

The conclusion objects make sense for any `j`; their intended open-immersion
application must verify the source hypotheses just listed. No compactified
Chow class, Chow restriction map, or graph-realization square is supplied by
either interface.

Sources: https://stacks.math.columbia.edu/tag/0H2W and
https://stacks.math.columbia.edu/tag/0BQF.
-/

set_option autoImplicit false

namespace HodgeConjecture.LiteratureInputs

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence

noncomputable section

universe u v

variable {X U Y : Scheme.{u}}

/-- An actual finite étale extension, identified with the original cover
after actual scheme base change. The comparison is an isomorphism over `U`. -/
structure FiniteEtaleExtension (j : U ⟶ X) (p : Y ⟶ U) where
  carrier : Scheme.{u}
  toBase : carrier ⟶ X
  finite : IsFinite toBase
  etale : IsEtale toBase
  comparison : Over.mk p ≅ (Over.pullback j).obj (Over.mk toBase)

/-- The selected existence conclusion of a finite étale extension theorem.
Supplying this class is an explicit hypothesis, not a default instance. -/
class FiniteEtaleExtensionHypothesis (j : U ⟶ X) (p : Y ⟶ U) : Prop where
  extension_nonempty : Nonempty (FiniteEtaleExtension j p)

/-- Choose an actual extension only under the explicitly stated existence input. -/
def chosenExtension (j : U ⟶ X) (p : Y ⟶ U)
    [FiniteEtaleExtensionHypothesis j p] : FiniteEtaleExtension j p :=
  Classical.choice (FiniteEtaleExtensionHypothesis.extension_nonempty (j := j) (p := p))

namespace FiniteEtaleExtension

variable {j : U ⟶ X} {p : Y ⟶ U}

/-- Forgetting the over-category comparison gives its actual scheme isomorphism. -/
def comparisonIso (E : FiniteEtaleExtension j p) :
    Y ≅ pullback E.toBase j :=
  (Over.forget U).mapIso E.comparison

@[simp, reassoc]
theorem comparisonIso_hom_snd (E : FiniteEtaleExtension j p) :
    E.comparisonIso.hom ≫ pullback.snd E.toBase j = p :=
  Over.w E.comparison.hom

/-- The comparison certifies finiteness of the original morphism itself. -/
theorem original_isFinite (E : FiniteEtaleExtension j p) : IsFinite p := by
  rw [← E.comparisonIso_hom_snd]
  exact MorphismProperty.comp_mem @IsFinite _ _ inferInstance
    (MorphismProperty.pullback_snd E.toBase j E.finite)

/-- The comparison likewise certifies that the original cover is étale. -/
theorem original_isEtale (E : FiniteEtaleExtension j p) : IsEtale p := by
  rw [← E.comparisonIso_hom_snd]
  exact MorphismProperty.comp_mem @IsEtale _ _ inferInstance
    (MorphismProperty.pullback_snd E.toBase j E.etale)

/-- The morphism from the original cover into its extension. -/
def inclusion (E : FiniteEtaleExtension j p) : Y ⟶ E.carrier :=
  E.comparisonIso.hom ≫ pullback.fst E.toBase j

@[simp, reassoc]
theorem inclusion_toBase (E : FiniteEtaleExtension j p) :
    E.inclusion ≫ E.toBase = p ≫ j := by
  rw [inclusion, Category.assoc, pullback.condition, ← Category.assoc,
    comparisonIso_hom_snd]

/-- In the intended open-immersion application, the original cover is an
actual open subscheme of the extended cover. -/
theorem inclusion_isOpenImmersion (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] : IsOpenImmersion E.inclusion := by
  unfold inclusion
  infer_instance

/-- The extended cover is proper because its structural morphism is finite. -/
theorem toBase_isProper (E : FiniteEtaleExtension j p) : IsProper E.toBase := by
  letI := E.finite
  infer_instance

/-- Actual restriction of deck automorphisms: base change in the slice
category, followed by the chosen comparison with the original cover. -/
def restriction (E : FiniteEtaleExtension j p) :
    DeckTransformation E.toBase →* DeckTransformation p :=
  (Aut.autMulEquivOfIso E.comparison.symm).toMonoidHom.comp
    ((Over.pullback j).mapAut (Over.mk E.toBase))

@[simp]
theorem restriction_toSchemeHom (E : FiniteEtaleExtension j p)
    (σ : DeckTransformation E.toBase) :
    (E.restriction σ).toSchemeHom =
      E.comparisonIso.hom ≫ ((Over.pullback j).map σ.hom).left ≫
        E.comparisonIso.inv := rfl

/-- Restriction really commutes with the original cover's inclusion. -/
@[reassoc]
theorem restriction_inclusion (E : FiniteEtaleExtension j p)
    (σ : DeckTransformation E.toBase) :
    (E.restriction σ).toSchemeHom ≫ E.inclusion =
      E.inclusion ≫ σ.toSchemeHom := by
  simp only [restriction_toSchemeHom, inclusion, Category.assoc,
    Iso.inv_hom_id_assoc]
  change E.comparisonIso.hom ≫
      pullback.lift (pullback.fst E.toBase j ≫ σ.toSchemeHom)
        (pullback.snd E.toBase j) _ ≫ pullback.fst E.toBase j = _
  rw [pullback.lift_fst]

end FiniteEtaleExtension

/-- The selected full-faithfulness consequence for one chosen finite étale
extension: every original deck automorphism extends uniquely. This is
separate from the existence of that extension and does not depend on an
auxiliary acting group. -/
class DeckExtensionHypothesis {j : U ⟶ X} {p : Y ⟶ U}
    (E : FiniteEtaleExtension j p) : Prop where
  restriction_bijective : Function.Bijective E.restriction

namespace FiniteEtaleExtension

variable {j : U ⟶ X} {p : Y ⟶ U}

/-- Restriction is an equivalence of the actual deck groups under its
explicit selected full-faithfulness hypothesis. -/
def deckEquiv (E : FiniteEtaleExtension j p) [DeckExtensionHypothesis E] :
    DeckTransformation E.toBase ≃* DeckTransformation p :=
  MulEquiv.ofBijective E.restriction
    (DeckExtensionHypothesis.restriction_bijective (E := E))

@[simp]
theorem deckEquiv_apply (E : FiniteEtaleExtension j p) [DeckExtensionHypothesis E]
    (σ : DeckTransformation E.toBase) : E.deckEquiv σ = E.restriction σ := rfl

/-- Lift any supplied group action using the actual deck-group equivalence. -/
def liftDeckAction (E : FiniteEtaleExtension j p) [DeckExtensionHypothesis E]
    {G : Type v} [Group G] (α : FiniteDeckAction p G) :
    FiniteDeckAction E.toBase G :=
  E.deckEquiv.symm.toMonoidHom.comp α

/-- Every lifted deck automorphism restricts to its prescribed original value. -/
@[simp]
theorem restriction_liftDeckAction (E : FiniteEtaleExtension j p)
    [DeckExtensionHypothesis E] {G : Type v} [Group G]
    (α : FiniteDeckAction p G) (g : G) :
    E.restriction (E.liftDeckAction α g) = α g :=
  E.deckEquiv.apply_symm_apply (α g)

/-- The whole lifted action has exactly the original restricted action. -/
theorem restriction_comp_liftDeckAction (E : FiniteEtaleExtension j p)
    [DeckExtensionHypothesis E] {G : Type v} [Group G]
    (α : FiniteDeckAction p G) :
    E.restriction.comp (E.liftDeckAction α) = α := by
  apply MonoidHom.ext
  intro g
  exact E.restriction_liftDeckAction α g

/-- The action lift is unique; uniqueness is not assumed again per group. -/
theorem liftDeckAction_unique (E : FiniteEtaleExtension j p)
    [DeckExtensionHypothesis E] {G : Type v} [Group G]
    (α : FiniteDeckAction p G) (β : FiniteDeckAction E.toBase G)
    (hβ : E.restriction.comp β = α) : β = E.liftDeckAction α := by
  apply MonoidHom.ext
  intro g
  apply (DeckExtensionHypothesis.restriction_bijective (E := E)).injective
  exact (DFunLike.congr_fun hβ g).trans (E.restriction_liftDeckAction α g).symm

/-- The original and extended actions commute with the actual cover inclusion. -/
@[reassoc]
theorem liftDeckAction_inclusion (E : FiniteEtaleExtension j p)
    [DeckExtensionHypothesis E] {G : Type v} [Group G]
    (α : FiniteDeckAction p G) (g : G) :
    (α g).toSchemeHom ≫ E.inclusion =
      E.inclusion ≫ (E.liftDeckAction α g).toSchemeHom := by
  rw [← E.restriction_liftDeckAction α g]
  exact E.restriction_inclusion _

end FiniteEtaleExtension

end

end HodgeConjecture.LiteratureInputs
