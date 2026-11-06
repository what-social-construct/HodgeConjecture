module

public import HodgeConjecture.Cycles.OpenGrading
public import HodgeConjecture.Cycles.GradedPushforward

@[expose] public section

/-!
# Exactness of open and closed maps on actual cycles

The reduced closed complement is constructed from the vanishing ideal of
the actual complement of the open image. Closed pushforward has image the
cycles supported on that boundary; open restriction has exactly that kernel.
The same equality holds in each dimension-function degree, over any semiring,
without Noetherianity or reducedness of the ambient scheme.

This is the cycle-support step in Stacks Lemma 42.19.3 (02RX):
https://stacks.math.columbia.edu/tag/02RX. Quotient exactness additionally
requires lifting principal relations; this file only concerns actual cycles.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

variable {X Z U : Scheme.{u}}

/-- The reduced closed boundary of the actual open image. -/
def openComplementIdeal (j : U ⟶ X) [IsOpenImmersion j] : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩

instance openComplement_isReduced (j : U ⟶ X) [IsOpenImmersion j] :
    IsReduced (openComplementIdeal j).subscheme :=
  vanishingIdeal_subscheme_isReduced X _

/-- The constructed closed scheme has precisely the complementary point set. -/
theorem range_openComplement (j : U ⟶ X) [IsOpenImmersion j] :
    Set.range (openComplementIdeal j).subschemeι.base = (Set.range j.base)ᶜ := by
  simp [openComplementIdeal, Scheme.IdealSheafData.range_subschemeι]

/-- Closed pushforward does not identify distinct integral supports. -/
theorem closedImageSubscheme_injective (i : Z ⟶ X) [IsClosedImmersion i] :
    Function.Injective (fun W ↦ closedImageSubscheme i W) := by
  intro W V h
  apply (pointEquivIntegralClosedSubscheme Z).symm.injective
  apply i.isClosedEmbedding.injective
  change i (ambientGenericPoint W) = i (ambientGenericPoint V)
  simpa only [ambientGenericPoint_closedImageSubscheme] using
    congrArg ambientGenericPoint h

/-- The original coefficient is retained on its actual closed image. -/
theorem closedImmersionPushforward_apply_image (R : Type v) [Semiring R]
    (i : Z ⟶ X) [IsClosedImmersion i] (c : Cycles Z R)
    (W : IntegralClosedSubscheme Z) :
    closedImmersionPushforward R i c (closedImageSubscheme i W) = c W := by
  classical
  have h : closedImmersionPushforward R i =
      Finsupp.lmapDomain R R (fun W ↦ closedImageSubscheme i W) := by
    apply Finsupp.lhom_ext
    intro V r
    simp [closedImageCycle, fundamentalCycle, Finsupp.smul_single]
  rw [h, Finsupp.lmapDomain_apply]
  exact Finsupp.mapDomain_apply_of_injective (closedImageSubscheme_injective i) c W

/-- The actual closed map reaches exactly the cycles with generic points
in its image, including trivial coefficient semirings. -/
theorem range_closedImmersionPushforward (R : Type v) [Semiring R]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    LinearMap.range (closedImmersionPushforward R i) =
      Finsupp.supported R R {W | ambientGenericPoint W ∈ Set.range i.base} := by
  rw [closedImmersionPushforward, Finsupp.range_linearCombination,
    Finsupp.supported_eq_span_single]
  congr 1
  ext c
  constructor
  · rintro ⟨W, rfl⟩
    exact ⟨closedImageSubscheme i W,
      ⟨ambientGenericPoint W, (ambientGenericPoint_closedImageSubscheme i W).symm⟩, rfl⟩
  · rintro ⟨W, ⟨z, hz⟩, rfl⟩
    refine ⟨pointSupport Z z, ?_⟩
    simp [closedImageCycle, closedImage_pointSupport, hz, pointSupport_ambientGenericPoint,
      fundamentalCycle]

/-- Restriction vanishes exactly on cycles supported away from the open. -/
theorem ker_openRestriction (R : Type v) [Semiring R]
    (j : U ⟶ X) [IsOpenImmersion j] :
    LinearMap.ker (openRestriction R j) =
      Finsupp.supported R R {W | ambientGenericPoint W ∉ Set.range j.base} := by
  classical
  ext c
  rw [LinearMap.mem_ker, Finsupp.mem_supported']
  constructor
  · intro hc W hW
    have hmem : ambientGenericPoint W ∈ Set.range j.base := by simpa using hW
    letI := (nonempty_openRestrictionSubscheme_iff j W).mpr hmem
    have h := congrArg (fun b : Cycles U R ↦ b (openRestrictionSubscheme j W)) hc
    simpa only [openRestriction_apply, openClosureSubscheme_openRestrictionSubscheme,
      Finsupp.zero_apply] using h
  · intro hc
    ext W
    rw [openRestriction_apply]
    exact hc (openClosureSubscheme j W) (by
      simp only [Set.mem_setOf_eq, openClosureSubscheme_ambientGenericPoint, not_not]
      exact ⟨ambientGenericPoint W, rfl⟩)

/-- Cycle exactness for any actual complementary open/closed pair. -/
theorem range_closedPushforward_eq_ker_openRestriction (R : Type v) [Semiring R]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) :
    LinearMap.range (closedImmersionPushforward R i) =
      LinearMap.ker (openRestriction R j) := by
  rw [range_closedImmersionPushforward, ker_openRestriction, hcomp]
  rfl

/-- Homogeneous exactness uses the actual restricted dimension functions.
The boundary representative automatically has the same dimension degree. -/
theorem range_gradedClosedPushforward_eq_ker_gradedOpenRestriction
    (R : Type v) [Semiring R] (δ : DimensionFunction X)
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hcomp : Set.range i.base = (Set.range j.base)ᶜ) (n : ℤ) :
    LinearMap.range (gradedClosedImmersionPushforwardWithCoefficients R
      (δ.comapClosedImmersion i) δ i
      (fun W ↦ (supportDegree_comapClosedImmersion δ i W).symm) n) =
      LinearMap.ker (gradedOpenRestriction R δ j n) := by
  ext c
  constructor
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    have h : closedImmersionPushforward R i b.val ∈
        LinearMap.range (closedImmersionPushforward R i) := ⟨b.val, rfl⟩
    rw [range_closedPushforward_eq_ker_openRestriction R i j hcomp] at h
    exact h
  · intro hc
    have hz : openRestriction R j c.val = 0 := congrArg Subtype.val hc
    change c.val ∈ LinearMap.ker (openRestriction R j) at hz
    rw [← range_closedPushforward_eq_ker_openRestriction R i j hcomp] at hz
    obtain ⟨b, hb⟩ := hz
    have hdegree : b ∈ cyclesOfDegree R (δ.comapClosedImmersion i) n := by
      apply (mem_cyclesOfDegree_iff R _ n b).mpr
      intro W hW
      rw [supportDegree_comapClosedImmersion]
      apply (mem_cyclesOfDegree_iff R δ n c.val).mp c.property
      rw [← hb, closedImmersionPushforward_apply_image]
      exact hW
    exact ⟨⟨b, hdegree⟩, Subtype.ext hb⟩

/-- Exactness is instantiated by the constructed reduced complement,
without a supplied complementary-pair hypothesis. -/
theorem range_openComplementPushforward_eq_ker (R : Type v) [Semiring R]
    (δ : DimensionFunction X) (j : U ⟶ X) [IsOpenImmersion j] (n : ℤ) :
    LinearMap.range (gradedClosedImmersionPushforwardWithCoefficients R
      (δ.comapClosedImmersion (openComplementIdeal j).subschemeι) δ
      (openComplementIdeal j).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion δ _ W).symm) n) =
      LinearMap.ker (gradedOpenRestriction R δ j n) :=
  range_gradedClosedPushforward_eq_ker_gradedOpenRestriction R δ _ j (range_openComplement j) n

end

end HodgeConjecture.SchemeCycles
