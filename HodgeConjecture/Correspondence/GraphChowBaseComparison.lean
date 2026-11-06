module

public import HodgeConjecture.Correspondence.GraphChowAlgebra
public import HodgeConjecture.Correspondence.GraphCycleBaseComparison
public import HodgeConjecture.Cycles.FiniteGrading
public import HodgeConjecture.Cycles.RationalChowPushforward

@[expose] public section

/-!
# Graph Chow classes in the absolute product

The closed inclusion of the relative pair product into the product over
the field preserves the canonical field grading. Its actual rational Chow
pushforward carries relative graph classes to their absolute graph classes.
The induced map on graph-generated convolution algebras is multiplicative
and realizes as this same closed Chow pushforward. This uses the existing
principal-relation quotients; it does not assert injectivity or construct
a compactification.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u

variable (k : Type u) [Field k] {X S : Scheme.{u}}
variable (p : X ⟶ S) (b : S ⟶ Spec (CommRingCat.of k))

@[reassoc (attr := simp)]
theorem pairBaseComparison_graphPairStructure :
    pairBaseComparison p b ≫ graphPairStructure k (p ≫ b) (𝟙 _) =
      graphPairStructure k p b := by
  simp [graphPairStructure]

theorem graphChowDimension_absolute [IsIntegral X] [LocallyOfFiniteType (p ≫ b)] :
    graphChowDimension k (p ≫ b) (𝟙 _) = graphChowDimension k p b := by
  simp only [graphChowDimension, Category.comp_id]

/-- Equality of integer degrees transports the existing Chow quotient linearly. -/
def chowDegreeEquiv {Y : Scheme.{u}} [IsNoetherian Y]
    (δ : DimensionFunction Y) {m n : ℤ} (h : m = n) :
    RationalChowGroup δ m ≃ₗ[ℚ] RationalChowGroup δ n := by
  subst n
  exact LinearEquiv.refl ℚ _

theorem chowDegreeEquiv_classMap {Y : Scheme.{u}} [IsNoetherian Y]
    (δ : DimensionFunction Y) {m n : ℤ} (h : m = n) (c : cyclesOfDegree ℚ δ m) :
    chowDegreeEquiv δ h (rationalClassMap δ m c) =
      rationalClassMap δ n ⟨c.val, Eq.mp (congrArg (fun d ↦ c.val ∈ cyclesOfDegree ℚ δ d) h)
        c.property⟩ := by
  subst n
  rfl

/-- The closed relative-to-absolute pair inclusion preserves actual support degrees. -/
theorem graphChowBaseComparison_supportDegree [IsSeparated b]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    [LocallyOfFiniteType (graphPairStructure k (p ≫ b) (𝟙 _))]
    (W : IntegralClosedSubscheme (pullback p p)) :
    supportDegree (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
        (closedImageSubscheme (pairBaseComparison p b) W) =
      supportDegree (graphPairDimensionFunction k p b) W := by
  rw [supportDegree_closedImageSubscheme]
  have h := DimensionFunction.ofLocallyOfFiniteType_apply_of_isFinite k
    (graphPairStructure k (p ≫ b) (𝟙 _)) (pairBaseComparison p b)
    (ambientGenericPoint W)
  simpa only [pairBaseComparison_graphPairStructure, graphPairDimensionFunction,
    supportDegree] using h.symm

/-- Actual closed Chow pushforward from the relative to the absolute pair product. -/
def graphChowBasePushforward [IsSeparated b]
    [LocallyOfFiniteType (graphPairStructure k p b)]
    [LocallyOfFiniteType (graphPairStructure k (p ≫ b) (𝟙 _))]
    [IsNoetherian (pullback p p)] [IsNoetherian (pullback (p ≫ b) (p ≫ b))]
    (n : ℤ) :
    RationalChowGroup (graphPairDimensionFunction k p b) n →ₗ[ℚ]
      RationalChowGroup (graphPairDimensionFunction k (p ≫ b) (𝟙 _)) n :=
  rationalChowClosedImmersionPushforward
    (graphPairDimensionFunction k p b) (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
    (pairBaseComparison p b) (graphChowBaseComparison_supportDegree k p b) n

section Graphs

variable [IsSeparated p] [IsSeparated b] [IsIntegral X]
variable [LocallyOfFiniteType (p ≫ b)]
variable [LocallyOfFiniteType (graphPairStructure k p b)]
variable [LocallyOfFiniteType (graphPairStructure k (p ≫ b) (𝟙 _))]
variable [IsNoetherian (pullback p p)] [IsNoetherian (pullback (p ≫ b) (p ≫ b))]

/-- The same absolute graph, expressed in the relative source's equal canonical degree. -/
def absoluteGradedGraphCycle (σ : DeckTransformation p) :
    cyclesOfDegree ℚ (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
      (graphChowDimension k p b) :=
  ⟨graphCycle (p ≫ b) ℚ (forgetDeckBase p b σ), by
    have h := (gradedGraphCycle k (p ≫ b) (𝟙 _) (forgetDeckBase p b σ)).property
    change graphCycle (p ≫ b) ℚ (forgetDeckBase p b σ) ∈
      cyclesOfDegree ℚ (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
        (graphChowDimension k (p ≫ b) (𝟙 _)) at h
    rwa [graphChowDimension_absolute] at h⟩

/-- The actual absolute graph class, with its degree normalized to the source. -/
def absoluteGraphChowClass (σ : DeckTransformation p) :
    RationalChowGroup (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
      (graphChowDimension k p b) :=
  rationalClassMap _ _ (absoluteGradedGraphCycle k p b σ)

/-- Only the equal integer degree is transported; the actual absolute Chow quotient is retained. -/
def graphChowAbsoluteDegreeEquiv :
    RationalChowGroup (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
        (graphChowDimension k (p ≫ b) (𝟙 _)) ≃ₗ[ℚ]
      RationalChowGroup (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
        (graphChowDimension k p b) :=
  chowDegreeEquiv _ (graphChowDimension_absolute k p b)

omit [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)] in
@[simp]
theorem graphChowAbsoluteDegreeEquiv_graphChowClass (σ : DeckTransformation p) :
    graphChowAbsoluteDegreeEquiv k p b
        (graphChowClass k (p ≫ b) (𝟙 _) (forgetDeckBase p b σ)) =
      absoluteGraphChowClass k p b σ := by
  unfold graphChowAbsoluteDegreeEquiv graphChowClass absoluteGraphChowClass
  rw [chowDegreeEquiv_classMap]
  congr 1

/-- Closed Chow pushforward carries each relative graph to its actual absolute graph. -/
@[simp]
theorem graphChowBasePushforward_graphChowClass (σ : DeckTransformation p) :
    graphChowBasePushforward k p b (graphChowDimension k p b) (graphChowClass k p b σ) =
      absoluteGraphChowClass k p b σ := by
  change rationalClassMap _ _
    (gradedClosedImmersionPushforwardWithCoefficients ℚ _ _ _ _ _
      (gradedGraphCycle k p b σ)) = rationalClassMap _ _ _
  congr 1
  apply Subtype.ext
  exact graphCycle_pairBaseComparison p b ℚ σ

/-- Weighted graph assembly in the actual absolute Chow group. -/
def absoluteGraphChowLinearMap :
    MonoidAlgebra ℚ (DeckTransformation p) →ₗ[ℚ]
      RationalChowGroup (graphPairDimensionFunction k (p ≫ b) (𝟙 _))
        (graphChowDimension k p b) :=
  (Finsupp.linearCombination ℚ (absoluteGraphChowClass k p b)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

omit [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)] in
@[simp]
theorem absoluteGraphChowLinearMap_single (σ : DeckTransformation p) (q : ℚ) :
    absoluteGraphChowLinearMap k p b (MonoidAlgebra.single σ q) =
      q • absoluteGraphChowClass k p b σ := by
  simp [absoluteGraphChowLinearMap]

/-- The complete weighted graph square descends through rational equivalence. -/
theorem graphChowLinearMap_baseComparison :
    (graphChowBasePushforward k p b (graphChowDimension k p b)).comp
        (graphChowLinearMap k p b) = absoluteGraphChowLinearMap k p b := by
  apply (LinearMap.cancel_right (MonoidAlgebra.coeffLinearEquiv ℚ).symm.surjective).mp
  apply Finsupp.lhom_ext
  intro σ q
  change graphChowBasePushforward k p b (graphChowDimension k p b)
      (graphChowLinearMap k p b (MonoidAlgebra.single σ q)) =
    absoluteGraphChowLinearMap k p b (MonoidAlgebra.single σ q)
  rw [graphChowLinearMap_single, map_smul,
    graphChowBasePushforward_graphChowClass, absoluteGraphChowLinearMap_single]

omit [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)] in
/-- The normalized assembly is the original absolute assembly after forgetting the base. -/
theorem absoluteGraphChowLinearMap_eq :
    absoluteGraphChowLinearMap k p b =
      (graphChowAbsoluteDegreeEquiv k p b).toLinearMap.comp
        ((graphChowLinearMap k (p ≫ b) (𝟙 _)).comp
          (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b)).toLinearMap) := by
  apply (LinearMap.cancel_right (MonoidAlgebra.coeffLinearEquiv ℚ).symm.surjective).mp
  apply Finsupp.lhom_ext
  intro σ q
  change absoluteGraphChowLinearMap k p b (MonoidAlgebra.single σ q) =
    graphChowAbsoluteDegreeEquiv k p b
      (graphChowLinearMap k (p ≫ b) (𝟙 _)
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b)
          (MonoidAlgebra.single σ q)))
  simp only [absoluteGraphChowLinearMap_single,
    MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    graphChowLinearMap_single, map_smul,
    graphChowAbsoluteDegreeEquiv_graphChowClass]

/-- The actual closed Chow square carries every relative graph relation to an absolute one. -/
theorem graphChowKernelIdeal_le_comap_forgetDeckBase :
    graphChowKernelIdeal k p b ≤
      (graphChowKernelIdeal k (p ≫ b) (𝟙 _)).comap
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b)) := by
  intro a ha
  change graphChowLinearMap k (p ≫ b) (𝟙 _)
    (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b) a) = 0
  have hrel : graphChowLinearMap k p b a = 0 := ha
  have hnorm : absoluteGraphChowLinearMap k p b a = 0 := by
    rw [← LinearMap.congr_fun (graphChowLinearMap_baseComparison k p b) a]
    change graphChowBasePushforward k p b _ (graphChowLinearMap k p b a) = 0
    rw [hrel, map_zero]
  rw [absoluteGraphChowLinearMap_eq] at hnorm
  change graphChowAbsoluteDegreeEquiv k p b
    (graphChowLinearMap k (p ≫ b) (𝟙 _)
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b) a)) = 0 at hnorm
  exact (graphChowAbsoluteDegreeEquiv k p b).injective
    (by simpa only [map_zero] using hnorm)

/-- Genuine closed Chow pushforward on graph classes is multiplicative for graph convolution. -/
def graphChowBaseAlgHom : GraphChowAlgebra k p b →ₐ[ℚ]
    GraphChowAlgebra k (p ≫ b) (𝟙 _) :=
  Ideal.quotientMapₐ (graphChowKernelIdeal k (p ≫ b) (𝟙 _))
    (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b))
    (graphChowKernelIdeal_le_comap_forgetDeckBase k p b)

@[simp]
theorem graphChowBaseAlgHom_graphChowAlgHom (a : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowBaseAlgHom k p b (graphChowAlgHom k p b a) =
      graphChowAlgHom k (p ≫ b) (𝟙 _)
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b) a) := rfl

/-- Multiplicative graph passage to the absolute product realizes as actual closed Chow pushforward. -/
theorem graphChowBaseAlgHom_realization (z : GraphChowAlgebra k p b) :
    graphChowAbsoluteDegreeEquiv k p b
        (graphChowRealization k (p ≫ b) (𝟙 _) (graphChowBaseAlgHom k p b z)) =
      graphChowBasePushforward k p b (graphChowDimension k p b)
        (graphChowRealization k p b z) := by
  obtain ⟨a, rfl⟩ := graphChowAlgHom_surjective k p b z
  rw [graphChowBaseAlgHom_graphChowAlgHom, graphChowRealization_graphChowAlgHom,
    graphChowRealization_graphChowAlgHom]
  have h := LinearMap.congr_fun (graphChowLinearMap_baseComparison k p b) a
  rw [absoluteGraphChowLinearMap_eq] at h
  exact h.symm

/-- In particular, passage to absolute graph classes preserves actual convolution idempotents. -/
theorem graphChowBaseAlgHom_isIdempotent (z : GraphChowAlgebra k p b)
    (hz : IsIdempotentElem z) : IsIdempotentElem (graphChowBaseAlgHom k p b z) :=
  hz.map (graphChowBaseAlgHom k p b)

end Graphs

end

end HodgeConjecture.SchemeCorrespondence
