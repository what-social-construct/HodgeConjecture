module

import HodgeConjecture.Correspondence.GraphChowAlgebra
import HodgeConjecture.Correspondence.GraphChowBaseComparison
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
Actual graph classes, their geometric left and right actions, and the exact
graph-generated Chow quotient. Run with
`lake env lean research/GraphChowVerification.lean`.

These regressions retain the order of arbitrary deck transformations,
descend actual principal relations on both sides, and compare the resulting
projectors with their actual rational Chow representatives. The absolute
comparison is the genuine closed Chow pushforward. No ambient intersection
product or prescribed cohomological realization is assumed. The declaration
audit rejects every axiom outside the standard three.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCycles HodgeConjecture.SchemeCorrespondence

noncomputable section

universe u v

variable (k : Type u) [Field k] {X S : Scheme.{u}}
variable (p : X ⟶ S) (b : S ⟶ Spec (CommRingCat.of k))
variable [IsSeparated p] [IsIntegral X] [LocallyOfFiniteType (p ≫ b)]
variable [LocallyOfFiniteType (graphPairStructure k p b)] [IsNoetherian (pullback p p)]

-- Signed rational weights survive passage through homogeneous cycles to Chow.
example (σ τ : DeckTransformation p) :
    graphChowLinearMap k p b
      (MonoidAlgebra.single σ (-3 / 2 : ℚ) + MonoidAlgebra.single τ (5 / 3 : ℚ)) =
      (-3 / 2 : ℚ) • graphChowClass k p b σ +
        (5 / 3 : ℚ) • graphChowClass k p b τ := by
  simp only [map_add, graphChowLinearMap_single]

-- Right composition reverses endomorphism order; no commutativity is assumed.
example (n : ℤ) (σ τ : DeckTransformation p)
    (z : RationalChowGroup (graphPairDimensionFunction k p b) n) :
    graphChowRightAction k p b n τ (graphChowRightAction k p b n σ z) =
      graphChowRightAction k p b n (σ * τ) z := by
  rw [graphChowRightAction_mul]
  rfl

example (n : ℤ) (σ τ : DeckTransformation p)
    (z : RationalChowGroup (graphPairDimensionFunction k p b) n) :
    graphChowLeftAction k p b n σ (graphChowLeftAction k p b n τ z) =
      graphChowLeftAction k p b n (σ * τ) z := by
  rw [graphChowLeftAction_mul]
  rfl

-- The actual coordinate pullbacks commute on every degree, independently
-- of any equality between the deck transformations themselves.
example (n : ℤ) (σ τ : DeckTransformation p) :
    (graphChowLeftAction k p b n σ).comp (graphChowRightAction k p b n τ) =
      (graphChowRightAction k p b n τ).comp (graphChowLeftAction k p b n σ) := by
  unfold graphChowLeftAction graphChowRightAction
  rw [graphPairChowPullback_comp, graphPairChowPullback_comp]
  apply graphPairChowPullback_congr
  apply pullback.hom_ext <;> simp [Category.assoc]

-- The two actions keep opposite multiplication orders on the same graph class.
example (σ τ : DeckTransformation p)
    (h : graphChowClass k p b (σ * τ) ≠ graphChowClass k p b (τ * σ)) :
    graphChowRightAction k p b (graphChowDimension k p b) τ (graphChowClass k p b σ) ≠
      graphChowLeftAction k p b (graphChowDimension k p b) τ (graphChowClass k p b σ) := by
  simpa only [graphChowRightAction_graphChowClass, graphChowLeftAction_graphChowClass]
    using h

-- Left and right multiplication commute on graph classes by associativity,
-- even when the underlying deck transformations do not commute.
example (σ τ υ : DeckTransformation p) :
    graphChowLeftAction k p b (graphChowDimension k p b) σ
        (graphChowRightAction k p b (graphChowDimension k p b) τ
          (graphChowClass k p b υ)) =
      graphChowRightAction k p b (graphChowDimension k p b) τ
        (graphChowLeftAction k p b (graphChowDimension k p b) σ
          (graphChowClass k p b υ)) := by
  simp only [graphChowRightAction_graphChowClass, graphChowLeftAction_graphChowClass,
    mul_assoc]

-- Actual principal relations vanish in the exact graph quotient.
example (a : MonoidAlgebra ℚ (DeckTransformation p))
    (ha : gradedGraphCycleLinearMap k p b a ∈
      rationalPrincipalRelations (graphPairDimensionFunction k p b) (graphChowDimension k p b)) :
    graphChowAlgHom k p b a = 0 := by
  have h : graphChowLinearMap k p b a = 0 :=
    (rationalClassMap_eq_zero_iff _ _ _).mpr ha
  simpa only [map_zero] using (graphChowAlgHom_eq_iff k p b a 0).mpr
    (by simpa only [map_zero] using h)

-- Equality of actual Chow classes is preserved by multiplication on both sides.
example (a c r : MonoidAlgebra ℚ (DeckTransformation p))
    (h : graphChowLinearMap k p b a = graphChowLinearMap k p b c) :
    graphChowLinearMap k p b (r * a) = graphChowLinearMap k p b (r * c) ∧
      graphChowLinearMap k p b (a * r) = graphChowLinearMap k p b (c * r) := by
  constructor
  · rw [← graphChowLeftLinearAction_graphChowLinearMap,
      ← graphChowLeftLinearAction_graphChowLinearMap, h]
  · rw [← graphChowRightLinearAction_graphChowLinearMap,
      ← graphChowRightLinearAction_graphChowLinearMap, h]

-- The algebra has exactly the existing graph-Chow equalities.
example (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowLinearMap k p b a = graphChowLinearMap k p b c ↔
      graphChowAlgHom k p b a = graphChowAlgHom k p b c :=
  (graphChowAlgHom_eq_iff k p b a c).symm

-- Multiplication realizes as an actual representative in the original quotient.
example (a c : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowRealization k p b (graphChowAlgHom k p b a * graphChowAlgHom k p b c) =
      rationalClassMap (graphPairDimensionFunction k p b) (graphChowDimension k p b)
        (gradedGraphCycleLinearMap k p b (a * c)) := by
  rw [← map_mul, graphChowRealization_graphChowAlgHom, graphChowLinearMap_apply]

section Average

variable {G : Type v} [Group G] [Fintype G] (α : FiniteDeckAction p G)

-- The idempotent and its geometric representative are checked together.
example :
    IsIdempotentElem (graphChowAveragingProjector k p b α) ∧
      graphChowRealization k p b (graphChowAveragingProjector k p b α) =
        (Fintype.card G : ℚ)⁻¹ • ∑ g : G, graphChowClass k p b (α g) :=
  ⟨graphChowAveragingProjector_isIdempotent k p b α,
    graphChowRealization_averagingProjector k p b α⟩

example :
    IsIdempotentElem (graphChowComplementaryProjector k p b α) ∧
      graphChowAveragingProjector k p b α * graphChowComplementaryProjector k p b α = 0 ∧
      graphChowComplementaryProjector k p b α * graphChowAveragingProjector k p b α = 0 := by
  exact ⟨graphChowComplementaryProjector_isIdempotent k p b α, by simp, by simp⟩

example :
    graphChowRealization k p b (graphChowAveragingProjector k p b α) +
        graphChowRealization k p b (graphChowComplementaryProjector k p b α) =
      graphChowClass k p b 1 :=
  graphChowRealization_average_add_complement k p b α

end Average

-- Only the averaged subgroup must be finite; the ambient action group is arbitrary.
example {G : Type v} [Group G] (H : Subgroup G) [Fintype H]
    (α : FiniteDeckAction p G) :
    IsIdempotentElem (graphChowSubgroupProjector k p b H α) ∧
      graphChowRealization k p b (graphChowSubgroupProjector k p b H α) =
        (Fintype.card H : ℚ)⁻¹ • ∑ h : H, graphChowClass k p b (α h) :=
  ⟨graphChowSubgroupProjector_isIdempotent k p b H α,
    graphChowRealization_subgroupProjector k p b H α⟩

section Absolute

variable [IsSeparated b]
variable [LocallyOfFiniteType (graphPairStructure k (p ≫ b) (𝟙 _))]
variable [IsNoetherian (pullback (p ≫ b) (p ≫ b))]

-- The whole weighted graph square descends through actual rational equivalence.
example (a : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowBasePushforward k p b (graphChowDimension k p b)
        (graphChowRealization k p b (graphChowAlgHom k p b a)) =
      absoluteGraphChowLinearMap k p b a := by
  rw [graphChowRealization_graphChowAlgHom]
  exact LinearMap.congr_fun (graphChowLinearMap_baseComparison k p b) a

-- The target is the ordinary absolute graph map after its actual degree equality.
example (a : MonoidAlgebra ℚ (DeckTransformation p)) :
    graphChowBasePushforward k p b (graphChowDimension k p b) (graphChowLinearMap k p b a) =
      graphChowAbsoluteDegreeEquiv k p b
        (graphChowLinearMap k (p ≫ b) (𝟙 _)
          (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b) a)) := by
  calc
    _ = absoluteGraphChowLinearMap k p b a :=
      LinearMap.congr_fun (graphChowLinearMap_baseComparison k p b) a
    _ = _ := LinearMap.congr_fun (absoluteGraphChowLinearMap_eq k p b) a

-- This tests a signed sum, not just a coefficient-one graph.
example (σ τ : DeckTransformation p) :
    graphChowBasePushforward k p b (graphChowDimension k p b)
        ((-2 : ℚ) • graphChowClass k p b σ + (1 / 3 : ℚ) • graphChowClass k p b τ) =
      (-2 : ℚ) • absoluteGraphChowClass k p b σ +
        (1 / 3 : ℚ) • absoluteGraphChowClass k p b τ := by
  simp only [map_add, map_smul, graphChowBasePushforward_graphChowClass]

-- Multiplicative absolute passage preserves the projector and has exactly
-- the normalized absolute graph sum as its actual Chow realization.
example {G : Type v} [Group G] [Fintype G] (α : FiniteDeckAction p G) :
    IsIdempotentElem
        (graphChowBaseAlgHom k p b (graphChowAveragingProjector k p b α)) ∧
      graphChowAbsoluteDegreeEquiv k p b
          (graphChowRealization k (p ≫ b) (𝟙 _)
            (graphChowBaseAlgHom k p b (graphChowAveragingProjector k p b α))) =
        (Fintype.card G : ℚ)⁻¹ • ∑ g : G, absoluteGraphChowClass k p b (α g) := by
  constructor
  · exact graphChowBaseAlgHom_isIdempotent k p b _
      (graphChowAveragingProjector_isIdempotent k p b α)
  · rw [graphChowBaseAlgHom_realization, graphChowRealization_averagingProjector]
    simp only [map_smul, map_sum, graphChowBasePushforward_graphChowClass]

end Absolute

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCorrespondence.graphIntegralSubscheme_supportDegree,
    `HodgeConjecture.SchemeCorrespondence.gradedGraphCycleLinearMap_val,
    `HodgeConjecture.SchemeCorrespondence.graphChowLinearMap_single,
    `HodgeConjecture.SchemeCorrespondence.graphPairDimensionFunction_comap,
    `HodgeConjecture.SchemeCorrespondence.rationalPrincipalRelations_le_comap_graphPairPullback,
    `HodgeConjecture.SchemeCorrespondence.graphPairChowPullback,
    `HodgeConjecture.SchemeCorrespondence.graphChowRightAction_mul,
    `HodgeConjecture.SchemeCorrespondence.graphChowLeftAction_mul,
    `HodgeConjecture.SchemeCorrespondence.graphChowRightLinearAction_graphChowLinearMap,
    `HodgeConjecture.SchemeCorrespondence.graphChowLeftLinearAction_graphChowLinearMap,
    `HodgeConjecture.SchemeCorrespondence.graphChowKernelIdeal_isTwoSided,
    `HodgeConjecture.SchemeCorrespondence.graphChowRealization_injective,
    `HodgeConjecture.SchemeCorrespondence.graphChowRangeEquiv,
    `HodgeConjecture.SchemeCorrespondence.graphChowRealization_mul_left,
    `HodgeConjecture.SchemeCorrespondence.graphChowRealization_mul_right,
    `HodgeConjecture.SchemeCorrespondence.graphChowAveragingProjector_isIdempotent,
    `HodgeConjecture.SchemeCorrespondence.graphChowRealization_averagingProjector,
    `HodgeConjecture.SchemeCorrespondence.graphChowComplementaryProjector_isIdempotent,
    `HodgeConjecture.SchemeCorrespondence.graphChowRealization_average_add_complement,
    `HodgeConjecture.SchemeCorrespondence.graphChowSubgroupProjector_isIdempotent,
    `HodgeConjecture.SchemeCorrespondence.graphChowRealization_subgroupProjector,
    `HodgeConjecture.SchemeCorrespondence.graphChowBaseComparison_supportDegree,
    `HodgeConjecture.SchemeCorrespondence.graphChowBasePushforward_graphChowClass,
    `HodgeConjecture.SchemeCorrespondence.graphChowLinearMap_baseComparison,
    `HodgeConjecture.SchemeCorrespondence.graphChowAbsoluteDegreeEquiv_graphChowClass,
    `HodgeConjecture.SchemeCorrespondence.absoluteGraphChowLinearMap_eq,
    `HodgeConjecture.SchemeCorrespondence.graphChowKernelIdeal_le_comap_forgetDeckBase,
    `HodgeConjecture.SchemeCorrespondence.graphChowBaseAlgHom_realization,
    `HodgeConjecture.SchemeCorrespondence.graphChowBaseAlgHom_isIdempotent]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
