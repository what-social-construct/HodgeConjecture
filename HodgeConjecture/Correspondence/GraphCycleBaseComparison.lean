module

public import HodgeConjecture.Correspondence.GraphBaseComparison
public import HodgeConjecture.Correspondence.GraphCycleComposition
public import HodgeConjecture.Cycles.IsomorphismTransport

@[expose] public section

/-!
# Graph cycles under a change of structural base

The closed pair and triple comparisons carry actual relative graph and
intersection cycles to the cycles over the structural base. Their cycle
pushforwards commute with the graph-slice operations on the entire finite
cycle modules, as well as with rational weighted graph assembly.

Taking the structural base to be `Spec k` gives absolute products. These
are cycle-level comparisons, not a rational-equivalence quotient or a
comparison with an arbitrary intersection product.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u v

variable {X S B : Scheme.{u}} (p : X ⟶ S) (b : S ⟶ B)

/-- The pair inclusion carries the actual graph cycle to the same graph
regarded over the structural base. -/
theorem graphCycle_pairBaseComparison (R : Type v) [Semiring R]
    [IsSeparated p] [IsSeparated b] [IsIntegral X] (σ : DeckTransformation p) :
    closedImmersionPushforward R (pairBaseComparison p b) (graphCycle p R σ) =
      graphCycle (p ≫ b) R (forgetDeckBase p b σ) := by
  exact closedImmersionPushforward_fundamentalCycle_of_map_eq
    (pairBaseComparison p b) R (graphIntegralSubscheme p σ)
    (graphIntegralSubscheme (p ≫ b) (forgetDeckBase p b σ))
    (graphIdeal_map_pairBaseComparison p b σ)

/-- The triple inclusion carries the actual integral intersection cycle
to its structural-base counterpart. -/
theorem graphIntersectionCycle_tripleBaseComparison (R : Type v) [Semiring R]
    [IsSeparated p] [IsSeparated b] [IsIntegral X] (σ τ : DeckTransformation p) :
    closedImmersionPushforward R (tripleBaseComparison p b)
        (graphIntersectionCycle p R σ τ) =
      graphIntersectionCycle (p ≫ b) R
        (forgetDeckBase p b σ) (forgetDeckBase p b τ) := by
  exact closedImmersionPushforward_fundamentalCycle_of_map_eq
    (tripleBaseComparison p b) R (graphIntersectionIntegralSubscheme p σ τ)
    (graphIntersectionIntegralSubscheme (p ≫ b)
      (forgetDeckBase p b σ) (forgetDeckBase p b τ))
    (graphIntersectionIdeal_map_tripleBaseComparison p b σ τ)

/-- The whole cycle module, not just graph generators, satisfies the
pair-isomorphism comparison square. -/
theorem graphRightPullback_baseComparison (R : Type v) [Semiring R]
    [IsSeparated b] (τ : DeckTransformation p) :
    (closedImmersionPushforward R (pairBaseComparison p b)).comp
        (graphRightPullback p R τ) =
      (graphRightPullback (p ≫ b) R (forgetDeckBase p b τ)).comp
        (closedImmersionPushforward R (pairBaseComparison p b)) := by
  exact pushforward_openRestriction_iso R (pairBaseComparison p b)
    (asIso (graphSlicePairMap p τ))
    (asIso (graphSlicePairMap (p ≫ b) (forgetDeckBase p b τ)))
    (graphSlicePairMap_baseComparison p b τ)

/-- Graph-slice pull–push commutes with passage to the structural base on
all finite cycles; neither ambient integrality nor étaleness is needed. -/
theorem graphSlicePullPush_baseComparison (R : Type v) [Semiring R]
    [IsSeparated p] [IsSeparated b] (τ : DeckTransformation p) :
    (closedImmersionPushforward R (tripleBaseComparison p b)).comp
        (graphSlicePullPush p R τ) =
      (graphSlicePullPush (p ≫ b) R (forgetDeckBase p b τ)).comp
        (closedImmersionPushforward R (pairBaseComparison p b)) := by
  unfold graphSlicePullPush
  rw [← LinearMap.comp_assoc, closedImmersionPushforward_comp]
  simp only [graphSliceMorphism_baseComparison]
  rw [← closedImmersionPushforward_comp,
    LinearMap.comp_assoc, graphRightPullback_baseComparison,
    ← LinearMap.comp_assoc]

/-- Rational graph assembly commutes with the actual closed inclusion and
the group-algebra map induced by forgetting the base. -/
theorem graphCycleLinearMap_baseComparison
    [IsSeparated p] [IsSeparated b] [IsIntegral X] :
    (closedImmersionPushforward ℚ (pairBaseComparison p b)).comp
        (graphCycleLinearMap p) =
      (graphCycleLinearMap (p ≫ b)).comp
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b)).toLinearMap := by
  apply (LinearMap.cancel_right (MonoidAlgebra.coeffLinearEquiv ℚ).symm.surjective).mp
  apply Finsupp.lhom_ext
  intro σ q
  change closedImmersionPushforward ℚ (pairBaseComparison p b)
      (graphCycleLinearMap p (MonoidAlgebra.single σ q)) =
    graphCycleLinearMap (p ≫ b)
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (forgetDeckBase p b)
        (MonoidAlgebra.single σ q))
  rw [graphCycleLinearMap_single, map_smul, graphCycle_pairBaseComparison]
  simp only [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    graphCycleLinearMap_single]

end

end HodgeConjecture.SchemeCorrespondence
