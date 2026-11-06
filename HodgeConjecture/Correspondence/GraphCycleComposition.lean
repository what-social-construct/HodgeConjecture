module

public import HodgeConjecture.Correspondence.GraphSlice
public import HodgeConjecture.Correspondence.GraphCycles
public import HodgeConjecture.Cycles.OpenRestriction
public import HodgeConjecture.Cycles.ClosedImmersionPushforward

@[expose] public section

/-!
# Graph-slice pull–push on actual finite cycles

Pullback through the actual pair isomorphism `(x,z) ↦ (τ x,z)` carries
the graph cycle of `σ` to that of `σ * τ`. Closed pushforward through
the graph slice then yields the integral intersection cycle in the triple
product. Its supportwise outer projection has degree one and recovers
the composite graph cycle.

These operations use the existing actual scheme-cycle module. No component
cycle is assigned to a possibly reducible pulled-back graph, and no
ambient cycle product or rational-equivalence quotient is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCorrespondence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SchemeCycles

noncomputable section

universe u v

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- The actual intersection is integral by its proved source isomorphism. -/
def graphIntersectionIntegralSubscheme [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) : IntegralClosedSubscheme (tripleProduct pX) :=
  ⟨graphIntersectionIdeal pX σ τ, isIntegral_of_iso (graphIntersectionIso pX σ τ)⟩

@[simp]
theorem graphIntersectionIntegralSubscheme_val [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    (graphIntersectionIntegralSubscheme pX σ τ).val = graphIntersectionIdeal pX σ τ := rfl

/-- The integral cycle of the actual graph-intersection scheme. -/
def graphIntersectionCycle (R : Type v) [Semiring R] [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) : Cycles (tripleProduct pX) R :=
  fundamentalCycle R (graphIntersectionIntegralSubscheme pX σ τ)

/-- The pair isomorphism acts on cycles by genuine open restriction. -/
def graphRightPullback (R : Type v) [Semiring R] (τ : DeckTransformation pX) :
    Cycles (pullback pX pX) R →ₗ[R] Cycles (pullback pX pX) R :=
  openRestriction R (graphSlicePairMap pX τ)

@[simp]
theorem graphRightPullback_graphCycle (R : Type v) [Semiring R]
    [IsSeparated pX] [IsIntegral X] (σ τ : DeckTransformation pX) :
    graphRightPullback pX R τ (graphCycle pX R σ) = graphCycle pX R (σ * τ) := by
  exact openRestriction_fundamentalCycle_of_comap_eq (graphSlicePairMap pX τ) R
    (graphIntegralSubscheme pX σ) (graphIntegralSubscheme pX (σ * τ))
    (graphIdeal_comap_graphSlicePairMap pX σ τ)

/-- Pull through the pair isomorphism, then push into the graph slice. -/
def graphSlicePullPush (R : Type v) [Semiring R] [IsSeparated pX]
    (τ : DeckTransformation pX) :
    Cycles (pullback pX pX) R →ₗ[R] Cycles (tripleProduct pX) R :=
  (closedImmersionPushforward R (graphSliceMorphism pX τ)).comp
    (graphRightPullback pX R τ)

@[simp]
theorem graphSlicePullPush_graphCycle (R : Type v) [Semiring R]
    [IsSeparated pX] [IsIntegral X] (σ τ : DeckTransformation pX) :
    graphSlicePullPush pX R τ (graphCycle pX R σ) = graphIntersectionCycle pX R σ τ := by
  change closedImmersionPushforward R (graphSliceMorphism pX τ)
    (graphRightPullback pX R τ (graphCycle pX R σ)) = _
  rw [graphRightPullback_graphCycle]
  exact closedImmersionPushforward_fundamentalCycle_of_map_eq (graphSliceMorphism pX τ) R
    (graphIntegralSubscheme pX (σ * τ)) (graphIntersectionIntegralSubscheme pX σ τ)
    (graphIdeal_map_graphSliceMorphism pX σ τ)

/-- Only the intersection support, not the ambient projection, is closed in the target. -/
instance graphIntersectionProjection_isClosedImmersion [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) :
    IsClosedImmersion ((graphIntersectionIntegralSubscheme pX σ τ).val.subschemeι ≫
      tripleProductP13 pX) := by
  change IsClosedImmersion ((graphIntersectionIdeal pX σ τ).subschemeι ≫ tripleProductP13 pX)
  rw [← graphCompositionIso_hom_subschemeι]
  infer_instance

/-- The supportwise, degree-one image of the intersection cycle is the composite graph. -/
theorem graphIntersectionCycle_image_p13 (R : Type v) [Semiring R]
    [IsSeparated pX] [IsIntegral X] (σ τ : DeckTransformation pX) :
    closedImageCycle (tripleProductP13 pX) R (graphIntersectionIntegralSubscheme pX σ τ) =
      graphCycle pX R (σ * τ) := by
  exact closedImageCycle_of_map_eq (tripleProductP13 pX) R
    (graphIntersectionIntegralSubscheme pX σ τ) (graphIntegralSubscheme pX (σ * τ))
    (graphIntersectionIdeal_map_p13 pX σ τ)

/-- Weighted graph sums retain their coefficients through the geometric pull–push. -/
theorem graphSlicePullPush_graphCycleLinearMap_single [IsSeparated pX] [IsIntegral X]
    (σ τ : DeckTransformation pX) (q : ℚ) :
    graphSlicePullPush pX ℚ τ (graphCycleLinearMap pX (MonoidAlgebra.single σ q)) =
      q • graphIntersectionCycle pX ℚ σ τ := by
  rw [graphCycleLinearMap_single, map_smul, graphSlicePullPush_graphCycle]

end

end HodgeConjecture.SchemeCorrespondence
