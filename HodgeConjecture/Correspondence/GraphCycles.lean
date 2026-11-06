module

public import HodgeConjecture.Correspondence.GraphSubscheme
public import HodgeConjecture.Cycles.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Integral graph cycles

The closed graph of a deck transformation of an integral scheme is an
actual integral closed subscheme of the relative product. Its fundamental
cycle is therefore a generator of the finite cycle module. The graph
subscheme has the same topological Krull dimension as the source, by the
already constructed scheme isomorphism.

Linear extension sends a rational group-algebra basis element to its actual
graph cycle. This map is only linear: no Chow quotient, cycle multiplication,
or compatibility with correspondence convolution is asserted here.
-/

set_option autoImplicit false

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SchemeCorrespondence

variable {S X : Scheme.{u}} (pX : X ⟶ S)

/-- The actual closed graph is integral when its source is integral. -/
theorem graphIdeal_isIntegral [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) : IsIntegral (graphIdeal pX σ).subscheme :=
  SchemeCycles.isIntegral_of_iso (graphSubschemeIso pX σ)

/-- The ideal of the graph, regarded as an actual integral cycle generator. -/
def graphIntegralSubscheme [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) : SchemeCycles.IntegralClosedSubscheme (pullback pX pX) :=
  ⟨graphIdeal pX σ, graphIdeal_isIntegral pX σ⟩

@[simp]
theorem graphIntegralSubscheme_val
    [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) :
    (graphIntegralSubscheme pX σ).val = graphIdeal pX σ := rfl

/-- Graph dimension is inherited through the actual graph-subscheme isomorphism. -/
theorem graphIdeal_topologicalKrullDim [hSeparated : IsSeparated pX]
    (σ : DeckTransformation pX) :
    topologicalKrullDim (graphIdeal pX σ).subscheme = topologicalKrullDim X := by
  let e := Scheme.homeoOfIso (graphSubschemeIso pX σ)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

/-- The coefficient-one cycle of the actual integral graph. -/
def graphCycle (R : Type v) [Semiring R]
    [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) : SchemeCycles.Cycles (pullback pX pX) R :=
  SchemeCycles.fundamentalCycle R (graphIntegralSubscheme pX σ)

@[simp]
theorem graphCycle_eq_single (R : Type v) [Semiring R]
    [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) :
    graphCycle pX R σ = Finsupp.single (graphIntegralSubscheme pX σ) 1 := rfl

/-- A graph cycle is nonzero over nontrivial coefficients. -/
theorem graphCycle_ne_zero (R : Type v) [Semiring R] [Nontrivial R]
    [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) : graphCycle pX R σ ≠ 0 :=
  SchemeCycles.fundamentalCycle_ne_zero R (graphIntegralSubscheme pX σ)

/-- Linear graph-cycle assembly, without an assumed cycle convolution product. -/
def graphCycleLinearMap [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X] :
    MonoidAlgebra ℚ (DeckTransformation pX) →ₗ[ℚ]
      SchemeCycles.Cycles (pullback pX pX) ℚ :=
  (Finsupp.linearCombination ℚ (graphCycle pX ℚ)).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp]
theorem graphCycleLinearMap_single
    [hSeparated : IsSeparated pX] [hIntegral : IsIntegral X]
    (σ : DeckTransformation pX) (q : ℚ) :
    graphCycleLinearMap pX (MonoidAlgebra.single σ q) = q • graphCycle pX ℚ σ := by
  simpa [graphCycleLinearMap] using
    (Finsupp.linearCombination_single ℚ (graphCycle pX ℚ) σ q)

end SchemeCorrespondence

end

end HodgeConjecture
