module

public import HodgeConjecture.Boundary.GraphRestriction
public import HodgeConjecture.Correspondence.GraphCycles
public import HodgeConjecture.Cycles.OpenRestriction

@[expose] public section

/-!
# Restriction of actual integral graph cycles

For a supplied finite étale extension with integral source, a nonempty
original cover is integral through its actual open inclusion. The proved
scheme-theoretic graph-ideal restriction then identifies the restricted
fundamental graph cycle, and linear extension gives the same equality for
rational sums of deck transformations.

The weighted equality is a square of linear maps into actual finite cycle
modules. It does not assert a Chow quotient, cycle convolution, or a
cohomological realization. Restriction of a supplied automorphism does not
require the separate hypothesis that every original automorphism extends.
-/

set_option autoImplicit false

namespace HodgeConjecture.LiteratureInputs.FiniteEtaleExtension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HodgeConjecture.SchemeCorrespondence HodgeConjecture.SchemeCycles

noncomputable section

universe u v

variable {X U Y : Scheme.{u}} {j : U ⟶ X} {p : Y ⟶ U}

/-- A nonempty original cover is integral when the extended cover is integral. -/
theorem original_isIntegral (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] [IsIntegral E.carrier] [Nonempty Y] : IsIntegral Y := by
  letI := E.inclusion_isOpenImmersion
  exact isIntegral_of_isOpenImmersion E.inclusion

/-- Open restriction sends an actual integral graph cycle to its restricted graph.
Finiteness supplies separatedness; original integrality and pair openness
come from the actual cover inclusion, not additional hypotheses. -/
theorem graphCycle_restriction (E : FiniteEtaleExtension j p)
    (R : Type v) [Semiring R] [IsOpenImmersion j]
    [IsIntegral E.carrier] [Nonempty Y] (σ : DeckTransformation E.toBase) :
    letI := E.finite
    letI := E.original_isFinite
    letI := E.original_isIntegral
    letI := E.pairInclusion_isOpenImmersion
    openRestriction R E.pairInclusion (graphCycle E.toBase R σ) =
      graphCycle p R (E.restriction σ) := by
  letI := E.finite
  letI := E.original_isFinite
  letI := E.original_isIntegral
  letI := E.pairInclusion_isOpenImmersion
  exact openRestriction_fundamentalCycle_of_comap_eq E.pairInclusion R
    (graphIntegralSubscheme E.toBase σ)
    (graphIntegralSubscheme p (E.restriction σ))
    (E.graphIdeal_restriction σ).symm

/-- The same actual graph-cycle restriction law for every rational weighted sum.
Only the deck-group reindexing is an algebra homomorphism; both graph-cycle
assembly and cycle restriction remain linear maps. -/
theorem graphCycleLinearMap_restriction (E : FiniteEtaleExtension j p)
    [IsOpenImmersion j] [IsIntegral E.carrier] [Nonempty Y] :
    letI := E.finite
    letI := E.original_isFinite
    letI := E.original_isIntegral
    letI := E.pairInclusion_isOpenImmersion
    (openRestriction ℚ E.pairInclusion).comp (graphCycleLinearMap E.toBase) =
      (graphCycleLinearMap p).comp
        (MonoidAlgebra.mapDomainAlgHom ℚ ℚ E.restriction).toLinearMap := by
  letI := E.finite
  letI := E.original_isFinite
  letI := E.original_isIntegral
  letI := E.pairInclusion_isOpenImmersion
  apply (LinearMap.cancel_right (MonoidAlgebra.coeffLinearEquiv ℚ).symm.surjective).mp
  apply Finsupp.lhom_ext
  intro σ q
  change openRestriction ℚ E.pairInclusion
      (graphCycleLinearMap E.toBase (MonoidAlgebra.single σ q)) =
    graphCycleLinearMap p
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ E.restriction (MonoidAlgebra.single σ q))
  simp only [graphCycleLinearMap_single, MonoidAlgebra.mapDomainAlgHom_apply,
    MonoidAlgebra.mapDomain_single, map_smul]
  rw [E.graphCycle_restriction ℚ σ]

end

end HodgeConjecture.LiteratureInputs.FiniteEtaleExtension
