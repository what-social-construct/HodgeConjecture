module

public import HodgeConjecture.Boundary.Normalization.HeightOneBoundaryPole
public import HodgeConjecture.Boundary.Normalization.NormalizationTraceBound

@[expose] public section

/-!
# Actual boundary poles and the separation criterion

A height-one prime containing the fixed--moving ideal yields a genuine
section outside the normalization ring. If the intermediate extension is
separable, the trace-dual bound then proves that every nonzero multiplier
fails on some actual boundary section.

Consequently, uniform landing for every nontrivial subgroup implies the
existing conjugate-boundary separation condition. Uniform landing remains
an explicit hypothesis; no candidate ideal or replacement section carrier
is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.NormalizationInertia

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable {U : Scheme.{u}}
variable {j : U ⟶ intermediateNormalization (B := B) (L := L)}
variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)
variable [IsNoetherianRing B]

local notation "T₀" => NormalClosureNormalizationRing (B := B) (N := N)

/-- A removed height-one prime makes the actual boundary-section image
strictly larger than the normalization ring. -/
theorem boundarySectionSubalgebra_ne_bot_of_heightOne
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.height = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal) :
    boundarySectionSubalgebra C I hI ≠ ⊥ := by
  letI : IsNoetherianRing T₀ := normalization_isNoetherianRing C
  letI : IsFractionRing T₀ N := normalization_isFractionRing C
  letI := fixedMovingBoundaryOpen_nonempty C I hI
  have hJ : fixedMovingBoundaryIdeal C I ≠ ⊥ := by
    intro h
    apply fixedLocusIdeal_ne_bot C I hI
    apply le_bot_iff.mp
    exact (show fixedLocusIdeal I ≤ fixedMovingBoundaryIdeal C I from le_sup_left).trans
      (le_of_eq h)
  exact affineSectionSubalgebra_ne_bot_of_heightOne
    (T := .of T₀) (N := N) (fixedMovingBoundaryOpen C I)
    (fixedMovingBoundaryIdeal C I) hJ (fun x => x.property) p hp hJp

/-- If every nontrivial subgroup's actual section algebra is the base,
no height-one prime contains its fixed--moving ideal. -/
theorem conjugateBoundarySeparation_of_boundarySectionSubalgebra_eq_bot
    (hSections : ∀ (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥),
      boundarySectionSubalgebra C I hI = ⊥) :
    ConjugateBoundarySeparation C := by
  intro I hI p hp hJp
  exact (boundarySectionSubalgebra_ne_bot_of_heightOne C I hI p hp hJp)
    (hSections I hI)

/-- Every nonzero proposed trace multiplier fails on an actual regular
section when the boundary contains a height-one prime. -/
theorem boundarySection_tracePoleWitness [Algebra.IsSeparable K L]
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.height = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal)
    (s : T₀) (hs : s ≠ 0) :
    ∃ z : BoundarySectionRing C I,
      (s : N) * boundarySectionsToNormalClosure C I hI z ∉
        normalizationTraceDual C := by
  classical
  by_contra h
  push_neg at h
  exact (boundarySectionSubalgebra_ne_bot_of_heightOne C I hI p hp hJp)
    (boundarySectionSubalgebra_eq_bot_of_trace_landing C I hI s hs h)

/-- A height-one boundary prime forces the existing trace transporter
of the actual section algebra to be zero. -/
theorem normalizationTraceDual_colon_eq_bot_of_heightOne [Algebra.IsSeparable K L]
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.height = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal) :
    (normalizationTraceDual C).colon
      (boundarySectionSubalgebra C I hI).toSubmodule = ⊥ :=
  normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot C I hI
    (boundarySectionSubalgebra_ne_bot_of_heightOne C I hI p hp hJp)

/-- A proved nonzero uniform trace multiplier for each nontrivial subgroup
is sufficient for the existing conjugate-boundary separation endpoint. -/
theorem conjugateBoundarySeparation_of_traceLanding [Algebra.IsSeparable K L]
    (hLanding : ∀ (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥),
      ∃ s : T₀, s ≠ 0 ∧ ∀ z : BoundarySectionRing C I,
        (s : N) * boundarySectionsToNormalClosure C I hI z ∈
          normalizationTraceDual C) :
    ConjugateBoundarySeparation C := by
  apply conjugateBoundarySeparation_of_boundarySectionSubalgebra_eq_bot C
  intro I hI
  obtain ⟨s, hs, hsz⟩ := hLanding I hI
  exact boundarySectionSubalgebra_eq_bot_of_trace_landing C I hI s hs hsz

end

end HodgeConjecture.NormalizationInertia
