import HodgeConjecture.Boundary.Normalization.BoundaryPole
import Lean.Util.CollectAxioms

/-!
Focused SP67 regressions. Run with
`lake env lean research/BoundaryPoleVerification.lean`.
Local fractions yield actual sections, and a removed height-one prime
constructs the pole used by the trace obstruction. The generic construction
does not assume normality. All nine new public declarations have an enforced
standard-axiom allowlist.
The SP75 trace tests use separability of the marked extension directly.
-/

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.NormalizationInertia

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

section Generic

universe u v

variable {T : CommRingCat.{u}} [IsDomain T]
variable {N : Type v} [Field N] [Algebra T N] [IsFractionRing T N]

-- Membership is witnessed by a genuine structure-sheaf section, not a new carrier.
example (U : (Spec T).Opens) [Nonempty U] (z : N)
    (h : ∀ x : U, ∃ a b : T, b ∉ x.1.asIdeal ∧
      algebraMap T N b * z = algebraMap T N a) :
    ∃ s : Γ(Spec T, U), affineSectionsToFractionField U s = z := by
  exact (mem_affineSectionSubalgebra_iff U z).mp
    (mem_affineSectionSubalgebra_of_localFractions U z h)

example (U : (Spec T).Opens) [Nonempty U] (J : Ideal T) (n : ℕ) (z : N)
    (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (hz : ∀ t ∈ J ^ n, ∃ a : T, algebraMap T N t * z = algebraMap T N a) :
    z ∈ affineSectionSubalgebra U := by
  fail_if_success have _ : IsNoetherianRing T := inferInstance
  fail_if_success have _ : IsIntegrallyClosed T := inferInstance
  exact mem_affineSectionSubalgebra_of_ideal_pow_mul U J n z hU hz

-- The zero exponent is covered; it imposes global denominator clearing.
example (U : (Spec T).Opens) [Nonempty U] (J : Ideal T) (z : N)
    (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (hz : ∀ t ∈ J ^ 0, ∃ a : T, algebraMap T N t * z = algebraMap T N a) :
    ∃ s : Γ(Spec T, U), affineSectionsToFractionField U s = z := by
  exact (mem_affineSectionSubalgebra_iff U z).mp
    (mem_affineSectionSubalgebra_of_ideal_pow_mul U J 0 z hU hz)

-- On a nonempty open inside a principal open, local fractions construct the reciprocal.
example (V : (Spec T).Opens) [Nonempty V] (f : T) (hf : f ≠ 0)
    (hV : V ≤ PrimeSpectrum.basicOpen f) :
    (algebraMap T N f)⁻¹ ∈ affineSectionSubalgebra V := by
  apply mem_affineSectionSubalgebra_of_localFractions V ((algebraMap T N f)⁻¹)
  intro x
  refine ⟨1, f, hV x.property, ?_⟩
  have hfN : algebraMap T N f ≠ 0 := by
    simpa using (IsFractionRing.injective T N).ne hf
  simp [hfN]

variable [IsNoetherianRing T]

-- Normality is not needed to construct the ideal-power denominator.
example (J : Ideal T) (hJ : J ≠ ⊥) (p : PrimeSpectrum T)
    (hp : p.asIdeal.primeHeight = 1) (hJp : J ≤ p.asIdeal) :
    ∃ (f t : T) (n : ℕ), f ∈ J ∧ f ≠ 0 ∧ t ∉ p.asIdeal ∧
      ∀ x ∈ J ^ n, t * x ∈ Ideal.span {f} := by
  fail_if_success have _ : IsIntegrallyClosed T := inferInstance
  exact exists_heightOne_boundary_denominator J hJ p hp hJp

-- The height-one prime constructs properness; no pole witness is assumed.
example (U : (Spec T).Opens) [Nonempty U]
    (J : Ideal T) (hJ : J ≠ ⊥) (hU : ∀ x : U, ¬ J ≤ x.1.asIdeal)
    (p : PrimeSpectrum T) (hp : p.asIdeal.primeHeight = 1)
    (hJp : J ≤ p.asIdeal) : affineSectionSubalgebra (N := N) U ≠ ⊥ := by
  fail_if_success have _ : IsIntegrallyClosed T := inferInstance
  exact affineSectionSubalgebra_ne_bot_of_heightOne U J hJ hU p hp hJp

end Generic

section Boundary

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

example (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.primeHeight = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal) :
    boundarySectionSubalgebra C I hI ≠ ⊥ :=
  boundarySectionSubalgebra_ne_bot_of_heightOne C I hI p hp hJp

-- Properness yields an actual section whose rational function is not in the base.
example (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.primeHeight = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal) :
    ∃ z : BoundarySectionRing C I,
      boundarySectionsToNormalClosure C I hI z ∉ (algebraMap T₀ N).range := by
  classical
  by_contra h
  push_neg at h
  apply boundarySectionSubalgebra_ne_bot_of_heightOne C I hI p hp hJp
  apply le_antisymm ?_ bot_le
  rintro x ⟨z, rfl⟩
  exact (Algebra.mem_bot).mpr (h z)

-- This separation criterion does not require perfectness or trace data.
example (hSections : ∀ (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥),
      boundarySectionSubalgebra C I hI = ⊥) :
    ConjugateBoundarySeparation C :=
  conjugateBoundarySeparation_of_boundarySectionSubalgebra_eq_bot C hSections

variable [Algebra.IsSeparable K L]

-- For every proposed nonzero multiplier, a failing actual section is constructed.
example (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.primeHeight = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal) (s : T₀) (hs : s ≠ 0) :
    ∃ z : BoundarySectionRing C I,
      (s : N) * boundarySectionsToNormalClosure C I hI z ∉
        normalizationTraceDual C :=
  boundarySection_tracePoleWitness C I hI p hp hJp s hs

example (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (p : PrimeSpectrum T₀) (hp : p.asIdeal.primeHeight = 1)
    (hJp : fixedMovingBoundaryIdeal C I ≤ p.asIdeal) :
    (normalizationTraceDual C).colon
      (boundarySectionSubalgebra C I hI).toSubmodule = ⊥ :=
  normalizationTraceDual_colon_eq_bot_of_heightOne C I hI p hp hJp

-- Uniform landing is explicit and quantifies over all actual boundary sections.
example (hLanding : ∀ (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥),
      ∃ s : T₀, s ≠ 0 ∧ ∀ z : BoundarySectionRing C I,
        (s : N) * boundarySectionsToNormalClosure C I hI z ∈
          normalizationTraceDual C) :
    ConjugateBoundarySeparation C :=
  conjugateBoundarySeparation_of_traceLanding C hLanding

end Boundary

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.NormalizationInertia.mem_affineSectionSubalgebra_of_localFractions,
      `HodgeConjecture.NormalizationInertia.mem_affineSectionSubalgebra_of_ideal_pow_mul,
      `HodgeConjecture.NormalizationInertia.exists_heightOne_boundary_denominator,
      `HodgeConjecture.NormalizationInertia.affineSectionSubalgebra_ne_bot_of_heightOne,
      `HodgeConjecture.NormalizationInertia.boundarySectionSubalgebra_ne_bot_of_heightOne,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_of_boundarySectionSubalgebra_eq_bot,
      `HodgeConjecture.NormalizationInertia.boundarySection_tracePoleWitness,
      `HodgeConjecture.NormalizationInertia.normalizationTraceDual_colon_eq_bot_of_heightOne,
      `HodgeConjecture.NormalizationInertia.conjugateBoundarySeparation_of_traceLanding] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
