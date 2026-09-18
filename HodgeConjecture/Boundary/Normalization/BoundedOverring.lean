import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Uniformly bounded overrings of a normal Noetherian domain

A subalgebra of the fraction field with one nonzero scalar clearing all its
denominators is the base algebra. Multiplicative closure is essential: the
module bound gives finiteness, and the algebra structure then gives integrality.

This is the algebraic input for the boundary-section/trace-landing route.
The bounded stage below is an ordinary submodule and its transporter is the
existing `Submodule.colon`; neither a new ideal object nor a geometric landing
axiom is introduced. Actual boundary sections, the trace-dual specialization,
and uniform geometric landing are separate constructions.

The first proof is adapted from the sibling collision-ideals project's
`Planar/Research/MonogenicLanding.lean`, with only Mathlib imports.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

universe u v

variable (T : Type u) [CommRing T] [IsNoetherianRing T] [IsIntegrallyClosed T]
variable (N : Type v) [Field N] [Algebra T N] [IsFractionRing T N]

/-- A normal Noetherian domain has no proper overring in its fraction field
whose denominators are uniformly cleared by one nonzero base element.
Here `R = ⊥` means that `R` is the image of `T`, not the zero ring. -/
theorem subalgebra_eq_bot_of_nonzero_mul_mem_base
    (R : Subalgebra T N) (a : T) (ha : a ≠ 0)
    (hBound : ∀ r : R,
      algebraMap T N a * (r : N) ∈ Set.range (algebraMap T N)) :
    R = ⊥ := by
  let baseEquiv : T ≃ₗ[T] LinearMap.range (Algebra.linearMap T N) :=
    LinearEquiv.ofInjective (Algebra.linearMap T N)
      (IsFractionRing.injective T N)
  let multiplied : R →ₗ[T] N :=
    (LinearMap.mulLeft T (algebraMap T N a)).comp R.val.toLinearMap
  let multipliedRange : R →ₗ[T] LinearMap.range (Algebra.linearMap T N) :=
    multiplied.codRestrict _ (fun r => hBound r)
  let reduce : R →ₗ[T] T :=
    baseEquiv.symm.toLinearMap.comp multipliedRange
  have haN : algebraMap T N a ≠ 0 := by
    intro haImage
    apply ha
    apply IsFractionRing.injective T N
    simpa using haImage
  have hReduce : Function.Injective reduce := by
    intro x y hxy
    have hxyRange : multipliedRange x = multipliedRange y :=
      baseEquiv.symm.injective hxy
    have hxyN :
        algebraMap T N a * (x : N) =
          algebraMap T N a * (y : N) :=
      congrArg Subtype.val hxyRange
    exact Subtype.ext (mul_left_cancel₀ haN hxyN)
  letI : Module.Finite T R :=
    Module.Finite.of_injective reduce hReduce
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Algebra.mem_bot]
  have hxIntegralR : IsIntegral T (⟨x, hx⟩ : R) :=
    IsIntegral.of_finite T _
  have hxIntegralN : IsIntegral T x := hxIntegralR.map R.val
  exact IsIntegrallyClosed.isIntegral_iff.mp hxIntegralN

/-- Landing in a submodule with a uniform denominator gives a uniform
denominator for the entire overring. The landing condition uses the existing
colon ideal, and quantifies over every element of `R`. -/
theorem subalgebra_eq_bot_of_mem_colon
    (R : Subalgebra T N) (M : Submodule T N)
    (d : T) (hd : d ≠ 0)
    (hDenominator : ∀ z ∈ M,
      algebraMap T N d * z ∈ Set.range (algebraMap T N))
    (s : T) (hs : s ≠ 0) (hLanding : s ∈ M.colon R.toSubmodule) :
    R = ⊥ := by
  letI : IsDomain T := (IsFractionRing.injective T N).isDomain
  apply subalgebra_eq_bot_of_nonzero_mul_mem_base T N R (d * s)
    (mul_ne_zero hd hs)
  intro r
  have h := hDenominator _ (Submodule.mem_colon.mp hLanding r r.property)
  simpa only [map_mul, Algebra.smul_def, mul_assoc] using h

/-- For a proper overring, the transporter into a uniformly bounded stage
is the zero ideal. A geometric pole witness can supply `hProper`; boundedness
alone does not assert that an actual boundary-section algebra is proper. -/
theorem colon_eq_bot_of_subalgebra_ne_bot
    (R : Subalgebra T N) (hProper : R ≠ ⊥) (M : Submodule T N)
    (d : T) (hd : d ≠ 0)
    (hDenominator : ∀ z ∈ M,
      algebraMap T N d * z ∈ Set.range (algebraMap T N)) :
    M.colon R.toSubmodule = ⊥ := by
  apply le_bot_iff.mp
  intro s hs
  change s = 0
  by_contra hs0
  exact hProper
    (subalgebra_eq_bot_of_mem_colon T N R M d hd hDenominator s hs0 hs)

end

end HodgeConjecture.NormalizationInertia
