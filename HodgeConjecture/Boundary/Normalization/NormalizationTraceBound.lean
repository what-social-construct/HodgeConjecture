import HodgeConjecture.Boundary.Normalization.BoundarySections
import HodgeConjecture.Boundary.Normalization.BoundedOverring
import HodgeConjecture.Boundary.Normalization.TraceDualBound

/-!
# The normalization trace dual and actual boundary-section landing

The trace dual is Mathlib's existing `Submodule.traceDual` of the unit
order, not a second trace-integral carrier. Separability of the intermediate
extension makes its finite normal closure separable, so the generic
denominator theorem supplies one nonzero denominator for the entire trace
dual.

Under Noetherianity of the base, a nonzero uniform multiplier sending all
actual boundary sections into this dual forces their image to be the base
normalization algebra. The multiplier is an explicit hypothesis; the
denominator theorem does not construct geometric trace landing.
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

local notation "T₀" => NormalClosureNormalizationRing (B := B) (N := N)

/-- The trace dual of the actual normalization order, using Mathlib's
existing carrier. No inclusion of the order in its dual is assumed. -/
abbrev normalizationTraceDual
    (_C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j) :
    Submodule T₀ N :=
  Submodule.traceDual B K (1 : Submodule T₀ N)

variable (C : NormalizedCover (B := B) (K := K) (L := L) (N := N) U j)

omit [IsFractionRing B K] [IsScalarTower B K L] in
/-- Membership tests the field trace against every normalization element. -/
@[simp]
theorem mem_normalizationTraceDual_iff (z : N) :
    z ∈ normalizationTraceDual C ↔
      ∀ t : T₀, Algebra.trace K N (z * (t : N)) ∈
        Set.range (algebraMap B K) :=
  mem_traceDual_unit_iff B K T₀ N z

include C in
omit [IsFractionRing B K] [IsScalarTower B K L] [IsScalarTower B K N] [Algebra B K] in
/-- The supplied finite normalization model is Noetherian over a
Noetherian base. -/
theorem normalization_isNoetherianRing [IsNoetherianRing B] :
    IsNoetherianRing T₀ := by
  letI : Module.Finite B T₀ := C.finiteNormalClosureModel
  exact IsNoetherianRing.of_finite B T₀

include C in
omit [IsScalarTower B K L] in
/-- Normality of the normalization ring follows from the finite field
extension; normality of the original base is not required. -/
theorem normalization_isIntegrallyClosed : IsIntegrallyClosed T₀ := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : FiniteDimensional K N := C.normalClosure.finiteNormal
  exact integralClosure.isIntegrallyClosedOfFiniteExtension K

omit [IsScalarTower B K L] in
/-- One nonzero normalization element clears the whole trace dual.
Separability passes from the intermediate extension to its normal closure. -/
theorem exists_nonzero_normalizationTraceDual_denominator [Algebra.IsSeparable K L] :
    ∃ d : T₀, d ≠ 0 ∧ ∀ z ∈ normalizationTraceDual C,
      (d : N) * z ∈ Set.range (algebraMap T₀ N) := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : FiniteDimensional K N := C.normalClosure.finiteNormal
  letI : Algebra.IsSeparable K N := C.normalClosure.isSeparable
  letI : IsFractionRing T₀ N := normalization_isFractionRing C
  exact exists_nonzero_traceDual_unit_denominator B K T₀ N

/-- A nonzero element of the existing trace-dual colon ideal forces the
actual boundary-section algebra to equal the embedded normalization. -/
theorem boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon
    [Algebra.IsSeparable K L] [IsNoetherianRing B]
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (s : T₀) (hs : s ≠ 0)
    (hLanding : s ∈ (normalizationTraceDual C).colon
      (boundarySectionSubalgebra C I hI).toSubmodule) :
    boundarySectionSubalgebra C I hI = ⊥ := by
  letI : IsNoetherianRing T₀ := normalization_isNoetherianRing C
  letI : IsIntegrallyClosed T₀ := normalization_isIntegrallyClosed C
  letI : IsFractionRing T₀ N := normalization_isFractionRing C
  obtain ⟨d, hd, hdz⟩ := exists_nonzero_normalizationTraceDual_denominator C
  exact subalgebra_eq_bot_of_mem_colon T₀ N
    (boundarySectionSubalgebra C I hI) (normalizationTraceDual C)
    d hd hdz s hs hLanding

/-- The same criterion expressed on every actual regular section, before
passing to its image in the normal-closure field. -/
theorem boundarySectionSubalgebra_eq_bot_of_trace_landing
    [Algebra.IsSeparable K L] [IsNoetherianRing B]
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (s : T₀) (hs : s ≠ 0)
    (hLanding : ∀ z : BoundarySectionRing C I,
      (s : N) * boundarySectionsToNormalClosure C I hI z ∈
        normalizationTraceDual C) :
    boundarySectionSubalgebra C I hI = ⊥ := by
  apply boundarySectionSubalgebra_eq_bot_of_mem_traceDual_colon C I hI s hs
  apply Submodule.mem_colon.mpr
  intro z hz
  obtain ⟨section_, rfl⟩ := (mem_boundarySectionSubalgebra_iff C I hI z).mp hz
  exact hLanding section_

/-- A proper boundary-section overring has zero transporter into the
normalization trace dual. Properness remains an explicit geometric premise. -/
theorem normalizationTraceDual_colon_eq_bot_of_boundarySectionSubalgebra_ne_bot
    [Algebra.IsSeparable K L] [IsNoetherianRing B]
    (I : Subgroup C.GaloisGroup) (hI : I ≠ ⊥)
    (hProper : boundarySectionSubalgebra C I hI ≠ ⊥) :
    (normalizationTraceDual C).colon
      (boundarySectionSubalgebra C I hI).toSubmodule = ⊥ := by
  letI : IsNoetherianRing T₀ := normalization_isNoetherianRing C
  letI : IsIntegrallyClosed T₀ := normalization_isIntegrallyClosed C
  letI : IsFractionRing T₀ N := normalization_isFractionRing C
  obtain ⟨d, hd, hdz⟩ := exists_nonzero_normalizationTraceDual_denominator C
  exact colon_eq_bot_of_subalgebra_ne_bot T₀ N
    (boundarySectionSubalgebra C I hI) hProper (normalizationTraceDual C) d hd hdz

end

end HodgeConjecture.NormalizationInertia
