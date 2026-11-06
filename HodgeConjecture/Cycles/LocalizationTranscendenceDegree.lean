module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.SetTheory.Cardinal.ToNat

@[expose] public section

/-!
# Transcendence degree of an actual localization

Localizing a domain at non-zero-divisors preserves its transcendence
degree over a field. The proof derives injectivity and the domain property
of the actual localization, then applies tower additivity to the algebraic
localization map. No finite-type or finite-transcendence-degree assumption
is needed. The cardinal comparison is primary; the natural-number result
is its consequence and does not assert finiteness.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

noncomputable section

universe u v w

/-- Actual localization preserves transcendence degree, with cardinal
lifts allowing the two carriers to inhabit different universes. -/
theorem lift_trdeg_eq_of_isLocalization
    (k : Type u) [Field k] (B : Type v) [CommRing B] [IsDomain B]
    (B' : Type w) [CommRing B'] [Algebra k B] [Algebra B B'] [Algebra k B']
    [IsScalarTower k B B'] (M : Submonoid B) [IsLocalization M B']
    (hM : M ≤ nonZeroDivisors B) :
    Cardinal.lift.{w} (Algebra.trdeg k B) =
      Cardinal.lift.{v} (Algebra.trdeg k B') := by
  letI : IsDomain B' := IsLocalization.isDomain_of_le_nonZeroDivisors B' hM
  letI : FaithfulSMul B B' :=
    (faithfulSMul_iff_algebraMap_injective B B').mpr (IsLocalization.injective B' hM)
  letI : Algebra.IsAlgebraic B B' := IsLocalization.isAlgebraic B' M
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero] using lift_trdeg_add_eq k B B'

/-- When the carriers share a universe, the comparison is an equality
of the original transcendence-degree cardinals. -/
theorem trdeg_eq_of_isLocalization
    (k : Type u) [Field k] (B : Type v) [CommRing B] [IsDomain B]
    (B' : Type v) [CommRing B'] [Algebra k B] [Algebra B B'] [Algebra k B']
    [IsScalarTower k B B'] (M : Submonoid B) [IsLocalization M B']
    (hM : M ≤ nonZeroDivisors B) :
    Algebra.trdeg k B = Algebra.trdeg k B' := by
  simpa only [Cardinal.lift_id] using lift_trdeg_eq_of_isLocalization k B B' M hM

/-- The numeric comparison follows from cardinal invariance, without
adding a finiteness assumption or using it in place of that invariance. -/
theorem trdeg_toNat_eq_of_isLocalization
    (k : Type u) [Field k] (B : Type v) [CommRing B] [IsDomain B]
    (B' : Type w) [CommRing B'] [Algebra k B] [Algebra B B'] [Algebra k B']
    [IsScalarTower k B B'] (M : Submonoid B) [IsLocalization M B']
    (hM : M ≤ nonZeroDivisors B) :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k B').toNat := by
  simpa only [Cardinal.toNat_lift] using
    congrArg Cardinal.toNat (lift_trdeg_eq_of_isLocalization k B B' M hM)

end

end HodgeConjecture.SchemeCycles
