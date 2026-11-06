module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# The ideal-power ramification index under the current API

Mathlib now calls the original ideal-power index `ramificationIdx'`.
Keep that same quantity in the existing normalization interfaces. The
unramified implication below is the original localization argument.
-/

public section
namespace HodgeConjecture.CommutativeAlgebra

open Algebra

theorem ramificationIdx'_eq_one_of_isUnramifiedAt
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] [IsNoetherianRing S] [EssFiniteType R S]
    (p : Ideal S) [p.IsPrime] [IsUnramifiedAt R p] (hp : p ≠ ⊥) :
    Ideal.ramificationIdx' (p.under R) p = 1 := by
  letI := Localization.AtPrime.algebraOfLiesOver (p.under R) p
  exact Ideal.ramificationIdx'_eq_one_of_map_localization Ideal.map_comap_le hp
    p.primeCompl_le_nonZeroDivisors
    ((isUnramifiedAt_iff_map_eq R (p.under R) p).mp inferInstance).2

end HodgeConjecture.CommutativeAlgebra
