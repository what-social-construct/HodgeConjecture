module

public import HodgeConjecture.Boundary.Different
public import Mathlib.RingTheory.DedekindDomain.Different

@[expose] public section

/-!
# The height-one different and ramification

At a codimension-one point of a normal model, localization produces a
Dedekind/DVR calculation. Mathlib's Dedekind different detects exactly the
primes at which the finite extension is ramified.

The collision construction produces instead the Noether different

`μ(ann(ker μ))`, where `μ : S ⊗[R] S → S`.

These differents agree under familiar extra hypotheses (for example in
appropriate local complete-intersection or monogenic situations), but that
comparison should not be silently assumed. `CollisionDifferentComparison`
therefore records the precise bridge needed at a height-one localization.
Under that bridge, the collision contact subscheme is supported exactly at
the ramified primes. The locally owned valuation/inertia foundation can then
turn this ramification statement into an inertia
statement.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

section LocalCriterion

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]
variable (P : Ideal S) [P.IsPrime]

/--
The pointwise input needed by the boundary-projector criterion: the
collision different detects ramification at the selected prime.

This formulation is appropriate in higher dimension because it can be proved
after localizing at one height-one point; it does not require the global
normalization rings themselves to be Dedekind domains.
-/
def CollisionDifferentDetectsRamificationAt : Prop :=
  collisionNoetherDifferentIdeal R S ≤ P ↔
    ¬ Algebra.IsUnramifiedAt R P

end LocalCriterion

section Dedekind

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsDedekindDomain R] [IsDedekindDomain S]
variable [NoZeroSMulDivisors R S] [Module.Finite R S]
variable [Algebra.IsSeparable (FractionRing R) (FractionRing S)]

/--
The local comparison required to identify the collision Noether different
with the classical Dedekind different.

Keeping this as an explicit hypothesis isolates the genuinely geometric
input: it can later be discharged after localizing a finite normalization at
a height-one point and imposing the desired presentation hypotheses.
-/
def CollisionDifferentComparison : Prop :=
  collisionNoetherDifferentIdeal R S = differentIdeal R S

/--
In a finite separable extension of Dedekind domains, containment of the
different in a prime is equivalent to ramification at that prime.
-/
theorem dedekindDifferent_le_prime_iff_ramified
    {P : Ideal S} [P.IsPrime] :
    differentIdeal R S ≤ P ↔
      ¬ Algebra.IsUnramifiedAt R P := by
  simpa only [Ideal.dvd_iff_le] using
    (dvd_differentIdeal_iff (A := R) (B := S) (P := P))

/--
After comparing the two differents, a prime contains the collision different
exactly when it is ramified.
-/
theorem collisionNoetherDifferent_le_prime_iff_ramified
    (hComparison : CollisionDifferentComparison R S)
    {P : Ideal S} [P.IsPrime] :
    collisionNoetherDifferentIdeal R S ≤ P ↔
      ¬ Algebra.IsUnramifiedAt R P := by
  rw [hComparison]
  exact dedekindDifferent_le_prime_iff_ramified R S

/--
A global comparison with the Dedekind different supplies the pointwise
ramification criterion at every prime.  Higher-dimensional applications may
instead establish `CollisionDifferentDetectsRamificationAt` after localization.
-/
theorem collisionDifferentDetectsRamificationAt_of_comparison
    (hComparison : CollisionDifferentComparison R S)
    {P : Ideal S} [P.IsPrime] :
    CollisionDifferentDetectsRamificationAt R S P := by
  unfold CollisionDifferentDetectsRamificationAt
  exact
    collisionNoetherDifferent_le_prime_iff_ramified
      R S hComparison

/-- The zero locus of the classical different is the ramification locus. -/
theorem dedekindDifferent_zeroLocus_eq_ramificationLocus :
    PrimeSpectrum.zeroLocus (differentIdeal R S : Set S) =
      collisionRamificationLocus R S := by
  ext p
  change differentIdeal R S ≤ p.asIdeal ↔
    ¬ Algebra.IsUnramifiedAt R p.asIdeal
  exact dedekindDifferent_le_prime_iff_ramified R S

/--
Under the height-one different comparison, the contact ideal cut out on the
diagonal has exactly the ramification locus as its underlying closed set.
-/
theorem collisionNoetherDifferent_zeroLocus_eq_ramificationLocus
    (hComparison : CollisionDifferentComparison R S) :
    PrimeSpectrum.zeroLocus
        (collisionNoetherDifferentIdeal R S : Set S) =
      collisionRamificationLocus R S := by
  rw [hComparison]
  exact dedekindDifferent_zeroLocus_eq_ramificationLocus R S

end Dedekind

end

end HodgeConjecture
