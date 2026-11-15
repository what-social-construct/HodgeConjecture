module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

@[expose] public section

/-!
# Fixed-point carriers under a change of base

The fixed-point subalgebra has the same underlying ring when the base changes
and both base actions are fixed. Its carrier depends only on the action.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Changing the base of a fixed-point subalgebra does not change its
underlying ring. -/
def fixedPointsBaseChangeRingEquiv
    {B C T G : Type*}
    [CommRing B] [CommRing C] [CommRing T]
    [Algebra B T] [Algebra C T]
    [Group G] [MulSemiringAction G T]
    [SMulCommClass G B T] [SMulCommClass G C T]
    (H : Subgroup G) :
    FixedPoints.subalgebra B T H ≃+* FixedPoints.subalgebra C T H :=
  RingEquiv.refl _

/-- The selected prime in the fixed-point ring has the same carrier for
either base. -/
theorem fixedPointsBaseChange_under_eq
    {B C T G : Type*}
    [CommRing B] [CommRing C] [CommRing T]
    [Algebra B T] [Algebra C T]
    [Group G] [MulSemiringAction G T]
    [SMulCommClass G B T] [SMulCommClass G C T]
    (H : Subgroup G) (P : Ideal T) :
    P.under (FixedPoints.subalgebra B T H) =
      P.under (FixedPoints.subalgebra C T H) :=
  rfl

/-- The `C`-algebra structure on the same fixed-point carrier, presented as
a `B`-subalgebra. This explicit instance can be used when transporting an
étale statement from the `C` presentation. -/
abbrev fixedPointsBaseChangeAlgebra
    {B C T G : Type*}
    [CommRing B] [CommRing C] [CommRing T]
    [Algebra B T] [Algebra C T]
    [Group G] [MulSemiringAction G T]
    [SMulCommClass G B T] [SMulCommClass G C T]
    (H : Subgroup G) : Algebra C (FixedPoints.subalgebra B T H) :=
  inferInstanceAs (Algebra C (FixedPoints.subalgebra C T H))

/-- The canonical `C`-algebra structure on the selected local ring is the
same for either presentation of the fixed-point ring. -/
abbrev fixedPointsBaseChangeAtPrimeAlgebra
    {B C T G : Type*}
    [CommRing B] [CommRing C] [CommRing T]
    [Algebra B T] [Algebra C T]
    [Group G] [MulSemiringAction G T]
    [SMulCommClass G B T] [SMulCommClass G C T]
    (H : Subgroup G) (P : Ideal T) [P.IsPrime] :
    Algebra C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
  inferInstanceAs
    (Algebra C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra C T H))))

/-- Étaleness on the selected local fixed ring does not depend on which base
was used to present that fixed ring as a subalgebra of `T`. -/
theorem fixedPointsBaseChange_etale_atPrime
    {B C T G : Type*}
    [CommRing B] [CommRing C] [CommRing T]
    [Algebra B T] [Algebra C T]
    [Group G] [MulSemiringAction G T]
    [SMulCommClass G B T] [SMulCommClass G C T]
    (H : Subgroup G) (P : Ideal T) [P.IsPrime]
    (h : Algebra.Etale C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra C T H)))) :
    letI : Algebra C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) :=
      fixedPointsBaseChangeAtPrimeAlgebra H P
    Algebra.Etale C
      (Localization.AtPrime (P.under (FixedPoints.subalgebra B T H))) := by
  exact h

end

end HodgeConjecture.NormalizationInertia
