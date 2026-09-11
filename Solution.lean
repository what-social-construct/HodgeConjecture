import HodgeConjecture.Boundary.Normalization.FixedRingLocalization

/-!
# Height-one fixed-ring descent: proved solutions

Comparator checks these declarations against `Challenge.lean`.  The proof
wrappers expose the project theorems through a Mathlib-only statement
surface; in particular, they replace the project's source-input record by
its single explicit unramifiedness premise.
-/

set_option autoImplicit false

namespace HodgeConjecture.Palomar

noncomputable section

theorem fixedPoints_heightOne_contraction
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (H : Subgroup G) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.primeHeight = 1) :
    (Q.under (FixedPoints.subalgebra A S H)).primeHeight = 1 := by
  exact
    NormalizationInertia.fixedPoints_primeHeight_under_eq_one
      (A := A) H Q hQ

theorem heightOne_fixedRing_unramified_descent
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    [IsNoetherianRing A] [Module.Finite A S]
    (I H : Subgroup G) (hIH : I ≤ H)
    [IsIntegrallyClosed (FixedPoints.subalgebra A S H)]
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.primeHeight = 1)
    (hI : Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S I))) :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S H)) := by
  exact
    NormalizationInertia.fixedRing_isUnramifiedAt_of_inertia_le_of_primeHeight_eq_one
      I H hIH Q hQ ⟨hI⟩

end

end HodgeConjecture.Palomar
