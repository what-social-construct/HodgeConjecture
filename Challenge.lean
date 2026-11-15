module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Invariant.Basic

@[expose] public section

/-!
# Height-one fixed-ring descent: advertised statements

This is the small statement surface for the fixed-ring localization result.
It uses only Mathlib notions.

The first theorem says that, for a finite group acting on a domain, a
height-one prime stays height one after contraction to a subgroup-fixed
ring.  The second combines that fact with local unramified descent: for
`I ≤ H`, unramifiedness at the selected prime of `S^I` descends to the
selected prime of `S^H` when `S^H` is normal and the finite/Noetherian
hypotheses make its height-one localization a DVR.

The second theorem is deliberately conditional. Its hypothesis `hI` is
unramifiedness for the `I`-fixed ring; this submission neither identifies
`I` with the inertia group nor proves Stacks Project Tag `0BST`. Both
conclusions concern one selected prime, not a globally étale cover, and
neither theorem is a statement of the Hodge conjecture.
-/

set_option autoImplicit false

namespace HodgeConjecture.Palomar

noncomputable section

/-- For a finite group acting on a domain, contraction of a height-one prime
to any subgroup-fixed ring again has height one. -/
theorem fixedPoints_heightOne_contraction
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (H : Subgroup G) (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.height = 1) :
    (Q.under (FixedPoints.subalgebra A S H)).height = 1 := by
  sorry

/-- Let `I ≤ H`.  At a height-one prime `Q`, if the contraction to the
`I`-fixed ring is unramified over `A`, then the contraction to the `H`-fixed
ring is unramified over `A`, provided the latter fixed ring is integrally
closed. The unramifiedness premise for the `I`-fixed ring remains explicit. -/
theorem heightOne_fixedRing_unramified_descent
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    [IsNoetherianRing A] [Module.Finite A S]
    (I H : Subgroup G) (hIH : I ≤ H)
    [IsIntegrallyClosed (FixedPoints.subalgebra A S H)]
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.height = 1)
    (hI : Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S I))) :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S H)) := by
  sorry

end

end HodgeConjecture.Palomar
