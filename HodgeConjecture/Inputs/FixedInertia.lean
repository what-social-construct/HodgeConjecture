module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Invariant.Basic

@[expose] public section

/-!
# The selected fixed-inertia unramifiedness input

This is the canonical source-conclusion interface used by fixed-ring
descent. It records only the local unramifiedness premise needed by the
project, not a proof of the Stacks Project's fixed-inertia theorem.

To obtain this premise from Stacks Tag `0BST`, an application must identify
the base with the full invariant ring and the subgroup with the actual
prime inertia group. Tag `09EH` supplies a separate DVR formulation.
Those source matches are not consequences of this record's definition.

Consumers take an explicit `(hI : InertiaFixedRingUnramifiedAt ...)`
argument. No global instance, project axiom, or blanket literature package
asserts its existence. The Palomar `Challenge`/`Solution` statements retain
the equivalent, unbundled Mathlib premise in their own signatures.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

/-- The selected prime of the proposed inertia fixed ring is unramified
over the base. This does not itself identify `I` as an inertia subgroup. -/
structure InertiaFixedRingUnramifiedAt
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (I : Subgroup G) (Q : Ideal S) [Q.IsPrime] : Prop where
  isUnramifiedAt :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S I))

/-- Bundling the source premise changes neither its meaning nor its strength. -/
theorem inertiaFixedRingUnramifiedAt_iff
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (I : Subgroup G) (Q : Ideal S) [Q.IsPrime] :
    InertiaFixedRingUnramifiedAt (A := A) I Q ↔
      Algebra.IsUnramifiedAt A
        (Q.under (FixedPoints.subalgebra A S I)) :=
  ⟨fun hI ↦ hI.isUnramifiedAt, fun hI ↦ ⟨hI⟩⟩

end HodgeConjecture.NormalizationInertia
