module

public import HodgeConjecture.Inputs.FixedInertia
public import Mathlib.RingTheory.Etale.Locus

@[expose] public section

/-!
# From an étale inertia neighbourhood to the local descent input

The Stacks Project's fixed-inertia theorem gives an étale principal
neighbourhood of the selected prime in the inertia fixed ring. This module
records the remaining consumer step: such a neighbourhood yields the
`IsUnramifiedAt` proposition used by the existing fixed-ring descent.

The existence of the étale neighbourhood is an explicit premise here. No
fixed-inertia theorem is proved or assumed globally by this module.
-/

set_option autoImplicit false

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- Étaleness at the selected fixed-ring prime gives the exact local
unramifiedness premise used by descent. -/
theorem inertiaFixedRingUnramifiedAt_of_isEtaleAt
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (I : Subgroup G) (Q : Ideal S) [Q.IsPrime]
    (h : Algebra.IsEtaleAt A
      (Q.under (FixedPoints.subalgebra A S I))) :
    InertiaFixedRingUnramifiedAt (A := A) I Q := by
  have : Algebra.FormallyEtale A
      (Localization.AtPrime (Q.under (FixedPoints.subalgebra A S I))) := h
  exact ⟨inferInstance⟩

/-- An étale selected localization, as in the DVR fixed-inertia theorem,
supplies the same local unramifiedness premise. -/
theorem inertiaFixedRingUnramifiedAt_of_etaleAtPrime
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (I : Subgroup G) (Q : Ideal S) [Q.IsPrime]
    (h : Algebra.Etale A
      (Localization.AtPrime (Q.under (FixedPoints.subalgebra A S I)))) :
    InertiaFixedRingUnramifiedAt (A := A) I Q :=
  inertiaFixedRingUnramifiedAt_of_isEtaleAt I Q h.formallyEtale

/-- An étale principal neighbourhood of the contracted prime supplies the
unramifiedness premise consumed by fixed-ring descent. -/
theorem inertiaFixedRingUnramifiedAt_of_exists_etaleAway
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (I : Subgroup G) (Q : Ideal S) [Q.IsPrime]
    (h : ∃ g : FixedPoints.subalgebra A S I,
      g ∉ Q.under (FixedPoints.subalgebra A S I) ∧
      Algebra.Etale A (Localization.Away g)) :
    InertiaFixedRingUnramifiedAt (A := A) I Q := by
  let SI := FixedPoints.subalgebra A S I
  let qI := Q.under SI
  obtain ⟨g, hg, hetale⟩ := h
  have hformal : Algebra.FormallyEtale A (Localization.Away g) :=
    hetale.formallyEtale
  have hsubset :
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum SI)) ⊆
        Algebra.etaleLocus A SI :=
    Algebra.basicOpen_subset_etaleLocus_iff.mpr hformal
  have hmem : (⟨qI, inferInstance⟩ : PrimeSpectrum SI) ∈
      PrimeSpectrum.basicOpen g :=
    (PrimeSpectrum.mem_basicOpen g _).mpr hg
  have hlocal : Algebra.IsEtaleAt A qI := hsubset hmem
  exact inertiaFixedRingUnramifiedAt_of_isEtaleAt I Q hlocal

end

end HodgeConjecture.NormalizationInertia
