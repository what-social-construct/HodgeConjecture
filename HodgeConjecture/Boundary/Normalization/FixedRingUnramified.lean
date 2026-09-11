import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Unramified intermediate fixed rings

This module isolates the conclusion needed from a fixed-inertia theorem and
proves the remaining subgroup descent internally.

For a prime `Q` of a ring with a finite-group action, Stacks Project Tag
`0BST` identifies the inertia fixed ring as an étale neighbourhood at the
selected prime; Tag `09EH` is the discrete-valuation formulation.  Mathlib
currently defines inertia subgroups but does not yet contain that theorem,
so `InertiaFixedRingUnramifiedAt` records only its needed conclusion.  A
geometric instantiation must still identify the base with the full invariant
ring, the subgroup with the actual inertia group, and the source hypotheses.

Once it is supplied, `fixedRing_isUnramifiedAt_of_inertia_le_localized`
proves in Lean that `I ≤ H` makes the selected prime of the `H`-fixed ring
unramified.  Its Dedekind hypothesis is imposed only after localizing the
`H`-fixed ring at that prime.  The older global-Dedekind statement is retained
as a compatibility wrapper.  Both are statements about one selected branch,
not the whole `G/H` cover.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture

noncomputable section

namespace NormalizationInertia

/-- A source-conclusion interface for the local fixed-inertia input: the
selected prime of the proposed inertia fixed ring is unramified over the
base.  This record does not itself identify `I` as an inertia subgroup. -/
structure InertiaFixedRingUnramifiedAt
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    (I : Subgroup G) (Q : Ideal S) [Q.IsPrime] : Prop where
  isUnramifiedAt :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S I))

private theorem localRingHom_injective_of_injective
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    (f : R →+* S) (hpP : p = P.comap f) (hf : Function.Injective f) :
    Function.Injective (Localization.localRingHom p P f hpP) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨r, s, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  rw [Localization.localRingHom_mk'] at hx
  rw [IsLocalization.mk'_eq_zero_iff] at hx ⊢
  obtain ⟨t, ht⟩ := hx
  have ht0 : (t : S) ≠ 0 := by
    intro hzero
    exact t.property (hzero ▸ P.zero_mem)
  have hfr : f r = 0 := (mul_eq_zero.mp ht).resolve_left ht0
  exact ⟨1, by simpa using hf (by simpa using hfr)⟩

section LocalMap

variable {A S G : Type*}
variable [CommRing A] [CommRing S] [Algebra A S]
variable [Group G] [MulSemiringAction G S] [SMulCommClass G A S]

/-- The canonical local morphism associated to `I ≤ H`: fixed rings are
contravariant in the subgroup, so `S^H ⊆ S^I`, and contraction of `Q`
makes the two selected primes lie over one another. -/
noncomputable def fixedPointsLocalRingHom
    (I H : Subgroup G) (hIH : I ≤ H)
    (Q : Ideal S) [Q.IsPrime] :
    Localization.AtPrime
        (Q.under (FixedPoints.subalgebra A S H)) →+*
      Localization.AtPrime
        (Q.under (FixedPoints.subalgebra A S I)) := by
  let SH := FixedPoints.subalgebra A S H
  let SI := FixedPoints.subalgebra A S I
  have hSHSI : SH ≤ SI := by
    intro x hx
    exact fixedPoints_subgroup_antitone G S hIH hx
  letI : Algebra SH SI := (Subalgebra.inclusion hSHSI).toAlgebra
  letI : IsScalarTower SH SI S :=
    Subalgebra.inclusion.isScalarTower_right hSHSI S
  exact Localization.localRingHom
    (Q.under SH) (Q.under SI) (algebraMap SH SI)
    (Ideal.under_under (A := SH) (B := SI) Q).symm

/-- The canonical morphism between the selected fixed-ring localizations is
a local homomorphism. -/
theorem fixedPointsLocalRingHom_isLocalHom
    (I H : Subgroup G) (hIH : I ≤ H)
    (Q : Ideal S) [Q.IsPrime] :
    IsLocalHom (fixedPointsLocalRingHom (A := A) I H hIH Q) := by
  let SH := FixedPoints.subalgebra A S H
  let SI := FixedPoints.subalgebra A S I
  have hSHSI : SH ≤ SI := by
    intro x hx
    exact fixedPoints_subgroup_antitone G S hIH hx
  letI : Algebra SH SI := (Subalgebra.inclusion hSHSI).toAlgebra
  letI : IsScalarTower SH SI S :=
    Subalgebra.inclusion.isScalarTower_right hSHSI S
  exact Localization.isLocalHom_localRingHom
    (Q.under SH) (Q.under SI) (algebraMap SH SI)
    (Ideal.under_under (A := SH) (B := SI) Q).symm

/-- The canonical morphism between selected fixed-ring localizations is
injective when the ambient ring is a domain. -/
theorem fixedPointsLocalRingHom_injective
    [IsDomain S]
    (I H : Subgroup G) (hIH : I ≤ H)
    (Q : Ideal S) [Q.IsPrime] :
    Function.Injective (fixedPointsLocalRingHom (A := A) I H hIH Q) := by
  let SH := FixedPoints.subalgebra A S H
  let SI := FixedPoints.subalgebra A S I
  have hSHSI : SH ≤ SI := by
    intro x hx
    exact fixedPoints_subgroup_antitone G S hIH hx
  letI : Algebra SH SI := (Subalgebra.inclusion hSHSI).toAlgebra
  letI : IsScalarTower SH SI S :=
    Subalgebra.inclusion.isScalarTower_right hSHSI S
  exact localRingHom_injective_of_injective
    (Q.under SH) (Q.under SI) (algebraMap SH SI)
    (Ideal.under_under (A := SH) (B := SI) Q).symm
    (Subalgebra.inclusion_injective hSHSI)

end LocalMap

private theorem formallyUnramified_localizationAtMaximalIdeal_iff
    {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [IsLocalRing R] :
    Algebra.FormallyUnramified A
        (Localization.AtPrime (IsLocalRing.maximalIdeal R)) ↔
      Algebra.FormallyUnramified A R := by
  let eR : R ≃ₐ[R] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
    IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
      (fun _ hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx)
  let e : R ≃ₐ[A] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
    eR.restrictScalars A
  exact (Algebra.FormallyUnramified.iff_of_equiv e).symm

/-- If the inertia fixed ring is unramified at the selected prime and
`I ≤ H`, then the corresponding selected prime of the `H`-fixed ring is
unramified.  Only the selected local ring of `S^H` is required to be
Dedekind; no global one-dimensional hypothesis is imposed on `S^H`.

The proof forms the local tower
`A → (S^H)_{q_H} → (S^I)_{q_I}`, descends along its maximal
ideals, and then identifies the localization of the already-local lower ring
at its maximal ideal with the lower ring itself. -/
theorem fixedRing_isUnramifiedAt_of_inertia_le_localized
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    [IsNoetherianRing A] [Module.Finite A S]
    (I H : Subgroup G) (hIH : I ≤ H)
    (Q : Ideal S) [Q.IsPrime]
    [IsDedekindDomain
      (Localization.AtPrime
        (Q.under (FixedPoints.subalgebra A S H)))]
    (hI : InertiaFixedRingUnramifiedAt (A := A) (S := S) I Q) :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S H)) := by
  let SH := FixedPoints.subalgebra A S H
  let SI := FixedPoints.subalgebra A S I
  letI : Module.Finite A SH :=
    Module.Finite.of_injective SH.val.toLinearMap Subtype.val_injective
  letI : Module.Finite A SI :=
    Module.Finite.of_injective SI.val.toLinearMap Subtype.val_injective
  have hSHSI : SH ≤ SI := by
    intro x hx
    exact fixedPoints_subgroup_antitone G S hIH hx
  letI : Algebra SH SI := (Subalgebra.inclusion hSHSI).toAlgebra
  letI : IsScalarTower A SH SI :=
    Subalgebra.inclusion.isScalarTower_left hSHSI A
  letI : IsScalarTower SH SI S :=
    Subalgebra.inclusion.isScalarTower_right hSHSI S
  letI : (Q.under SI).LiesOver (Q.under SH) := by
    constructor
    exact (Ideal.under_under (A := SH) (B := SI) Q).symm
  let qH := Q.under SH
  let qI := Q.under SI
  let SHq := Localization.AtPrime qH
  let SIq := Localization.AtPrime qI
  letI : IsLocalHom (algebraMap SHq SIq) :=
    fixedPointsLocalRingHom_isLocalHom I H hIH Q
  have hlocal_injective : Function.Injective (algebraMap SHq SIq) :=
    fixedPointsLocalRingHom_injective I H hIH Q
  letI : FaithfulSMul SHq SIq :=
    (faithfulSMul_iff_algebraMap_injective SHq SIq).mpr hlocal_injective
  letI : NoZeroSMulDivisors SHq SIq :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr hlocal_injective
  letI : (IsLocalRing.maximalIdeal SIq).LiesOver
      (IsLocalRing.maximalIdeal SHq) := by
    constructor
    exact (((IsLocalRing.local_hom_TFAE (algebraMap SHq SIq)).out 0 4 rfl rfl).mp
      (inferInstance : IsLocalHom (algebraMap SHq SIq))).symm
  letI : Algebra.IsUnramifiedAt A (Q.under SI) :=
    hI.isUnramifiedAt
  have hmax : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal SHq) :=
    Algebra.IsUnramifiedAt.of_liesOver A
      (IsLocalRing.maximalIdeal SHq) (IsLocalRing.maximalIdeal SIq)
  change Algebra.FormallyUnramified A SHq
  exact formallyUnramified_localizationAtMaximalIdeal_iff.mp hmax

/-- Global-Dedekind compatibility wrapper for
`fixedRing_isUnramifiedAt_of_inertia_le_localized`. -/
theorem fixedRing_isUnramifiedAt_of_inertia_le
    {A S G : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsDomain S] [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S]
    [IsNoetherianRing A] [Module.Finite A S]
    (I H : Subgroup G) (hIH : I ≤ H)
    [IsDedekindDomain (FixedPoints.subalgebra A S H)]
    (Q : Ideal S) [Q.IsPrime]
    (hI : InertiaFixedRingUnramifiedAt (A := A) (S := S) I Q) :
    Algebra.IsUnramifiedAt A
      (Q.under (FixedPoints.subalgebra A S H)) := by
  exact fixedRing_isUnramifiedAt_of_inertia_le_localized I H hIH Q hI

end NormalizationInertia

end

end HodgeConjecture
