-- SPDX-License-Identifier: Apache-2.0
module

public import HodgeConjecture.Boundary.Normalization.DvrInertiaEtale
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.Smooth.IntegralClosure

@[expose] public section

/-!
# Étaleness at the inertia fixed prime of a DVR

This proof adapts the étaleness component of Stacks Project Tag `09EH` from
AxiomMath/Stacks, revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/RingTheory/DiscreteValuationRing/Inertia/InvariantRing.lean`,
under Apache-2.0; see `third_party/axiom-stacks/LICENSE`.

The source also identifies the inertia fixed subring as an integral closure.
Here that fact is established internally to obtain finiteness and flatness;
the interface exposes only the étaleness conclusion used by the normalization
comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.NormalizationInertia

noncomputable section

/-- A DVR has exactly the zero and maximal primes, hence finite spectrum. -/
private theorem finite_primeSpectrum_of_isDiscreteValuationRing
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    Finite (PrimeSpectrum A) := by
  apply Finite.of_injective (fun x : PrimeSpectrum A ↦ x = ⊥)
  intro x y h
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top x with hx | hx <;>
    rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top y with hy | hy <;>
    simp_all

/-- **Stacks Tag `09EH`, étaleness component.** If `B` is the integral closure
of a DVR `A` in a finite Galois field extension and `P` is a maximal prime of
`B`, localization of the ring fixed by `P`'s inertia subgroup at the prime
below `P` is étale over `A`. -/
theorem inertia_fixedSubalgebra_etale_atPrime
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal] :
    let B := integralClosure A L
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI : SMulCommClass Gal(L/K) A B :=
      ⟨fun g a b ↦ by
        simp only [Algebra.smul_def]
        change galRestrict A K L B g (algebraMap A B a * b) =
          algebraMap A B a * galRestrict A K L B g b
        rw [map_mul, AlgEquiv.commutes]⟩
    let I := P.inertia Gal(L/K)
    let B' := FixedPoints.subalgebra A B I
    Algebra.Etale A (Localization.AtPrime (P.under B')) := by
  dsimp only
  let B := integralClosure A L
  let := IsIntegralClosure.MulSemiringAction A K L B
  let : SMulCommClass Gal(L/K) A B :=
    ⟨fun g a b ↦ by
      simp only [Algebra.smul_def]
      change galRestrict A K L B g (algebraMap A B a * b) =
        algebraMap A B a * galRestrict A K L B g b
      rw [map_mul, AlgEquiv.commutes]⟩
  let I := P.inertia Gal(L/K)
  let B' := FixedPoints.subalgebra A B I
  let L' := IntermediateField.fixedField I
  let inclusion : B' →ₐ[A] L := (integralClosure A L).val.comp B'.val
  let iota : B' →ₐ[A] L' :=
    inclusion.codRestrict (L'.toSubalgebra.restrictScalars A) (fun b ↦ by
      change (inclusion b : L) ∈ L'
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      exact (algebraMap_galRestrict_apply A g (b : B)).symm.trans
        (congrArg (algebraMap B L) (b.property ⟨g, hg⟩)))
  let := iota.toAlgebra
  have hIC : IsIntegralClosure B' A L' := by
    have hiota : Function.Injective iota := by
      intro x y h
      have hL := congrArg L'.val h
      change inclusion x = inclusion y at hL
      exact Subtype.ext (Subtype.ext hL)
    refine ⟨hiota, fun {x} ↦ ⟨fun hx ↦ ?_, ?_⟩⟩
    · obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp (hx.map L'.val)
      have hfix : ∀ g : I, g • b = b := by
        intro g
        apply Subtype.ext
        change algebraMap B L (galRestrict A K L B (g : Gal(L/K)) b) = algebraMap B L b
        rw [algebraMap_galRestrict_apply A (g : Gal(L/K)) (b : B), hb]
        exact x.property g
      exact ⟨⟨b, hfix⟩, Subtype.ext hb⟩
    · rintro ⟨b, rfl⟩
      exact ((isIntegral_algHom_iff B'.val Subtype.val_injective).mp
        (Algebra.IsIntegral.isIntegral (b : B))).map iota
  let := hIC
  have : IsScalarTower A B' L' := IsScalarTower.of_algebraMap_eq fun a ↦ (iota.commutes a).symm
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : Module.Finite A B' := IsIntegralClosure.finite A K L' B'
  have : IsDedekindDomain B' := IsIntegralClosure.isDedekindDomain A K L' B'
  have : Module.Finite B' B := Module.Finite.right A B' B
  have : Module.IsTorsionFree B' B := inferInstance
  have : Module.Flat B' B := inferInstance
  have : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := Module.IsTorsionFree.of_faithfulSMul B A L
  have : Module.Flat A B := inferInstance
  have : IsGaloisGroup Gal(L/K) A B := IsGaloisGroup.of_isFractionRing Gal(L/K) A B K L
  have : IsGaloisGroup I B' B := inferInstance
  let p := P.under A
  let q := P.under B'
  have : p.IsMaximal := Ideal.IsMaximal.under A P
  have : q.IsMaximal := Ideal.IsMaximal.under B' P
  have : q.LiesOver p := Ideal.LiesOver.tower_bot P q p
  obtain ⟨he, hsep⟩ := ramificationIdx_eq_one_and_isSeparable_of_inertia
    (G := Gal(L/K)) p P B' q
  have : Finite (PrimeSpectrum A) := finite_primeSpectrum_of_isDiscreteValuationRing A
  have : Finite (PrimeSpectrum B') := Algebra.QuasiFinite.finite_primeSpectrum A B'
  have : Module.IsTorsionFree A B' := Module.IsTorsionFree.of_faithfulSMul B' A B
  let : Algebra.IsSeparable (A ⧸ p) (B' ⧸ q) := hsep
  exact etale_atPrime_of_ramificationIdx_eq_one p q he

end

end HodgeConjecture.NormalizationInertia
