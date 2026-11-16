module

public import HodgeConjecture.Cycles.UFDHeightOneLocalOrder
public import HodgeConjecture.Cycles.ProjectiveLineOrderDictionary
public import HodgeConjecture.Cycles.PrincipalRelationOfDivisor
public import HodgeConjecture.Cycles.AffineDimensionFunction
public import HodgeConjecture.Cycles.IntegralCodimension

/-!
# Height-one prime cycles are principal on an affine UFD

At a height-one prime of a Noetherian UFD, the prime ideal is principal.
The actual local-order coefficients of its generator are one at that
prime and zero at every other codimension-one point of the spectrum.
Thus its actual principal-divisor cycle is the fundamental cycle of the
reduced prime closure.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles.ProjectiveLineDegree

noncomputable section

universe u

variable (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]

private theorem spec_divisorPoint_height_one
    (x : DivisorPoint (Spec A)) : x.val.asIdeal.height = 1 := by
  letI : Algebra A ((Spec A).presheaf.stalk x.val) := specStalkAlgebra A x.val
  letI : IsLocalization.AtPrime ((Spec A).presheaf.stalk x.val) x.val.asIdeal :=
    specStalkIsLocalization A x.val
  have h := x.property
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.val.asIdeal] at h
  exact_mod_cast h

private theorem spec_pointSupport_codimension_one
    (p : Spec A) (hp : p.asIdeal.height = 1) :
    supportCodimension (pointSupport (Spec A) p) = 1 := by
  apply (supportCodimension_eq_one_iff _).2
  rw [ambientGenericPoint_pointSupport]
  letI : Algebra A ((Spec A).presheaf.stalk p) := specStalkAlgebra A p
  letI : IsLocalization.AtPrime ((Spec A).presheaf.stalk p) p.asIdeal :=
    specStalkIsLocalization A p
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal, hp]
  rfl

/-- On the actual affine spectrum, the divisor order of a generator of
a principal height-one prime is the Kronecker delta at that prime. -/
theorem spec_divisorOrder_primeGenerator
    [DecidableEq (Spec A)]
    (p : Spec A) (hp : p.asIdeal.height = 1)
    (a : A) (ha : a ≠ 0) (hP : p.asIdeal = Ideal.span {a})
    (x : DivisorPoint (Spec A)) :
    divisorOrder (Spec A) x
      (Units.mk0 (algebraMap A (Spec A).functionField a)
        (by simpa only [map_zero] using
          (IsFractionRing.injective A (Spec A).functionField).ne ha)) =
      if x.val = p then 1 else 0 := by
  letI : Algebra A (Spec A).functionField := specFunctionFieldAlgebra A
  letI : IsFractionRing A (Spec A).functionField := specFunctionFieldIsFractionRing A
  letI : Algebra A ((Spec A).presheaf.stalk x.val) := specStalkAlgebra A x.val
  letI : IsLocalization.AtPrime ((Spec A).presheaf.stalk x.val) x.val.asIdeal :=
    specStalkIsLocalization A x.val
  letI : IsScalarTower A ((Spec A).presheaf.stalk x.val) (Spec A).functionField :=
    spec_stalk_functionField_isScalarTower A x.val
  by_cases hx : x.val = p
  · rw [if_pos hx]
    have hxP : x.val.asIdeal = Ideal.span {a} := by rw [hx]; exact hP
    change localOrder ((Spec A).presheaf.stalk x.val) _ = 1
    exact localOrder_atPrime_generator_self (R := A)
      (L := (Spec A).presheaf.stalk x.val)
      (K := (Spec A).functionField) (P := x.val.asIdeal) a ha hxP
  · rw [if_neg hx]
    have hPQ : p.asIdeal ≠ x.val.asIdeal := by
      intro h
      exact hx (PrimeSpectrum.ext h.symm)
    change localOrder ((Spec A).presheaf.stalk x.val) _ = 0
    exact localOrder_atPrime_generator_other (R := A)
      (L := (Spec A).presheaf.stalk x.val)
      (K := (Spec A).functionField) (P := p.asIdeal)
      (Q := x.val.asIdeal) hp (spec_divisorPoint_height_one A x)
      hPQ a ha hP

/-- The principal divisor of a generator of a principal height-one prime
is exactly the original fundamental cycle of its reduced closed support. -/
theorem spec_principalDivisor_primeGenerator
    (p : Spec A) (hp : p.asIdeal.height = 1)
    (a : A) (ha : a ≠ 0) (hP : p.asIdeal = Ideal.span {a}) :
    principalDivisor (Spec A)
      (Units.mk0 (algebraMap A (Spec A).functionField a)
        (by simpa only [map_zero] using
          (IsFractionRing.injective A (Spec A).functionField).ne ha)) =
      fundamentalCycle ℤ (pointSupport (Spec A) p) := by
  classical
  let f : (Spec A).functionFieldˣ :=
    Units.mk0 (algebraMap A (Spec A).functionField a)
      (by simpa only [map_zero] using
        (IsFractionRing.injective A (Spec A).functionField).ne ha)
  apply Finsupp.ext
  intro Z
  by_cases hcodim : supportCodimension Z = 1
  · let x : DivisorPoint (Spec A) :=
      (divisorPointEquivPrimeDivisor (Spec A)).symm ⟨Z, hcodim⟩
    have hx : x.val = ambientGenericPoint Z := rfl
    rw [principalDivisor_apply_prime (Spec A) f ⟨Z, hcodim⟩]
    change divisorOrder (Spec A) x f = _
    rw [spec_divisorOrder_primeGenerator A p hp a ha hP x, hx]
    by_cases hZ : ambientGenericPoint Z = p
    · rw [if_pos hZ]
      have hZeq : Z = pointSupport (Spec A) p := by
        calc
          Z = pointSupport (Spec A) (ambientGenericPoint Z) :=
            (pointSupport_ambientGenericPoint Z).symm
          _ = pointSupport (Spec A) p := congrArg _ hZ
      rw [hZeq, fundamentalCycle_apply_self]
    · rw [if_neg hZ]
      have hZne : Z ≠ pointSupport (Spec A) p := by
        intro heq
        exact hZ (by rw [heq, ambientGenericPoint_pointSupport])
      simp [fundamentalCycle, hZne]
  · rw [principalDivisor_apply_of_not_prime (Spec A) f Z hcodim]
    have hZne : Z ≠ pointSupport (Spec A) p := by
      intro heq
      exact hcodim (heq ▸ spec_pointSupport_codimension_one A p hp)
    simp [fundamentalCycle, hZne]

/-- Every actual codimension-one carrier in the spectrum of a Noetherian
UFD is the principal divisor of some nonzero regular function. -/
theorem spec_fundamentalCycle_eq_principalDivisor
    [UniqueFactorizationMonoid A]
    (W : IntegralClosedSubscheme (Spec A))
    (hW : supportCodimension W = 1) :
    ∃ f : (Spec A).functionFieldˣ,
      fundamentalCycle ℤ W = principalDivisor (Spec A) f := by
  let x : DivisorPoint (Spec A) :=
    (divisorPointEquivPrimeDivisor (Spec A)).symm ⟨W, hW⟩
  have hx : x.val = ambientGenericPoint W := rfl
  have hheight := spec_divisorPoint_height_one A x
  obtain ⟨a, hP⟩ :=
    exists_generator_of_height_one x.val.asIdeal hheight
  have ha : a ≠ 0 := by
    intro h
    have hbot : x.val.asIdeal = ⊥ := by simpa [h] using hP
    have hne : x.val.asIdeal ≠ ⊥ :=
      x.val.asIdeal.ne_bot_of_height_eq_one hheight
    exact hne hbot
  refine ⟨Units.mk0 (algebraMap A (Spec A).functionField a)
      (by simpa only [map_zero] using
        (IsFractionRing.injective A (Spec A).functionField).ne ha), ?_⟩
  have hpoint : W = pointSupport (Spec A) x.val := by
    rw [hx]
    exact (pointSupport_ambientGenericPoint W).symm
  rw [hpoint]
  exact (spec_principalDivisor_primeGenerator A x.val hheight a ha hP).symm

end

end HodgeConjecture.SchemeCycles

end
