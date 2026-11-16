module

public import HodgeConjecture.Cycles.UFDZeroDivisorUnit
public import HodgeConjecture.Cycles.ProjectiveLineOrderDictionary

/-!
# Zero divisors in the actual function field of an affine UFD

The reduced-fraction argument is repeated in the actual generic-point
stalk of `Spec A`. Its local orders are the scheme divisor coefficients,
so no separate transport from a chosen fraction field is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles.ProjectiveLineDegree

noncomputable section

universe u

variable (A : CommRingCat.{u}) [IsDomain A] [IsNoetherianRing A]

/-- Zero scheme-divisor order of a nonzero affine function is equivalent
to its germ being a unit at that divisor point. -/
theorem spec_divisorOrder_algebraMap_eq_zero_iff_isUnit
    (x : DivisorPoint (Spec A)) (a : A) (ha : a ≠ 0) :
    divisorOrder (Spec A) x
      (Units.mk0 (algebraMap A (Spec A).functionField a)
        (by simpa only [map_zero] using
          (IsFractionRing.injective A (Spec A).functionField).ne ha)) = 0 ↔
      IsUnit (algebraMap A ((Spec A).presheaf.stalk x.val) a) := by
  letI : Algebra A (Spec A).functionField := specFunctionFieldAlgebra A
  letI : IsFractionRing A (Spec A).functionField := specFunctionFieldIsFractionRing A
  letI : Algebra A ((Spec A).presheaf.stalk x.val) := specStalkAlgebra A x.val
  letI : IsLocalization.AtPrime ((Spec A).presheaf.stalk x.val) x.val.asIdeal :=
    specStalkIsLocalization A x.val
  letI : IsScalarTower A ((Spec A).presheaf.stalk x.val) (Spec A).functionField :=
    spec_stalk_functionField_isScalarTower A x.val
  have haL : algebraMap A ((Spec A).presheaf.stalk x.val) a ≠ 0 :=
    (map_ne_zero_iff _
      (IsLocalization.injective ((Spec A).presheaf.stalk x.val)
        x.val.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  change localOrder ((Spec A).presheaf.stalk x.val) _ = 0 ↔ _
  simpa only [← IsScalarTower.algebraMap_apply] using
    (localOrder_algebraMap_eq_zero_iff_isUnit
      (L := (Spec A).presheaf.stalk x.val) (K := (Spec A).functionField)
      (algebraMap A ((Spec A).presheaf.stalk x.val) a) haL)

variable [UniqueFactorizationMonoid A]

/-- Coprime affine functions with the same actual scheme-divisor orders
have an invertible first function. -/
private theorem spec_isUnit_of_coprime_equal_divisorOrders
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) (hab : IsRelPrime a b)
    (heq : ∀ x : DivisorPoint (Spec A),
      divisorOrder (Spec A) x
        (Units.mk0 (algebraMap A (Spec A).functionField a)
          (by simpa only [map_zero] using
            (IsFractionRing.injective A (Spec A).functionField).ne ha)) =
      divisorOrder (Spec A) x
        (Units.mk0 (algebraMap A (Spec A).functionField b)
          (by simpa only [map_zero] using
            (IsFractionRing.injective A (Spec A).functionField).ne hb))) :
    IsUnit a := by
  by_contra hna
  obtain ⟨p, hp, hpa⟩ := WfDvdMonoid.exists_irreducible_factor hna ha
  let P : Ideal A := Ideal.span {p}
  letI : P.IsPrime := Ideal.isPrime_span_singleton_of_prime hp.prime
  have hP : P.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero) hp.not_isUnit
  let x : Spec A := ⟨P, inferInstance⟩
  letI : Algebra A ((Spec A).presheaf.stalk x) := specStalkAlgebra A x
  letI : IsLocalization.AtPrime ((Spec A).presheaf.stalk x) P :=
    specStalkIsLocalization A x
  let dx : DivisorPoint (Spec A) := ⟨x, by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP]
    rfl⟩
  have hpb : ¬p ∣ b := by
    intro hpb
    exact hp.not_isUnit (hab hpa hpb)
  have haP : a ∈ P := Ideal.mem_span_singleton.mpr hpa
  have hbP : b ∉ P := fun h => hpb (Ideal.mem_span_singleton.mp h)
  have hbunit : IsUnit (algebraMap A ((Spec A).presheaf.stalk x) b) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff ((Spec A).presheaf.stalk x) P b).mpr hbP
  have hb0 := (spec_divisorOrder_algebraMap_eq_zero_iff_isUnit A dx b hb).mpr hbunit
  have ha0 := (heq dx).trans hb0
  have haunit := (spec_divisorOrder_algebraMap_eq_zero_iff_isUnit A dx a ha).mp ha0
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff
    ((Spec A).presheaf.stalk x) P a).mp haunit) haP

/-- If an actual affine-scheme rational function has zero coefficient at
every divisor point, it is the image of a unit of the UFD coordinate ring. -/
theorem spec_exists_unit_of_all_divisorOrder_zero
    (f : (Spec A).functionFieldˣ)
    (hzero : ∀ x : DivisorPoint (Spec A), divisorOrder (Spec A) x f = 0) :
    ∃ u : Aˣ,
      Units.map (algebraMap A (Spec A).functionField).toMonoidHom u = f := by
  letI : Algebra A (Spec A).functionField := specFunctionFieldAlgebra A
  letI : IsFractionRing A (Spec A).functionField := specFunctionFieldIsFractionRing A
  let a : A := IsFractionRing.num A (f : (Spec A).functionField)
  let b : A := IsFractionRing.den A (f : (Spec A).functionField)
  have ha : a ≠ 0 := by
    intro h
    exact f.ne_zero (IsFractionRing.eq_zero_of_num_eq_zero (A := A) h)
  have hb : b ≠ 0 := by
    simpa only [b] using
      (mem_nonZeroDivisors_iff_ne_zero.mp
        (IsFractionRing.den A (f : (Spec A).functionField)).property)
  have hab : IsRelPrime a b := IsFractionRing.num_den_reduced A (f : (Spec A).functionField)
  let ua : (Spec A).functionFieldˣ := Units.mk0 (algebraMap A (Spec A).functionField a)
    (by simpa only [map_zero] using
      (IsFractionRing.injective A (Spec A).functionField).ne ha)
  let ub : (Spec A).functionFieldˣ := Units.mk0 (algebraMap A (Spec A).functionField b)
    (by simpa only [map_zero] using
      (IsFractionRing.injective A (Spec A).functionField).ne hb)
  have hf : f = ua / ub := by
    apply Units.ext
    exact (IsFractionRing.mk'_num_den' A (f : (Spec A).functionField)).symm
  have heq : ∀ x : DivisorPoint (Spec A),
      divisorOrder (Spec A) x ua = divisorOrder (Spec A) x ub := by
    intro x
    have h := hzero x
    change localOrder ((Spec A).presheaf.stalk x.val) f = 0 at h
    rw [hf, localOrder_div] at h
    exact sub_eq_zero.mp h
  have hau : IsUnit a := spec_isUnit_of_coprime_equal_divisorOrders A a b ha hb hab heq
  have hbu : IsUnit b := spec_isUnit_of_coprime_equal_divisorOrders A b a hb ha hab.symm
    (fun x => (heq x).symm)
  obtain ⟨u, hu⟩ := hau
  obtain ⟨v, hv⟩ := hbu
  refine ⟨u / v, ?_⟩
  apply Units.ext
  have hval : (f : (Spec A).functionField) =
      algebraMap A (Spec A).functionField a /
        algebraMap A (Spec A).functionField b := by
    exact (IsFractionRing.mk'_num_den' A (f : (Spec A).functionField)).symm
  rw [← hu, ← hv] at hval
  simpa using hval.symm

end

end HodgeConjecture.SchemeCycles

end
