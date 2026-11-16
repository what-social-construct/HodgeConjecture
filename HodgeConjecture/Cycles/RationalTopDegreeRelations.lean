module

public import HodgeConjecture.Cycles.TopDegreePrincipalRelations
public import HodgeConjecture.Cycles.RationalChow
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Clearing denominators in rational top-degree Chow relations

Rational homogeneous cycles are the localization of integral homogeneous
cycles at nonzero integers. The same is true of the ordinary Chow quotient.
Consequently, a rational relation becomes an actual integral relation after
multiplication by a nonzero integer. On an integral scheme one degree below
the generic degree, that integral relation is a single ambient principal
divisor.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry TensorProduct

noncomputable section

universe u

private instance cyclesOfDegreeRationalize_isLocalizedModule
    {X : Scheme.{u}} (δ : DimensionFunction X) (n : ℤ) :
    IsLocalizedModule (nonZeroDivisors ℤ) (cyclesOfDegreeRationalize δ n) := by
  let e : (ℚ ⊗[ℤ] cyclesOfDegree ℤ δ n) ≃ₗ[ℤ] cyclesOfDegree ℚ δ n :=
    (cyclesOfDegreeRationalizationEquiv δ n).restrictScalars ℤ
  have heq : e.toLinearMap.comp
      (TensorProduct.mk ℤ ℚ (cyclesOfDegree ℤ δ n) 1) =
        cyclesOfDegreeRationalize δ n := by
    apply LinearMap.ext
    intro c
    exact cyclesOfDegreeRationalizationEquiv_one_tmul δ n c
  rw [← heq]
  letI : IsLocalizedModule (nonZeroDivisors ℤ)
      (TensorProduct.mk ℤ ℚ (cyclesOfDegree ℤ δ n) 1) :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
  exact IsLocalizedModule.of_linearEquiv
    (S := nonZeroDivisors ℤ)
    (f := TensorProduct.mk ℤ ℚ (cyclesOfDegree ℤ δ n) 1) e

/-- Every rational homogeneous cycle becomes the coefficient extension of
an integral homogeneous cycle after multiplication by a nonzero integer. -/
theorem exists_nonzero_multiple_rational_cycle_integral
    {X : Scheme.{u}} (δ : DimensionFunction X) (n : ℤ)
    (c : cyclesOfDegree ℚ δ n) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ t : cyclesOfDegree ℤ δ n,
      m • c = cyclesOfDegreeRationalize δ n t := by
  obtain ⟨⟨t, ⟨m, hm⟩⟩, h⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ) (cyclesOfDegreeRationalize δ n) c
  exact ⟨m, (mem_nonZeroDivisors_iff_ne_zero.mp hm), t, h⟩

/-- An integral cycle whose rational class vanishes is an actual integral
principal relation after multiplication by a nonzero integer. -/
theorem exists_nonzero_multiple_integral_relation
    {X : Scheme.{u}} [IsNoetherian X]
    (δ : DimensionFunction X) (n : ℤ)
    (t : cyclesOfDegree ℤ δ n)
    (ht : cyclesOfDegreeRationalize δ n t ∈ rationalPrincipalRelations δ n) :
    ∃ m : ℤ, m ≠ 0 ∧ m • t ∈ principalRelations δ n := by
  have hzero : rationalClassMap δ n (cyclesOfDegreeRationalize δ n t) = 0 :=
    (rationalClassMap_eq_zero_iff δ n _).mpr ht
  have htensor : (1 : ℚ) ⊗ₜ[ℤ] classMap δ n t = 0 := by
    apply (chowRationalizationEquiv δ n).injective
    simpa only [map_zero, chowRationalizationEquiv_tmul_classMap,
      one_smul] using hzero
  obtain ⟨⟨m, hmS⟩, hm⟩ :=
    (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)
      (TensorProduct.mk ℤ ℚ (ChowGroup δ n) 1)).mp htensor
  refine ⟨m, mem_nonZeroDivisors_iff_ne_zero.mp hmS, ?_⟩
  apply (classMap_eq_zero_iff δ n _).mp
  simpa only [map_zsmul, Submonoid.smul_def] using hm

/-- Any rational relation in the degree immediately below the generic
degree is, after clearing denominators, the coefficient extension of one
ambient principal divisor. All objects are the existing Chow cycles and
their original principal-relation quotient. -/
theorem rationalRelation_has_ambientPrincipalDivisor_multiple
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (δ : DimensionFunction X) (n : ℤ)
    (hn : δ (genericPoint X) - 1 = n)
    (c : cyclesOfDegree ℚ δ n)
    (hc : c ∈ rationalPrincipalRelations δ n) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ f : X.functionFieldˣ,
      ∃ t : cyclesOfDegree ℤ δ n,
        (t : Cycles X ℤ) = principalDivisor X f ∧
          m • c = cyclesOfDegreeRationalize δ n t := by
  obtain ⟨r, hr, t, hrt⟩ := exists_nonzero_multiple_rational_cycle_integral δ n c
  have ht : cyclesOfDegreeRationalize δ n t ∈ rationalPrincipalRelations δ n := by
    rw [← hrt]
    exact zsmul_mem hc r
  obtain ⟨s, hs, hsrel⟩ := exists_nonzero_multiple_integral_relation δ n t ht
  obtain ⟨f, hf⟩ :=
    (mem_principalRelations_iff_exists_ambientPrincipalDivisor X δ n hn (s • t)).mp hsrel
  refine ⟨s * r, mul_ne_zero hs hr, f, s • t, hf, ?_⟩
  rw [mul_smul, hrt, map_zsmul]

end

end HodgeConjecture.SchemeCycles

end
