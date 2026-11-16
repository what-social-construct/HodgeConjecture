module

public import HodgeConjecture.Cycles.RationalTopDegreeRelations
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroFiberRestriction
public import HodgeConjecture.Cycles.ProjectiveLineProductGenericDegree
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroChartComplex
public import HodgeConjecture.Cycles.ProjectiveLineProductZeroCarriersDistinct
public import HodgeConjecture.Cycles.AffineProductScalarUnits
public import HodgeConjecture.Cycles.SpecUFDZeroDivisorUnit
public import HodgeConjecture.Cycles.BaseFieldScalarOpenTransport
public import HodgeConjecture.Cycles.CoefficientRestriction

/-!
# Independence of the two ordinary Chow fiber classes on P¹ × P¹

The opposite affine product chart is the complement of the two named zero
fibers. A rational relation between them becomes one ambient principal
divisor after clearing denominators. Its restriction to the affine chart
is zero. The chart coordinate ring is a UFD, so the function is a unit
there; every such unit is a nonzero complex scalar. Transport through the
actual chart's function field then makes the ambient divisor zero.
Distinct fiber carriers finally force both rational coefficients to vanish.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace HodgeConjecture.ProjectiveLineProductFiberChowIndependence

open AlgebraicGeometry CategoryTheory SchemeCycles TensorProduct
open HodgeConjecture.ProjectiveLineProductChow
open HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization
open HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators
open HodgeConjecture.ProjectiveLineProductZeroFiberRestriction
open HodgeConjecture.ProjectiveLineProductComplexPoints
open HodgeConjecture.SchemeCycles.ProjectiveLineDegree

noncomputable section

private abbrev B := Polynomial ℂ ⊗[ℂ] Polynomial ℂ
private abbrev X := projectiveLineProduct ℂ
private abbrev U := Spec (.of B)
private abbrev j : U ⟶ X := chart ℂ
private abbrev δ : DimensionFunction X := dimensionFunction ℂ

private instance : IsDomain B :=
  HodgeConjecture.ProjectiveLineProductFiberCodimension.affineProduct_isDomain ℂ

private instance : IsNoetherianRing B :=
  Algebra.FiniteType.isNoetherianRing ℂ B

private instance : UniqueFactorizationMonoid B :=
  (projectiveLineAffineProductRingEquiv ℂ).symm.toRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

/-- A principal divisor supported on the two missing fibers vanishes:
on the affine chart its function is a unit, hence a base scalar, and the
same scalar has zero ambient principal divisor. -/
private theorem principalDivisor_zero_of_chart_restriction_zero
    (f : X.functionFieldˣ)
    (hopen : openRestriction ℤ j (principalDivisor X f) = 0) :
    principalDivisor X f = 0 := by
  letI : IsIntegral U := inferInstance
  letI : IsDominant (projectiveLineProductStructureMorphism ℂ) :=
    isDominant_toSpecField ℂ X (projectiveLineProductStructureMorphism ℂ)
  letI : Algebra ℂ (Spec (.of ℂ)).functionField :=
    specFunctionFieldAlgebra (.of ℂ)
  letI : Algebra B U.functionField := specFunctionFieldAlgebra (.of B)
  let q := AffineComplexPoints.structureMorphism B
  letI : IsDominant q := isDominant_toSpecField ℂ U q
  let fU : U.functionFieldˣ :=
    Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom f
  have hdivU : principalDivisor U fU = 0 := by
    have h := openRestriction_principalDivisor_of_isOpenImmersion j f
    rw [hopen] at h
    exact h.symm
  have horders : ∀ x : DivisorPoint U, divisorOrder U x fU = 0 := by
    intro x
    simpa only [primeDivisorOrder_pointSupport] using
      ((principalDivisor_eq_zero_iff U fU).mp hdivU)
        (divisorPointEquivPrimeDivisor U x)
  obtain ⟨u, hu⟩ :=
    spec_exists_unit_of_all_divisorOrder_zero (.of B) fU horders
  obtain ⟨c, hc⟩ := exists_baseScalar_of_affineProduct_specUnit u
  have hchart : j ≫ projectiveLineProductStructureMorphism ℂ = q := by
    change chart ℂ ≫ productBase = AffineComplexPoints.structureMorphism B
    rw [chart_complex_eq_productTensorChart_true_true]
    exact productTensorChart_comp_structureMorphism true true
  let g : X.functionFieldˣ :=
    Units.map (functionFieldMapOfDominant
      (projectiveLineProductStructureMorphism ℂ)).hom.toMonoidHom
        (Units.map (algebraMap ℂ (Spec (.of ℂ)).functionField).toMonoidHom c)
  have hscalar := baseFieldScalar_openImmersion ℂ j
    (projectiveLineProductStructureMorphism ℂ) q hchart c
  have hfg : fU = Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom g := by
    calc
      fU = Units.map (algebraMap B U.functionField).toMonoidHom u := hu.symm
      _ = Units.map (functionFieldMapOfDominant q).hom.toMonoidHom
            (Units.map (algebraMap ℂ (Spec (.of ℂ)).functionField).toMonoidHom c) := hc
      _ = Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom g := hscalar.symm
  have hfg' : f = g := by
    apply Units.ext
    apply (functionFieldEquivOfOpenImmersion j).injective
    exact congrArg Units.val hfg
  rw [hfg']
  exact principalDivisor_baseFieldScalar_zero ℂ X
    (projectiveLineProductStructureMorphism ℂ) c

/-- The finite rational cycle with coefficients on the two actual zero
fibers. -/
private def fiberCombination (a b : ℚ) : cyclesOfDegree ℚ δ 1 :=
  a • cyclesOfDegreeRationalize δ 1 (firstZeroCycle ℂ) +
    b • cyclesOfDegreeRationalize δ 1 (secondZeroCycle ℂ)

private theorem fiberCombination_class (a b : ℚ) :
    rationalClassMap δ 1 (fiberCombination a b) =
      a • firstZeroRationalChowClass ℂ + b • secondZeroRationalChowClass ℂ := by
  simp only [fiberCombination, map_add, map_smul]
  simp only [firstZeroRationalChowClass, secondZeroRationalChowClass,
    firstZeroChowClass, secondZeroChowClass, chowRationalize_classMap]

private theorem fiberCombination_restrict_zero (a b : ℚ) :
    openRestriction ℚ j (fiberCombination a b).val = 0 := by
  change openRestriction ℚ j
      (a • (cyclesOfDegreeRationalize δ 1 (firstZeroCycle ℂ)).val +
        b • (cyclesOfDegreeRationalize δ 1 (secondZeroCycle ℂ)).val) = 0
  rw [map_add, map_smul, map_smul,
    firstZeroCycle_restrict_zero, secondZeroCycle_restrict_zero]
  simp

/-- The two actual ordinary rational Chow classes of the coordinate-zero
fibers are linearly independent. This is proved from the original rational
equivalence quotient and the actual chart function field. -/
theorem rational_zero_fiber_classes_independent (a b : ℚ)
    (h : a • firstZeroRationalChowClass ℂ +
      b • secondZeroRationalChowClass ℂ = 0) :
    a = 0 ∧ b = 0 := by
  let z := fiberCombination a b
  have hz : z ∈ rationalPrincipalRelations δ 1 := by
    apply (rationalClassMap_eq_zero_iff δ 1 z).mp
    simpa only [z, fiberCombination_class] using h
  obtain ⟨m, hm, f, t, ht, hmt⟩ :=
    rationalRelation_has_ambientPrincipalDivisor_multiple X δ 1
      (generic_degree_sub_one_eq_one ℂ) z hz
  have hqopen : openRestriction ℚ j (cyclesOfDegreeRationalize δ 1 t).val = 0 := by
    have h := congrArg
      (fun v : cyclesOfDegree ℚ δ 1 ↦ openRestriction ℚ j v.val) hmt
    rw [← h]
    change openRestriction ℚ j (m • z.val) = 0
    rw [map_zsmul, fiberCombination_restrict_zero, smul_zero]
  have hzopen : openRestriction ℤ j t.val = 0 := by
    have hrat : Finsupp.mapRange (Int.castAddHom ℚ) (map_zero _)
        (openRestriction ℤ j t.val) = 0 := by
      rw [← openRestriction_rationalize j t.val]
      exact hqopen
    exact (Finsupp.mapRange_injective (Int.castAddHom ℚ) (map_zero _)
      Int.cast_injective) (by simpa using hrat)
  have hpdiv : principalDivisor X f = 0 := by
    apply principalDivisor_zero_of_chart_restriction_zero f
    simpa only [ht] using hzopen
  have htzero : t = 0 := Subtype.ext (by rw [ht, hpdiv]; rfl)
  have hmz : m • z = 0 := by rw [hmt, htzero, map_zero]
  have hz0 : z = 0 := by
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have hmq : (m : ℚ) • z = 0 := by
      exact (Int.cast_smul_eq_zsmul ℚ m z).trans hmz
    exact (smul_eq_zero.mp hmq).resolve_left hmQ
  have ha : a = 0 := by
    have hv := congrArg (fun v : cyclesOfDegree ℚ δ 1 ↦
      v.val (projectiveLineProductZeroFirstCarrier ℂ)) hz0
    simpa [z, fiberCombination, firstZeroCycle_rationalized_val,
      secondZeroCycle_rationalized_val, fundamentalCycle,
      firstZeroCarrier_ne_secondZeroCarrier ℂ] using hv
  have hb : b = 0 := by
    have hv := congrArg (fun v : cyclesOfDegree ℚ δ 1 ↦
      v.val (projectiveLineProductZeroSecondCarrier ℂ)) hz0
    simpa [z, fiberCombination, firstZeroCycle_rationalized_val,
      secondZeroCycle_rationalized_val, fundamentalCycle,
      firstZeroCarrier_ne_secondZeroCarrier ℂ] using hv
  exact ⟨ha, hb⟩

end

end HodgeConjecture.ProjectiveLineProductFiberChowIndependence

end
