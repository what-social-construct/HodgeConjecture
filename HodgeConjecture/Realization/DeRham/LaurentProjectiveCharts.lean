module

public import HodgeConjecture.Realization.DeRham.LaurentResidue
public import HodgeConjecture.CommutativeAlgebra.DeRham.Complex
public import Mathlib.RingTheory.Kaehler.Polynomial

@[expose] public section

/-!
# The two projective-line chart maps on actual Kähler differentials

The overlap coordinate maps are the actual polynomial-to-Laurent map and
its composition with inversion. Universal Kähler pullback gives their maps
on one-forms. Both images are closed in the original de Rham complex and
have residue zero. Thus they can be used in the genuine two-chart Čech
de Rham differential, without assuming a compatibility or exactness square.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineDeRham

open KaehlerDifferential LaurentPolynomial LaurentDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- Restriction of regular functions from the zero chart to the actual overlap algebra. -/
def chartZeroRingMap : Polynomial k →ₐ[k] LaurentPolynomial k := Polynomial.toLaurentAlg

/-- Restriction from the infinity chart sends its coordinate to the inverse overlap coordinate. -/
def chartInfinityRingMap : Polynomial k →ₐ[k] LaurentPolynomial k :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

@[simp]
theorem chartZeroRingMap_X : chartZeroRingMap k Polynomial.X = T 1 :=
  Polynomial.toLaurent_X

@[simp]
theorem chartInfinityRingMap_X : chartInfinityRingMap k Polynomial.X = T (-1) := by
  simp [chartInfinityRingMap]

/-- Pullback on the original universal Kähler modules through the specified chart ring map. -/
def polynomialKaehlerPullback (f : Polynomial k →ₐ[k] LaurentPolynomial k) :
    Ω[Polynomial k⁄k] →ₗ[k] Ω[LaurentPolynomial k⁄k] := by
  letI : Algebra (Polynomial k) (LaurentPolynomial k) := f.toRingHom.toAlgebra
  letI : IsScalarTower k (Polynomial k) (LaurentPolynomial k) :=
    .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  exact (KaehlerDifferential.map k k (Polynomial k) (LaurentPolynomial k)).restrictScalars k

@[simp]
theorem polynomialKaehlerPullback_D (f : Polynomial k →ₐ[k] LaurentPolynomial k)
    (p : Polynomial k) :
    polynomialKaehlerPullback k f (D k (Polynomial k) p) =
      D k (LaurentPolynomial k) (f p) := by
  let : Algebra (Polynomial k) (LaurentPolynomial k) := f.toRingHom.toAlgebra
  let : IsScalarTower k (Polynomial k) (LaurentPolynomial k) :=
    .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  change KaehlerDifferential.map k k (Polynomial k) (LaurentPolynomial k)
    (D k (Polynomial k) p) = _
  exact KaehlerDifferential.map_D k k (Polynomial k) (LaurentPolynomial k) p

theorem polynomialKaehlerPullback_smul (f : Polynomial k →ₐ[k] LaurentPolynomial k)
    (p : Polynomial k) (ω : Ω[Polynomial k⁄k]) :
    polynomialKaehlerPullback k f (p • ω) = f p • polynomialKaehlerPullback k f ω := by
  let : Algebra (Polynomial k) (LaurentPolynomial k) := f.toRingHom.toAlgebra
  let : IsScalarTower k (Polynomial k) (LaurentPolynomial k) :=
    .of_algebraMap_eq fun a ↦ (f.commutes a).symm
  change KaehlerDifferential.map k k (Polynomial k) (LaurentPolynomial k) (p • ω) = _
  rw [map_smul]
  exact IsScalarTower.algebraMap_smul (LaurentPolynomial k) p _

/-- The generator formula is derived from the existing polynomial Kähler equivalence. -/
theorem polynomialKaehlerPullback_eq (f : Polynomial k →ₐ[k] LaurentPolynomial k)
    (ω : Ω[Polynomial k⁄k]) :
    polynomialKaehlerPullback k f ω =
      f (polynomialEquiv k ω) • D k (LaurentPolynomial k) (f Polynomial.X) := by
  have hω : ω = polynomialEquiv k ω • D k (Polynomial k) Polynomial.X :=
    ((polynomialEquiv k).symm_apply_apply ω).symm
  calc
    _ = polynomialKaehlerPullback k f
        (polynomialEquiv k ω • D k (Polynomial k) Polynomial.X) := congrArg _ hω
    _ = _ := by rw [polynomialKaehlerPullback_smul, polynomialKaehlerPullback_D]

/-- The actual polynomial chain rule through an arbitrary chart ring map. -/
theorem differential_polynomialMap (f : Polynomial k →ₐ[k] LaurentPolynomial k)
    (p : Polynomial k) :
    D k (LaurentPolynomial k) (f p) =
      f (Polynomial.derivative p) • D k (LaurentPolynomial k) (f Polynomial.X) := by
  rw [← polynomialKaehlerPullback_D k f p, polynomialKaehlerPullback_eq,
    polynomialEquiv_D]

/-- Every polynomial-chart one-form pulls back to an actually closed overlap one-form. -/
theorem polynomialKaehlerPullback_closed (f : Polynomial k →ₐ[k] LaurentPolynomial k)
    (ω : Ω[Polynomial k⁄k]) :
    deRhamDifferential (A := k) 1
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (polynomialKaehlerPullback k f ω)) = 0 := by
  rw [polynomialKaehlerPullback_eq, map_smul]
  have hι :
      (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
          (D k (LaurentPolynomial k) (f Polynomial.X)) =
        exteriorPower.ιMulti (LaurentPolynomial k) 1
          (fun _ ↦ D k (LaurentPolynomial k) (f Polynomial.X)) := by
    apply (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).injective
    simp
  rw [hι]
  have h := deRhamDifferential_smul_ιMulti_D (A := k) (B := LaurentPolynomial k) 1
    (Fin.cons (f (polynomialEquiv k ω)) (fun _ : Fin 1 ↦ f Polynomial.X))
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [h]
  have hv :
      (fun i : Fin 2 ↦ D k (LaurentPolynomial k)
        ((Fin.cons (f (polynomialEquiv k ω)) (fun _ : Fin 1 ↦ f Polynomial.X) :
          Fin 2 → LaurentPolynomial k) i)) =
      Function.update (fun _ : Fin 2 ↦ D k (LaurentPolynomial k) (f Polynomial.X)) 0
        (f (Polynomial.derivative (polynomialEquiv k ω)) •
          D k (LaurentPolynomial k) (f Polynomial.X)) := by
    ext i
    fin_cases i
    · simpa using differential_polynomialMap k f (polynomialEquiv k ω)
    · simp
  rw [hv, AlternatingMap.map_update_smul]
  have hz : exteriorPower.ιMulti (LaurentPolynomial k) 2
      (fun _ : Fin 2 ↦ D k (LaurentPolynomial k) (f Polynomial.X)) = 0 :=
    (exteriorPower.ιMulti (LaurentPolynomial k) 2).map_eq_zero_of_eq
      (fun _ : Fin 2 ↦ D k (LaurentPolynomial k) (f Polynomial.X))
      (i := 0) (j := 1) rfl (by decide)
  rw [Function.update_eq_self, hz, smul_zero]

/-- The actual zero-chart restriction on Kähler one-forms. -/
def chartZeroFormsMap : Ω[Polynomial k⁄k] →ₗ[k] Ω[LaurentPolynomial k⁄k] :=
  polynomialKaehlerPullback k (chartZeroRingMap k)

/-- The actual infinity-chart restriction on Kähler one-forms. -/
def chartInfinityFormsMap : Ω[Polynomial k⁄k] →ₗ[k] Ω[LaurentPolynomial k⁄k] :=
  polynomialKaehlerPullback k (chartInfinityRingMap k)

@[simp]
theorem chartZeroFormsMap_D (p : Polynomial k) :
    chartZeroFormsMap k (D k (Polynomial k) p) =
      D k (LaurentPolynomial k) (chartZeroRingMap k p) :=
  polynomialKaehlerPullback_D k _ p

@[simp]
theorem chartInfinityFormsMap_D (p : Polynomial k) :
    chartInfinityFormsMap k (D k (Polynomial k) p) =
      D k (LaurentPolynomial k) (chartInfinityRingMap k p) :=
  polynomialKaehlerPullback_D k _ p

theorem chartZeroForms_closed (ω : Ω[Polynomial k⁄k]) :
    deRhamDifferential (A := k) 1
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (chartZeroFormsMap k ω)) = 0 :=
  polynomialKaehlerPullback_closed k _ ω

theorem chartInfinityForms_closed (ω : Ω[Polynomial k⁄k]) :
    deRhamDifferential (A := k) 1
      ((exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
        (chartInfinityFormsMap k ω)) = 0 :=
  polynomialKaehlerPullback_closed k _ ω

theorem constantCoefficient_positiveChart (p : Polynomial k) :
    constantCoefficient k (Polynomial.toLaurent p * T 1) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq, add_zero]
  | monomial n a =>
    rw [Polynomial.toLaurent_C_mul_T, mul_T_assoc, ← single_eq_C_mul_T,
      constantCoefficient_single]
    split_ifs with h
    · omega
    · rfl

theorem constantCoefficient_negativeChart (p : Polynomial k) :
    constantCoefficient k (LaurentPolynomial.invert (Polynomial.toLaurent p) * T (-1)) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_mul, hp, hq, add_zero]
  | monomial n a =>
    simp only [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T]
    rw [mul_T_assoc, ← single_eq_C_mul_T, constantCoefficient_single]
    split_ifs with h
    · omega
    · rfl

/-- Zero-chart regular one-forms have zero residue in the genuine overlap module. -/
theorem residue_chartZeroFormsMap (ω : Ω[Polynomial k⁄k]) :
    kaehlerResidue k (chartZeroFormsMap k ω) = 0 := by
  rw [chartZeroFormsMap, polynomialKaehlerPullback_eq, chartZeroRingMap_X]
  change constantCoefficient k ((eulerDerivation k).liftKaehlerDifferential
    (chartZeroRingMap k (polynomialEquiv k ω) • D k (LaurentPolynomial k) (T 1))) = 0
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, eulerDerivation_T]
  simp only [one_zsmul, smul_eq_mul]
  exact constantCoefficient_positiveChart k _

/-- Infinity-chart regular one-forms also have zero residue, including inversion's sign. -/
theorem residue_chartInfinityFormsMap (ω : Ω[Polynomial k⁄k]) :
    kaehlerResidue k (chartInfinityFormsMap k ω) = 0 := by
  rw [chartInfinityFormsMap, polynomialKaehlerPullback_eq, chartInfinityRingMap_X]
  change constantCoefficient k ((eulerDerivation k).liftKaehlerDifferential
    (chartInfinityRingMap k (polynomialEquiv k ω) • D k (LaurentPolynomial k) (T (-1)))) = 0
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, eulerDerivation_T]
  simp only [neg_smul, one_smul, smul_eq_mul, mul_neg, map_neg]
  change -(constantCoefficient k
    (LaurentPolynomial.invert (Polynomial.toLaurent (polynomialEquiv k ω)) * T (-1))) = 0
  rw [constantCoefficient_negativeChart, neg_zero]

end

end HodgeConjecture.ProjectiveLineDeRham
