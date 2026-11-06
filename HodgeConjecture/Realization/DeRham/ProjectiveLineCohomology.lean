module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineChern

@[expose] public section

/-!
# Computing the actual two-chart projective-line cohomology in degree two

Every actual Laurent one-form has its proved Kähler coordinate times
`dlog T`. Positive Laurent monomials are restrictions of zero-chart forms;
negative monomials are restrictions of infinity-chart forms. Both kinds
are actual total boundaries. The surviving constant Laurent coefficient
therefore identifies the constructed degree-two Čech–de Rham cohomology
with the coefficient ring, with the coordinate Chern class mapping to one.

No division by integers is needed, so the computation holds over every
commutative ring. Its categorical target is homology of the actual total
complex, with scheme/Betti comparison retaining its separate scope.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.ProjectiveLineDeRham

open KaehlerDifferential AffineDeRham LaurentDeRham LaurentPolynomial CategoryTheory

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- Every actual overlap one-form is closed because its second exterior power vanishes. -/
def overlapClosedForm : Ω[LaurentPolynomial k⁄k] →ₗ[k] closedForms k (LaurentPolynomial k) 1 :=
  (LinearMap.restrictScalars k
    (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm.toLinearMap).codRestrict _
      (fun _ ↦ (laurentForms_subsingleton k (1 + 1) (by decide)).elim _ _)

/-- The total degree-two class of an actual Kähler form on the overlap. -/
def overlapClass : Ω[LaurentPolynomial k⁄k] →ₗ[k] CechH2 k :=
  (cechClass k).comp (overlapClosedForm k)

@[simp]
theorem overlapClass_chartZero (ω : Ω[Polynomial k⁄k]) :
    overlapClass k (chartZeroFormsMap k ω) = 0 := by
  apply (cechClass_eq_zero_iff k _).mpr
  refine ⟨(-ω, 0, 0), ?_⟩
  change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
    (chartInfinityFormsMap k 0 - chartZeroFormsMap k (-ω) - D k (LaurentPolynomial k) 0) = _
  simp only [map_zero, map_neg, zero_sub, neg_neg, sub_zero]
  rfl

@[simp]
theorem overlapClass_chartInfinity (ω : Ω[Polynomial k⁄k]) :
    overlapClass k (chartInfinityFormsMap k ω) = 0 := by
  apply (cechClass_eq_zero_iff k _).mpr
  refine ⟨(0, ω, 0), ?_⟩
  change (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm
    (chartInfinityFormsMap k ω - chartZeroFormsMap k 0 - D k (LaurentPolynomial k) 0) = _
  simp only [map_zero, sub_zero]
  rfl

/-- Laurent coefficients are used only through their actual scalar multiples of `dlog T`. -/
def laurentClass : LaurentPolynomial k →ₗ[k] CechH2 k where
  toFun f := overlapClass k (f • dlogT k)
  map_add' f g := by rw [add_smul, map_add]
  map_smul' a f := by
    change overlapClass k ((a • f) • dlogT k) = a • overlapClass k (f • dlogT k)
    rw [smul_assoc, map_smul]

/-- A positive Laurent logarithmic monomial is the restriction of a regular zero-chart form. -/
theorem chartZero_monomial_form (n : ℕ) (a : k) :
    chartZeroFormsMap k (Polynomial.monomial n a • D k (Polynomial k) Polynomial.X) =
      (C a * T ((n : ℤ) + 1) : LaurentPolynomial k) • dlogT k := by
  rw [chartZeroFormsMap, polynomialKaehlerPullback_smul, polynomialKaehlerPullback_D,
    chartZeroRingMap_X]
  change Polynomial.toLaurent (Polynomial.monomial n a) •
    D k (LaurentPolynomial k) (T 1) = _
  rw [Polynomial.toLaurent_C_mul_T, ← T_smul_dlogT, smul_smul, mul_T_assoc]

/-- The infinity chart supplies every negative Laurent logarithmic monomial, with the inversion sign. -/
theorem chartInfinity_monomial_form (n : ℕ) (a : k) :
    chartInfinityFormsMap k (Polynomial.monomial n a • D k (Polynomial k) Polynomial.X) =
      -((C a * T (-(n : ℤ) - 1) : LaurentPolynomial k) • dlogT k) := by
  rw [chartInfinityFormsMap, polynomialKaehlerPullback_smul, polynomialKaehlerPullback_D,
    chartInfinityRingMap_X]
  change LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.monomial n a)) •
    D k (LaurentPolynomial k) (T (-1)) = _
  simp only [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T]
  rw [D_T_neg_one, smul_neg, smul_smul, mul_T_assoc]
  rfl

theorem laurentClass_positive (n : ℕ) (a : k) :
    laurentClass k (C a * T ((n : ℤ) + 1)) = 0 := by
  have h := overlapClass_chartZero k (Polynomial.monomial n a • D k (Polynomial k) Polynomial.X)
  rw [chartZero_monomial_form] at h
  exact h

theorem laurentClass_negative (n : ℕ) (a : k) :
    laurentClass k (C a * T (-(n : ℤ) - 1)) = 0 := by
  have h := overlapClass_chartInfinity k
    (Polynomial.monomial n a • D k (Polynomial k) Polynomial.X)
  rw [chartInfinity_monomial_form, map_neg, neg_eq_zero] at h
  exact h

theorem laurentClass_constant (a : k) :
    laurentClass k (C a) = a • chernCoordinate k := by
  change overlapClass k ((algebraMap k (LaurentPolynomial k) a) • dlogT k) = _
  rw [IsScalarTower.algebraMap_smul, map_smul]
  congr 1

/-- Monomial reduction occurs inside the original boundary quotient. -/
theorem laurentClass_monomial (n : ℤ) (a : k) :
    laurentClass k (C a * T n) = constantCoefficient k (C a * T n) • chernCoordinate k := by
  induction n using Int.induction_on with
  | zero =>
    rw [← single_eq_C_mul_T, constantCoefficient_single]
    simpa only [single_eq_C_mul_T, T_zero, mul_one, ↓reduceIte] using laurentClass_constant k a
  | succ n _ =>
    rw [laurentClass_positive]
    rw [← single_eq_C_mul_T, constantCoefficient_single]
    have h : (n : ℤ) + 1 ≠ 0 := by omega
    simp only [h, ↓reduceIte, zero_smul]
  | pred n _ =>
    rw [laurentClass_negative]
    rw [← single_eq_C_mul_T, constantCoefficient_single]
    have h : -(n : ℤ) - 1 ≠ 0 := by omega
    simp only [h, ↓reduceIte, zero_smul]

/-- Every actual overlap class is its constant logarithmic coefficient times the coordinate Chern class. -/
theorem laurentClass_eq_constantCoefficient (f : LaurentPolynomial k) :
    laurentClass k f = constantCoefficient k f • chernCoordinate k := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, add_smul, hf, hg]
  | C_mul_T n a => exact laurentClass_monomial k n a

/-- This computes an arbitrary closed-form representative, with its original residue. -/
theorem cechClass_eq_residue_smul (ω : closedForms k (LaurentPolynomial k) 1) :
    cechClass k ω = LaurentDeRham.closedFormResidue k ω • chernCoordinate k := by
  let η := exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k] ω.val
  have h := laurentClass_eq_constantCoefficient k (kaehlerCoordinates k η)
  change overlapClass k ((eulerDerivation k).liftKaehlerDifferential η • dlogT k) =
    LaurentDeRham.closedFormResidue k ω • chernCoordinate k at h
  rw [eulerLift_smul_dlogT] at h
  have hω : overlapClosedForm k η = ω := by
    apply Subtype.ext
    exact (exteriorPower.oneEquiv (LaurentPolynomial k) Ω[LaurentPolynomial k⁄k]).symm_apply_apply ω.val
  change cechClass k (overlapClosedForm k η) = _ at h
  rwa [hω] at h

/-- Residue and the coordinate-class inclusion are inverse on the entire actual degree-two quotient. -/
@[simp]
theorem chernCoordinateLinearMap_cechResidue (z : CechH2 k) :
    chernCoordinateLinearMap k (cechResidue k z) = z := by
  obtain ⟨ω, rfl⟩ := (cechBoundaries k).mkQ_surjective z
  change LaurentDeRham.closedFormResidue k ω • chernCoordinate k = cechClass k ω
  exact (cechClass_eq_residue_smul k ω).symm

/-- The actual degree-two Čech–de Rham cohomology of the projective-line cover is the base ring. -/
def cechResidueEquiv : CechH2 k ≃ₗ[k] k where
  __ := cechResidue k
  invFun := chernCoordinateLinearMap k
  left_inv := chernCoordinateLinearMap_cechResidue k
  right_inv := cechResidue_chernCoordinateLinearMap k

theorem cechResidue_injective : Function.Injective (cechResidue k) :=
  (cechResidueEquiv k).injective

theorem cechResidue_surjective : Function.Surjective (cechResidue k) :=
  (cechResidueEquiv k).surjective

/-- The same computation on categorical homology of the original constructed total complex. -/
def cechCohomologyTwoCoordinates : (cechComplex k).homology 2 ≅ ModuleCat.of k k :=
  cechCohomologyTwoIso k ≪≫ (cechResidueEquiv k).toModuleIso

end

end HodgeConjecture.ProjectiveLineDeRham
