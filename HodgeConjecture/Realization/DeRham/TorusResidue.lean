module

public import HodgeConjecture.Realization.DeRham.LaurentResidue
public import HodgeConjecture.CommutativeAlgebra.DeRham.Complex

@[expose] public section

/-!
# Actual two-form residue on the two-dimensional algebraic torus

Two commuting coordinate Euler derivations induce actual linear functionals
on the universal Kähler module. Their determinant gives an alternating
two-form functional. Taking the constant coefficient in both Laurent
variables defines the torus residue. The residue kills incoming actual
de Rham differentials and normalizes the two coordinate logarithmic forms.
-/

set_option autoImplicit false

namespace HodgeConjecture.TorusDeRham

open KaehlerDifferential LaurentPolynomial LaurentDeRham

noncomputable section

universe u

variable (k : Type u) [CommRing k]

abbrev CoordinateRing := LaurentPolynomial (LaurentPolynomial k)

/-- Inner-coordinate Euler differentiation of the actual Laurent coefficients. -/
def innerEulerMap : CoordinateRing k →ₗ[k] CoordinateRing k :=
  (Finsupp.lsum k fun n ↦ (AddMonoidAlgebra.lsingle (R := k) n).comp
    (eulerDerivation k).toLinearMap).comp
      (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem innerEulerMap_single (n : ℤ) (a : LaurentPolynomial k) :
    innerEulerMap k (.single n a) = .single n (eulerDerivation k a) := by
  simp only [innerEulerMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.lsum_single, AddMonoidAlgebra.lsingle_apply]
  rfl

/-- The inner Euler derivation differentiates each Laurent coefficient. -/
def innerEulerDerivation : Derivation k (CoordinateRing k) (CoordinateRing k) where
  toLinearMap := innerEulerMap k
  map_one_eq_zero' := by
    rw [← single_zero_one_eq_one, innerEulerMap_single]
    simp
  leibniz' p q := by
    induction p using LaurentPolynomial.induction_on' with
    | add p p' hp hp' =>
      rw [add_mul, map_add, hp, hp', map_add, smul_add, add_smul]
      abel
    | C_mul_T m a =>
      induction q using LaurentPolynomial.induction_on' with
      | add q q' hq hq' =>
        rw [mul_add, map_add, hq, hq', map_add, smul_add, add_smul]
        abel
      | C_mul_T n b =>
        rw [← single_eq_C_mul_T, ← single_eq_C_mul_T, AddMonoidAlgebra.single_mul_single,
          innerEulerMap_single, innerEulerMap_single, innerEulerMap_single,
          smul_eq_mul, smul_eq_mul, AddMonoidAlgebra.single_mul_single,
          AddMonoidAlgebra.single_mul_single, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        simp only [add_comm n m, AddMonoidAlgebra.single_add]

/-- The outer Euler derivation is the original Laurent Euler derivation, restricted over `k`. -/
def outerEulerDerivation : Derivation k (CoordinateRing k) (CoordinateRing k) :=
  (eulerDerivation (LaurentPolynomial k)).restrictScalars k

@[simp]
theorem innerEulerDerivation_single (n : ℤ) (a : LaurentPolynomial k) :
    innerEulerDerivation k (.single n a) = .single n (eulerDerivation k a) :=
  innerEulerMap_single k n a

@[simp]
theorem outerEulerDerivation_single (n : ℤ) (a : LaurentPolynomial k) :
    outerEulerDerivation k (.single n a) = n • (.single n a : CoordinateRing k) :=
  eulerDerivation_single (LaurentPolynomial k) n a

/-- The actual inner-coordinate functional on the universal Kähler module. -/
def innerProjection : Ω[CoordinateRing k⁄k] →ₗ[CoordinateRing k] CoordinateRing k :=
  (innerEulerDerivation k).liftKaehlerDifferential

/-- The actual outer-coordinate functional on the universal Kähler module. -/
def outerProjection : Ω[CoordinateRing k⁄k] →ₗ[CoordinateRing k] CoordinateRing k :=
  (outerEulerDerivation k).liftKaehlerDifferential

@[simp]
theorem innerProjection_D (a : CoordinateRing k) :
    innerProjection k (D k (CoordinateRing k) a) = innerEulerDerivation k a :=
  Derivation.liftKaehlerDifferential_comp_D _ _

@[simp]
theorem outerProjection_D (a : CoordinateRing k) :
    outerProjection k (D k (CoordinateRing k) a) = outerEulerDerivation k a :=
  Derivation.liftKaehlerDifferential_comp_D _ _

/-- The determinant of the two actual Kähler coordinate functionals. -/
def determinantAlternating : Ω[CoordinateRing k⁄k] [⋀^Fin 2]→ₗ[CoordinateRing k]
    CoordinateRing k where
  toFun v := innerProjection k (v 0) * outerProjection k (v 1) -
    outerProjection k (v 0) * innerProjection k (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [map_add] <;> ring
  map_update_smul' v i a x := by
    fin_cases i <;> simp [map_smul, smul_eq_mul] <;> ring
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all <;> ring

/-- The induced genuine linear functional on the actual second exterior power. -/
def determinantForm : (⋀[CoordinateRing k]^2 Ω[CoordinateRing k⁄k]) →ₗ[CoordinateRing k]
    CoordinateRing k :=
  exteriorPower.alternatingMapLinearEquiv (determinantAlternating k)

@[simp]
theorem determinantForm_ιMulti (v : Fin 2 → Ω[CoordinateRing k⁄k]) :
    determinantForm k (exteriorPower.ιMulti (CoordinateRing k) 2 v) =
      innerProjection k (v 0) * outerProjection k (v 1) -
        outerProjection k (v 0) * innerProjection k (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The constant coefficient in both actual Laurent variables. -/
def doubleConstantCoefficient : CoordinateRing k →ₗ[k] k :=
  (constantCoefficient k).comp ((constantCoefficient (LaurentPolynomial k)).restrictScalars k)

@[simp]
theorem doubleConstantCoefficient_single (n : ℤ) (a : LaurentPolynomial k) :
    doubleConstantCoefficient k (.single n a) =
      if n = 0 then constantCoefficient k a else 0 := by
  change constantCoefficient k (constantCoefficient (LaurentPolynomial k) (.single n a)) = _
  rw [constantCoefficient_single]
  split_ifs <;> simp

@[simp]
theorem doubleConstantCoefficient_one : doubleConstantCoefficient k 1 = 1 := by
  change constantCoefficient k (constantCoefficient (LaurentPolynomial k) 1) = 1
  rw [constantCoefficient_one, constantCoefficient_one]

/-- The actual two-form residue; no coordinates are substituted for the exterior-power carrier. -/
def twoFormResidue : (⋀[CoordinateRing k]^2 Ω[CoordinateRing k⁄k]) →ₗ[k] k :=
  (doubleConstantCoefficient k).comp ((determinantForm k).restrictScalars k)

/-- Constant-coefficient integration by parts for the inner Laurent Euler derivation. -/
theorem constantCoefficient_innerEuler_mul (a b : LaurentPolynomial k) :
    constantCoefficient k (eulerDerivation k a * b + a * eulerDerivation k b) = 0 := by
  have h := constantCoefficient_eulerDerivation k (a * b)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h
  convert h using 2
  ring

/-- The constant coefficient of the actual Euler Jacobian of two functions vanishes. -/
theorem doubleConstantCoefficient_eulerDet (a b : CoordinateRing k) :
    doubleConstantCoefficient k
      (innerEulerDerivation k a * outerEulerDerivation k b -
        outerEulerDerivation k a * innerEulerDerivation k b) = 0 := by
  induction a using LaurentPolynomial.induction_on' with
  | add a a' ha ha' =>
    simp only [map_add, add_mul]
    rw [add_sub_add_comm, map_add, ha, ha', add_zero]
  | C_mul_T m a =>
    induction b using LaurentPolynomial.induction_on' with
    | add b b' hb hb' =>
      simp only [map_add, mul_add]
      rw [add_sub_add_comm, map_add, hb, hb', add_zero]
    | C_mul_T n b =>
      rw [← single_eq_C_mul_T, ← single_eq_C_mul_T,
        innerEulerDerivation_single, innerEulerDerivation_single,
        outerEulerDerivation_single, outerEulerDerivation_single,
        mul_smul_comm, smul_mul_assoc, AddMonoidAlgebra.single_mul_single,
        AddMonoidAlgebra.single_mul_single]
      rw [map_sub, map_zsmul, map_zsmul, doubleConstantCoefficient_single,
        doubleConstantCoefficient_single]
      by_cases h : m + n = 0
      · have hn : n = -m := by omega
        subst n
        simp only [add_neg_cancel, ↓reduceIte, neg_zsmul]
        have hi := constantCoefficient_innerEuler_mul k a b
        rw [map_add] at hi
        rw [sub_eq_add_neg, ← neg_add, ← smul_add, hi, smul_zero, neg_zero]
      · simp only [h, ↓reduceIte, smul_zero, sub_zero]

/-- Residue vanishes on the actual differential of every scalar-times-exact one-form. -/
theorem twoFormResidue_differential_generator (a b : CoordinateRing k) :
    twoFormResidue k
      (deRhamDifferential (A := k) 1
        (a • exteriorPower.ιMulti (CoordinateRing k) 1 (fun _ ↦ D k (CoordinateRing k) b))) = 0 := by
  have h := deRhamDifferential_smul_ιMulti_D (A := k) (B := CoordinateRing k) 1
    (Fin.cons a (fun _ : Fin 1 ↦ b))
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [h]
  change doubleConstantCoefficient k (determinantForm k _) = 0
  rw [determinantForm_ιMulti]
  simpa [innerProjection_D, outerProjection_D] using doubleConstantCoefficient_eulerDet k a b

/-- Residue kills every incoming differential from the actual first exterior power. -/
theorem twoFormResidue_differential_one
    (ω : ⋀[CoordinateRing k]^1 Ω[CoordinateRing k⁄k]) :
    twoFormResidue k (deRhamDifferential (A := k) 1 ω) = 0 := by
  have h (η : Ω[CoordinateRing k⁄k]) :
      twoFormResidue k (deRhamDifferential (A := k) 1
        ((exteriorPower.oneEquiv (CoordinateRing k) Ω[CoordinateRing k⁄k]).symm η)) = 0 := by
    obtain ⟨f, rfl⟩ := linearCombination_surjective k (CoordinateRing k) η
    induction f using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add f g hf hg => simp only [map_add, hf, hg, add_zero]
    | single a b =>
      rw [Finsupp.linearCombination_single]
      have hrep :
          (exteriorPower.oneEquiv (CoordinateRing k) Ω[CoordinateRing k⁄k]).symm
              (b • D k (CoordinateRing k) a) =
            b • exteriorPower.ιMulti (CoordinateRing k) 1
              (fun _ ↦ D k (CoordinateRing k) a) := by
        apply (exteriorPower.oneEquiv (CoordinateRing k) Ω[CoordinateRing k⁄k]).injective
        simp
      rw [hrep]
      exact twoFormResidue_differential_generator k b a
  simpa only [LinearEquiv.symm_apply_apply] using
    h (exteriorPower.oneEquiv (CoordinateRing k) Ω[CoordinateRing k⁄k] ω)

/-- The actual inner coordinate unit in the iterated Laurent coordinate ring. -/
def innerUnit : (CoordinateRing k)ˣ :=
  Units.map (LaurentPolynomial.C : LaurentPolynomial k →+* CoordinateRing k).toMonoidHom
    (variableUnit k)

/-- The actual outer coordinate unit in the iterated Laurent coordinate ring. -/
def outerUnit : (CoordinateRing k)ˣ := variableUnit (LaurentPolynomial k)

/-- The actual inner-coordinate logarithmic Kähler differential. -/
def innerLogarithmicDifferential : Ω[CoordinateRing k⁄k] :=
  (C (T (-1)) : CoordinateRing k) • D k (CoordinateRing k) (C (T 1))

/-- The actual outer-coordinate logarithmic Kähler differential. -/
def outerLogarithmicDifferential : Ω[CoordinateRing k⁄k] :=
  (T (-1) : CoordinateRing k) • D k (CoordinateRing k) (T 1)

@[simp]
theorem innerProjection_innerLogarithmicDifferential :
    innerProjection k (innerLogarithmicDifferential k) = 1 := by
  rw [innerLogarithmicDifferential, map_smul, innerProjection_D]
  change (C (T (-1)) : CoordinateRing k) •
    innerEulerDerivation k (.single 0 (T 1)) = 1
  rw [innerEulerDerivation_single, eulerDerivation_T]
  simp only [one_zsmul, single_eq_C, smul_eq_mul, ← map_mul, ← T_add]
  norm_num

@[simp]
theorem outerProjection_innerLogarithmicDifferential :
    outerProjection k (innerLogarithmicDifferential k) = 0 := by
  rw [innerLogarithmicDifferential, map_smul, outerProjection_D]
  change (C (T (-1)) : CoordinateRing k) •
    outerEulerDerivation k (.single 0 (T 1)) = 0
  rw [outerEulerDerivation_single, zero_zsmul, smul_zero]

@[simp]
theorem innerProjection_outerLogarithmicDifferential :
    innerProjection k (outerLogarithmicDifferential k) = 0 := by
  rw [outerLogarithmicDifferential, map_smul, innerProjection_D]
  change (T (-1) : CoordinateRing k) • innerEulerDerivation k (.single 1 1) = 0
  rw [innerEulerDerivation_single, Derivation.map_one_eq_zero,
    AddMonoidAlgebra.single_zero, smul_zero]

@[simp]
theorem outerProjection_outerLogarithmicDifferential :
    outerProjection k (outerLogarithmicDifferential k) = 1 := by
  rw [outerLogarithmicDifferential, map_smul, outerProjection_D]
  change (T (-1) : CoordinateRing k) • outerEulerDerivation k (.single 1 1) = 1
  rw [outerEulerDerivation_single]
  change (T (-1) : CoordinateRing k) • (1 : ℤ) • T 1 = 1
  rw [one_zsmul, smul_eq_mul, ← T_add]
  norm_num

/-- The actual ordered wedge of the two coordinate logarithmic Kähler forms. -/
def coordinateTwoForm : ⋀[CoordinateRing k]^2 Ω[CoordinateRing k⁄k] :=
  exteriorPower.ιMulti (CoordinateRing k) 2
    ![innerLogarithmicDifferential k, outerLogarithmicDifferential k]

/-- The ordered two-coordinate logarithmic form has residue one. -/
@[simp]
theorem twoFormResidue_coordinateTwoForm : twoFormResidue k (coordinateTwoForm k) = 1 := by
  change doubleConstantCoefficient k (determinantForm k (coordinateTwoForm k)) = 1
  rw [coordinateTwoForm, determinantForm_ιMulti]
  simp

end

end HodgeConjecture.TorusDeRham
