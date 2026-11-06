module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Kaehler.Basic

@[expose] public section

/-!
# Residue of actual Kähler differentials on the multiplicative line

The Euler derivation multiplies the coefficient of `Tⁿ` by `n`. Its universal
Kähler lift followed by constant-coefficient evaluation is the residue of a
one-form, with `Res(T⁻¹ dT) = 1` and `Res(df) = 0`. Consequently the actual
logarithmic differential is not an exact Kähler differential.

The Euler construction and its monomial proofs are selectively adapted from
AxiomMath/Stacks, revision `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/RingTheory/DeRham/LaurentHomotopy.lean`, Apache-2.0.
See `third_party/axiom-stacks/LICENSE`. No upstream package is imported.
-/

set_option autoImplicit false

namespace HodgeConjecture.LaurentDeRham

open KaehlerDifferential LaurentPolynomial

noncomputable section

universe u

variable (k : Type u) [CommRing k]

/-- The actual Euler operator on Laurent polynomials, formed by linear monomial assembly. -/
def eulerDerivMap : LaurentPolynomial k →ₗ[k] LaurentPolynomial k :=
  (Finsupp.lsum k fun n ↦ (n : ℤ) • AddMonoidAlgebra.lsingle (R := k) n).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem eulerDerivMap_single (n : ℤ) (a : k) :
    eulerDerivMap k (.single n a) = n • (.single n a : LaurentPolynomial k) := by
  simp only [eulerDerivMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single, Finsupp.lsum_single,
    LinearMap.smul_apply, AddMonoidAlgebra.lsingle_apply]

/-- The Euler derivation `T ∂/∂T` on the original Laurent polynomial algebra. -/
def eulerDerivation : Derivation k (LaurentPolynomial k) (LaurentPolynomial k) where
  toLinearMap := eulerDerivMap k
  map_one_eq_zero' := by
    rw [← single_zero_one_eq_one, eulerDerivMap_single]
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
          eulerDerivMap_single, eulerDerivMap_single, eulerDerivMap_single,
          smul_comm (.single m a : LaurentPolynomial k),
          smul_comm (.single n b : LaurentPolynomial k),
          smul_eq_mul, smul_eq_mul, AddMonoidAlgebra.single_mul_single,
          AddMonoidAlgebra.single_mul_single, mul_comm b a, add_comm n m, add_smul]
        exact add_comm _ _

@[simp]
theorem eulerDerivation_single (n : ℤ) (a : k) :
    eulerDerivation k (.single n a) = n • (.single n a : LaurentPolynomial k) :=
  eulerDerivMap_single k n a

@[simp]
theorem eulerDerivation_T (n : ℤ) :
    eulerDerivation k (T n) = n • (T n : LaurentPolynomial k) :=
  eulerDerivation_single k n 1

@[simp]
theorem eulerDerivation_C (a : k) : eulerDerivation k (C a) = 0 := by
  rw [← single_eq_C, eulerDerivation_single]
  simp

/-- Evaluation at exponent zero on the actual Laurent coefficients. -/
def constantCoefficient : LaurentPolynomial k →ₗ[k] k :=
  (Finsupp.lapply 0).comp (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp]
theorem constantCoefficient_apply (f : LaurentPolynomial k) :
    constantCoefficient k f = f.coeff 0 := rfl

@[simp]
theorem constantCoefficient_single (n : ℤ) (a : k) :
    constantCoefficient k (.single n a) = if n = 0 then a else 0 := by
  change Finsupp.single n a 0 = if n = 0 then a else 0
  exact Finsupp.single_apply

@[simp]
theorem constantCoefficient_one : constantCoefficient k 1 = 1 := by
  rw [← single_zero_one_eq_one, constantCoefficient_single]
  simp

/-- An exact differential has zero residue because the Euler derivative has zero constant term. -/
theorem constantCoefficient_eulerDerivation (f : LaurentPolynomial k) :
    constantCoefficient k (eulerDerivation k f) = 0 := by
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | C_mul_T n a =>
    rw [← single_eq_C_mul_T, eulerDerivation_single, map_zsmul,
      constantCoefficient_single]
    split_ifs with h
    · subst n
      simp
    · simp

/-- The residue functional is the universal Kähler lift of the actual Euler derivation,
followed by constant-coefficient evaluation. -/
def kaehlerResidue : Ω[LaurentPolynomial k⁄k] →ₗ[k] k :=
  (constantCoefficient k).comp
    ((eulerDerivation k).liftKaehlerDifferential.restrictScalars k)

@[simp]
theorem kaehlerResidue_D (f : LaurentPolynomial k) :
    kaehlerResidue k (D k (LaurentPolynomial k) f) = 0 := by
  change constantCoefficient k
    ((eulerDerivation k).liftKaehlerDifferential (D k (LaurentPolynomial k) f)) = 0
  rw [Derivation.liftKaehlerDifferential_comp_D, constantCoefficient_eulerDerivation]

/-- The unit giving the actual regular coordinate on the multiplicative line. -/
def variableUnit : (LaurentPolynomial k)ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add]; norm_num
  inv_val := by rw [← T_add]; norm_num

@[simp]
theorem variableUnit_val : (variableUnit k : LaurentPolynomial k) = T 1 := rfl

@[simp]
theorem variableUnit_inv_val : (↑((variableUnit k)⁻¹) : LaurentPolynomial k) = T (-1) := rfl

/-- The original Kähler logarithmic differential of the Laurent coordinate. -/
def dlogT : Ω[LaurentPolynomial k⁄k] :=
  (T (-1) : LaurentPolynomial k) • D k (LaurentPolynomial k) (T 1)

/-- Residue is normalized on the actual logarithmic form. -/
@[simp]
theorem kaehlerResidue_dlogT : kaehlerResidue k (dlogT k) = 1 := by
  change constantCoefficient k
    ((eulerDerivation k).liftKaehlerDifferential
      ((T (-1) : LaurentPolynomial k) • D k (LaurentPolynomial k) (T 1))) = 1
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, eulerDerivation_T]
  simp only [one_zsmul, smul_eq_mul, ← T_add]
  norm_num

/-- Residue detects the exponent of every actual Laurent monomial unit. -/
theorem kaehlerResidue_monomial_dlog (n : ℤ) :
    kaehlerResidue k
      ((T (-n) : LaurentPolynomial k) • D k (LaurentPolynomial k) (T n)) = n := by
  change constantCoefficient k
    ((eulerDerivation k).liftKaehlerDifferential
      ((T (-n) : LaurentPolynomial k) • D k (LaurentPolynomial k) (T n))) = n
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, eulerDerivation_T,
    smul_comm, smul_eq_mul, ← T_add, neg_add_cancel, T_zero, map_zsmul,
    constantCoefficient_one]
  simp

/-- The logarithmic form cannot be the differential of any regular Laurent polynomial. -/
theorem dlogT_not_exact [Nontrivial k] :
    dlogT k ∉ Set.range (D k (LaurentPolynomial k)) := by
  rintro ⟨f, hf⟩
  have h := congrArg (kaehlerResidue k) hf
  rw [kaehlerResidue_D, kaehlerResidue_dlogT] at h
  exact zero_ne_one h

end

end HodgeConjecture.LaurentDeRham
