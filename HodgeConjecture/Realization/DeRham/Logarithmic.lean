module

public import HodgeConjecture.Realization.DeRham.AffineCohomology

@[expose] public section

/-!
# The logarithmic regulator into actual degree-one de Rham cohomology

For every unit, the actual Kähler form u⁻¹ du is closed. Multiplication of
units becomes addition of forms and of cohomology classes. The resulting
regulator lands in the actual closed/exact quotient and hence in categorical
homology of the original affine de Rham complex. A comparison with Bloch
higher Chow groups or singular/Hodge realization is not asserted here.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open KaehlerDifferential

noncomputable section

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- The actual logarithmic Kähler differential of a unit. -/
def logarithmicDifferential (u : Aˣ) : Ω[A⁄k] :=
  ((u⁻¹ : Aˣ) : A) • D k A (u : A)

/-- The same Kähler form in the existing first exterior power. -/
def logarithmicForm (u : Aˣ) : ⋀[A]^1 Ω[A⁄k] :=
  (exteriorPower.oneEquiv A Ω[A⁄k]).symm (logarithmicDifferential k A u)

@[simp]
theorem oneEquiv_logarithmicForm (u : Aˣ) :
    exteriorPower.oneEquiv A Ω[A⁄k] (logarithmicForm k A u) =
      logarithmicDifferential k A u := LinearEquiv.apply_symm_apply _ _

/-- The generator expression in the same exterior power, retaining the inverse coefficient. -/
theorem logarithmicForm_eq_smul (u : Aˣ) :
    logarithmicForm k A u =
      ((u⁻¹ : Aˣ) : A) • exteriorPower.ιMulti A 1 (fun _ ↦ D k A (u : A)) := by
  apply (exteriorPower.oneEquiv A Ω[A⁄k]).injective
  simp [logarithmicDifferential]

/-- The universal derivation of the inverse of a unit, with no field hypothesis. -/
theorem differential_unit_inv (u : Aˣ) :
    D k A ((u⁻¹ : Aˣ) : A) = -(((u⁻¹ : Aˣ) : A) ^ 2) • D k A (u : A) :=
  (D k A).leibniz_of_mul_eq_one (by simp)

/-- Closedness uses the original de Rham differential and alternating repeated factors. -/
theorem logarithmicForm_closed (u : Aˣ) :
    deRhamDifferential (A := k) 1 (logarithmicForm k A u) = 0 := by
  rw [logarithmicForm_eq_smul]
  have h := deRhamDifferential_smul_ιMulti_D (A := k) (B := A) 1
    (Fin.cons (((u⁻¹ : Aˣ) : A)) (fun _ : Fin 1 ↦ (u : A)))
  simp only [Fin.cons_zero, Fin.cons_succ] at h
  rw [h]
  have hvec :
      (fun i : Fin 2 ↦ D k A ((Fin.cons (((u⁻¹ : Aˣ) : A))
        (fun _ : Fin 1 ↦ (u : A)) : Fin 2 → A) i)) =
      Function.update (fun _ : Fin 2 ↦ D k A (u : A)) 0
        (-(((u⁻¹ : Aˣ) : A) ^ 2) • D k A (u : A)) := by
    ext i
    fin_cases i <;> simp [differential_unit_inv]
  rw [hvec, AlternatingMap.map_update_smul]
  have hz : exteriorPower.ιMulti A 2 (fun _ : Fin 2 ↦ D k A (u : A)) = 0 :=
    (exteriorPower.ιMulti A 2).map_eq_zero_of_eq
      (fun _ : Fin 2 ↦ D k A (u : A)) (i := 0) (j := 1) rfl (by decide)
  simp [hz]

/-- The logarithmic form in the actual kernel of the outgoing differential. -/
def closedLogarithmicForm (u : Aˣ) : closedForms k A 1 :=
  ⟨logarithmicForm k A u, logarithmicForm_closed k A u⟩

@[simp]
theorem closedLogarithmicForm_val (u : Aˣ) :
    (closedLogarithmicForm k A u).val = logarithmicForm k A u := rfl

/-- The degree-one class of the actual logarithmic form, modulo actual exact forms. -/
def logarithmicClass (u : Aˣ) : Cohomology k A 1 :=
  cohomologyClass k A 1 (closedLogarithmicForm k A u)

@[simp]
theorem logarithmicDifferential_one : logarithmicDifferential k A 1 = 0 := by
  simp [logarithmicDifferential]

/-- The logarithmic identity is proved on the actual Kähler forms. -/
theorem logarithmicDifferential_mul (u v : Aˣ) :
    logarithmicDifferential k A (u * v) =
      logarithmicDifferential k A u + logarithmicDifferential k A v := by
  have hu : (((u * v)⁻¹ : Aˣ) : A) * (u : A) = ((v⁻¹ : Aˣ) : A) := by
    change (((u * v)⁻¹ * u : Aˣ) : A) = ((v⁻¹ : Aˣ) : A)
    congr 1
    group
  have hv : (((u * v)⁻¹ : Aˣ) : A) * (v : A) = ((u⁻¹ : Aˣ) : A) := by
    change (((u * v)⁻¹ * v : Aˣ) : A) = ((u⁻¹ : Aˣ) : A)
    congr 1
    rw [mul_inv_rev]
    calc
      v⁻¹ * u⁻¹ * v = (v⁻¹ * v) * u⁻¹ := by ac_rfl
      _ = u⁻¹ := by simp
  unfold logarithmicDifferential
  change (((u * v)⁻¹ : Aˣ) : A) • D k A ((u : A) * (v : A)) = _
  rw [Derivation.leibniz, smul_add, smul_smul, smul_smul, hu, hv, add_comm]

/-- Multiplicativity already holds before passing to any quotient. -/
def logarithmicDifferentialHom : Additive Aˣ →+ Ω[A⁄k] where
  toFun u := logarithmicDifferential k A u.toMul
  map_zero' := logarithmicDifferential_one k A
  map_add' u v := logarithmicDifferential_mul k A u.toMul v.toMul

@[simp]
theorem logarithmicDifferential_inv (u : Aˣ) :
    logarithmicDifferential k A u⁻¹ = -logarithmicDifferential k A u :=
  (logarithmicDifferentialHom k A).map_neg (Additive.ofMul u)

theorem logarithmicDifferential_zpow (u : Aˣ) (n : ℤ) :
    logarithmicDifferential k A (u ^ n) = n • logarithmicDifferential k A u :=
  (logarithmicDifferentialHom k A).map_zsmul n (Additive.ofMul u)

/-- Multiplication by the original unit recovers its universal derivative. -/
@[simp]
theorem unit_smul_logarithmicDifferential (u : Aˣ) :
    (u : A) • logarithmicDifferential k A u = D k A (u : A) := by
  simp [logarithmicDifferential, smul_smul]

@[simp]
theorem logarithmicForm_one : logarithmicForm k A 1 = 0 := by
  simp [logarithmicForm]

theorem logarithmicForm_mul (u v : Aˣ) :
    logarithmicForm k A (u * v) = logarithmicForm k A u + logarithmicForm k A v := by
  apply (exteriorPower.oneEquiv A Ω[A⁄k]).injective
  simp only [map_add, oneEquiv_logarithmicForm, logarithmicDifferential_mul]

@[simp]
theorem closedLogarithmicForm_one : closedLogarithmicForm k A 1 = 0 :=
  Subtype.ext (logarithmicForm_one k A)

theorem closedLogarithmicForm_mul (u v : Aˣ) :
    closedLogarithmicForm k A (u * v) =
      closedLogarithmicForm k A u + closedLogarithmicForm k A v :=
  Subtype.ext (logarithmicForm_mul k A u v)

@[simp]
theorem logarithmicClass_one : logarithmicClass k A 1 = 0 := by
  simp [logarithmicClass]

theorem logarithmicClass_mul (u v : Aˣ) :
    logarithmicClass k A (u * v) = logarithmicClass k A u + logarithmicClass k A v := by
  simp only [logarithmicClass, closedLogarithmicForm_mul, map_add]

/-- The logarithmic regulator is a group homomorphism into actual H¹. -/
def logarithmicRegulator : Additive Aˣ →+ Cohomology k A 1 where
  toFun u := logarithmicClass k A u.toMul
  map_zero' := logarithmicClass_one k A
  map_add' u v := logarithmicClass_mul k A u.toMul v.toMul

@[simp]
theorem logarithmicRegulator_apply (u : Aˣ) :
    logarithmicRegulator k A (Additive.ofMul u) = logarithmicClass k A u := rfl

@[simp]
theorem logarithmicClass_inv (u : Aˣ) : logarithmicClass k A u⁻¹ = -logarithmicClass k A u :=
  (logarithmicRegulator k A).map_neg (Additive.ofMul u)

theorem logarithmicClass_pow (u : Aˣ) (n : ℕ) :
    logarithmicClass k A (u ^ n) = n • logarithmicClass k A u :=
  (logarithmicRegulator k A).map_nsmul n (Additive.ofMul u)

/-- Actual Kähler pullback carries a unit's logarithmic differential to that of its image. -/
theorem map_logarithmicDifferential (B : Type u) [CommRing B]
    [Algebra k B] [Algebra A B] [IsScalarTower k A B] (u : Aˣ) :
    KaehlerDifferential.map k k A B (logarithmicDifferential k A u) =
      logarithmicDifferential k B (Units.map (algebraMap A B) u) := by
  simp only [logarithmicDifferential, map_smul, KaehlerDifferential.map_D]
  rw [← algebraMap_smul B]
  rfl

end

end HodgeConjecture.AffineDeRham
