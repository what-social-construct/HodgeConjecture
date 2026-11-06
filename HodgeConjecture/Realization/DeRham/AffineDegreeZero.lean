module

public import HodgeConjecture.CommutativeAlgebra.DeRham.Complex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Unramified.Pi

@[expose] public section

/-!
# Affine algebraic de Rham cohomology in degree zero

Closed functions are the kernel of the actual universal Kähler derivation.
The exterior-power coordinates identify this kernel with degree-zero
cohomology of the constructed affine de Rham complex. No comparison with
scheme hypercohomology or with singular cohomology is assumed here.
-/

set_option autoImplicit false

namespace HodgeConjecture.AffineDeRham

open CategoryTheory KaehlerDifferential

noncomputable section

universe u

variable (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]

/-- Closed regular functions, with the equation imposed by the actual differential. -/
def closedFunctions : Subalgebra k A where
  carrier := {a | D k A a = 0}
  zero_mem' := map_zero _
  one_mem' := Derivation.map_one_eq_zero _
  add_mem' {a b} ha hb := by
    change D k A a = 0 at ha
    change D k A b = 0 at hb
    change D k A (a + b) = 0
    rw [map_add, ha, hb, add_zero]
  mul_mem' {a b} ha hb := by
    change D k A a = 0 at ha
    change D k A b = 0 at hb
    change D k A (a * b) = 0
    rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
  algebraMap_mem' := Derivation.map_algebraMap _

/-- Affine de Rham cohomology in degree zero, before any realization comparison. -/
abbrev H0 := ↥(closedFunctions k A)

@[simp]
theorem mem_closedFunctions (a : A) : a ∈ closedFunctions k A ↔ D k A a = 0 := Iff.rfl

/-- In exterior-power coordinates the first de Rham arrow is the universal derivation. -/
theorem differential_zero (a : A) :
    exteriorPower.oneEquiv A Ω[A⁄k]
      (deRhamDifferential (A := k) 0 ((exteriorPower.zeroEquiv A Ω[A⁄k]).symm a)) =
        D k A a := by
  have h := deRhamDifferential_smul_ιMulti_D (A := k) 0 (fun _ ↦ a)
  have h' : exteriorPower.oneEquiv A Ω[A⁄k]
      (deRhamDifferential (A := k) 0
        (a • exteriorPower.ιMulti A 0 (fun _ ↦ D k A a))) = D k A a := by
    calc
      _ = exteriorPower.oneEquiv A Ω[A⁄k]
          (exteriorPower.ιMulti A 1 (fun _ ↦ D k A a)) :=
        congrArg (exteriorPower.oneEquiv A Ω[A⁄k]) h
      _ = _ := exteriorPower.oneEquiv_ιMulti _
  rw [exteriorPower.zeroEquiv_symm_apply]
  convert h' using 2
  congr 2

/-- Closed-function coordinates on the actual kernel of the first de Rham arrow. -/
def kernelCoordinates :
    LinearMap.ker (deRhamDifferential (A := k) (B := A) 0) ≃ₗ[k] H0 k A where
  toFun x := ⟨exteriorPower.zeroEquiv A Ω[A⁄k] x.val, by
    change D k A (exteriorPower.zeroEquiv A Ω[A⁄k] x.val) = 0
    rw [← differential_zero k A]
    simp only [LinearEquiv.symm_apply_apply, LinearMap.mem_ker.mp x.property, map_zero]⟩
  invFun a := ⟨(exteriorPower.zeroEquiv A Ω[A⁄k]).symm a.val, by
    apply (exteriorPower.oneEquiv A Ω[A⁄k]).injective
    rw [differential_zero, map_zero]
    exact a.property⟩
  left_inv x := Subtype.ext ((exteriorPower.zeroEquiv A Ω[A⁄k]).symm_apply_apply x.val)
  right_inv a := Subtype.ext ((exteriorPower.zeroEquiv A Ω[A⁄k]).apply_symm_apply a.val)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := Subtype.ext (LinearMap.map_smul_of_tower _ r _)

/-- This closed-function model is the categorical homology of the actual affine complex. -/
def cohomologyZeroIso :
    (deRhamComplex k A).homology 0 ≅ ModuleCat.of k (H0 k A) := by
  refine (CochainComplex.isoHomologyπ₀ (deRhamComplex k A)).symm ≪≫
    (deRhamComplex k A).cyclesIsoSc' 0 0 1 (by simp)
      ((ComplexShape.up ℕ).next_eq' (by decide)) ≪≫
    ((deRhamComplex k A).sc' 0 0 1).moduleCatCyclesIso ≪≫ ?_
  change ModuleCat.of k (LinearMap.ker (((deRhamComplex k A).d 0 (0 + 1)).hom)) ≅ _
  rw [deRhamComplex_d]
  exact (kernelCoordinates k A).toModuleIso

variable {A} {B : Type u} [CommRing B] [Algebra k B]

/-- An algebra homomorphism carries closed functions to closed functions. -/
theorem map_closed (f : A →ₐ[k] B) {a : A} (ha : D k A a = 0) : D k B (f a) = 0 := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B := .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have h := congrArg (KaehlerDifferential.map k k A B) ha
  simpa only [KaehlerDifferential.map_D, map_zero,
    RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

/-- Pullback on closed functions is induced by the original map of coordinate rings. -/
def map (f : A →ₐ[k] B) : H0 k A →ₐ[k] H0 k B where
  toFun a := ⟨f a.val, map_closed k f a.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' a b := Subtype.ext (map_add f a.val b.val)
  map_mul' a b := Subtype.ext (map_mul f a.val b.val)
  commutes' r := Subtype.ext (f.commutes r)

@[simp]
theorem map_coe (f : A →ₐ[k] B) (a : H0 k A) : (map k f a).val = f a.val := rfl

variable (A)

/-- Formally unramified algebras have every function closed, proved from Ω = 0. -/
def unramifiedCoordinates [Algebra.FormallyUnramified k A] : H0 k A ≃ₐ[k] A where
  toFun := Subtype.val
  invFun a := ⟨a, Subsingleton.elim _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

end

end HodgeConjecture.AffineDeRham
