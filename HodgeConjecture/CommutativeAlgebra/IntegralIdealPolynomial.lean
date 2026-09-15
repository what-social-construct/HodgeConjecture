import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Maps

/-!
# Annihilating polynomials for elements of extended ideals

Finite witnesses for membership in an extended ideal lie in a finite
integral subalgebra. The ideal-sensitive Cayley--Hamilton theorem on
that finite module produces a monic annihilator whose lower coefficients
lie in the original ideal. The ambient integral algebra need not itself
be finite, and no domain, normality, or Noetherianity is assumed.
-/

set_option autoImplicit false

namespace HodgeConjecture.CommutativeAlgebra

noncomputable section

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]
  [Algebra R S] [Algebra.IsIntegral R S]

/-- The determinant trick retains the powers of the original ideal in
the coefficients of an actual monic annihilator. -/
theorem exists_monic_annihilator_coeff_mem_pow_of_mem_map
    (I : Ideal R) (y : S) (hy : y ∈ I.map (algebraMap R S)) :
    ∃ F : Polynomial R, F.Monic ∧ Polynomial.aeval y F = 0 ∧
      ∀ i, F.coeff i ∈ I ^ (F.natDegree - i) := by
  classical
  change y ∈ Submodule.span S (algebraMap R S '' (I : Set R)) at hy
  obtain ⟨a, t, ht, _, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hy
  let C : Subalgebra R S := Algebra.adjoin R (a '' (t : Set S))
  letI : Module.Finite R C :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (t.finite_toSet.image a)
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hyIC : y ∈ I • C.toSubmodule := by
    rw [← hsum]
    apply Submodule.sum_mem
    intro x hx
    obtain ⟨r, hr, rfl⟩ := ht hx
    change a (algebraMap R S r) * algebraMap R S r ∈ I • C.toSubmodule
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr
      (Algebra.subset_adjoin ⟨algebraMap R S r, hx, rfl⟩)
  have hyC : y ∈ C := Submodule.smul_le_right hyIC
  let z : C := ⟨y, hyC⟩
  have hz : z ∈ I • (⊤ : Submodule R C) :=
    (Submodule.mem_smul_top_iff (I := I) C.toSubmodule z).mpr hyIC
  have hzI : z ∈ I.map (algebraMap R C) := by
    rw [Ideal.smul_top_eq_map] at hz
    exact hz
  have hrange : LinearMap.range (Algebra.lmul R C z) ≤ I • (⊤ : Submodule R C) := by
    rw [Ideal.smul_top_eq_map]
    rintro _ ⟨b, rfl⟩
    exact (I.map (algebraMap R C)).mul_mem_right b hzI
  obtain ⟨F, hmonic, hcoeff, hroot⟩ :=
    LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
      R (Algebra.lmul R C z) I hrange
  have hzroot : Polynomial.aeval z F = 0 := by
    apply Algebra.lmul_injective (R := R)
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact hroot
  refine ⟨F, hmonic, ?_, hcoeff⟩
  have h := congrArg C.val hzroot
  simpa only [← Polynomial.aeval_algHom_apply, map_zero] using h

/-- In particular, every lower coefficient belongs to the original ideal. -/
theorem exists_monic_annihilator_of_mem_map
    (I : Ideal R) (y : S) (hy : y ∈ I.map (algebraMap R S)) :
    ∃ F : Polynomial R, F.Monic ∧ Polynomial.aeval y F = 0 ∧
      ∀ i < F.natDegree, F.coeff i ∈ I := by
  obtain ⟨F, hmonic, hroot, hcoeff⟩ :=
    exists_monic_annihilator_coeff_mem_pow_of_mem_map R S I y hy
  refine ⟨F, hmonic, hroot, fun i hi ↦ ?_⟩
  exact (Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hi)) (hcoeff i)

end

end HodgeConjecture.CommutativeAlgebra
