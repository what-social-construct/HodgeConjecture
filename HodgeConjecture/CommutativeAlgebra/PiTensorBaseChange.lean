import HodgeConjecture.CommutativeAlgebra.FiniteTensorProduct

/-!
# Base change of finite tensor products of algebras

Scalar extension commutes with the existing finite-index tensor product.
The comparison is constructed from the two tensor universal properties,
and its inverse laws are checked on the original algebra factors.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct Classical

universe uI uB uA uK

/-- Factorwise algebra equivalences induce an equivalence of the existing
finite-index tensor products. -/
def piTensorProductCongr
    {ι : Type uI} {R : Type uB} {A : ι → Type uA} {C : ι → Type uK}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, CommRing (C i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (C i)]
    (e : ∀ i, A i ≃ₐ[R] C i) : (⨂[R] i, A i) ≃ₐ[R] (⨂[R] i, C i) :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.congr fun i => (e i).toLinearEquiv)
    (by simp [PiTensorProduct.one_def]; rfl) (by
      apply (LinearMap.map_mul_iff _).mpr
      ext x y
      change PiTensorProduct.congr (fun i => (e i).toLinearEquiv)
          (PiTensorProduct.tprod R x * PiTensorProduct.tprod R y) =
        PiTensorProduct.congr (fun i => (e i).toLinearEquiv) (PiTensorProduct.tprod R x) *
          PiTensorProduct.congr (fun i => (e i).toLinearEquiv) (PiTensorProduct.tprod R y)
      simp only [PiTensorProduct.tprod_mul_tprod, PiTensorProduct.congr_tprod]
      congr 1
      funext i
      exact (e i).map_mul (x i) (y i))

/-- Factorwise algebra equivalence acts coordinatewise on pure tensors. -/
theorem piTensorProductCongr_tprod
    {ι : Type uI} {R : Type uB} {A : ι → Type uA} {C : ι → Type uK}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, CommRing (C i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (C i)]
    (e : ∀ i, A i ≃ₐ[R] C i) (x : ∀ i, A i) :
    piTensorProductCongr e (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => e i (x i)) :=
  PiTensorProduct.congr_tprod (fun i => (e i).toLinearEquiv) x

/-- Factorwise algebra equivalence preserves each distinguished tensor factor. -/
theorem piTensorProductCongr_singleAlgHom
    {ι : Type uI} {R : Type uB} {A : ι → Type uA} {C : ι → Type uK}
    [CommRing R] [∀ i, CommRing (A i)] [∀ i, CommRing (C i)]
    [∀ i, Algebra R (A i)] [∀ i, Algebra R (C i)]
    (e : ∀ i, A i ≃ₐ[R] C i) (i : ι) (a : A i) :
    piTensorProductCongr e (PiTensorProduct.singleAlgHom i a) =
      PiTensorProduct.singleAlgHom i (e i a) := by
  simp only [PiTensorProduct.singleAlgHom_apply, MonoidHom.mulSingle_apply,
    piTensorProductCongr_tprod]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.mulSingle, Function.update_of_ne h]

variable {ι : Type uI} {B : Type uB} {A : Type uA} {K : Type uK}
variable [Fintype ι] [CommRing B] [CommRing A] [CommRing K]
variable [Algebra B A] [Algebra B K]

private def piTensorBaseChangeForward :
    (K ⊗[B] (⨂[B] _ : ι, A)) →ₐ[K] (⨂[K] _ : ι, K ⊗[B] A) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _)
    (piTensorProductEvaluation (R := B) (A := A) (S := ⨂[K] _ : ι, K ⊗[B] A) fun i =>
      ((PiTensorProduct.singleAlgHom (R := K) (A := fun _ : ι => K ⊗[B] A) i).restrictScalars B).comp
        (Algebra.TensorProduct.includeRight (R := B) (A := K) (B := A)))
    (by
      intro k z
      exact Algebra.commutes k _)

private def piTensorBaseChangeBackward :
    (⨂[K] _ : ι, K ⊗[B] A) →ₐ[K] (K ⊗[B] (⨂[B] _ : ι, A)) :=
  piTensorProductEvaluation fun i =>
    Algebra.TensorProduct.lift (Algebra.ofId K _)
      (Algebra.TensorProduct.includeRight.comp
        (PiTensorProduct.singleAlgHom (R := B) (A := fun _ : ι => A) i))
      (fun _ _ => mul_comm _ _)

private theorem piTensorBaseChangeForward_tmul_single (k : K) (i : ι) (a : A) :
    piTensorBaseChangeForward (ι := ι) (B := B) (A := A) (K := K)
        (k ⊗ₜ[B] PiTensorProduct.singleAlgHom (R := B) (A := fun _ : ι => A) i a) =
      k • PiTensorProduct.singleAlgHom (R := K) (A := fun _ : ι => K ⊗[B] A)
        i ((1 : K) ⊗ₜ[B] a) := by
  rw [piTensorBaseChangeForward, Algebra.TensorProduct.lift_tmul,
    piTensorProductEvaluation_singleAlgHom]
  exact (Algebra.smul_def k _).symm

private theorem piTensorBaseChangeBackward_single_tmul (i : ι) (k : K) (a : A) :
    piTensorBaseChangeBackward (ι := ι) (B := B) (A := A) (K := K)
        (PiTensorProduct.singleAlgHom (R := K) (A := fun _ : ι => K ⊗[B] A)
          i (k ⊗ₜ[B] a)) =
      k ⊗ₜ[B] (PiTensorProduct.singleAlgHom i a : ⨂[B] _ : ι, A) := by
  rw [piTensorBaseChangeBackward, piTensorProductEvaluation_singleAlgHom]
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- Scalar extension commutes with a finite tensor product of algebras.
Both sides use the existing tensor carriers, including when the index is empty. -/
def piTensorProductBaseChangeEquiv :
    (K ⊗[B] (⨂[B] _ : ι, A)) ≃ₐ[K] (⨂[K] _ : ι, K ⊗[B] A) :=
  AlgEquiv.ofAlgHom (piTensorBaseChangeForward (ι := ι) (B := B) (A := A) (K := K))
    (piTensorBaseChangeBackward (ι := ι) (B := B) (A := A) (K := K))
    (by
      apply PiTensorProduct.algHom_ext
      intro i
      apply Algebra.TensorProduct.ext'
      intro k a
      simp only [AlgHom.comp_apply, AlgHom.id_apply,
        piTensorBaseChangeBackward_single_tmul, piTensorBaseChangeForward_tmul_single]
      rw [← map_smul]
      congr 1
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one])
    (by
      apply Algebra.TensorProduct.ext
      · apply AlgHom.ext
        intro k
        change piTensorBaseChangeBackward (ι := ι) (B := B) (A := A) (K := K)
          (piTensorBaseChangeForward (ι := ι) (B := B) (A := A) (K := K)
          (algebraMap K (K ⊗[B] (⨂[B] _ : ι, A)) k)) =
            algebraMap K (K ⊗[B] (⨂[B] _ : ι, A)) k
        simp only [AlgHom.commutes]
      · apply PiTensorProduct.algHom_ext
        intro i
        apply AlgHom.ext
        intro a
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, AlgHom.id_apply,
          piTensorBaseChangeForward_tmul_single, one_smul,
          piTensorBaseChangeBackward_single_tmul])

/-- The base-change comparison sends each original factor to its scalar extension. -/
theorem piTensorProductBaseChangeEquiv_tmul_singleAlgHom
    (k : K) (i : ι) (a : A) :
    piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)
        (k ⊗ₜ[B] PiTensorProduct.singleAlgHom (R := B) (A := fun _ : ι => A) i a) =
      k • PiTensorProduct.singleAlgHom (R := K) (A := fun _ : ι => K ⊗[B] A)
        i ((1 : K) ⊗ₜ[B] a) :=
  piTensorBaseChangeForward_tmul_single k i a

/-- The inverse comparison preserves the marked tensor factor. -/
theorem piTensorProductBaseChangeEquiv_symm_singleAlgHom_tmul
    (i : ι) (k : K) (a : A) :
    (piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)).symm
        (PiTensorProduct.singleAlgHom (R := K) (A := fun _ : ι => K ⊗[B] A)
          i (k ⊗ₜ[B] a)) =
      k ⊗ₜ[B] (PiTensorProduct.singleAlgHom i a : ⨂[B] _ : ι, A) :=
  piTensorBaseChangeBackward_single_tmul i k a

private theorem tprod_eq_prod_singleAlgHom
    {R : Type*} {C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    (x : ι → C) :
    PiTensorProduct.tprod R x = ∏ i, PiTensorProduct.singleAlgHom i (x i) := by
  simpa only [Finset.univ_prod_mulSingle] using
    (PiTensorProduct.tprod_prod (R := R) Finset.univ fun i => Pi.mulSingle i (x i))

/-- On pure tensors the canonical comparison only extends the scalars in each factor. -/
theorem piTensorProductBaseChangeEquiv_tmul_tprod (k : K) (x : ι → A) :
    piTensorProductBaseChangeEquiv (ι := ι) (B := B) (A := A) (K := K)
        (k ⊗ₜ[B] PiTensorProduct.tprod B x) =
      k • PiTensorProduct.tprod K (fun i => (1 : K) ⊗ₜ[B] x i) := by
  change piTensorBaseChangeForward (ι := ι) (B := B) (A := A) (K := K)
    (k ⊗ₜ[B] PiTensorProduct.tprod B x) = _
  rw [piTensorBaseChangeForward, Algebra.TensorProduct.lift_tmul,
    piTensorProductEvaluation_tprod]
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply,
    tprod_eq_prod_singleAlgHom]
  exact (Algebra.smul_def k _).symm

end

end HodgeConjecture.CollisionFoundations
