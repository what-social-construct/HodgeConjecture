import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.Data.Fintype.Option

/-!
# Finite étale tensor products indexed by a finite type

The existing `PiTensorProduct` of finitely many copies of a finite étale
algebra is finite and étale. The proof upgrades the existing linear
reindexing and tensor regrouping equivalences to algebra equivalences;
no new tensor carrier is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct

universe u

variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]

private def tensorReindex {ι κ : Type u} (e : ι ≃ κ) :
    (⨂[B] _ : ι, A) ≃ₐ[B] (⨂[B] _ : κ, A) :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.reindex B (fun _ : ι => A) e)
    (by simp [PiTensorProduct.one_def]; rfl) (by
      apply (LinearMap.map_mul_iff _).mpr
      ext x y
      change PiTensorProduct.reindex B (fun _ : ι => A) e
          (PiTensorProduct.tprod B x * PiTensorProduct.tprod B y) =
        PiTensorProduct.reindex B (fun _ : ι => A) e (PiTensorProduct.tprod B x) *
          PiTensorProduct.reindex B (fun _ : ι => A) e (PiTensorProduct.tprod B y)
      simp only [PiTensorProduct.tprod_mul_tprod, PiTensorProduct.reindex_tprod]
      rfl)

private def tensorEmpty (ι : Type u) [IsEmpty ι] :
    (⨂[B] _ : ι, A) ≃ₐ[B] B :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.isEmptyEquiv ι)
    (by simp [PiTensorProduct.one_def]) (by
      apply (LinearMap.map_mul_iff _).mpr
      ext x y
      simp [PiTensorProduct.tprod_mul_tprod])

private def tensorSingleton : (⨂[B] _ : PUnit.{u+1}, A) ≃ₐ[B] A :=
  AlgEquiv.ofLinearEquiv (PiTensorProduct.subsingletonEquiv PUnit.unit)
    (by simp [PiTensorProduct.one_def]) (by
      apply (LinearMap.map_mul_iff _).mpr
      ext x y
      simp [PiTensorProduct.tprod_mul_tprod])

private def tensorSum (ι κ : Type u) :
    ((⨂[B] _ : ι, A) ⊗[B] (⨂[B] _ : κ, A)) ≃ₐ[B]
      (⨂[B] _ : ι ⊕ κ, A) :=
  (AlgEquiv.ofLinearEquiv (PiTensorProduct.tmulEquiv B A).symm
    (by simp [PiTensorProduct.one_def]; rfl) (by
      apply (LinearMap.map_mul_iff _).mpr
      ext x y
      change (PiTensorProduct.tmulEquiv B A).symm
          (PiTensorProduct.tprod B x * PiTensorProduct.tprod B y) =
        (PiTensorProduct.tmulEquiv B A).symm (PiTensorProduct.tprod B x) *
          (PiTensorProduct.tmulEquiv B A).symm (PiTensorProduct.tprod B y)
      simp only [PiTensorProduct.tprod_mul_tprod, PiTensorProduct.tmulEquiv_symm_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      rfl)).symm

/-- Finitely many copies of a module-finite algebra have module-finite
tensor product, on the existing finite-index tensor carrier. -/
theorem piTensorProduct_finite (ι : Type u) [Finite ι] [Module.Finite B A] :
    Module.Finite B (⨂[B] _ : ι, A) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
      letI := ih
      exact Module.Finite.equiv (tensorReindex (B := B) (A := A) e).toLinearEquiv
  | h_empty =>
      exact Module.Finite.equiv (tensorEmpty (B := B) (A := A) PEmpty).symm.toLinearEquiv
  | @h_option ι _ ih =>
      letI := ih
      letI : Module.Finite B (⨂[B] _ : PUnit.{u+1}, A) :=
        Module.Finite.equiv (tensorSingleton (B := B) (A := A)).symm.toLinearEquiv
      letI : Module.Finite B (⨂[B] _ : ι ⊕ PUnit.{u+1}, A) :=
        Module.Finite.equiv (tensorSum (B := B) (A := A) ι PUnit).toLinearEquiv
      exact Module.Finite.equiv
        (tensorReindex (B := B) (A := A) (Equiv.optionEquivSumPUnit ι).symm).toLinearEquiv

/-- A finite tensor product of copies of an étale algebra is étale over
the original base, by binary base change and composition. -/
theorem piTensorProduct_etale (ι : Type u) [Finite ι] [Algebra.Etale B A] :
    Algebra.Etale B (⨂[B] _ : ι, A) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
      letI := ih
      exact Algebra.Etale.of_equiv (tensorReindex (B := B) (A := A) e)
  | h_empty =>
      letI : Algebra.Etale B B :=
        { formallyEtale := by
            constructor
            intro Q _ _ I _
            exact ⟨fun _ _ _ => Subsingleton.elim _ _,
              fun _ => ⟨Algebra.ofId B Q, Subsingleton.elim _ _⟩⟩ }
      exact Algebra.Etale.of_equiv (tensorEmpty (B := B) (A := A) PEmpty).symm
  | @h_option ι _ ih =>
      letI := ih
      letI : Algebra.Etale B (⨂[B] _ : PUnit.{u+1}, A) :=
        Algebra.Etale.of_equiv (tensorSingleton (B := B) (A := A)).symm
      letI : Algebra.Etale B ((⨂[B] _ : ι, A) ⊗[B] (⨂[B] _ : PUnit.{u+1}, A)) :=
        Algebra.Etale.comp B (⨂[B] _ : ι, A) _
      letI : Algebra.Etale B (⨂[B] _ : ι ⊕ PUnit.{u+1}, A) :=
        Algebra.Etale.of_equiv (tensorSum (B := B) (A := A) ι PUnit)
      exact Algebra.Etale.of_equiv
        (tensorReindex (B := B) (A := A) (Equiv.optionEquivSumPUnit ι).symm)

end

end HodgeConjecture.CollisionFoundations
