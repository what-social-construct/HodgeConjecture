import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.RingTheory.LocalProperties.Basic

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

open scoped TensorProduct Classical

universe u uI uR uA uS

/-- The algebra homomorphism multiplying a finite family of algebra maps.
This same evaluation applies to affine coordinate algebras and their fields. -/
def piTensorProductEvaluation
    {ι : Type uI} {R : Type uR} {A : Type uA} {S : Type uS}
    [Fintype ι] [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (f : ι → A →ₐ[R] S) :
    (⨂[R] _ : ι, A) →ₐ[R] S :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R ι S).compLinearMap fun i => (f i).toLinearMap)
    (by simp [MultilinearMap.mkPiAlgebra_apply])
    (by
      intro x y
      simp [MultilinearMap.mkPiAlgebra_apply, Finset.prod_mul_distrib])

/-- Evaluation on a pure tensor is the product of its marked images. -/
theorem piTensorProductEvaluation_tprod
    {ι : Type uI} {R : Type uR} {A : Type uA} {S : Type uS}
    [Fintype ι] [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (f : ι → A →ₐ[R] S) (x : ι → A) :
    piTensorProductEvaluation f (PiTensorProduct.tprod R x) = ∏ i, f i (x i) := by
  simp [piTensorProductEvaluation, MultilinearMap.mkPiAlgebra_apply]

/-- Each tensor factor evaluates by its original algebra map. -/
theorem piTensorProductEvaluation_singleAlgHom
    {ι : Type uI} {R : Type uR} {A : Type uA} {S : Type uS}
    [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (f : ι → A →ₐ[R] S) (i : ι) (x : A) :
    piTensorProductEvaluation f (PiTensorProduct.singleAlgHom i x) = f i x := by
  simp [PiTensorProduct.singleAlgHom, piTensorProductEvaluation_tprod,
    Pi.mulSingle_apply, apply_ite]

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

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- A ring-homomorphism property preserved by isomorphism, identity, composition,
and base change passes from an algebra to the existing tensor product of finitely
many copies. In particular this applies to geometric local presentation properties,
without replacing the tensor carrier or requiring a converse smoothness theorem. -/
theorem piTensorProduct_ringHomProperty
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hIso : RingHom.RespectsIso P) (hId : RingHom.ContainsIdentities P)
    (hComp : RingHom.StableUnderComposition P)
    (hBase : RingHom.IsStableUnderBaseChange P)
    (ι : Type u) [Finite ι] (hA : P (algebraMap B A)) :
    P (algebraMap B (⨂[B] _ : ι, A)) := by
  have transport {S T : Type u} [CommRing S] [CommRing T]
      [Algebra B S] [Algebra B T] (e : S ≃ₐ[B] T)
      (hS : P (algebraMap B S)) : P (algebraMap B T) := by
    have he : e.toRingEquiv.toRingHom.comp (algebraMap B S) = algebraMap B T := by
      ext b
      exact e.commutes b
    rw [← he]
    exact hIso.1 _ e.toRingEquiv hS
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
      exact transport (tensorReindex (B := B) (A := A) e) ih
  | h_empty =>
      exact transport (tensorEmpty (B := B) (A := A) PEmpty).symm (hId B)
  | @h_option ι _ ih =>
      have hSingle : P (algebraMap B (⨂[B] _ : PUnit.{u+1}, A)) :=
        transport (tensorSingleton (B := B) (A := A)).symm hA
      have hBinary : P (algebraMap B
          ((⨂[B] _ : ι, A) ⊗[B] (⨂[B] _ : PUnit.{u+1}, A))) := by
        rw [IsScalarTower.algebraMap_eq B (⨂[B] _ : ι, A)
          ((⨂[B] _ : ι, A) ⊗[B] (⨂[B] _ : PUnit.{u+1}, A))]
        exact hComp _ _ ih (hBase B (⨂[B] _ : PUnit.{u+1}, A) (⨂[B] _ : ι, A) _ hSingle)
      exact transport
        (tensorReindex (B := B) (A := A) (Equiv.optionEquivSumPUnit ι).symm)
        (transport (tensorSum (B := B) (A := A) ι PUnit) hBinary)

end

end HodgeConjecture.CollisionFoundations
