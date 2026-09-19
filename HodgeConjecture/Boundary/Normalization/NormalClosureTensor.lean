import HodgeConjecture.Boundary.Normalization.NormalClosure
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.PiTensorProduct

/-!
# Tensor evaluation onto a marked normal closure

The finite tensor product indexed by all embeddings of the intermediate
field evaluates onto the existing marked normal closure.  The evaluation
is an algebra homomorphism, and its surjectivity follows from normal-closure
generation rather than being supplied as an additional hypothesis.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct Classical

universe uI uR uA uS uK uL uN

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

namespace NormalClosureData

variable {K : Type uK} {L : Type uL} {N : Type uN}
variable [Field K] [Field L] [Field N]
variable [Algebra K L] [Algebra K N]

/-- All embeddings of the intermediate field determine an algebra map from
their finite tensor product into the existing normal-closure field. -/
def tensorEvaluation (D : NormalClosureData K L N) :
    (⨂[K] _ : L →ₐ[K] N, L) →ₐ[K] N := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  exact piTensorProductEvaluation (fun σ : L →ₐ[K] N => σ)

/-- The factor marked by an embedding evaluates by that embedding. -/
theorem tensorEvaluation_singleAlgHom
    (D : NormalClosureData K L N) (σ : L →ₐ[K] N) (x : L) :
    D.tensorEvaluation (PiTensorProduct.singleAlgHom σ x) = σ x := by
  classical
  letI : FiniteDimensional K L := D.finiteIntermediate
  exact piTensorProductEvaluation_singleAlgHom (fun σ : L →ₐ[K] N => σ) σ x

/-- The tensor evaluation is onto because every conjugate field lies in its
algebraic range and these fields generate the given normal closure. -/
theorem tensorEvaluation_surjective (D : NormalClosureData K L N) :
    Function.Surjective D.tensorEvaluation := by
  classical
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  letI : IsNormalClosure K L N := D.normalClosure
  let E : IntermediateField K N :=
    subalgebraEquivIntermediateField D.tensorEvaluation.range
  have hNormalClosure : IntermediateField.normalClosure K L N = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff
      (F := K) (K := L) (L := N)).mp inferInstance |>.2
  have hle : IntermediateField.normalClosure K L N ≤ E := by
    rw [normalClosure_le_iff]
    intro σ y hy
    obtain ⟨x, rfl⟩ := hy
    change σ x ∈ D.tensorEvaluation.range
    exact ⟨PiTensorProduct.singleAlgHom σ x, D.tensorEvaluation_singleAlgHom σ x⟩
  have hE : E = ⊤ := top_unique (hNormalClosure ▸ hle)
  intro y
  have hy : y ∈ E := by rw [hE]; trivial
  exact hy

/-- The evaluation kernel selects a field quotient of the tensor algebra. -/
theorem tensorEvaluation_ker_isMaximal (D : NormalClosureData K L N) :
    (RingHom.ker D.tensorEvaluation.toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective D.tensorEvaluation.toRingHom
    D.tensorEvaluation_surjective

/-- The quotient selected by the evaluation kernel is the existing marked
normal-closure field, with its original base-field algebra structure. -/
def tensorEvaluationQuotientEquiv (D : NormalClosureData K L N) :
    ((⨂[K] _ : L →ₐ[K] N, L) ⧸ RingHom.ker D.tensorEvaluation.toRingHom) ≃ₐ[K] N :=
  Ideal.quotientKerAlgEquivOfSurjective D.tensorEvaluation_surjective

/-- The quotient comparison commutes with the original tensor evaluation. -/
theorem tensorEvaluationQuotientEquiv_mk
    (D : NormalClosureData K L N) (x : ⨂[K] _ : L →ₐ[K] N, L) :
    D.tensorEvaluationQuotientEquiv
        (Ideal.Quotient.mk (RingHom.ker D.tensorEvaluation.toRingHom) x) =
      D.tensorEvaluation x := rfl

end NormalClosureData

end

end HodgeConjecture.CollisionFoundations
