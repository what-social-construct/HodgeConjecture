import HodgeConjecture.Boundary.Normalization.NormalizationTensor
import HodgeConjecture.CommutativeAlgebra.PiTensorBaseChange
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change of the normalization tensor evaluation

Localizing the integral closure in an algebraic field extension at the
nonzero elements of the base gives that field. Its canonical algebra
equivalence identifies the base change of the existing integral tensor
algebra with the existing field tensor algebra. Under these identifications,
the two evaluation homomorphisms commute as algebra homomorphisms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct Classical nonZeroDivisors

universe u

section OneFactor

variable (B K L : Type u) [CommRing B] [Field K] [Field L]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra B L] [IsScalarTower B K L]
variable [Algebra.IsAlgebraic K L]

/-- The canonical base change of the integral closure in an algebraic
extension of the fraction field is that same field extension. -/
def normalizedCoordinateRingBaseChangeEquiv :
    (K ⊗[B] normalizedCoordinateRing B L) ≃ₐ[K] L := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (normalizedCoordinateRing B L) B⁰) L :=
    IsIntegralClosure.isLocalization B K L (normalizedCoordinateRing B L)
  letI : Algebra.IsPushout B K (normalizedCoordinateRing B L) L :=
    (Algebra.isPushout_of_isLocalization B⁰ K
      (normalizedCoordinateRing B L) L).symm
  exact Algebra.IsPushout.equiv B K (normalizedCoordinateRing B L) L

/-- The base-change equivalence uses the original scalar map and the
inclusion of the integral closure into its ambient field. -/
theorem normalizedCoordinateRingBaseChangeEquiv_tmul
    (k : K) (x : normalizedCoordinateRing B L) :
    normalizedCoordinateRingBaseChangeEquiv B K L (k ⊗ₜ[B] x) =
      algebraMap K L k * (x : L) := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  letI : IsLocalization
      (Algebra.algebraMapSubmonoid (normalizedCoordinateRing B L) B⁰) L :=
    IsIntegralClosure.isLocalization B K L (normalizedCoordinateRing B L)
  letI : Algebra.IsPushout B K (normalizedCoordinateRing B L) L :=
    (Algebra.isPushout_of_isLocalization B⁰ K
      (normalizedCoordinateRing B L) L).symm
  exact Algebra.IsPushout.equiv_tmul B K (normalizedCoordinateRing B L) L k x

end OneFactor

namespace NormalClosureData

variable {B K L N : Type u} [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B L]
variable [IsScalarTower B K L]

/-- The original integral tensor algebra has the original field tensor
algebra as its canonical base change. -/
def normalizationTensorBaseChangeEquiv (D : NormalClosureData K L N) :
    (K ⊗[B] (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L)) ≃ₐ[K]
      (⨂[K] _ : L →ₐ[K] N, L) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  exact piTensorProductBaseChangeEquiv.trans
    (piTensorProductCongr fun _ : L →ₐ[K] N =>
      normalizedCoordinateRingBaseChangeEquiv B K L)

/-- The canonical comparison preserves the factor marked by each embedding. -/
theorem normalizationTensorBaseChangeEquiv_tmul_singleAlgHom
    (D : NormalClosureData K L N) (k : K) (σ : L →ₐ[K] N)
    (x : normalizedCoordinateRing B L) :
    D.normalizationTensorBaseChangeEquiv (B := B)
        (k ⊗ₜ[B] PiTensorProduct.singleAlgHom σ x) =
      k • (PiTensorProduct.singleAlgHom σ (x : L) : ⨂[K] _ : L →ₐ[K] N, L) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  simp only [normalizationTensorBaseChangeEquiv, AlgEquiv.trans_apply,
    piTensorProductBaseChangeEquiv_tmul_singleAlgHom, Algebra.smul_def, map_mul,
    AlgEquiv.commutes,
    piTensorProductCongr_singleAlgHom, normalizedCoordinateRingBaseChangeEquiv_tmul,
    map_one, one_mul]

/-- On pure tensors the comparison uses the inclusions of the original
integral closures into the intermediate field. -/
theorem normalizationTensorBaseChangeEquiv_tmul_tprod
    (D : NormalClosureData K L N) (k : K)
    (x : (L →ₐ[K] N) → normalizedCoordinateRing B L) :
    D.normalizationTensorBaseChangeEquiv (B := B) (k ⊗ₜ[B] PiTensorProduct.tprod B x) =
      k • PiTensorProduct.tprod K (fun σ => (x σ : L)) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  change (piTensorProductCongr fun _ : L →ₐ[K] N =>
      normalizedCoordinateRingBaseChangeEquiv B K L)
      (piTensorProductBaseChangeEquiv (ι := L →ₐ[K] N) (B := B)
        (A := normalizedCoordinateRing B L) (K := K)
        (k ⊗ₜ[B] PiTensorProduct.tprod B x)) = _
  rw [piTensorProductBaseChangeEquiv_tmul_tprod]
  rw [map_smul (piTensorProductCongr fun _ : L →ₐ[K] N =>
    normalizedCoordinateRingBaseChangeEquiv B K L) k]
  simp only [piTensorProductCongr_tprod, normalizedCoordinateRingBaseChangeEquiv_tmul,
    map_one, one_mul]

variable [Algebra B N] [IsScalarTower B K N]

/-- Base change identifies the entire integral evaluation homomorphism
with the field evaluation homomorphism, not only their pure-tensor values. -/
theorem normalizationTensorEvaluation_baseChange (D : NormalClosureData K L N) :
    letI : FiniteDimensional K N := D.finiteNormal
    D.tensorEvaluation.comp (D.normalizationTensorBaseChangeEquiv (B := B)).toAlgHom =
      (normalizedCoordinateRingBaseChangeEquiv B K N).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id K K)
          (D.normalizationTensorEvaluation (B := B))) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : FiniteDimensional K N := D.finiteNormal
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro k
    change D.tensorEvaluation (D.normalizationTensorBaseChangeEquiv (B := B)
        (algebraMap K (K ⊗[B] (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L)) k)) =
      normalizedCoordinateRingBaseChangeEquiv B K N
        ((Algebra.TensorProduct.map (AlgHom.id K K)
          (D.normalizationTensorEvaluation (B := B))) (algebraMap K _ k))
    simp only [AlgHom.commutes, AlgEquiv.commutes]
  · apply PiTensorProduct.algHom_ext
    intro σ
    apply AlgHom.ext
    intro x
    change D.tensorEvaluation (D.normalizationTensorBaseChangeEquiv (B := B)
        ((1 : K) ⊗ₜ[B] PiTensorProduct.singleAlgHom σ x)) =
      normalizedCoordinateRingBaseChangeEquiv B K N
        ((Algebra.TensorProduct.map (AlgHom.id K K)
          (D.normalizationTensorEvaluation (B := B)))
          ((1 : K) ⊗ₜ[B] PiTensorProduct.singleAlgHom σ x))
    rw [normalizationTensorBaseChangeEquiv_tmul_singleAlgHom,
      one_smul, tensorEvaluation_singleAlgHom, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, normalizedCoordinateRingBaseChangeEquiv_tmul, map_one, one_mul,
      normalizationTensorEvaluation_coe_singleAlgHom]

end NormalClosureData

end

end HodgeConjecture.CollisionFoundations
