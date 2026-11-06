module

public import HodgeConjecture.Boundary.Normalization.NormalClosureTensor
public import HodgeConjecture.Boundary.Normalization.FiniteNormalClosure
public import HodgeConjecture.CommutativeAlgebra.FiniteTensorProduct

@[expose] public section

/-!
# Integral tensor evaluation for a marked normal closure

Every embedding of the intermediate field restricts to its existing
normalization ring. Multiplying these restrictions defines an algebra map
from their finite tensor product into the existing normal-closure
normalization. Its evaluation in the normal-closure field is the previously
constructed field tensor evaluation.

A finite normal étale intermediate affine model makes the source tensor
algebra finite and étale over the base. The integral map and the generic
field map retain their respective scalar rings throughout.
-/

set_option autoImplicit false

namespace HodgeConjecture.CollisionFoundations

noncomputable section

open scoped TensorProduct Classical

universe u

namespace NormalClosureData

variable {B K L N : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [Algebra K L] [Algebra K N]
variable [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]

/-- Tensor evaluation of the canonical restrictions of all field embeddings
to the existing integral-closure rings. -/
def normalizationTensorEvaluation (D : NormalClosureData K L N) :
    (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) →ₐ[B]
      normalizedCoordinateRing B N := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  exact piTensorProductEvaluation
    (fun σ : L →ₐ[K] N => normalizationMap N (σ.restrictScalars B))

/-- The factor indexed by a field embedding is exactly its existing
restriction to integral closures. -/
theorem normalizationTensorEvaluation_singleAlgHom
    (D : NormalClosureData K L N) (σ : L →ₐ[K] N)
    (x : normalizedCoordinateRing B L) :
    D.normalizationTensorEvaluation (PiTensorProduct.singleAlgHom σ x) =
      normalizationMap N (σ.restrictScalars B) x := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  exact piTensorProductEvaluation_singleAlgHom
    (fun σ : L →ₐ[K] N => normalizationMap N (σ.restrictScalars B)) σ x

/-- On each integral tensor factor the map into the ambient field is the
original marked field embedding, with no independently supplied map. -/
theorem normalizationTensorEvaluation_coe_singleAlgHom
    (D : NormalClosureData K L N) (σ : L →ₐ[K] N)
    (x : normalizedCoordinateRing B L) :
    ((D.normalizationTensorEvaluation (PiTensorProduct.singleAlgHom σ x) :
      normalizedCoordinateRing B N) : N) = σ (x : L) := by
  rw [normalizationTensorEvaluation_singleAlgHom]
  rfl

/-- Evaluating an integral pure tensor and then including into the
normal-closure field agrees with the existing generic tensor evaluation. -/
theorem normalizationTensorEvaluation_coe_tprod
    (D : NormalClosureData K L N)
    (x : (L →ₐ[K] N) → normalizedCoordinateRing B L) :
    ((D.normalizationTensorEvaluation (PiTensorProduct.tprod B x) :
      normalizedCoordinateRing B N) : N) =
      D.tensorEvaluation (PiTensorProduct.tprod K (fun σ => (x σ : L))) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  change (algebraMap (normalizedCoordinateRing B N) N)
      (piTensorProductEvaluation
        (fun σ : L →ₐ[K] N => normalizationMap N (σ.restrictScalars B))
        (PiTensorProduct.tprod B x)) =
    piTensorProductEvaluation (fun σ : L →ₐ[K] N => σ)
      (PiTensorProduct.tprod K (fun σ => (x σ : L)))
  simp only [piTensorProductEvaluation_tprod, map_prod]
  rfl

section FiniteNormalAffineModel

variable {A : Type u} [CommRing A]
variable [Algebra B A] [Algebra A L] [IsScalarTower B A L]
variable [IsFractionRing A L] [IsIntegrallyClosed A] [Module.Finite B A]

include A in
omit [Algebra B K] [Algebra B N] [IsScalarTower B K L] [IsScalarTower B K N] in
/-- An actual finite normal intermediate affine algebra makes the source
of integral tensor evaluation finite over the original base. -/
theorem normalizationTensor_finite (D : NormalClosureData K L N) :
    Module.Finite B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : Module.Finite B (normalizedCoordinateRing B L) :=
    normalizedCoordinateRing_finite (A := A)
  exact piTensorProduct_finite (L →ₐ[K] N)

include A in
omit [Algebra B K] [Algebra B N] [IsScalarTower B K L] [IsScalarTower B K N] in
/-- If the actual finite normal intermediate affine algebra is étale, so
is the source of integral tensor evaluation over the original base. -/
theorem normalizationTensor_etale [Algebra.Etale B A]
    (D : NormalClosureData K L N) :
    Algebra.Etale B (⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  letI : Algebra.Etale B (normalizedCoordinateRing B L) :=
    normalizedCoordinateRing_etale (A := A)
  exact piTensorProduct_etale (L →ₐ[K] N)

end FiniteNormalAffineModel

end NormalClosureData

end

end HodgeConjecture.CollisionFoundations
