import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Finite normalization in the constructed normal closure

The integral closure of a normal Noetherian affine base in a finite separable
extension is finite. Applying this to the marked normal closure constructs
the normal-closure model required by `NormalizedCover`, without supplying a
second finite normal affine algebra. The intermediate visible model remains
the existing canonical normalization map of the actual finite normal algebra.

For an actual finite dominant, formally unramified morphism of integral
schemes, the same theorem gives finiteness over each nonempty normal
Noetherian affine chart. The field and its marking are exactly those of
`functionFieldNormalClosureData`; the scalar map is induced by the base's
generic germ. No new field, normalization carrier or cover package is used.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace CollisionFoundations

/-- A finite separable extension of the fraction field of a normal
Noetherian domain has finite integral closure. -/
theorem normalizedCoordinateRing_finite_of_isSeparable
    {B K E : Type u} [CommRing B] [Field K] [Field E]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K E] [Algebra B E] [IsScalarTower B K E]
    [IsIntegrallyClosed B] [IsNoetherianRing B]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Module.Finite B (normalizedCoordinateRing B E) := by
  letI : IsDomain B := (IsFractionRing.injective B K).isDomain
  exact IsIntegralClosure.finite B K E (integralClosure B E)

end CollisionFoundations

namespace NormalizationInertia

/-- The existing normal-closure datum supplies the finite separable
extension needed to construct its finite normalization over the base. -/
theorem normalClosureNormalizationRing_finite
    {B K L N : Type u} [CommRing B] [Field K] [Field L] [Field N]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra K N] [Algebra B N] [IsScalarTower B K N]
    [IsIntegrallyClosed B] [IsNoetherianRing B] [Algebra.IsSeparable K L]
    (D : CollisionFoundations.NormalClosureData K L N) :
    Module.Finite B (NormalClosureNormalizationRing (B := B) (N := N)) := by
  letI : FiniteDimensional K N := D.finiteNormal
  letI : Algebra.IsSeparable K N := D.isSeparable
  exact CollisionFoundations.normalizedCoordinateRing_finite_of_isSeparable (K := K)

section FiniteNormalAffineModel

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N]
variable [Algebra B K] [IsFractionRing B K]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [CommRing A] [Algebra B A] [Algebra A L]
variable [IsScalarTower B A L] [IsFractionRing A L] [IsIntegrallyClosed A]
variable [Module.Finite B A]

/-- One finite normal intermediate affine model constructs the existing
normalized cover over a normal Noetherian base. Finiteness of the
normal-closure model is proved, not supplied through a second algebra. -/
def normalizedCoverOfFiniteNormalAffineModel
    [IsIntegrallyClosed B] [IsNoetherianRing B] [Algebra.IsSeparable K L]
    (D : CollisionFoundations.NormalClosureData K L N) :
    NormalizedCover (B := B) (K := K) (L := L) (N := N)
      (Spec (.of A))
      (CollisionFoundations.intermediateToNormalization
        (B := B) (A := A) (E := L)) where
  normalClosure := D
  finiteIntermediateModel :=
    CollisionFoundations.normalizedCoordinateRing_finite (A := A)
  finiteNormalClosureModel := normalClosureNormalizationRing_finite D
  visibleOpen := by
    letI := CollisionFoundations.intermediateToNormalization_isIso
      (B := B) (A := A) (E := L)
    infer_instance

/-- The one-model construction is fully visible, so the existing
conjugate-boundary separation theorem applies directly. -/
theorem conjugateBoundarySeparation_normalizedCoverOfFiniteNormalAffineModel
    [IsIntegrallyClosed B] [IsNoetherianRing B] [Algebra.IsSeparable K L]
    (D : CollisionFoundations.NormalClosureData K L N) :
    ConjugateBoundarySeparation
      (normalizedCoverOfFiniteNormalAffineModel (B := B) (A := A) D) :=
  conjugateBoundarySeparation_of_surjective _
    (CollisionFoundations.intermediateToNormalization_base_surjective
      (B := B) (A := A) (E := L))

end FiniteNormalAffineModel

end NormalizationInertia

namespace CollisionFoundations

/-- The normal closure of the actual generic extension has finite
normalization over every nonempty normal Noetherian affine base chart. -/
theorem functionFieldNormalClosure_normalization_finite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [IsDominant p] [IsFinite p] [FormallyUnramified p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] [IsNoetherianRing Γ(X, U)] :
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    Module.Finite Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) := by
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField N :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Algebra.IsSeparable X.functionField Y.functionField :=
    functionFieldMapOfDominant_isSeparable p
  exact NormalizationInertia.normalClosureNormalizationRing_finite
    (functionFieldNormalClosureData p)

/-- The actual whole affine preimage supplies a fully visible normalized
cover with its constructed marked normal closure. Only its local-ring
normality and the normal Noetherian base chart remain explicit. -/
def finiteAffinePreimageNormalizedCover
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [IsDominant p] [IsFinite p] [FormallyUnramified p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] [IsNoetherianRing Γ(X, U)]
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI := SchemeCycles.nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    NormalizationInertia.NormalizedCover (B := Γ(X, U))
      (K := X.functionField) (L := Y.functionField) (N := N)
      (p ⁻¹ᵁ U).toScheme (finiteAffinePreimageNormalizationIso p U hU hNormal).hom := by
  letI := SchemeCycles.nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  exact {
    normalClosure := functionFieldNormalClosureData p
    finiteIntermediateModel := finiteAffinePreimage_normalization_finite p U hU hNormal
    finiteNormalClosureModel := functionFieldNormalClosure_normalization_finite p U hU
    visibleOpen := by infer_instance }

/-- Full visibility gives boundary separation for the normalized cover
constructed from the actual affine inverse image and generic extension. -/
theorem conjugateBoundarySeparation_finiteAffinePreimageNormalizedCover
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) [IsDominant p] [IsFinite p] [FormallyUnramified p]
    (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U)
    [IsIntegrallyClosed Γ(X, U)] [IsNoetherianRing Γ(X, U)]
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI := SchemeCycles.nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra X.functionField Y.functionField :=
      (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
    let N := IntermediateField.normalClosure X.functionField Y.functionField
      (AlgebraicClosure Y.functionField)
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField N :=
      IsScalarTower.of_algebraMap_eq' rfl
    NormalizationInertia.ConjugateBoundarySeparation
      (finiteAffinePreimageNormalizedCover p U hU hNormal) := by
  letI := SchemeCycles.nonempty_preimage_of_isDominant p U
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra X.functionField Y.functionField :=
    (SchemeCycles.functionFieldMapOfDominant p).hom.toAlgebra
  let N := IntermediateField.normalClosure X.functionField Y.functionField
    (AlgebraicClosure Y.functionField)
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField N :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact NormalizationInertia.conjugateBoundarySeparation_of_surjective _
    (ConcreteCategory.bijective_of_isIso
      (finiteAffinePreimageNormalizationIso p U hU hNormal).hom.base).surjective

end CollisionFoundations

end

end HodgeConjecture
