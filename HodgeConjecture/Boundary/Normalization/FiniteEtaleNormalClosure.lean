module

public import HodgeConjecture.Boundary.Normalization.NormalizationIntegralFactor
public import HodgeConjecture.Boundary.Normalization.FunctionFieldNormalClosure
public import HodgeConjecture.Boundary.Normalization.EtaleTensorSource
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

@[expose] public section

/-!
# The actual finite étale affine normal-closure refinement

The integral selector identifies the existing normal-closure normalization
with an open component of the tensor source. Scheme étaleness is transported
from the actual intermediate cover through finite tensor products and this
open immersion. No converse from algebraic to scheme étaleness is assumed.

On a nonempty affine chart, the same marked function-field extension gives
the existing `NormalizedCover`, its structural map to the actual chart, and
its refinement map to the actual whole inverse image. Normal stalks remain
explicit; there is no Noetherian-base hypothesis or global gluing assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace NormalClosureData

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N] [CommRing A]
variable [Algebra B K] [IsFractionRing B K] [IsIntegrallyClosed B]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [Algebra B A] [Algebra A L] [IsScalarTower B A L]
variable [IsFractionRing A L] [IsIntegrallyClosed A] [Module.Finite B A]
variable [Algebra.Etale B A]

include A in
/-- The actual integral evaluation cuts out an open component of its
existing tensor source, using the complementary-idempotent kernel. -/
theorem normalizationTensorEvaluation_isOpenImmersion
    (D : NormalClosureData K L N) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (D.normalizationTensorEvaluation (B := B)).toRingHom)) := by
  apply (isOpenImmersion_SpecMap_iff_of_surjective _
    (D.normalizationTensorEvaluation_surjective (B := B) (A := A))).mpr
  exact ⟨1 - D.normalizationTensorIdempotent (B := B) (A := A),
    (D.normalizationTensorIdempotent_spec (B := B) (A := A)).1.one_sub,
    (D.normalizationTensorIdempotent_spec (B := B) (A := A)).2.2.2⟩

include A in
/-- Scheme étaleness of the intermediate normalization passes through
the actual finite tensor source and its selected open component. -/
theorem normalizationToBase_isEtale_of_etaleModel
    (D : NormalClosureData K L N)
    (hL : Etale (normalizedModelToBase B L)) :
    Etale (normalizedModelToBase B N) := by
  letI : FiniteDimensional K L := D.finiteIntermediate
  let P := ⨂[B] _ : L →ₐ[K] N, normalizedCoordinateRing B L
  let q := Spec.map (CommRingCat.ofHom
    (D.normalizationTensorEvaluation (B := B)).toRingHom)
  let s := Spec.map (CommRingCat.ofHom (algebraMap B P))
  letI : IsOpenImmersion q :=
    D.normalizationTensorEvaluation_isOpenImmersion (B := B) (A := A)
  letI : Etale s := piTensorProduct_isEtale (L →ₐ[K] N) hL
  have hcomp : q ≫ s = normalizedModelToBase B N := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (D.normalizationTensorEvaluation (B := B)).comp_algebraMap
  rw [← hcomp]
  infer_instance

end NormalClosureData

section ActualAffineChart

open SchemeCycles NormalizationInertia

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [Etale p]
variable (U : X.Opens) [Nonempty U]

local instance : Nonempty (p ⁻¹ᵁ U) := nonempty_preimage_of_isDominant p U
local instance : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

/-- The original generic extension and actual affine inverse image
give finite étale normalization without a Noetherian-base premise. -/
theorem functionFieldNormalClosure_normalization_finite_etale
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    Module.Finite Γ(X, U) (normalizedCoordinateRing Γ(X, U) Nₚ) ∧
      Algebra.Etale Γ(X, U) (normalizedCoordinateRing Γ(X, U) Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsIntegrallyClosed Γ(X, U) := affineSections_isIntegrallyClosed_of_stalks hU hX
  letI : IsIntegrallyClosed Γ(Y, p ⁻¹ᵁ U) :=
    affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hY
  letI : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := finiteAffinePreimage_moduleFinite p U hU
  letI : Algebra.Etale Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := finiteAffinePreimage_etale p U hU
  exact ⟨(functionFieldNormalClosureData p).normalization_finite_of_etaleModel
      (B := Γ(X, U)) (A := Γ(Y, p ⁻¹ᵁ U)),
    (functionFieldNormalClosureData p).normalization_etale_of_etaleModel
      (B := Γ(X, U)) (A := Γ(Y, p ⁻¹ᵁ U))⟩

/-- The same existing normalized-cover package, with its actual visible
inverse image and constructed marked normal closure. -/
def finiteEtaleAffinePreimageNormalizedCover
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    NormalizedCover (B := Γ(X, U)) (K := X.functionField)
      (L := Y.functionField) (N := Nₚ)
      (p ⁻¹ᵁ U).toScheme (finiteAffinePreimageNormalizationIso p U hU hY).hom := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact {
    normalClosure := functionFieldNormalClosureData p
    finiteIntermediateModel := finiteAffinePreimage_normalization_finite p U hU hY
    finiteNormalClosureModel :=
      (functionFieldNormalClosure_normalization_finite_etale p U hU hX hY).1
    visibleOpen := by infer_instance }

/-- The cover retains precisely the original marked generic extension. -/
theorem finiteEtaleAffinePreimageNormalizedCover_normalClosure
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    (finiteEtaleAffinePreimageNormalizedCover p U hU hX hY).normalClosure =
      functionFieldNormalClosureData p := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact rfl

/-- Full visibility supplies boundary separation for this actual cover. -/
theorem conjugateBoundarySeparation_finiteEtaleAffinePreimageNormalizedCover
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    ConjugateBoundarySeparation (finiteEtaleAffinePreimageNormalizedCover p U hU hX hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact conjugateBoundarySeparation_of_surjective _
    (ConcreteCategory.bijective_of_isIso
      (finiteAffinePreimageNormalizationIso p U hU hY).hom.base).surjective

/-- The existing normal-closure structural map is finite and scheme-étale.
Étaleness uses the actual intermediate scheme, not a postulated ring-to-scheme bridge. -/
theorem finiteEtaleAffineNormalClosureToBase_finite_etale
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsFinite (normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ)) ∧
      Etale (normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  constructor
  · apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr
      (functionFieldNormalClosure_normalization_finite_etale p U hU hX hY).1
  · letI : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
    letI : IsIntegrallyClosed Γ(X, U) := affineSections_isIntegrallyClosed_of_stalks hU hX
    letI : IsIntegrallyClosed Γ(Y, p ⁻¹ᵁ U) :=
      affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hY
    letI : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := finiteAffinePreimage_moduleFinite p U hU
    letI : Algebra.Etale Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := finiteAffinePreimage_etale p U hU
    apply (functionFieldNormalClosureData p).normalizationToBase_isEtale_of_etaleModel
      (B := Γ(X, U)) (A := Γ(Y, p ⁻¹ᵁ U))
    let ν := finiteAffinePreimageNormalizationIso p U hU hY
    let μ := normalizedModelToBase Γ(X, U) Y.functionField
    haveI : Etale ((ν.hom ≫ μ) ≫ hU.fromSpec) := by
      rw [Category.assoc, finiteAffinePreimageNormalizationIso_hom_comp_toBase]
      infer_instance
    haveI : Etale (ν.hom ≫ μ) := Etale.of_comp _ hU.fromSpec
    have h : Etale (ν.inv ≫ (ν.hom ≫ μ)) := inferInstance
    simpa only [Iso.inv_hom_id_assoc] using h

/-- The normal-closure normalization maps to the actual affine open,
using its canonical affine presentation. -/
def finiteEtaleAffineNormalClosureToChart
    (hU : IsAffineOpen U) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    normalClosureNormalization (B := Γ(X, U)) (N := Nₚ) ⟶ U.toScheme := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ) ≫ hU.isoSpec.inv

omit [IsFinite p] [Etale p] in
/-- The chart structural map has the original composite to the base scheme. -/
theorem finiteEtaleAffineNormalClosureToChart_comp_inclusion
    (hU : IsAffineOpen U) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    finiteEtaleAffineNormalClosureToChart p U hU ≫ U.ι =
      normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ) ≫ hU.fromSpec := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  simp only [finiteEtaleAffineNormalClosureToChart, Category.assoc, IsAffineOpen.isoSpec_inv_ι]

/-- The structural morphism to the actual chart is finite étale. -/
theorem finiteEtaleAffineNormalClosureToChart_finite_etale
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsFinite (finiteEtaleAffineNormalClosureToChart p U hU) ∧
      Etale (finiteEtaleAffineNormalClosureToChart p U hU) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI := (finiteEtaleAffineNormalClosureToBase_finite_etale p U hU hX hY).1
  letI := (finiteEtaleAffineNormalClosureToBase_finite_etale p U hU hX hY).2
  constructor <;> dsimp [finiteEtaleAffineNormalClosureToChart] <;> infer_instance

/-- The refinement to the actual inverse image uses the original marked
normalization leg followed by the canonical visible isomorphism. -/
def finiteEtaleAffineNormalClosureToPreimage
    (hU : IsAffineOpen U)
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    normalClosureNormalization (B := Γ(X, U)) (N := Nₚ) ⟶ (p ⁻¹ᵁ U).toScheme := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact normalClosureToIntermediateNormalization (B := Γ(X, U)) (functionFieldNormalClosureData p) ≫
    (finiteAffinePreimageNormalizationIso p U hU hY).inv

omit [Etale p] in
/-- The refinement recovers exactly the existing marked normalization leg. -/
theorem finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso
    (hU : IsAffineOpen U)
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫
        (finiteAffinePreimageNormalizationIso p U hU hY).hom =
      normalClosureToIntermediateNormalization (B := Γ(X, U))
        (functionFieldNormalClosureData p) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  simp only [finiteEtaleAffineNormalClosureToPreimage, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

omit [Etale p] in
/-- The refinement is over the original base scheme and its original map. -/
theorem finiteEtaleAffineNormalClosureToPreimage_comp_toBase
    (hU : IsAffineOpen U)
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫ (p ⁻¹ᵁ U).ι ≫ p =
      normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ) ≫ hU.fromSpec := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  rw [← finiteAffinePreimageNormalizationIso_hom_comp_toBase p U hU hY]
  rw [← Category.assoc, finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso,
    ← Category.assoc]
  exact congrArg (fun q => q ≫ hU.fromSpec)
    (normalClosureToIntermediateNormalization_comp_toBase
      (B := Γ(X, U)) (functionFieldNormalClosureData p))

omit [Etale p] in
/-- The marked refinement factors the structural morphism on the actual chart. -/
theorem finiteEtaleAffineNormalClosureToPreimage_comp_restrict
    (hU : IsAffineOpen U)
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫ (p ∣_ U) =
      finiteEtaleAffineNormalClosureToChart p U hU := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι,
    finiteEtaleAffineNormalClosureToPreimage_comp_toBase,
    finiteEtaleAffineNormalClosureToChart_comp_inclusion]

/-- The actual marked refinement to the whole affine inverse image is
itself finite étale. -/
theorem finiteEtaleAffineNormalClosureToPreimage_finite_etale
    (hU : IsAffineOpen U)
    (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    IsFinite (finiteEtaleAffineNormalClosureToPreimage p U hU hY) ∧
      Etale (finiteEtaleAffineNormalClosureToPreimage p U hU hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  constructor
  · let q := normalClosureToIntermediateNormalization (B := Γ(X, U))
      (functionFieldNormalClosureData p)
    haveI : IsFinite q := by
      apply (IsFinite.SpecMap_iff _).mpr
      apply RingHom.Finite.of_comp_finite (f :=
        algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) Y.functionField))
      change ((normalizationMap Nₚ (normalClosureEmbeddingOverBase (B := Γ(X, U))
        (functionFieldNormalClosureData p))).toRingHom.comp
        (algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) Y.functionField))).Finite
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
      exact RingHom.finite_algebraMap.mpr
        (functionFieldNormalClosure_normalization_finite_etale p U hU hX hY).1
    change IsFinite (q ≫ (finiteAffinePreimageNormalizationIso p U hU hY).inv)
    infer_instance
  · haveI : Etale (p ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Etale) inferInstance U
    haveI : Etale (finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫ (p ∣_ U)) := by
      rw [finiteEtaleAffineNormalClosureToPreimage_comp_restrict]
      exact (finiteEtaleAffineNormalClosureToChart_finite_etale p U hU hX hY).2
    exact Etale.of_comp _ (p ∣_ U)

omit [IsFinite p] [Etale p] in
/-- Lying-over makes the structural map onto the actual affine chart. -/
theorem finiteEtaleAffineNormalClosureToChart_surjective
    (hU : IsAffineOpen U) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    Surjective (finiteEtaleAffineNormalClosureToChart p U hU) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let i : Γ(X, U) →+* normalizedCoordinateRing Γ(X, U) Nₚ := algebraMap _ _
  have hi : i.IsIntegral := fun x => integralClosure.isIntegral x
  have hinj : Function.Injective i := by
    intro b c h
    apply X.germToFunctionField_injective U
    apply (algebraMap X.functionField Nₚ).injective
    exact congrArg (fun z : normalizedCoordinateRing Γ(X, U) Nₚ => (z : Nₚ)) h
  haveI : Surjective (normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ)) :=
    ⟨hi.comap_surjective hinj⟩
  unfold finiteEtaleAffineNormalClosureToChart
  infer_instance

omit [Etale p] in
/-- The marked refinement is onto the original whole affine inverse image. -/
theorem finiteEtaleAffineNormalClosureToPreimage_surjective
    (hU : IsAffineOpen U)
    (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
      functionFieldMapOfDominant_sectionScalarTower p U
    letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    Surjective (finiteEtaleAffineNormalClosureToPreimage p U hU hY) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let φ : normalizedCoordinateRing Γ(X, U) Y.functionField →ₐ[Γ(X, U)]
      normalizedCoordinateRing Γ(X, U) Nₚ :=
    normalizationMap Nₚ (normalClosureEmbeddingOverBase (B := Γ(X, U))
      (functionFieldNormalClosureData p))
  have hInt : φ.toRingHom.IsIntegral := by
    apply RingHom.IsIntegral.tower_top
      (algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) Y.functionField))
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact fun x => integralClosure.isIntegral x
  have hinj : Function.Injective φ :=
    normalizationMap_injective Nₚ _
      (normalClosureEmbeddingOverBase (B := Γ(X, U)) (functionFieldNormalClosureData p)).injective
  haveI : Surjective (normalClosureToIntermediateNormalization (B := Γ(X, U))
      (functionFieldNormalClosureData p)) := ⟨hInt.comap_surjective hinj⟩
  unfold finiteEtaleAffineNormalClosureToPreimage
  infer_instance

end ActualAffineChart

end

end HodgeConjecture.CollisionFoundations
