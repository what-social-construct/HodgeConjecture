import HodgeConjecture.Boundary.Normalization.FiniteAffineCover
import HodgeConjecture.Boundary.Normalization.AffineEtaleAlgebra
import HodgeConjecture.Boundary.Normalization.AffineNormality
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Whole affine inverse images as normalization models

For a finite morphism `p : Y ⟶ X` and an affine open `U` in `X`, use the
actual section rings on `U` and its whole inverse image. Finiteness comes
from `p`; étaleness, when given, comes from its scheme-theoretic hypothesis.
For integral `Y`, the existing function field is the fraction field of the
nonempty affine inverse image. Explicit normality of its stalks then gives
the canonical normalization isomorphism over `X`.

The scalar structures below are local and are induced by the existing
section map and generic germ. No replacement ring, field or cover package
is introduced. Normal stalks are an explicit geometric hypothesis, not
inferred from smoothness or étaleness here.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens)

set_option quotPrecheck false in
local notation "Bᵤ" => Γ(X, U)
set_option quotPrecheck false in
local notation "Aᵤ" => Γ(Y, p ⁻¹ᵁ U)

-- These are the actual pullback of sections and its composite with the generic germ.
local instance : Algebra Bᵤ Aᵤ := (p.app U).hom.toAlgebra

/-- A finite morphism supplies the finite algebra of its whole affine inverse image. -/
theorem finiteAffinePreimage_moduleFinite [IsFinite p] (hU : IsAffineOpen U) :
    Module.Finite Bᵤ Aᵤ :=
  IsFinite.finite_app U hU

/-- Scheme étaleness gives étaleness of the finite affine inverse-image algebra. -/
theorem finiteAffinePreimage_etale [IsFinite p] [IsEtale p] (hU : IsAffineOpen U) :
    Algebra.Etale Bᵤ Aᵤ := by
  have h := affine_appLE_etale p ⟨U, hU⟩ ⟨p ⁻¹ᵁ U, hU.preimage p⟩ le_rfl
  simpa only [Scheme.Hom.appLE_eq_app] using h

variable [IsIntegral Y] [Nonempty (p ⁻¹ᵁ U)]

variable [IsFinite p]

/-- The whole affine preimage is canonically the normalization in the actual
function field, when its stalks are normal. -/
def finiteAffinePreimageNormalizationIso (hU : IsAffineOpen U)
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    (p ⁻¹ᵁ U).toScheme ≅ normalizedAffineModel Bᵤ Y.functionField := by
  letI : Algebra Bᵤ Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : IsScalarTower Bᵤ Aᵤ Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite Bᵤ Aᵤ := finiteAffinePreimage_moduleFinite p U hU
  letI : IsFractionRing Aᵤ Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsIntegrallyClosed Aᵤ :=
    NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hNormal
  exact (hU.preimage p).isoSpec ≪≫
    intermediateNormalizationIso (B := Bᵤ) (A := Aᵤ) (E := Y.functionField)

/-- The new geometric isomorphism uses the existing canonical normalization
map after the canonical affine presentation of the inverse image. -/
theorem finiteAffinePreimageNormalizationIso_hom (hU : IsAffineOpen U)
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : IsScalarTower Bᵤ Aᵤ Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing Aᵤ Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
    letI : IsIntegrallyClosed Aᵤ :=
      NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hNormal
    (finiteAffinePreimageNormalizationIso p U hU hNormal).hom =
      (hU.preimage p).isoSpec.hom ≫
        intermediateToNormalization (B := Bᵤ) (A := Aᵤ) (E := Y.functionField) := rfl

/-- The normalization identification lies over the original geometric base,
not just over an abstractly isomorphic coordinate ring. -/
theorem finiteAffinePreimageNormalizationIso_hom_comp_toBase (hU : IsAffineOpen U)
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    (finiteAffinePreimageNormalizationIso p U hU hNormal).hom ≫
        normalizedModelToBase Bᵤ Y.functionField ≫ hU.fromSpec =
      (p ⁻¹ᵁ U).ι ≫ p := by
  letI : Algebra Bᵤ Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : IsScalarTower Bᵤ Aᵤ Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Aᵤ Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsIntegrallyClosed Aᵤ :=
    NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hNormal
  rw [finiteAffinePreimageNormalizationIso_hom]
  rw [Category.assoc, ← Category.assoc (intermediateToNormalization (B := Bᵤ)
    (A := Aᵤ) (E := Y.functionField))]
  rw [intermediateToNormalization_comp_toBase (B := Bᵤ) (A := Aᵤ) (E := Y.functionField)]
  change (hU.preimage p).isoSpec.hom ≫ Spec.map (p.app U) ≫ hU.fromSpec = _
  rw [p.app_eq_appLE, IsAffineOpen.Spec_map_appLE_fromSpec p hU (hU.preimage p) le_rfl]
  rw [← Category.assoc, IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]

/-- Finiteness of the normalization is derived from the actual finite morphism. -/
theorem finiteAffinePreimage_normalization_finite (hU : IsAffineOpen U)
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    Module.Finite Bᵤ (normalizedCoordinateRing Bᵤ Y.functionField) := by
  letI : Algebra Bᵤ Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : IsScalarTower Bᵤ Aᵤ Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite Bᵤ Aᵤ := finiteAffinePreimage_moduleFinite p U hU
  letI : IsFractionRing Aᵤ Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsIntegrallyClosed Aᵤ :=
    NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hNormal
  exact normalizedCoordinateRing_finite (A := Aᵤ)

/-- Étaleness of the normalization is derived from the actual étale morphism. -/
theorem finiteAffinePreimage_normalization_etale [IsEtale p] (hU : IsAffineOpen U)
    (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    Algebra.Etale Bᵤ (normalizedCoordinateRing Bᵤ Y.functionField) := by
  letI : Algebra Bᵤ Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : IsScalarTower Bᵤ Aᵤ Y.functionField := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite Bᵤ Aᵤ := finiteAffinePreimage_moduleFinite p U hU
  letI : Algebra.Etale Bᵤ Aᵤ := finiteAffinePreimage_etale p U hU
  letI : IsFractionRing Aᵤ Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsIntegrallyClosed Aᵤ :=
    NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hNormal
  exact normalizedCoordinateRing_etale (A := Aᵤ)

end

end HodgeConjecture.CollisionFoundations
