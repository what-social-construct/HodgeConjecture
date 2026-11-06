module

public import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosure
public import HodgeConjecture.Boundary.Normalization.AffineNormalizationRestriction

@[expose] public section

/-!
# Restriction compatibility of the marked affine refinement

The structural map and the refinement to the original inverse image both
commute with affine restriction. The function-field normal closure and its
marking are unchanged. These identities do not require étaleness; the
finite étale conclusions remain those of the existing chart construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory SchemeCycles NormalizationInertia

noncomputable section

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]

local instance finiteEtaleRestrictionPreimageNonemptyU : Nonempty (p ⁻¹ᵁ U) :=
  nonempty_preimage_of_isDominant p U
local instance finiteEtaleRestrictionPreimageNonemptyV : Nonempty (p ⁻¹ᵁ V) :=
  nonempty_preimage_of_isDominant p V

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

/-- The actual chart structural morphisms commute with restriction,
on the same marked normal-closure field. -/
theorem finiteEtaleAffineNormalClosureToChart_restriction
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V Nₚ hVU ≫
        finiteEtaleAffineNormalClosureToChart p U hU =
      finiteEtaleAffineNormalClosureToChart p V hV ≫ X.homOfLE hVU := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField V).hom).toAlgebra
  exact affineNormalizationRestriction_comp_toChart U V Nₚ hVU hU hV

/-- The marked refinement to the actual inverse image commutes with restriction,
not merely its composite with the map to the base. -/
theorem finiteEtaleAffineNormalClosureToPreimage_restriction [IsFinite p]
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hYU : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val))
    (hYV : ∀ y : p ⁻¹ᵁ V, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V Nₚ hVU ≫
        finiteEtaleAffineNormalClosureToPreimage p U hU hYU =
      finiteEtaleAffineNormalClosureToPreimage p V hV hYV ≫
        Y.homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ h => hVU h) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, V) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ V)).hom.comp (p.app V).hom).toAlgebra
  letI : Algebra Γ(X, U) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) Nₚ :=
    ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p U
  letI : IsScalarTower Γ(X, V) X.functionField Y.functionField :=
    functionFieldMapOfDominant_sectionScalarTower p V
  letI : IsScalarTower Γ(X, U) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, V) X.functionField Nₚ :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, U) Γ(X, V) Y.functionField :=
    finiteAffinePreimageRestriction_functionFieldScalarTower U V p hVU
  letI : IsScalarTower Γ(X, U) Γ(X, V) Nₚ :=
    sectionRestriction_ambientScalarTower U V Nₚ hVU
  apply (cancel_mono (finiteAffinePreimageNormalizationIso p U hU hYU).hom).mp
  rw [Category.assoc, finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso]
  rw [Category.assoc, ← finiteAffinePreimageNormalizationIso_restriction U V p hVU hU hV hYU hYV]
  rw [← Category.assoc, finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso]
  exact normalizationBaseChange_naturality
    (B := Γ(X, U)) (C := Γ(X, V))
    (normalClosureEmbeddingOverBase (B := Γ(X, V)) (functionFieldNormalClosureData p))

end

end HodgeConjecture.CollisionFoundations
