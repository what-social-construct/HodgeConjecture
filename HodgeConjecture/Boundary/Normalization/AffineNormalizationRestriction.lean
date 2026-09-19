import HodgeConjecture.Boundary.Normalization.NormalizationLocalization
import HodgeConjecture.Boundary.Normalization.FiniteAffineChart
import HodgeConjecture.Boundary.Normalization.FiniteFunctionField
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Restricting affine normalization models

Restriction of sections on nested nonempty opens preserves their maps into
the existing function field and any fixed extension of it. The resulting
normalization restriction maps are defined by the same ambient elements;
their structural squares commute over the actual open subschemes.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace HodgeConjecture.CollisionFoundations

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]

/-- Restriction of sections retains the original germ into the function field. -/
theorem sectionRestriction_functionFieldScalarTower (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) X.functionField := by
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg (fun f => f.hom)
    (X.presheaf.germ_res (homOfLE hVU) (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
        (by simpa using (inferInstance : Nonempty V))))).symm

variable (N : Type u) [Field N] [Algebra X.functionField N]

/-- The fixed extension uses the same germ-derived scalar maps on both opens. -/
theorem sectionRestriction_ambientScalarTower (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) N := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, V) X.functionField :=
    sectionRestriction_functionFieldScalarTower U V hVU
  apply IsScalarTower.of_algebraMap_eq
  intro b
  change algebraMap X.functionField N ((X.germToFunctionField U).hom b) =
    algebraMap X.functionField N
      ((X.germToFunctionField V).hom ((X.presheaf.map (homOfLE hVU).op).hom b))
  exact congrArg (algebraMap X.functionField N)
    (IsScalarTower.algebraMap_apply Γ(X, U) Γ(X, V) X.functionField b)

/-- The restriction morphism uses the original normalization rings in the
same fixed ambient extension, with no choice of a replacement field. -/
def affineNormalizationRestriction (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    normalizedAffineModel Γ(X, V) N ⟶ normalizedAffineModel Γ(X, U) N := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, V) N :=
    sectionRestriction_ambientScalarTower U V N hVU
  exact Spec.map (CommRingCat.ofHom
    (normalizationBaseChangeMap (B := Γ(X, U)) (C := Γ(X, V)) (E := N)).toRingHom)

/-- Restriction commutes with the original affine structural maps. -/
theorem affineNormalizationRestriction_comp_toBase (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V N hVU ≫ normalizedModelToBase Γ(X, U) N =
      normalizedModelToBase Γ(X, V) N ≫
        Spec.map (X.presheaf.map (homOfLE hVU).op) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, V) N :=
    sectionRestriction_ambientScalarTower U V N hVU
  unfold affineNormalizationRestriction normalizedModelToBase
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext b
  change algebraMap Γ(X, U) N b =
    algebraMap Γ(X, V) N ((X.presheaf.map (homOfLE hVU).op).hom b)
  exact IsScalarTower.algebraMap_apply Γ(X, U) Γ(X, V) N b

/-- The affine restriction square also commutes over the actual opens in X. -/
theorem affineNormalizationRestriction_comp_toChart (hVU : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V N hVU ≫
        normalizedModelToBase Γ(X, U) N ≫ hU.isoSpec.inv =
      normalizedModelToBase Γ(X, V) N ≫ hV.isoSpec.inv ≫ X.homOfLE hVU := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  rw [← Category.assoc, affineNormalizationRestriction_comp_toBase,
    Category.assoc, IsAffineOpen.map_fromSpec]


/-- The same normalization ring on a principal subchart is the localization
of the original normalization ring at the pulled-back section. -/
theorem affineNormalizationRestriction_basicOpen_isLocalization
    (hU : IsAffineOpen U) (f : Γ(X, U)) [Nonempty (X.basicOpen f)] :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, X.basicOpen f) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) N :=
      sectionRestriction_ambientScalarTower U (X.basicOpen f) N (X.basicOpen_le f)
    letI : Algebra (normalizedCoordinateRing Γ(X, U) N)
        (normalizedCoordinateRing Γ(X, X.basicOpen f) N) :=
      (normalizationBaseChangeMap (B := Γ(X, U))
        (C := Γ(X, X.basicOpen f)) (E := N)).toAlgebra
    IsLocalization.Away (algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) f)
      (normalizedCoordinateRing Γ(X, X.basicOpen f) N) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, X.basicOpen f) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) N :=
    sectionRestriction_ambientScalarTower U (X.basicOpen f) N (X.basicOpen_le f)
  letI : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  letI : Algebra (normalizedCoordinateRing Γ(X, U) N)
      (normalizedCoordinateRing Γ(X, X.basicOpen f) N) :=
    (normalizationBaseChangeMap (B := Γ(X, U))
      (C := Γ(X, X.basicOpen f)) (E := N)).toAlgebra
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
    (normalizedCoordinateRing_isLocalization (B := Γ(X, U))
      (C := Γ(X, X.basicOpen f)) (E := N) (Submonoid.powers f))

/-- Restriction to a principal affine subchart is an actual open immersion. -/
theorem affineNormalizationRestriction_basicOpen_isOpenImmersion
    (hU : IsAffineOpen U) (f : Γ(X, U)) [Nonempty (X.basicOpen f)] :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, X.basicOpen f) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
    IsOpenImmersion
      (affineNormalizationRestriction U (X.basicOpen f) N (X.basicOpen_le f)) := by
  letI : Algebra Γ(X, U) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, X.basicOpen f) N :=
    ((algebraMap X.functionField N).comp (X.germToFunctionField (X.basicOpen f)).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) N :=
    sectionRestriction_ambientScalarTower U (X.basicOpen f) N (X.basicOpen_le f)
  letI : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  letI : Algebra (normalizedCoordinateRing Γ(X, U) N)
      (normalizedCoordinateRing Γ(X, X.basicOpen f) N) :=
    (normalizationBaseChangeMap (B := Γ(X, U))
      (C := Γ(X, X.basicOpen f)) (E := N)).toAlgebra
  letI : IsLocalization.Away
      (algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) f)
      (normalizedCoordinateRing Γ(X, X.basicOpen f) N) :=
    affineNormalizationRestriction_basicOpen_isLocalization U N hU f
  exact IsOpenImmersion.of_isLocalization
    (algebraMap Γ(X, U) (normalizedCoordinateRing Γ(X, U) N) f)


section Preimage

open SchemeCycles

variable {Y : Scheme.{u}} [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p]

local instance affineRestrictionPreimageNonemptyU : Nonempty (p ⁻¹ᵁ U) :=
  nonempty_preimage_of_isDominant p U
local instance affineRestrictionPreimageNonemptyV : Nonempty (p ⁻¹ᵁ V) :=
  nonempty_preimage_of_isDominant p V

/-- Restriction also preserves the original pullback-derived algebra on the
upstairs function field used by the whole-preimage normalization isomorphism. -/
theorem finiteAffinePreimageRestriction_functionFieldScalarTower (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, V) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ V)).hom.comp (p.app V).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) Y.functionField := by
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, V) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ V)).hom.comp (p.app V).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  change (p.app U ≫ Y.germToFunctionField (p ⁻¹ᵁ U)).hom =
    (X.presheaf.map (homOfLE hVU).op ≫
      p.app V ≫ Y.germToFunctionField (p ⁻¹ᵁ V)).hom
  rw [← functionFieldMapOfDominant_germ p U,
    ← functionFieldMapOfDominant_germ p V, ← Category.assoc]
  congr 1
  simp only [Scheme.germToFunctionField, X.presheaf.germ_res]

variable [IsFinite p]

/-- The actual whole-preimage normalization isomorphisms commute with
restriction, using their original section rings and generic germs. -/
theorem finiteAffinePreimageNormalizationIso_restriction
    (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hYU : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val))
    (hYV : ∀ y : p ⁻¹ᵁ V, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, V) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ V)).hom.comp (p.app V).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(X, V) Y.functionField :=
      finiteAffinePreimageRestriction_functionFieldScalarTower U V p hVU
    (finiteAffinePreimageNormalizationIso p V hV hYV).hom ≫
        Spec.map (CommRingCat.ofHom (normalizationBaseChangeMap
          (B := Γ(X, U)) (C := Γ(X, V)) (E := Y.functionField)).toRingHom) =
      Y.homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ h => hVU h) ≫
        (finiteAffinePreimageNormalizationIso p U hU hYU).hom := by
  letI : Algebra Γ(X, U) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
  letI : Algebra Γ(X, V) Y.functionField :=
    ((Y.germToFunctionField (p ⁻¹ᵁ V)).hom.comp (p.app V).hom).toAlgebra
  letI : Algebra Γ(X, U) Γ(X, V) :=
    (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(X, V) Y.functionField :=
    finiteAffinePreimageRestriction_functionFieldScalarTower U V p hVU
  letI : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  letI : Algebra Γ(X, V) Γ(Y, p ⁻¹ᵁ V) := (p.app V).hom.toAlgebra
  letI : IsScalarTower Γ(X, U) Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower Γ(X, V) Γ(Y, p ⁻¹ᵁ V) Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
  letI : IsFractionRing Γ(Y, p ⁻¹ᵁ V) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y _ (hV.preimage p)
  letI : IsIntegrallyClosed Γ(Y, p ⁻¹ᵁ U) :=
    NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hYU
  letI : IsIntegrallyClosed Γ(Y, p ⁻¹ᵁ V) :=
    NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks (hV.preimage p) hYV
  let hpre : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U := fun _ h => hVU h
  let ψU := normalizationToIntermediate (B := Γ(X, U))
    (A := Γ(Y, p ⁻¹ᵁ U)) (E := Y.functionField)
  let ψV := normalizationToIntermediate (B := Γ(X, V))
    (A := Γ(Y, p ⁻¹ᵁ V)) (E := Y.functionField)
  let ρ := normalizationBaseChangeMap
    (B := Γ(X, U)) (C := Γ(X, V)) (E := Y.functionField)
  have hring : CommRingCat.ofHom ρ.toRingHom ≫ CommRingCat.ofHom ψV.toRingHom =
      CommRingCat.ofHom ψU.toRingHom ≫ Y.presheaf.map (homOfLE hpre).op := by
    apply CommRingCat.hom_ext
    ext x
    apply Y.germToFunctionField_injective (p ⁻¹ᵁ V)
    change algebraMap Γ(Y, p ⁻¹ᵁ V) Y.functionField (ψV (ρ x)) =
      (Y.germToFunctionField (p ⁻¹ᵁ V))
        ((Y.presheaf.map (homOfLE hpre).op) (ψU x))
    rw [algebraMap_normalizationToIntermediate]
    exact ((Y.presheaf.germ_res_apply (homOfLE hpre) (genericPoint Y)
      (((genericPoint_spec Y).mem_open_set_iff (p ⁻¹ᵁ V).isOpen).mpr
        (by simpa using (inferInstance : Nonempty (p ⁻¹ᵁ V)))) (ψU x)).trans
      (algebraMap_normalizationToIntermediate (B := Γ(X, U))
        (A := Γ(Y, p ⁻¹ᵁ U)) (E := Y.functionField) x)).symm
  rw [finiteAffinePreimageNormalizationIso_hom, finiteAffinePreimageNormalizationIso_hom]
  change ((hV.preimage p).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψV.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom ρ.toRingHom) =
    Y.homOfLE hpre ≫
      ((hU.preimage p).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψU.toRingHom))
  rw [Category.assoc, ← Spec.map_comp, hring, Spec.map_comp, ← Category.assoc]
  simp only [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_SpecMap_map, Category.assoc]

end Preimage


end

end HodgeConjecture.CollisionFoundations
