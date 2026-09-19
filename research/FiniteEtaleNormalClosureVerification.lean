import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosure
import Lean.Util.CollectAxioms

/-!
SP81 regressions for the actual finite étale affine normal-closure refinement.
Run with `lake env lean research/FiniteEtaleNormalClosureVerification.lean`.

The finite tensor bridge is tested at arbitrary, empty, and singleton index
types. The actual chart tests retain the original function-field marking,
generic-germ scalar map, normalization carrier, and visible isomorphism.
The structural and refinement maps are finite étale on the fixed chart,
and their squares commute over both that chart and the original base scheme.
Normality is local to this chart and its inverse image; neither Noetherianity
nor a perfect function field is assumed. No assertion concerns global gluing.
All nineteen new public declarations have an exact, duplicate-free
standard-three-axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.NormalizationInertia
open HodgeConjecture.SchemeCycles
open scoped TensorProduct

noncomputable section

universe u

section FiniteTensorSource

variable {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]

example
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hIso : RingHom.RespectsIso P) (hId : RingHom.ContainsIdentities P)
    (hComp : RingHom.StableUnderComposition P)
    (hBase : RingHom.IsStableUnderBaseChange P)
    (ι : Type u) [Finite ι] (hA : P (algebraMap B A)) :
    P (algebraMap B (⨂[B] _ : ι, A)) :=
  piTensorProduct_ringHomProperty P hIso hId hComp hBase ι hA

variable (hA : IsEtale (Spec.map (CommRingCat.ofHom (algebraMap B A))))

include hA

example (ι : Type u) [Finite ι] :
    IsEtale (Spec.map (CommRingCat.ofHom (algebraMap B (⨂[B] _ : ι, A)))) := by
  fail_if_success have _ : Nonempty ι := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact piTensorProduct_isEtale ι hA

example : IsEtale (Spec.map (CommRingCat.ofHom
    (algebraMap B (⨂[B] _ : PEmpty.{u+1}, A)))) :=
  piTensorProduct_isEtale PEmpty hA

example : IsEtale (Spec.map (CommRingCat.ofHom
    (algebraMap B (⨂[B] _ : PUnit.{u+1}, A)))) :=
  piTensorProduct_isEtale PUnit hA

end FiniteTensorSource

section GenericIntegralComponent

variable {B K L N A : Type u}
variable [CommRing B] [Field K] [Field L] [Field N] [CommRing A]
variable [Algebra B K] [IsFractionRing B K] [IsIntegrallyClosed B]
variable [Algebra K L] [Algebra K N] [Algebra B L] [Algebra B N]
variable [IsScalarTower B K L] [IsScalarTower B K N]
variable [Algebra B A] [Algebra A L] [IsScalarTower B A L]
variable [IsFractionRing A L] [IsIntegrallyClosed A] [Module.Finite B A]
variable [Algebra.Etale B A] (D : NormalClosureData K L N)

include A

example : IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (D.normalizationTensorEvaluation (B := B)).toRingHom)) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.normalizationTensorEvaluation_isOpenImmersion (B := B) (A := A)

example (hL : IsEtale (normalizedModelToBase B L)) :
    IsEtale (normalizedModelToBase B N) := by
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : PerfectField K := inferInstance
  exact D.normalizationToBase_isEtale_of_etaleModel (B := B) (A := A) hL

end GenericIntegralComponent

section ActualAffineChart

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [IsEtale p]
variable (U : X.Opens) [Nonempty U]

local instance : Nonempty (p ⁻¹ᵁ U) := nonempty_preimage_of_isDominant p U
local instance : Algebra Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

variable (hU : IsAffineOpen U)

omit [IsFinite p] [IsEtale p] in
example : Function.Surjective (finiteEtaleAffineNormalClosureToChart p U hU).base := by
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  exact (finiteEtaleAffineNormalClosureToChart_surjective p U hU).surj

-- The chart map and its canonical scalar action already exist before
-- either normal-stalk input is introduced.
omit [IsFinite p] [IsEtale p] in
example (b : Γ(X, U)) :
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
    algebraMap Γ(X, U) Nₚ b =
    algebraMap X.functionField Nₚ ((X.germToFunctionField U) b) := rfl

omit [IsFinite p] [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToChart p U hU =
    normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ) ≫ hU.isoSpec.inv := rfl

omit [IsFinite p] [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToChart p U hU ≫ U.ι =
    normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ) ≫ hU.fromSpec :=
  finiteEtaleAffineNormalClosureToChart_comp_inclusion p U hU

variable (hY : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val))

omit [IsEtale p] in
example : Function.Surjective (finiteEtaleAffineNormalClosureToPreimage p U hU hY).base :=
  (finiteEtaleAffineNormalClosureToPreimage_surjective p U hU hY).surj

-- These canonical factorization identities do not require normality of
-- the base chart; its normal-stalk input is introduced below.
omit [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToPreimage p U hU hY =
    normalClosureToIntermediateNormalization (B := Γ(X, U)) (functionFieldNormalClosureData p) ≫
      (finiteAffinePreimageNormalizationIso p U hU hY).inv := rfl

omit [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫
      (finiteAffinePreimageNormalizationIso p U hU hY).hom =
    normalClosureToIntermediateNormalization (B := Γ(X, U)) (functionFieldNormalClosureData p) :=
  finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso p U hU hY

omit [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫ (p ⁻¹ᵁ U).ι ≫ p =
    normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ) ≫ hU.fromSpec :=
  finiteEtaleAffineNormalClosureToPreimage_comp_toBase p U hU hY

omit [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫ (p ∣_ U) =
    finiteEtaleAffineNormalClosureToChart p U hU :=
  finiteEtaleAffineNormalClosureToPreimage_comp_restrict p U hU hY

omit [IsEtale p] in
example :
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
    finiteEtaleAffineNormalClosureToPreimage p U hU hY ≫ (p ⁻¹ᵁ U).ι ≫ p =
    finiteEtaleAffineNormalClosureToChart p U hU ≫ U.ι := by
  rw [finiteEtaleAffineNormalClosureToPreimage_comp_toBase,
    finiteEtaleAffineNormalClosureToChart_comp_inclusion]

variable (hX : ∀ x : U, IsIntegrallyClosed (X.presheaf.stalk x.val))

include hX hY

example :
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
    Module.Finite Γ(X, U) (normalizedCoordinateRing Γ(X, U) Nₚ) ∧
    Algebra.Etale Γ(X, U) (normalizedCoordinateRing Γ(X, U) Nₚ) := by
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact functionFieldNormalClosure_normalization_finite_etale p U hU hX hY

example :
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
    (finiteEtaleAffinePreimageNormalizedCover p U hU hX hY).normalClosure =
    functionFieldNormalClosureData p :=
  finiteEtaleAffinePreimageNormalizedCover_normalClosure p U hU hX hY

example :
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
    NormalizedCover (B := Γ(X, U)) (K := X.functionField)
    (L := Y.functionField) (N := Nₚ)
    (p ⁻¹ᵁ U).toScheme (finiteAffinePreimageNormalizationIso p U hU hY).hom :=
  finiteEtaleAffinePreimageNormalizedCover p U hU hX hY

example :
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
    Module.Finite Γ(X, U)
      (IntermediateNormalizationRing (B := Γ(X, U)) (L := Y.functionField)) ∧
    Module.Finite Γ(X, U) (NormalClosureNormalizationRing (B := Γ(X, U)) (N := Nₚ)) := by
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
  let C := finiteEtaleAffinePreimageNormalizedCover p U hU hX hY
  exact ⟨C.finiteIntermediateModel, C.finiteNormalClosureModel⟩

example :
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
    IsOpenImmersion (finiteAffinePreimageNormalizationIso p U hU hY).hom := by
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
  exact (finiteEtaleAffinePreimageNormalizedCover p U hU hX hY).visibleOpen

example :
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
    ConjugateBoundarySeparation (finiteEtaleAffinePreimageNormalizedCover p U hU hX hY) := by
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact conjugateBoundarySeparation_finiteEtaleAffinePreimageNormalizedCover p U hU hX hY

example :
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
    IsFinite (normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ)) ∧
    IsEtale (normalClosureNormalizationToBase (B := Γ(X, U)) (N := Nₚ)) := by
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact finiteEtaleAffineNormalClosureToBase_finite_etale p U hU hX hY

example :
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
    IsFinite (finiteEtaleAffineNormalClosureToChart p U hU) ∧
    IsEtale (finiteEtaleAffineNormalClosureToChart p U hU) :=
  finiteEtaleAffineNormalClosureToChart_finite_etale p U hU hX hY

example :
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
    IsFinite (finiteEtaleAffineNormalClosureToPreimage p U hU hY) ∧
    IsEtale (finiteEtaleAffineNormalClosureToPreimage p U hU hY) := by
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  exact finiteEtaleAffineNormalClosureToPreimage_finite_etale p U hU hX hY

end ActualAffineChart

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.piTensorProduct_ringHomProperty,
    `HodgeConjecture.CollisionFoundations.piTensorProduct_isEtale,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationTensorEvaluation_isOpenImmersion,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalizationToBase_isEtale_of_etaleModel,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosure_normalization_finite_etale,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffinePreimageNormalizedCover,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffinePreimageNormalizedCover_normalClosure,
    `HodgeConjecture.CollisionFoundations.conjugateBoundarySeparation_finiteEtaleAffinePreimageNormalizedCover,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToBase_finite_etale,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToChart,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToChart_comp_inclusion,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToChart_surjective,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToChart_finite_etale,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage_comp_normalizationIso,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage_comp_toBase,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage_comp_restrict,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage_surjective,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage_finite_etale]
  unless declarations.length == 19 do
    throwError "Expected exactly 19 SP81 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP81 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
  logInfo "PASS SP81 audit registry: 19 distinct public declarations"
