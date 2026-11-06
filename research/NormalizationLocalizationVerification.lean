module

import HodgeConjecture.Boundary.Normalization.NormalizationLocalization
import HodgeConjecture.Boundary.Normalization.AffineNormalizationRestriction
import HodgeConjecture.Boundary.Normalization.FiniteEtaleNormalClosureRestriction
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP82 regressions for localization in the original ambient overring.
Run with `lake env lean research/NormalizationLocalizationVerification.lean`.

These tests begin over arbitrary commutative rings. The comparison map is
the literal ambient inclusion, and denominator units come from the supplied
base localization. Normality, domains, fields, finite extensions, and
Noetherian hypotheses are absent from the commutative-algebra comparison.
The naturality tests preserve the actual ambient map, not only an abstract
isomorphism class of its source or target.
All twenty-eight new public declarations have an exact, duplicate-free
standard-three-axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations
open scoped TensorProduct

noncomputable section

universe u

section ArbitraryBaseChange

variable {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]

example (x : normalizedCoordinateRing B E) :
    ((normalizationBaseChangeMap (B := B) (C := C) (E := E) x :
      normalizedCoordinateRing C E) : E) = (x : E) := rfl

example : Function.Injective
    (normalizationBaseChangeMap (B := B) (C := C) (E := E)) :=
  normalizationBaseChangeMap_injective

example (b : B) :
    normalizationBaseChangeMap (B := B) (C := C) (E := E)
      (algebraMap B (normalizedCoordinateRing B E) b) =
      algebraMap B (normalizedCoordinateRing C E) b :=
  (normalizationBaseChangeMap (B := B) (C := C) (E := E)).commutes b

example (x y : normalizedCoordinateRing B E) :
    normalizationBaseChangeMap (B := B) (C := C) (E := E) (x * y) =
      normalizationBaseChangeMap (B := B) (C := C) (E := E) x *
      normalizationBaseChangeMap (B := B) (C := C) (E := E) y :=
  map_mul _ x y

example (x : normalizedCoordinateRing B E) :
    normalizationBaseChangeMap (B := B) (C := B) (E := E) x = x := by
  rw [normalizationBaseChangeMap_self]
  rfl

-- This is an actual subtype inclusion without any injectivity assumption
-- on the base algebra map B → C.
example (x : normalizedCoordinateRing B E) :
    IsIntegral C (normalizationBaseChangeMap (B := B) (C := C) (E := E) x : E) := by
  fail_if_success have _ : IsDomain B := inferInstance
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact (normalizationBaseChangeMap (B := B) (C := C) (E := E) x).property

end ArbitraryBaseChange

section Composition

variable {B C D E : Type u}
variable [CommRing B] [CommRing C] [CommRing D] [CommRing E]
variable [Algebra B C] [Algebra B D] [Algebra C D]
variable [Algebra B E] [Algebra C E] [Algebra D E]
variable [IsScalarTower B C D] [IsScalarTower B C E]
variable [IsScalarTower B D E] [IsScalarTower C D E]

example (x : normalizedCoordinateRing B E) :
    normalizationBaseChangeMap (B := C) (C := D) (E := E)
      (normalizationBaseChangeMap (B := B) (C := C) (E := E) x) =
      normalizationBaseChangeMap (B := B) (C := D) (E := E) x := by
  exact DFunLike.congr_fun
    (normalizationBaseChangeMap_trans (B := B) (C := C) (D := D) (E := E)) x

end Composition

section AmbientNaturality

variable {B C E F : Type u}
variable [CommRing B] [CommRing C] [CommRing E] [CommRing F]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]
variable [Algebra B F] [Algebra C F] [IsScalarTower B C F]

example (f : E →ₐ[C] F) (x : normalizedCoordinateRing B E) :
    normalizationMap F f
      (normalizationBaseChangeMap (B := B) (C := C) (E := E) x) =
      normalizationBaseChangeMap (B := B) (C := C) (E := F)
        (normalizationMap F (f.restrictScalars B) x) := by
  exact DFunLike.congr_fun (normalizationBaseChangeMap_naturality (B := B) f) x

example (f : E →ₐ[C] F) (x : normalizedCoordinateRing B E) :
    ((normalizationMap F f
      (normalizationBaseChangeMap (B := B) (C := C) (E := E) x) :
      normalizedCoordinateRing C F) : F) = f (x : E) := rfl

end AmbientNaturality

section Localization

variable {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]
variable (M : Submonoid B) [IsLocalization M C]

example :
    letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
      (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (normalizedCoordinateRing B E) M)
      (normalizedCoordinateRing C E) := by
  fail_if_success have _ : IsDomain B := inferInstance
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  fail_if_success have _ : Module.Finite B E := inferInstance
  exact normalizedCoordinateRing_isLocalization (C := C) (E := E) M

example (m : M) : IsUnit (algebraMap C (normalizedCoordinateRing C E)
    (algebraMap B C m)) :=
  (IsLocalization.map_units C m).map (algebraMap C (normalizedCoordinateRing C E))

example (x : normalizedCoordinateRing C E) :
    ∃ m : M, IsIntegral B (m • (x : E)) :=
  x.property.exists_multiple_integral_of_isLocalization M (x : E)

example (x : normalizedCoordinateRing B E) :
    letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
      (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
    ((algebraMap (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) x :
      normalizedCoordinateRing C E) : E) = (x : E) := rfl

end Localization

section TensorComparison

variable {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]
variable (M : Submonoid B) [IsLocalization M C]

example : Nonempty ((C ⊗[B] normalizedCoordinateRing B E) ≃ₐ[C]
    normalizedCoordinateRing C E) := by
  fail_if_success have _ : IsDomain B := inferInstance
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact ⟨normalizationLocalizationBaseChangeEquiv M⟩

example (c : C) (x : normalizedCoordinateRing B E) :
    ((normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M
      (c ⊗ₜ[B] x) : normalizedCoordinateRing C E) : E) =
      algebraMap C E c * (x : E) :=
  normalizationLocalizationBaseChangeEquiv_tmul M c x

example (x : normalizedCoordinateRing B E) :
    normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M (1 ⊗ₜ[B] x) =
      normalizationBaseChangeMap (B := B) (C := C) (E := E) x := by
  apply Subtype.ext
  simp only [normalizationLocalizationBaseChangeEquiv_tmul, map_one, one_mul,
    normalizationBaseChangeMap_coe]

example (c : C) :
    normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M
      (c ⊗ₜ[B] (1 : normalizedCoordinateRing B E)) =
      algebraMap C (normalizedCoordinateRing C E) c := by
  apply Subtype.ext
  simp only [normalizationLocalizationBaseChangeEquiv_tmul, Subalgebra.coe_one,
    mul_one, Subalgebra.coe_algebraMap]

example (x : normalizedCoordinateRing C E) :
    normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M
      ((normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M).symm x) = x :=
  (normalizationLocalizationBaseChangeEquiv (C := C) (E := E) M).apply_symm_apply x

end TensorComparison

section SchemeMaps

variable {B C E : Type u} [CommRing B] [CommRing C] [CommRing E]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]

example : normalizationBaseChange (B := B) (C := C) (E := E) =
    Spec.map (CommRingCat.ofHom
      (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toRingHom) := rfl

example :
    normalizationBaseChange (B := B) (C := C) (E := E) ≫ normalizedModelToBase B E =
      normalizedModelToBase C E ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) :=
  normalizationBaseChange_comp_toBase

example : normalizationBaseChange (B := B) (C := B) (E := E) = 𝟙 _ :=
  normalizationBaseChange_self

example {D : Type u} [CommRing D] [Algebra B D] [Algebra C D] [Algebra D E]
    [IsScalarTower B C D] [IsScalarTower B D E] [IsScalarTower C D E] :
    normalizationBaseChange (B := C) (C := D) (E := E) ≫
      normalizationBaseChange (B := B) (C := C) (E := E) =
      normalizationBaseChange (B := B) (C := D) (E := E) :=
  normalizationBaseChange_trans

example {F : Type u} [CommRing F] [Algebra B F] [Algebra C F] [IsScalarTower B C F]
    (f : E →ₐ[C] F) :
    normalizationBaseChange (B := B) (C := C) (E := F) ≫
      normalizationDomination F (f.restrictScalars B) =
      normalizationDomination F f ≫ normalizationBaseChange (B := B) (C := C) (E := E) :=
  normalizationBaseChange_naturality f

example (r : B) [IsLocalization.Away r C] :
    letI : Algebra (normalizedCoordinateRing B E) (normalizedCoordinateRing C E) :=
      (normalizationBaseChangeMap (B := B) (C := C) (E := E)).toAlgebra
    IsLocalization.Away (algebraMap B (normalizedCoordinateRing B E) r)
      (normalizedCoordinateRing C E) :=
  normalizedCoordinateRing_isLocalizationAway r

example (r : B) [IsLocalization.Away r C] :
    IsOpenImmersion (normalizationBaseChange (B := B) (C := C) (E := E)) := by
  fail_if_success have _ : IsDomain B := inferInstance
  fail_if_success have _ : IsIntegrallyClosed B := inferInstance
  fail_if_success have _ : IsNoetherianRing B := inferInstance
  exact normalizationBaseChange_isOpenImmersion r

example (r : B) [IsLocalization.Away r C] :
    Set.range (normalizationBaseChange (B := B) (C := C) (E := E)).base =
      (normalizedModelToBase B E).base ⁻¹'
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum B)) :=
  normalizationBaseChange_range r

end SchemeMaps

section FixedAmbientField

variable {B C E : Type u} [CommRing B] [CommRing C] [Field E]
variable [Algebra B C] [Algebra B E] [Algebra C E] [IsScalarTower B C E]
variable (M : Submonoid B) [IsLocalization M C]

-- The existing scalar tower into a field already prevents a zero
-- denominator; no replacement fraction field is introduced.
example (m : M) : algebraMap B E m ≠ 0 := by
  have h := ((IsLocalization.map_units C m).map (algebraMap C E)).ne_zero
  simpa only [IsScalarTower.algebraMap_apply B C E] using h

end FixedAmbientField

section ActualChartRestriction

variable {X : Scheme.{u}} [IsIntegral X]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) X.functionField :=
  sectionRestriction_functionFieldScalarTower U V hVU

example (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) N :=
  sectionRestriction_ambientScalarTower U V N hVU

example (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    letI : IsScalarTower Γ(X, U) Γ(X, V) N :=
      sectionRestriction_ambientScalarTower U V N hVU
    affineNormalizationRestriction U V N hVU =
      normalizationBaseChange (B := Γ(X, U)) (C := Γ(X, V)) (E := N) := rfl

example (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V N hVU ≫ normalizedModelToBase Γ(X, U) N =
      normalizedModelToBase Γ(X, V) N ≫
        Spec.map (X.presheaf.map (homOfLE hVU).op) :=
  affineNormalizationRestriction_comp_toBase U V N hVU

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, U) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) N :=
      ((algebraMap X.functionField N).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V N hVU ≫
      normalizedModelToBase Γ(X, U) N ≫ hU.isoSpec.inv =
      normalizedModelToBase Γ(X, V) N ≫ hV.isoSpec.inv ≫ X.homOfLE hVU :=
  affineNormalizationRestriction_comp_toChart U V N hVU hU hV

example (hU : IsAffineOpen U) (f : Γ(X, U)) [Nonempty (X.basicOpen f)] :
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
      (normalizedCoordinateRing Γ(X, X.basicOpen f) N) :=
  affineNormalizationRestriction_basicOpen_isLocalization U N hU f

example (hU : IsAffineOpen U) (f : Γ(X, U)) [Nonempty (X.basicOpen f)] :
    IsOpenImmersion
      (affineNormalizationRestriction U (X.basicOpen f) N (X.basicOpen_le f)) := by
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  exact affineNormalizationRestriction_basicOpen_isOpenImmersion U N hU f

end ActualChartRestriction

section ActualPreimageRestriction

open SchemeCycles

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]
variable (p : Y ⟶ X) [IsDominant p]

local instance : Nonempty (p ⁻¹ᵁ U) := nonempty_preimage_of_isDominant p U
local instance : Nonempty (p ⁻¹ᵁ V) := nonempty_preimage_of_isDominant p V

example (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : Algebra Γ(X, V) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ V)).hom.comp (p.app V).hom).toAlgebra
    letI : Algebra Γ(X, U) Γ(X, V) :=
      (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    IsScalarTower Γ(X, U) Γ(X, V) Y.functionField :=
  finiteAffinePreimageRestriction_functionFieldScalarTower U V p hVU

example [IsFinite p] (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
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
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  exact finiteAffinePreimageNormalizationIso_restriction U V p hVU hU hV hYU hYV

end ActualPreimageRestriction

section MarkedNormalClosureRestriction

open SchemeCycles

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p]
variable (U V : X.Opens) [Nonempty U] [Nonempty V]

local instance : Nonempty (p ⁻¹ᵁ U) := nonempty_preimage_of_isDominant p U
local instance : Nonempty (p ⁻¹ᵁ V) := nonempty_preimage_of_isDominant p V

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V Nₚ hVU ≫
      finiteEtaleAffineNormalClosureToChart p U hU =
      finiteEtaleAffineNormalClosureToChart p V hV ≫ X.homOfLE hVU := by
  fail_if_success have _ : IsFinite p := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  exact finiteEtaleAffineNormalClosureToChart_restriction p U V hVU hU hV

example [IsFinite p] (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
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
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  exact finiteEtaleAffineNormalClosureToPreimage_restriction p U V hVU hU hV hYU hYV

-- Normality on the smaller actual preimage is inherited from the larger
-- one; this invocation introduces no separate geometric assumption there.
example [IsFinite p] (hVU : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hYU : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : Algebra Γ(X, U) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) Nₚ :=
      ((algebraMap X.functionField Nₚ).comp (X.germToFunctionField V).hom).toAlgebra
    affineNormalizationRestriction U V Nₚ hVU ≫
      finiteEtaleAffineNormalClosureToPreimage p U hU hYU =
      finiteEtaleAffineNormalClosureToPreimage p V hV
        (fun y => hYU ⟨y.val, hVU y.property⟩) ≫
        Y.homOfLE (show p ⁻¹ᵁ V ≤ p ⁻¹ᵁ U from fun _ h => hVU h) :=
  finiteEtaleAffineNormalClosureToPreimage_restriction p U V hVU hU hV hYU
    (fun y => hYU ⟨y.val, hVU y.property⟩)

end MarkedNormalClosureRestriction

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.normalizationBaseChangeMap,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChangeMap_coe,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChangeMap_injective,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChangeMap_self,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChangeMap_trans,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChangeMap_naturality,
    `HodgeConjecture.CollisionFoundations.normalizedCoordinateRing_isLocalization,
    `HodgeConjecture.CollisionFoundations.normalizationLocalizationBaseChangeEquiv,
    `HodgeConjecture.CollisionFoundations.normalizationLocalizationBaseChangeEquiv_tmul,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange_comp_toBase,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange_naturality,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange_self,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange_trans,
    `HodgeConjecture.CollisionFoundations.normalizedCoordinateRing_isLocalizationAway,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange_isOpenImmersion,
    `HodgeConjecture.CollisionFoundations.normalizationBaseChange_range,
    `HodgeConjecture.CollisionFoundations.sectionRestriction_functionFieldScalarTower,
    `HodgeConjecture.CollisionFoundations.sectionRestriction_ambientScalarTower,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_comp_toBase,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_comp_toChart,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_basicOpen_isLocalization,
    `HodgeConjecture.CollisionFoundations.affineNormalizationRestriction_basicOpen_isOpenImmersion,
    `HodgeConjecture.CollisionFoundations.finiteAffinePreimageRestriction_functionFieldScalarTower,
    `HodgeConjecture.CollisionFoundations.finiteAffinePreimageNormalizationIso_restriction,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToChart_restriction,
    `HodgeConjecture.CollisionFoundations.finiteEtaleAffineNormalClosureToPreimage_restriction]
  unless declarations.length == 28 do
    throwError "Expected exactly 28 SP82 declarations, got {declarations.length}"
  unless declarations.eraseDups.length == declarations.length do
    throwError "Duplicate declaration in the SP82 audit registry"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
  logInfo "PASS SP82 audit registry: 28 distinct public declarations"
