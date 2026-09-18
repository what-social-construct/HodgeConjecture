import HodgeConjecture.Boundary
import Lean.Util.CollectAxioms

/-!
SP71 regressions for actual affine charts of finite étale scheme morphisms.
Run with `lake env lean research/FiniteAffineChartVerification.lean`.

The public boundary umbrella must expose every result.  General étale-chart
tests do not assume finiteness or normality; normalization tests retain the
explicit normal-stalk and nonempty-preimage hypotheses.  No Noetherian or
projectivity hypotheses are added.  Every new declaration has an enforced
standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.NormalizationInertia

noncomputable section

universe u

section GeneralCharts

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

-- Scheme smoothness is sufficient; neither finiteness nor étaleness is inferred.
example [IsSmooth p] (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ p ⁻¹ᵁ U.1) : (p.appLE U V e).hom.Smooth := by
  fail_if_success have _ : IsFinite p := inferInstance
  fail_if_success have _ : IsEtale p := inferInstance
  exact affine_appLE_smooth p U V e

-- Étaleness of the chart algebra does not need, or supply, normality.
example [IsEtale p] (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ p ⁻¹ᵁ U.1) :
    letI := (p.appLE U V e).hom.toAlgebra
    Algebra.Etale Γ(X, U) Γ(Y, V) := by
  fail_if_success have _ : IsFinite p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(Y, V) := inferInstance
  exact affine_appLE_etale p U V e

example [IsEtale p] [IsAffine X] [IsAffine Y] :
    letI := p.appTop.hom.toAlgebra
    Algebra.Etale Γ(X, ⊤) Γ(Y, ⊤) :=
  affine_appTop_etale p

-- An identity morphism supplies an actual scheme-level étale smoke test.
example (X : Scheme.{u}) [IsAffine X] :
    letI := (Scheme.Hom.appTop (𝟙 X)).hom.toAlgebra
    Algebra.Etale Γ(X, ⊤) Γ(X, ⊤) :=
  affine_appTop_etale (𝟙 X)

end GeneralCharts

section WholePreimage

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens)

set_option quotPrecheck false in
local notation "Bᵤ" => Γ(X, U)
set_option quotPrecheck false in
local notation "Aᵤ" => Γ(Y, p ⁻¹ᵁ U)

local instance : Algebra Bᵤ Aᵤ := (p.app U).hom.toAlgebra

example [IsFinite p] (hU : IsAffineOpen U) : IsAffineOpen (p ⁻¹ᵁ U) :=
  hU.preimage p

example [IsFinite p] (hU : IsAffineOpen U) : Module.Finite Bᵤ Aᵤ := by
  fail_if_success have _ : IsNoetherianRing Bᵤ := inferInstance
  fail_if_success have _ : Algebra.Etale Bᵤ Aᵤ := inferInstance
  exact finiteAffinePreimage_moduleFinite p U hU

example [IsFinite p] (hU : IsAffineOpen U) : Algebra.IsIntegral Bᵤ Aᵤ := by
  letI := finiteAffinePreimage_moduleFinite p U hU
  infer_instance

example [IsFinite p] [IsEtale p] (hU : IsAffineOpen U) :
    Algebra.Etale Bᵤ Aᵤ := by
  fail_if_success have _ : IsIntegrallyClosed Aᵤ := inferInstance
  exact finiteAffinePreimage_etale p U hU

end WholePreimage

section Normality

variable {Y : Scheme.{u}} [IsIntegral Y] {V : Y.Opens} [Nonempty V]

example (hV : IsAffineOpen V)
    (hNormal : ∀ y : V, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    IsIntegrallyClosed Γ(Y, V) := by
  fail_if_success have _ : IsNoetherianRing Γ(Y, V) := inferInstance
  exact affineSections_isIntegrallyClosed_of_stalks hV hNormal

-- This is the scheme's actual function field and its existing generic germ.
example (hV : IsAffineOpen V) : IsFractionRing Γ(Y, V) Y.functionField :=
  functionField_isFractionRing_of_isAffineOpen Y V hV

example (hV : IsAffineOpen V)
    (hNormal : ∀ y : V, IsIntegrallyClosed (Y.presheaf.stalk y.val)) :
    IsIntegralClosure Γ(Y, V) Γ(Y, V) Y.functionField := by
  letI := functionField_isFractionRing_of_isAffineOpen Y V hV
  letI := affineSections_isIntegrallyClosed_of_stalks hV hNormal
  infer_instance

end Normality

section Normalization

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.Opens)
variable [IsFinite p] [IsIntegral Y] [Nonempty (p ⁻¹ᵁ U)]
variable (hU : IsAffineOpen U)
variable (hNormal : ∀ y : p ⁻¹ᵁ U, IsIntegrallyClosed (Y.presheaf.stalk y.val))

set_option quotPrecheck false in
local notation "Bᵤ" => Γ(X, U)
set_option quotPrecheck false in
local notation "Aᵤ" => Γ(Y, p ⁻¹ᵁ U)

local instance : Algebra Bᵤ Aᵤ := (p.app U).hom.toAlgebra

example :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI : IsScalarTower Bᵤ Aᵤ Y.functionField :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing Aᵤ Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ (hU.preimage p)
    letI : IsIntegrallyClosed Aᵤ :=
      affineSections_isIntegrallyClosed_of_stalks (hU.preimage p) hNormal
    (finiteAffinePreimageNormalizationIso p U hU hNormal).hom =
      (hU.preimage p).isoSpec.hom ≫
        intermediateToNormalization (B := Bᵤ) (A := Aᵤ) (E := Y.functionField) :=
  finiteAffinePreimageNormalizationIso_hom p U hU hNormal

example : IsIso (finiteAffinePreimageNormalizationIso p U hU hNormal).hom := by
  infer_instance

example : Function.Surjective
    (finiteAffinePreimageNormalizationIso p U hU hNormal).hom.base :=
  (ConcreteCategory.bijective_of_isIso _).surjective

-- The canonical identification commutes over the original X, not just Spec Bᵤ.
example :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    (finiteAffinePreimageNormalizationIso p U hU hNormal).hom ≫
        normalizedModelToBase Bᵤ Y.functionField ≫ hU.fromSpec =
      (p ⁻¹ᵁ U).ι ≫ p :=
  finiteAffinePreimageNormalizationIso_hom_comp_toBase p U hU hNormal

example :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    Module.Finite Bᵤ (normalizedCoordinateRing Bᵤ Y.functionField) := by
  fail_if_success have _ : IsNoetherianRing Bᵤ := inferInstance
  fail_if_success have _ : IsEtale p := inferInstance
  exact finiteAffinePreimage_normalization_finite p U hU hNormal

example [IsEtale p] :
    letI : Algebra Bᵤ Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    Algebra.Etale Bᵤ (normalizedCoordinateRing Bᵤ Y.functionField) :=
  finiteAffinePreimage_normalization_etale p U hU hNormal

end Normalization

-- Finiteness also has an actual identity-morphism smoke test, on any affine open.
example (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    letI := (Scheme.Hom.app (𝟙 X) U).hom.toAlgebra
    Module.Finite Γ(X, U) Γ(X, (𝟙 X) ⁻¹ᵁ U) :=
  finiteAffinePreimage_moduleFinite (𝟙 X) U hU

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.affine_appLE_smooth,
      `HodgeConjecture.CollisionFoundations.affine_appLE_etale,
      `HodgeConjecture.CollisionFoundations.affine_appTop_etale,
      `HodgeConjecture.NormalizationInertia.affineSections_isIntegrallyClosed_of_stalks,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimage_moduleFinite,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimage_etale,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimageNormalizationIso,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimageNormalizationIso_hom,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimageNormalizationIso_hom_comp_toBase,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimage_normalization_finite,
      `HodgeConjecture.CollisionFoundations.finiteAffinePreimage_normalization_etale] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    for axiomName in state.axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {state.axioms.toList}"
