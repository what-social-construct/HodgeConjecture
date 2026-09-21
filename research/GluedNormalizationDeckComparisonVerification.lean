import HodgeConjecture.Boundary.Normalization.GluedNormalizationDeckComparison
import HodgeConjecture.Boundary.Normalization.GluedNormalClosureFunctionField
import Lean.Util.CollectAxioms

/-!
SP95 focused checks for generic-pullback extensionality and the full deck group.
Run with `lake env lean research/GluedNormalizationDeckComparisonVerification.lean`.

The generic comparison uses integral schemes and relative separatedness only.
Deck uniqueness does not require a finite ambient extension. Reconstruction
uses finite-dimensionality but not separability, étaleness or normal base
stalks. The marked specialization retains the original cover and embedding.
These checks do not establish fiber transitivity or an étale torsor statement.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open HodgeConjecture.SchemeCorrespondence

noncomputable section

universe u

#check functionFieldMapOfDominant_fromSpecStalk
#check eq_of_functionFieldMapOfDominant_eq
#check gluedNormalizationDeckTransformation_ext
#check gluedNormalizationDeckFieldAutomorphism
#check gluedNormalizationDeckFieldAutomorphism_apply
#check gluedNormalizationDeckAction_fieldAutomorphism
#check gluedNormalizationDeckAction_surjective
#check gluedNormalizationDeckEquiv

local instance verificationOverIntegral (X : Scheme.{u}) [IsIntegral X]
    (N : Type u) [Field N] [Algebra X.functionField N] :
    IsIntegral (Over.mk (gluedNormalizationToBase X N)).left :=
  inferInstanceAs (IsIntegral (gluedNormalizationModel X N))

section GenericPoint

variable {X Y S : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

example (f : X ⟶ Y) [IsDominant f] :
    Spec.map (functionFieldMapOfDominant f) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f :=
  functionFieldMapOfDominant_fromSpecStalk f

example (f g : X ⟶ Y) [IsDominant f] [IsDominant g]
    (s : Y ⟶ S) [IsSeparated s] (hb : f ≫ s = g ≫ s)
    (hf : functionFieldMapOfDominant f = functionFieldMapOfDominant g) : f = g := by
  fail_if_success have _ : IsFinite f := inferInstance
  fail_if_success have _ : IsEtale f := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact eq_of_functionFieldMapOfDominant_eq f g s hb hf

example (f g : X ⟶ Y) [IsDominant f] [IsDominant g]
    (s : Y ⟶ S) [IsSeparated s] (hb : f ≫ s = g ≫ s) :
    functionFieldMapOfDominant f = functionFieldMapOfDominant g ↔ f = g := by
  constructor
  · exact eq_of_functionFieldMapOfDominant_eq f g s hb
  · intro h
    subst g
    rfl

example :
    Spec.map (functionFieldMapOfDominant (𝟙 X)) ≫
        X.fromSpecStalk (genericPoint X) = X.fromSpecStalk (genericPoint X) := by
  rw [functionFieldMapOfDominant_fromSpecStalk, Category.comp_id]

end GenericPoint

section UnrestrictedAmbientExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]

example (d e : DeckTransformation (gluedNormalizationToBase X N))
    (hf : functionFieldMapOfDominant d.hom.left =
      functionFieldMapOfDominant e.hom.left) : d = e := by
  fail_if_success have _ : FiniteDimensional X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsAlgebraic X.functionField N := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField N := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact gluedNormalizationDeckTransformation_ext X N d e hf

example (d e : DeckTransformation (gluedNormalizationToBase X N))
    (hf : functionFieldMapOfDominant d.inv.left =
      functionFieldMapOfDominant e.inv.left) : d = e := by
  apply inv_injective
  exact gluedNormalizationDeckTransformation_ext X N d⁻¹ e⁻¹ hf

end UnrestrictedAmbientExtension

section FiniteAmbientExtension

variable {X : Scheme.{u}} [IsIntegral X]
variable (N : Type u) [Field N] [Algebra X.functionField N]
variable [FiniteDimensional X.functionField N]

local instance : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance : Algebra X.functionField (gluedNormalizationModel X N).functionField :=
  (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra

example (d : DeckTransformation (gluedNormalizationToBase X N)) :
    N ≃ₐ[X.functionField] N := gluedNormalizationDeckFieldAutomorphism X N d

example (d : DeckTransformation (gluedNormalizationToBase X N)) (x : N) :
    gluedNormalizationDeckFieldAutomorphism X N d x =
      gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant d.inv.left
          ((gluedNormalizationFunctionFieldEquiv X N).symm x)) :=
  gluedNormalizationDeckFieldAutomorphism_apply X N d x

example (d : DeckTransformation (gluedNormalizationToBase X N))
    (a : X.functionField) :
    gluedNormalizationDeckFieldAutomorphism X N d (algebraMap X.functionField N a) =
      algebraMap X.functionField N a :=
  (gluedNormalizationDeckFieldAutomorphism X N d).commutes a

example (d : DeckTransformation (gluedNormalizationToBase X N)) :
    gluedNormalizationDeckAction X N (gluedNormalizationDeckFieldAutomorphism X N d) = d :=
  gluedNormalizationDeckAction_fieldAutomorphism X N d

example : Function.Surjective (gluedNormalizationDeckAction X N) :=
  gluedNormalizationDeckAction_surjective X N

example : (N ≃ₐ[X.functionField] N) ≃*
    DeckTransformation (gluedNormalizationToBase X N) := by
  fail_if_success have _ : Algebra.IsSeparable X.functionField N := inferInstance
  fail_if_success have _ : IsGalois X.functionField N := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact gluedNormalizationDeckEquiv X N

example : (gluedNormalizationDeckEquiv X N).toMonoidHom =
    gluedNormalizationDeckAction X N := rfl

example (σ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationDeckEquiv X N σ = gluedNormalizationDeckAction X N σ := rfl

example (d : DeckTransformation (gluedNormalizationToBase X N)) :
    (gluedNormalizationDeckEquiv X N).symm d =
      gluedNormalizationDeckFieldAutomorphism X N d := rfl

example (σ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationDeckFieldAutomorphism X N (gluedNormalizationDeckAction X N σ) = σ :=
  (gluedNormalizationDeckEquiv X N).symm_apply_apply σ

example (d : DeckTransformation (gluedNormalizationToBase X N)) :
    gluedNormalizationDeckEquiv X N ((gluedNormalizationDeckEquiv X N).symm d) = d :=
  (gluedNormalizationDeckEquiv X N).apply_symm_apply d

example (σ τ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationDeckEquiv X N (σ * τ) =
      gluedNormalizationDeckEquiv X N σ * gluedNormalizationDeckEquiv X N τ :=
  (gluedNormalizationDeckEquiv X N).map_mul σ τ

example : gluedNormalizationDeckEquiv X N 1 = 1 :=
  (gluedNormalizationDeckEquiv X N).map_one

example (σ : N ≃ₐ[X.functionField] N) :
    gluedNormalizationDeckEquiv X N σ⁻¹ = (gluedNormalizationDeckEquiv X N σ)⁻¹ :=
  map_inv (gluedNormalizationDeckEquiv X N) σ

example (d e : DeckTransformation (gluedNormalizationToBase X N)) :
    gluedNormalizationDeckFieldAutomorphism X N (d * e) =
      gluedNormalizationDeckFieldAutomorphism X N d *
        gluedNormalizationDeckFieldAutomorphism X N e :=
  (gluedNormalizationDeckEquiv X N).symm.map_mul d e

example : gluedNormalizationDeckFieldAutomorphism X N 1 = 1 :=
  (gluedNormalizationDeckEquiv X N).symm.map_one

-- Forward geometric action is inverse pullback, while reconstruction uses d⁻¹.
example (σ : N ≃ₐ[X.functionField] N)
    (a : (gluedNormalizationModel X N).functionField) :
    gluedNormalizationFunctionFieldEquiv X N
        (functionFieldMapOfDominant (gluedNormalizationDeckEquiv X N σ).hom.left a) =
      σ.symm (gluedNormalizationFunctionFieldEquiv X N a) :=
  gluedNormalizationFunctionFieldEquiv_automorphism X N σ a

example :
    Function.Injective (gluedNormalizationDeckFieldAutomorphism X N) :=
  (gluedNormalizationDeckEquiv X N).symm.injective

end FiniteAmbientExtension

section OriginalMarkedNormalClosure

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    (Nₚ ≃ₐ[X.functionField] Nₚ) ≃*
      DeckTransformation (gluedNormalizationToBase X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  fail_if_success have _ : IsEtale p := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField Y.functionField := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact gluedNormalizationDeckEquiv X Nₚ

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    Function.Surjective (gluedNormalizationDeckAction X Nₚ) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  exact gluedNormalizationDeckAction_surjective X Nₚ

example (c : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    letI : Surjective (gluedNormalClosureToCover p hY) :=
      gluedNormalClosureToCover_surjective p hY
    ∀ d : DeckTransformation (gluedNormalizationToBase X Nₚ),
      gluedNormalizationDeckFieldAutomorphism X Nₚ d
          ((functionFieldNormalClosureData p).embedding c) =
        gluedNormalizationFunctionFieldEquiv X Nₚ
          (functionFieldMapOfDominant d.inv.left
            (functionFieldMapOfDominant (gluedNormalClosureToCover p hY) c)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  letI : Surjective (gluedNormalClosureToCover p hY) :=
    gluedNormalClosureToCover_surjective p hY
  letI : Surjective (gluedNormalizationToBase X Nₚ) :=
    gluedNormalizationToBase_surjective X Nₚ
  letI : Algebra X.functionField (gluedNormalizationModel X Nₚ).functionField :=
    (functionFieldMapOfDominant (gluedNormalizationToBase X Nₚ)).hom.toAlgebra
  intro d
  rw [← gluedNormalClosureFunctionFieldEquiv_toCover p hY c,
    gluedNormalizationDeckFieldAutomorphism_apply, AlgEquiv.symm_apply_apply]

end OriginalMarkedNormalClosure

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.SchemeCycles.functionFieldMapOfDominant_fromSpecStalk,
    `HodgeConjecture.SchemeCycles.eq_of_functionFieldMapOfDominant_eq,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckTransformation_ext,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckFieldAutomorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckFieldAutomorphism_apply,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckAction_fieldAutomorphism,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckAction_surjective,
    `HodgeConjecture.CollisionFoundations.gluedNormalizationDeckEquiv]
  unless declarations.length == 8 && declarations.eraseDups.length == 8 do
    throwError "Expected exactly eight distinct SP95 declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    let actual := state.axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP95 audit registry: eight distinct public declarations"
