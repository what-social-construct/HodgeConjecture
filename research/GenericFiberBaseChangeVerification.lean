module

import HodgeConjecture.Boundary.Normalization.GenericFiberBaseChange
import Mathlib.Algebra.Polynomial.Div
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP98 focused checks for base change of the actual generic fiber.
Run with `lake env lean research/GenericFiberBaseChangeVerification.lean`.

The tensor order is `E ⊗[K(X)] K(Y)`, with the actual dominant function-field
map supplying the second factor's scalar action. Local notation abbreviates
only the displayed tensor inclusions and scheme morphisms. Tests retain both
canonical projections and exercise the actual pullback universal property.
The extension algebra is only a commutative algebra, with explicit field and
genuinely nonfield polynomial-algebra specializations. No separability,
normality, étaleness, or Noetherianity is supplied. One exact public-declaration
audit checks the actual standard-three Lean axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles
open scoped TensorProduct

noncomputable section

universe u

#check functionFieldMapOfDominant_baseChange_isPullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]
variable (E : Type u) [CommRing E] [Algebra X.functionField E]

set_option quotPrecheck false in
local notation "Tₚ" => E ⊗[X.functionField] Y.functionField

set_option quotPrecheck false in
local notation "ιL" => (Algebra.TensorProduct.includeRight : Y.functionField →ₐ[X.functionField] Tₚ)

set_option quotPrecheck false in
local notation "ιE" => (Algebra.TensorProduct.includeLeftRingHom : E →+* Tₚ)

set_option quotPrecheck false in
local notation "πY" => Spec.map (CommRingCat.ofHom (ιL).toRingHom) ≫
  Y.fromSpecStalk (genericPoint Y)

set_option quotPrecheck false in
local notation "πE" => Spec.map (CommRingCat.ofHom ιE)

set_option quotPrecheck false in
local notation "bE" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField E)) ≫
  X.fromSpecStalk (genericPoint X)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap X.functionField Y.functionField = (functionFieldMapOfDominant p).hom := rfl

example (e : E) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ιE e = e ⊗ₜ[X.functionField] (1 : Y.functionField) := rfl

example (l : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ιL l = (1 : E) ⊗ₜ[X.functionField] l := rfl

example (k : X.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ιE (algebraMap X.functionField E k) = ιL ((functionFieldMapOfDominant p).hom k) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  exact RingHom.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := X.functionField) (A := E) (B := Y.functionField)) k

example (e : E) (l : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ιE e * ιL l = e ⊗ₜ[X.functionField] l := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  change (e ⊗ₜ[X.functionField] (1 : Y.functionField)) *
    ((1 : E) ⊗ₜ[X.functionField] l) = e ⊗ₜ[X.functionField] l
  simp

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsPullback πY πE p bE := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  fail_if_success have _ : Field E := inferInstance
  fail_if_success have _ : IsDomain E := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : Algebra.IsSeparable X.functionField Y.functionField := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  fail_if_success
    have _ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun _ => inferInstance
  exact functionFieldMapOfDominant_baseChange_isPullback p E

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    πY ≫ p = πE ≫ bE :=
  (functionFieldMapOfDominant_baseChange_isPullback p E).w

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Nonempty (Spec (CommRingCat.of Tₚ) ≅ pullback p bE) :=
  ⟨(functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.hom ≫
      pullback.fst p bE = πY :=
  (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback_hom_fst

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.hom ≫
      pullback.snd p bE = πE :=
  (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback_hom_snd

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.inv ≫
      πY = pullback.fst p bE :=
  (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback_inv_fst

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.inv ≫
      πE = pullback.snd p bE :=
  (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback_inv_snd

example {W : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ Spec (CommRingCat.of E))
    (h : a ≫ p = b ≫ bE) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldMapOfDominant_baseChange_isPullback p E).lift a b h ≫ πY = a ∧
      (functionFieldMapOfDominant_baseChange_isPullback p E).lift a b h ≫ πE = b :=
  ⟨(functionFieldMapOfDominant_baseChange_isPullback p E).lift_fst a b h,
    (functionFieldMapOfDominant_baseChange_isPullback p E).lift_snd a b h⟩

example {W : Scheme.{u}} (a : W ⟶ Y) (b : W ⟶ Spec (CommRingCat.of E))
    (h : a ≫ p = b ≫ bE) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∃! k : W ⟶ Spec (CommRingCat.of Tₚ), k ≫ πY = a ∧ k ≫ πE = b := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  let square := functionFieldMapOfDominant_baseChange_isPullback p E
  refine ⟨square.lift a b h, ⟨square.lift_fst a b h, square.lift_snd a b h⟩, ?_⟩
  intro k hk
  exact square.hom_ext (hk.1.trans (square.lift_fst a b h).symm)
    (hk.2.trans (square.lift_snd a b h).symm)

example {W : Scheme.{u}} :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ a b : W ⟶ Spec (CommRingCat.of Tₚ),
      a ≫ πY = b ≫ πY → a ≫ πE = b ≫ πE → a = b := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro a b hY hE
  exact (functionFieldMapOfDominant_baseChange_isPullback p E).hom_ext hY hE

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ z : Spec (CommRingCat.of Tₚ), p.base ((πY).base z) = (bE).base ((πE).base z) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro z
  exact congrArg (fun f : Spec (CommRingCat.of Tₚ) ⟶ X => f.base z)
    (functionFieldMapOfDominant_baseChange_isPullback p E).w

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.hom ≫
        (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.inv =
          𝟙 (Spec (CommRingCat.of Tₚ)) ∧
      (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.inv ≫
        (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.hom =
          𝟙 (pullback p bE) :=
  ⟨(functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.hom_inv_id,
    (functionFieldMapOfDominant_baseChange_isPullback p E).isoPullback.inv_hom_id⟩

example (F : Type u) [Field F] [Algebra X.functionField F] :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Y.functionField →ₐ[X.functionField]
          F ⊗[X.functionField] Y.functionField).toRingHom) ≫
        Y.fromSpecStalk (genericPoint Y))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        F →+* F ⊗[X.functionField] Y.functionField))) p
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField F)) ≫
        X.fromSpecStalk (genericPoint X)) :=
  functionFieldMapOfDominant_baseChange_isPullback p F

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ¬ IsField (Polynomial X.functionField) ∧
      IsPullback
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Y.functionField →ₐ[X.functionField]
            Polynomial X.functionField ⊗[X.functionField] Y.functionField).toRingHom) ≫
          Y.fromSpecStalk (genericPoint Y))
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          Polynomial X.functionField →+*
            Polynomial X.functionField ⊗[X.functionField] Y.functionField))) p
        (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Polynomial X.functionField))) ≫
          X.fromSpecStalk (genericPoint X)) :=
  ⟨Polynomial.not_isField X.functionField,
    functionFieldMapOfDominant_baseChange_isPullback p (Polynomial X.functionField)⟩

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_baseChange_isPullback]
  unless declarations.length == 1 && declarations.eraseDups.length == 1 do
    throwError "Expected exactly one SP98 public declaration"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP98 audit registry: one public declaration"
