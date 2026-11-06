module

import HodgeConjecture.Boundary.Normalization.SeparableFunctionField
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
Regressions for separability of the actual generic-stalk field extension.
Run with `lake env lean research/SeparableFunctionFieldVerification.lean`.

Affine formal unramifiedness is tested without finiteness or étaleness.
Separability is then tested under finite formal-unramified and finite étale
hypotheses, always with the algebra induced by the actual dominant map.
Normality, perfectness, characteristic zero and Noetherianity are not inputs.
Every new declaration has an enforced standard-axiom allowlist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory HodgeConjecture
open HodgeConjecture.SchemeCycles HodgeConjecture.CollisionFoundations

noncomputable section

universe u

section MinimalHypotheses

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [FormallyUnramified p]

example [IsAffineHom p] (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Y.functionField := by
  fail_if_success have _ : IsFinite p := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : IsNoetherianRing Γ(X, U) := inferInstance
  exact functionFieldMapOfDominant_formallyUnramified_of_affine p U hU

-- The global affine theorem selects a nonempty affine chart internally.
example [IsAffineHom p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Y.functionField :=
  functionFieldMapOfDominant_formallyUnramified p

-- Finiteness supplies affineness, without supplying étaleness or normality.
example [IsFinite p] (U : X.Opens) [Nonempty U] (hU : IsAffineOpen U) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Y.functionField := by
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : IsIntegrallyClosed Γ(X, U) := inferInstance
  exact functionFieldMapOfDominant_formallyUnramified_of_affine p U hU

example [IsFinite p] :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.IsSeparable X.functionField Y.functionField := by
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : CharZero X.functionField := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  exact functionFieldMapOfDominant_isSeparable p

-- The class provides separability of each actual upstairs rational function.
example [IsFinite p] (a : Y.functionField) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    IsSeparable X.functionField a := by
  letI := (functionFieldMapOfDominant p).hom.toAlgebra
  letI := functionFieldMapOfDominant_isSeparable p
  exact Algebra.IsSeparable.isSeparable X.functionField a

end MinimalHypotheses

section EtaleSpecialization

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p] [Etale p]

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Y.functionField :=
  functionFieldMapOfDominant_formallyUnramified p

example :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    Algebra.IsSeparable X.functionField Y.functionField :=
  functionFieldMapOfDominant_isSeparable p

-- The action is the actual map, not a separately chosen field extension.
example (a : X.functionField) :
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap X.functionField Y.functionField a = functionFieldMapOfDominant p a := rfl

example (U : X.Opens) [Nonempty U] :
    letI := nonempty_preimage_of_isDominant p U
    letI : Algebra Γ(X, U) Y.functionField :=
      ((Y.germToFunctionField (p ⁻¹ᵁ U)).hom.comp (p.app U).hom).toAlgebra
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    IsScalarTower Γ(X, U) X.functionField Y.functionField ∧
      Algebra.IsSeparable X.functionField Y.functionField :=
  ⟨functionFieldMapOfDominant_sectionScalarTower p U,
    functionFieldMapOfDominant_isSeparable p⟩

-- Under that same separable action, actual section pullback still commutes.
example (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    letI := nonempty_preimage_of_isDominant p U
    letI := (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap X.functionField Y.functionField ((X.germToFunctionField U) a) =
      Y.germToFunctionField (p ⁻¹ᵁ U) ((p.app U) a) := by
  letI := nonempty_preimage_of_isDominant p U
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (functionFieldMapOfDominant_germ p U)) a

end EtaleSpecialization

section Composition

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
variable (p : Y ⟶ X) (q : Z ⟶ Y) [IsDominant p] [IsDominant q]
variable [FormallyUnramified p] [FormallyUnramified q]

example [IsAffineHom p] [IsAffineHom q] :
    letI := (functionFieldMapOfDominant (q ≫ p)).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField Z.functionField := by
  letI : FormallyUnramified (q ≫ p) :=
    MorphismProperty.comp_mem _ q p inferInstance inferInstance
  exact functionFieldMapOfDominant_formallyUnramified (q ≫ p)

example [IsFinite p] [IsFinite q] :
    letI := (functionFieldMapOfDominant (q ≫ p)).hom.toAlgebra
    Algebra.IsSeparable X.functionField Z.functionField := by
  letI : FormallyUnramified (q ≫ p) :=
    MorphismProperty.comp_mem _ q p inferInstance inferInstance
  exact functionFieldMapOfDominant_isSeparable (q ≫ p)

-- Replacing the composite's map by the proved composite ring map changes nothing.
example [IsFinite p] [IsFinite q] :
    letI := ((functionFieldMapOfDominant q).hom.comp
      (functionFieldMapOfDominant p).hom).toAlgebra
    Algebra.IsSeparable X.functionField Z.functionField := by
  letI : FormallyUnramified (q ≫ p) :=
    MorphismProperty.comp_mem _ q p inferInstance inferInstance
  have h := functionFieldMapOfDominant_isSeparable (q ≫ p)
  rw [functionFieldMapOfDominant_comp] at h
  exact h

end Composition

-- Actual identity morphisms check the canonical self-action specializations.
example (X : Scheme.{u}) [IsIntegral X] :
    letI := (functionFieldMapOfDominant (𝟙 X)).hom.toAlgebra
    Algebra.FormallyUnramified X.functionField X.functionField :=
  functionFieldMapOfDominant_formallyUnramified (𝟙 X)

example (X : Scheme.{u}) [IsIntegral X] :
    letI := (functionFieldMapOfDominant (𝟙 X)).hom.toAlgebra
    Algebra.IsSeparable X.functionField X.functionField :=
  functionFieldMapOfDominant_isSeparable (𝟙 X)

example :
    let X := Spec (CommRingCat.of ℚ)
    letI := (functionFieldMapOfDominant (𝟙 X)).hom.toAlgebra
    Algebra.IsSeparable X.functionField X.functionField :=
  functionFieldMapOfDominant_isSeparable (𝟙 (Spec (CommRingCat.of ℚ)))

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_formallyUnramified_of_affine,
      `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_formallyUnramified,
      `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_isSeparable] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-axiom boundary: {declaration}; {axioms.toList}"
