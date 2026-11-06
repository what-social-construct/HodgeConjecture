module

import HodgeConjecture.Boundary.Normalization.GenericSplitFiberAction
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP100 focused checks for the original sheet evaluations and normalization
action. Run with
`lake env lean research/GenericSplitFiberActionVerification.lean`.

The notation below only abbreviates the original field, subgroup, evaluation
maps, generic-point map, and refinement. Each sheet retains both actual
pullback projections. The action comparison uses the inverse convention,
is independent of the chosen coset representative, recovers the base sheet,
and specializes to finite étale morphisms. The orbit comparison itself does
not require formal unramifiedness; the split-fiber statements do. Only the
upstairs normal-stalk hypothesis is supplied where the existing refinement
requires it. Exactly four public APIs receive a standard-three axiom audit.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles

noncomputable section

universe u

#check functionFieldNormalClosureSplitFiberIso_eval_fst
#check functionFieldNormalClosureSplitFiberIso_eval_snd
#check functionFieldNormalClosureSheetPoint_eq_normalizationOrbit
#check functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

set_option quotPrecheck false in
local notation "Hₚ" => (functionFieldNormalClosureData p).intermediateFixingSubgroup

set_option quotPrecheck false in
local notation "Gₚ" => (functionFieldNormalClosureData p).galoisGroup

set_option quotPrecheck false in
local notation "bN" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Nₚ)) ≫
  X.fromSpecStalk (genericPoint X)

set_option quotPrecheck false in
local notation "eₚ" => (fun s : GaloisSheets Hₚ =>
  Spec.map (CommRingCat.ofHom
    (Pi.evalAlgHom Nₚ (fun _ : GaloisSheets Hₚ => Nₚ) s).toRingHom))

set_option quotPrecheck false in
local notation "mₚ" => (fun s : GaloisSheets Hₚ =>
  Spec.map (CommRingCat.ofHom
    ((functionFieldNormalClosureData p).sheetEmbedding s).toRingHom) ≫
    Y.fromSpecStalk (genericPoint Y))

set_option quotPrecheck false in
local notation "jN" => Spec.map (CommRingCat.ofHom
  (gluedNormalizationFunctionFieldEquiv X Nₚ).toRingHom) ≫
  (gluedNormalizationModel X Nₚ).fromSpecStalk (genericPoint (gluedNormalizationModel X Nₚ))

section Evaluation

variable [FormallyUnramified p]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ s : GaloisSheets Hₚ,
      (eₚ s ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
        pullback.fst p bN = mₚ s := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success have _ : IsNoetherian Y := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  fail_if_success
    have _ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y) := fun _ => inferInstance
  exact functionFieldNormalClosureSplitFiberIso_eval_fst p

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ s : GaloisSheets Hₚ,
      (eₚ s ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
        pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) :=
  functionFieldNormalClosureSplitFiberIso_eval_snd p

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ s : GaloisSheets Hₚ, ∃! q : Spec (.of Nₚ) ⟶ pullback p bN,
      q ≫ pullback.fst p bN = mₚ s ∧
        q ≫ pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro s
  refine ⟨eₚ s ≫ (functionFieldNormalClosureSplitFiberIso p).hom, ?_, ?_⟩
  · exact ⟨functionFieldNormalClosureSplitFiberIso_eval_fst p s,
      functionFieldNormalClosureSplitFiberIso_eval_snd p s⟩
  · intro q hq
    apply pullback.hom_ext
    · exact hq.1.trans (functionFieldNormalClosureSplitFiberIso_eval_fst p s).symm
    · exact hq.2.trans (functionFieldNormalClosureSplitFiberIso_eval_snd p s).symm

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    eₚ (baseSheet Hₚ) = Spec.map (CommRingCat.ofHom
      (functionFieldNormalClosureData p).normalClosureBaseSheetAugmentation.toRingHom) := rfl

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (eₚ (baseSheet Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
      pullback.fst p bN =
        Spec.map (CommRingCat.ofHom (functionFieldNormalClosureData p).embedding.toRingHom) ≫
          Y.fromSpecStalk (genericPoint Y) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [functionFieldNormalClosureSplitFiberIso_eval_fst]
  rw [NormalClosureData.sheetEmbedding_baseSheet]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ g h : Gₚ, (g : GaloisSheets Hₚ) = (h : GaloisSheets Hₚ) →
      eₚ (g : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom =
        eₚ (h : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro g h hgh
  rw [hgh]

end Evaluation

-- These are derived bridges for the existing function-field comparison,
-- not additional hypotheses on the cover or the base.
local instance verificationOrbitBaseSurjective
    (N : Type u) [Field N] [Algebra X.functionField N]
    [FiniteDimensional X.functionField N] : Surjective (gluedNormalizationToBase X N) :=
  gluedNormalizationToBase_surjective X N

local instance verificationOrbitFieldAlgebra
    (N : Type u) [Field N] [Algebra X.functionField N]
    [FiniteDimensional X.functionField N] :
    Algebra X.functionField (gluedNormalizationModel X N).functionField :=
  (functionFieldMapOfDominant (gluedNormalizationToBase X N)).hom.toAlgebra

variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))

set_option quotPrecheck false in
local notation "oₚ" => (fun g : Gₚ =>
  jN ≫ (gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫ gluedNormalClosureToCover p hY)

section Orbit

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : Gₚ, mₚ (g : GaloisSheets Hₚ) = oₚ g := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  fail_if_success have _ : FormallyUnramified p := inferInstance
  fail_if_success have _ : Etale p := inferInstance
  fail_if_success have _ : PerfectField X.functionField := inferInstance
  fail_if_success have _ : IsNoetherian X := inferInstance
  fail_if_success
    have _ : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := fun _ => inferInstance
  exact functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : Gₚ, mₚ ((g⁻¹ : Gₚ) : GaloisSheets Hₚ) =
      jN ≫ (gluedNormalizationAutomorphism X Nₚ g).hom ≫ gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g
  simpa only [inv_inv] using
    functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY g⁻¹

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    mₚ (baseSheet Hₚ) = jN ≫ gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  simpa only [inv_one, gluedNormalizationAutomorphism_one, Category.id_comp] using
    functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY (1 : Gₚ)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ s : GaloisSheets Hₚ, mₚ s = oₚ s.out := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro s
  simpa only [Quotient.out_eq'] using
    functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY s.out

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g h : Gₚ, (g : GaloisSheets Hₚ) = (h : GaloisSheets Hₚ) → oₚ g = oₚ h := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g h hgh
  dsimp only
  rw [← functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY g,
    ← functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY h, hgh]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g h : Gₚ, mₚ ((g * h : Gₚ) : GaloisSheets Hₚ) =
      jN ≫ (gluedNormalizationAutomorphism X Nₚ g⁻¹).hom ≫
        (gluedNormalizationAutomorphism X Nₚ h⁻¹).hom ≫ gluedNormalClosureToCover p hY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g h
  dsimp only
  rw [functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY,
    mul_inv_rev, gluedNormalizationAutomorphism_mul]
  simp only [Category.assoc]

end Orbit

section SplitOrbit

variable [FormallyUnramified p]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : Gₚ, ∀ h : oₚ g ≫ p = (𝟙 (Spec (.of Nₚ))) ≫ bN,
      eₚ (g : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom =
        pullback.lift (oₚ g) (𝟙 (Spec (.of Nₚ))) h := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g h
  exact functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit p hY g

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : Gₚ,
      (eₚ (g : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
        pullback.fst p bN = oₚ g ∧
      (eₚ (g : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
        pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g
  constructor
  · rw [functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit p hY,
      pullback.lift_fst]
  · exact functionFieldNormalClosureSplitFiberIso_eval_snd p _

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : Gₚ, ∀ h :
      (jN ≫ (gluedNormalizationAutomorphism X Nₚ g).hom ≫ gluedNormalClosureToCover p hY) ≫
        p = (𝟙 (Spec (.of Nₚ))) ≫ bN,
      eₚ ((g⁻¹ : Gₚ) : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom =
        pullback.lift
          (jN ≫ (gluedNormalizationAutomorphism X Nₚ g).hom ≫ gluedNormalClosureToCover p hY)
          (𝟙 (Spec (.of Nₚ))) h := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro g h
  simpa only [inv_inv] using
    functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit p hY g⁻¹

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ s : GaloisSheets Hₚ, ∀ h : oₚ s.out ≫ p = (𝟙 (Spec (.of Nₚ))) ≫ bN,
      eₚ s ≫ (functionFieldNormalClosureSplitFiberIso p).hom =
        pullback.lift (oₚ s.out) (𝟙 (Spec (.of Nₚ))) h := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  intro s h
  simpa only [Quotient.out_eq'] using
    functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit p hY s.out

end SplitOrbit

section Etale

variable [Etale p]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    ∀ g : Gₚ, ∀ h : oₚ g ≫ p = (𝟙 (Spec (.of Nₚ))) ≫ bN,
      eₚ (g : GaloisSheets Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom =
        pullback.lift (oₚ g) (𝟙 (Spec (.of Nₚ))) h := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  have _ : FormallyUnramified p := inferInstance
  intro g h
  exact functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit p hY g

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    letI : FiniteDimensional X.functionField Nₚ :=
      (functionFieldNormalClosureData p).finiteNormal
    (eₚ (baseSheet Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
      pullback.fst p bN = jN ≫ gluedNormalClosureToCover p hY ∧
    (eₚ (baseSheet Hₚ) ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
      pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  letI : FiniteDimensional X.functionField Nₚ :=
    (functionFieldNormalClosureData p).finiteNormal
  constructor
  · rw [functionFieldNormalClosureSplitFiberIso_eval_fst]
    simpa only [inv_one, gluedNormalizationAutomorphism_one, Category.id_comp] using
      functionFieldNormalClosureSheetPoint_eq_normalizationOrbit p hY (1 : Gₚ)
  · exact functionFieldNormalClosureSplitFiberIso_eval_snd p _

end Etale

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso_eval_fst,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso_eval_snd,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSheetPoint_eq_normalizationOrbit,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso_eval_eq_normalizationOrbit]
  unless declarations.length == 4 && declarations.eraseDups.length == 4 do
    throwError "Expected exactly four distinct SP100 public declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP100 audit registry: four distinct public declarations"
