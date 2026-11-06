-- This dependency audit loads private imported proof bodies (legacy import mode).
import HodgeConjecture.Boundary.Normalization.GenericSplitFiber
import HodgeConjecture.Collision.AffineGeometry
import Lean.Util.CollectAxioms
import HodgeConjecture.MathlibCompat.DeclarationDependencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP99 focused checks for splitting the actual generic fiber over the original
normal-closure field. Run with
`lake env lean research/GenericSplitFiberVerification.lean`.

The local notation expands to the existing normal closure, fixing subgroup,
sheet algebra, and original marked embedding. Tests retain both actual
pullback projections, their inverse formulas, and the marked base-sheet point.
Finite dominant formally unramified morphisms suffice: no étaleness,
normality, perfectness, or Noetherianity is supplied to the main examples.
A separate finite-étale specialization checks automatic unramified inference.
The registry audits exactly the four new public declarations, including the
isomorphism definition, against the standard-three Lean axiom allowlist.
An additional transitive declaration audit checks the direction from
formal unramifiedness to separability to splitting, with the later project
splitting and affine collision constructions absent from separability's
dependency closure even though they are imported here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HodgeConjecture
open HodgeConjecture.CollisionFoundations HodgeConjecture.SchemeCycles

noncomputable section

universe u

#check functionFieldNormalClosureSplitFiberIso
#check functionFieldNormalClosureSplitFiberIso_hom_fst
#check functionFieldNormalClosureSplitFiberIso_hom_snd
#check functionFieldNormalClosureSplitFiberIso_baseSheet

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (p : Y ⟶ X) [IsDominant p] [IsFinite p]

set_option quotPrecheck false in
local notation "Nₚ" => IntermediateField.normalClosure X.functionField Y.functionField
  (AlgebraicClosure Y.functionField)

set_option quotPrecheck false in
local notation "Hₚ" => (functionFieldNormalClosureData p).intermediateFixingSubgroup

set_option quotPrecheck false in
local notation "Sₚ" => GenericSheetAlgebra Nₚ Hₚ

set_option quotPrecheck false in
local notation "bN" => Spec.map (CommRingCat.ofHom (algebraMap X.functionField Nₚ)) ≫
  X.fromSpecStalk (genericPoint X)

set_option quotPrecheck false in
local notation "πY" => Spec.map (CommRingCat.ofHom
  (Pi.algHom X.functionField (fun _ : GaloisSheets Hₚ => Nₚ)
    (functionFieldNormalClosureData p).sheetEmbedding).toRingHom) ≫
  Y.fromSpecStalk (genericPoint Y)

set_option quotPrecheck false in
local notation "πN" => Spec.map (CommRingCat.ofHom (algebraMap Nₚ Sₚ))

set_option quotPrecheck false in
local notation "a₀" => Spec.map (CommRingCat.ofHom
  (functionFieldNormalClosureData p).normalClosureBaseSheetAugmentation.toRingHom)

set_option quotPrecheck false in
local notation "mY" => Spec.map (CommRingCat.ofHom
  (functionFieldNormalClosureData p).embedding.toRingHom) ≫
  Y.fromSpecStalk (genericPoint Y)

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    algebraMap X.functionField Y.functionField = (functionFieldMapOfDominant p).hom := rfl

example (y : Y.functionField) :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ((functionFieldNormalClosureData p).embedding y : AlgebraicClosure Y.functionField) =
      algebraMap Y.functionField (AlgebraicClosure Y.functionField) y :=
  functionFieldNormalClosureData_embedding_apply p y

section FormallyUnramified

variable [FormallyUnramified p]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Nonempty (Spec (.of Sₚ) ≅ pullback p bN) := by
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
  exact ⟨functionFieldNormalClosureSplitFiberIso p⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).hom ≫ pullback.fst p bN = πY :=
  functionFieldNormalClosureSplitFiberIso_hom_fst p

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).hom ≫ pullback.snd p bN = πN :=
  functionFieldNormalClosureSplitFiberIso_hom_snd p

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).inv ≫ πY = pullback.fst p bN := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← functionFieldNormalClosureSplitFiberIso_hom_fst p, Iso.inv_hom_id_assoc]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).inv ≫ πN = pullback.snd p bN := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← functionFieldNormalClosureSplitFiberIso_hom_snd p, Iso.inv_hom_id_assoc]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    πY ≫ p = πN ≫ bN := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← functionFieldNormalClosureSplitFiberIso_hom_fst p,
    ← functionFieldNormalClosureSplitFiberIso_hom_snd p, Category.assoc,
    pullback.condition, ← Category.assoc]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ h : mY ≫ p = (𝟙 (Spec (.of Nₚ))) ≫ bN,
      a₀ ≫ (functionFieldNormalClosureSplitFiberIso p).hom =
        pullback.lift mY (𝟙 (Spec (.of Nₚ))) h := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro h
  exact functionFieldNormalClosureSplitFiberIso_baseSheet p

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (a₀ ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
      pullback.fst p bN = mY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_fst]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (a₀ ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
      pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_snd]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    a₀ ≫ πY = mY := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← functionFieldNormalClosureSplitFiberIso_hom_fst p, ← Category.assoc,
    functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_fst]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    a₀ ≫ πN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [← functionFieldNormalClosureSplitFiberIso_hom_snd p, ← Category.assoc,
    functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_snd]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∀ h : mY ≫ p = (𝟙 (Spec (.of Nₚ))) ≫ bN,
      pullback.lift mY (𝟙 (Spec (.of Nₚ))) h ≫
        (functionFieldNormalClosureSplitFiberIso p).inv = a₀ := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  intro h
  rw [← functionFieldNormalClosureSplitFiberIso_baseSheet p, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    ∃! q : Spec (.of Nₚ) ⟶ pullback p bN,
      q ≫ pullback.fst p bN = mY ∧
        q ≫ pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  refine ⟨a₀ ≫ (functionFieldNormalClosureSplitFiberIso p).hom, ?_, ?_⟩
  · constructor
    · rw [functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_fst]
    · rw [functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_snd]
  · intro q hq
    apply pullback.hom_ext
    · rw [functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_fst]
      exact hq.1
    · rw [functionFieldNormalClosureSplitFiberIso_baseSheet p, pullback.lift_snd]
      exact hq.2

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (functionFieldNormalClosureSplitFiberIso p).hom ≫
        (functionFieldNormalClosureSplitFiberIso p).inv = 𝟙 (Spec (.of Sₚ)) ∧
      (functionFieldNormalClosureSplitFiberIso p).inv ≫
        (functionFieldNormalClosureSplitFiberIso p).hom = 𝟙 (pullback p bN) :=
  ⟨(functionFieldNormalClosureSplitFiberIso p).hom_inv_id,
    (functionFieldNormalClosureSplitFiberIso p).inv_hom_id⟩

end FormallyUnramified

section Etale

variable [Etale p]

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    Nonempty (Spec (.of Sₚ) ≅ pullback p bN) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  have _ : FormallyUnramified p := inferInstance
  exact ⟨functionFieldNormalClosureSplitFiberIso p⟩

example :
    letI : Algebra X.functionField Y.functionField :=
      (functionFieldMapOfDominant p).hom.toAlgebra
    (a₀ ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
      pullback.fst p bN = mY ∧
        (a₀ ≫ (functionFieldNormalClosureSplitFiberIso p).hom) ≫
          pullback.snd p bN = 𝟙 (Spec (.of Nₚ)) := by
  letI : Algebra X.functionField Y.functionField :=
    (functionFieldMapOfDominant p).hom.toAlgebra
  rw [functionFieldNormalClosureSplitFiberIso_baseSheet p,
    pullback.lift_fst, pullback.lift_snd]
  exact ⟨rfl, rfl⟩

end Etale

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso_hom_fst,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso_hom_snd,
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso_baseSheet]
  unless declarations.length == 4 && declarations.eraseDups.length == 4 do
    throwError "Expected exactly four distinct SP99 public declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP99 audit registry: four distinct public declarations"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let separability :=
    `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_isSeparable
  let splitting :=
    `HodgeConjecture.CollisionFoundations.functionFieldNormalClosureSplitFiberIso
  let equivalence :=
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorGenericSheetsEquiv
  let forbidden := [equivalence,
    `HodgeConjecture.CollisionFoundations.NormalClosureData.normalClosureTensorToGenericSheets_bijective,
    `HodgeConjecture.affineSelfCollisionDecompositionOfFormallyUnramified,
    splitting]
  let predecessors := [
    `HodgeConjecture.CollisionFoundations.functionFieldMapOfDominant_formallyUnramified,
    `Algebra.FormallyUnramified.isSeparable]
  for declaration in separability :: forbidden ++ predecessors do
    unless env.contains declaration do
      throwError "Missing dependency-audit declaration {declaration}"
  let separabilityDependencies := HodgeConjecture.Research.declarationDependencies env separability
  for declaration in forbidden do
    if separabilityDependencies.contains declaration then
      throwError "Unexpected downstream dependency of separability: {declaration}"
  for declaration in predecessors do
    unless separabilityDependencies.contains declaration do
      throwError "Missing established separability predecessor {declaration}"
  logInfo m!"PASS SP99 separability dependency boundary: established predecessors {predecessors}; absent downstream declarations {forbidden}"
  let splittingDependencies := HodgeConjecture.Research.declarationDependencies env splitting
  for declaration in [separability, equivalence] do
    unless splittingDependencies.contains declaration do
      throwError "Missing expected forward splitting dependency {declaration}"
  logInfo "PASS SP99 splitting dependency direction: the split-fiber isomorphism depends on established separability and the tensor equivalence"
