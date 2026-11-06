-- This dependency audit loads private imported proof bodies (legacy import mode).
import HodgeConjecture.Realization.Chow.UpstairsGeneration
import Lean.Util.CollectAxioms
import HodgeConjecture.MathlibCompat.DeclarationDependencies

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP94 focused checks for specified upstairs recipes and normalized descent.
Run with `lake env lean research/UpstairsGenerationVerification.lean`.

The fixtures below are rational linear models, not geometric realizations.
They test the class quantifiers, actual normalized representative, missing
surjectivity hypotheses, and the separation of generation from transfer.
No finite cover, deck action, or positive-dimensional Chow--Betti model is
constructed by these tests.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

open HodgeConjecture

noncomputable section

universe u v w x y z

#check HodgePullbackGeneratedBy
#check hodgePullbackGeneratedBy_iff
#check normalizedPushforward_cycleClass
#check rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy
#check ClassDependentChowBettiGeneration
#check classDependentChowBettiGeneration_of_fixed
#check rationalHodgeConjectureAt_of_classDependentChowBettiGeneration

section GeneralContracts

variable {ChowX : Type u} {HX : Type v} {ChowY : Type w} {HY : Type x} {C : Type y}
variable [AddCommGroup ChowX] [Module ℚ ChowX] [AddCommGroup HX] [Module ℚ HX]
variable [AddCommGroup ChowY] [Module ℚ ChowY] [AddCommGroup HY] [Module ℚ HY]
variable [AddCommGroup C] [Module ℚ C]
variable (M : RationalHodgeCycleClassModel ChowX HX)
variable (clY : ChowY →ₗ[ℚ] HY) (pull : HX →ₗ[ℚ] HY) (recipe : C →ₗ[ℚ] ChowY)

example (generation : HodgePullbackGeneratedBy M clY pull recipe)
    (α : HX) (hα : IsRationalHodgeClass M α) :
    ∃ c : C, clY (recipe c) = pull α :=
  (hodgePullbackGeneratedBy_iff M clY pull recipe).mp generation α hα

example (generation : ∀ α : HX, IsRationalHodgeClass M α →
      ∃ c : C, clY (recipe c) = pull α) :
    HodgePullbackGeneratedBy M clY pull recipe :=
  (hodgePullbackGeneratedBy_iff M clY pull recipe).mpr generation

example (T : RationalDegreeTransfer HY HX) (pushCH : ChowY →ₗ[ℚ] ChowX)
    (hPush : M.cycleClass.comp pushCH = T.push.comp clY)
    (z : ChowY) (α : HX) (hz : clY z = T.pull α) :
    M.cycleClass ((T.degree : ℚ)⁻¹ • pushCH z) = α :=
  normalizedPushforward_cycleClass M clY T pushCH hPush z α hz

-- No upstairs Hodge model, recipe surjectivity, projector or group is an input.
example (T : RationalDegreeTransfer HY HX) (pushCH : ChowY →ₗ[ℚ] ChowX)
    (hPush : M.cycleClass.comp pushCH = T.push.comp clY)
    (generation : HodgePullbackGeneratedBy M clY T.pull recipe) :
    RationalHodgeConjectureAt M :=
  rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy
    M clY T pushCH hPush recipe generation

end GeneralContracts

section DependentContracts

variable {ChowX : Type u} {HX : Type v} {I : Type z}
variable {ChowY : I → Type w} {HY : I → Type x} {C : I → Type y}
variable [AddCommGroup ChowX] [Module ℚ ChowX] [AddCommGroup HX] [Module ℚ HX]
variable [∀ i, AddCommGroup (ChowY i)] [∀ i, Module ℚ (ChowY i)]
variable [∀ i, AddCommGroup (HY i)] [∀ i, Module ℚ (HY i)]
variable [∀ i, AddCommGroup (C i)] [∀ i, Module ℚ (C i)]
variable (M : RationalHodgeCycleClassModel ChowX HX)
variable (clY : ∀ i, ChowY i →ₗ[ℚ] HY i)
variable (pull : ∀ i, HX →ₗ[ℚ] HY i) (recipe : ∀ i, C i →ₗ[ℚ] ChowY i)

example (i : I) (generation : HodgePullbackGeneratedBy M (clY i) (pull i) (recipe i)) :
    ClassDependentChowBettiGeneration M clY pull recipe :=
  classDependentChowBettiGeneration_of_fixed M clY pull recipe i generation

example (T : ∀ i, RationalDegreeTransfer (HY i) HX)
    (pushCH : ∀ i, ChowY i →ₗ[ℚ] ChowX)
    (hPush : ∀ i, M.cycleClass.comp (pushCH i) = (T i).push.comp (clY i))
    (generation : ClassDependentChowBettiGeneration M clY (fun i => (T i).pull) recipe) :
    RationalHodgeConjectureAt M :=
  rationalHodgeConjectureAt_of_classDependentChowBettiGeneration
    M clY T pushCH hPush recipe generation

-- The chosen index is allowed to depend on the specified class.
example (generation : ClassDependentChowBettiGeneration M clY pull recipe)
    (α : HX) (hα : IsRationalHodgeClass M α) :
    ∃ i, ∃ c : C i, clY i (recipe i c) = pull i α :=
  generation α hα

end DependentContracts

namespace UpstairsGenerationVerification

private def fullModel (H : Type u) [AddCommGroup H] [Module ℚ H] :
    RationalHodgeCycleClassModel H H where
  hodgeClasses := ⊤
  cycleClass := LinearMap.id
  cycleClass_lands := le_top

private def zeroCycleModel : RationalHodgeCycleClassModel ℚ ℚ where
  hodgeClasses := ⊤
  cycleClass := 0
  cycleClass_lands := le_top

private def zeroHodgeModel : RationalHodgeCycleClassModel ℚ ℚ where
  hodgeClasses := ⊥
  cycleClass := 0
  cycleClass_lands := by simp

private def identityTransfer (H : Type u) [AddCommGroup H] [Module ℚ H] :
    RationalDegreeTransfer H H where
  pull := LinearMap.id
  push := LinearMap.id
  degree := 1
  degree_ne_zero := by decide
  push_comp_pull := by simp

private def doubleTransfer : RationalDegreeTransfer ℚ ℚ where
  pull := LinearMap.id
  push := (2 : ℚ) • LinearMap.id
  degree := 2
  degree_ne_zero := by decide
  push_comp_pull := by simp

private def leftTransfer : RationalDegreeTransfer (ℚ × ℚ) ℚ where
  pull := LinearMap.inl ℚ ℚ ℚ
  push := LinearMap.fst ℚ ℚ ℚ
  degree := 1
  degree_ne_zero := by decide
  push_comp_pull := by apply LinearMap.ext; intro q; simp

private theorem identityGeneration (H : Type u) [AddCommGroup H] [Module ℚ H] :
    HodgePullbackGeneratedBy (fullModel H) LinearMap.id LinearMap.id LinearMap.id := by
  rw [hodgePullbackGeneratedBy_iff]
  intro α _
  exact ⟨α, rfl⟩

example : HodgePullbackGeneratedBy (fullModel ℚ)
    LinearMap.id LinearMap.id LinearMap.id := identityGeneration ℚ

example : ¬ HodgePullbackGeneratedBy (fullModel ℚ)
    LinearMap.id LinearMap.id (0 : ℚ →ₗ[ℚ] ℚ) := by
  intro h
  obtain ⟨c, hc⟩ := (hodgePullbackGeneratedBy_iff _ _ _ _).mp h 1 (by trivial)
  norm_num at hc

-- The zero Hodge subspace needs only its zero class, not all upstairs classes.
example : HodgePullbackGeneratedBy zeroHodgeModel
    LinearMap.id LinearMap.id (0 : ℚ →ₗ[ℚ] ℚ) := by
  rw [hodgePullbackGeneratedBy_iff]
  intro α hα
  have hzero : α = 0 := hα
  exact ⟨0, by simp [hzero]⟩

-- Generation alone is deliberately not a descent theorem: zero pullback
-- loses every class if the positive-degree transfer law is unavailable.
example : HodgePullbackGeneratedBy zeroCycleModel
    (0 : ℚ →ₗ[ℚ] ℚ) 0 (0 : ℚ →ₗ[ℚ] ℚ) := by
  rw [hodgePullbackGeneratedBy_iff]
  intro α _
  exact ⟨0, rfl⟩

example : ¬ RationalHodgeConjectureAt zeroCycleModel := by
  intro h
  obtain ⟨z, hz⟩ := h (show (1 : ℚ) ∈ zeroCycleModel.hodgeClasses from by trivial)
  norm_num [zeroCycleModel] at hz

example : ¬ ∃ T : RationalDegreeTransfer ℚ ℚ, T.pull = 0 := by
  rintro ⟨T, hpull⟩
  have h := LinearMap.congr_fun T.push_comp_pull 1
  have hd : (T.degree : ℚ) ≠ 0 := by exact_mod_cast T.degree_ne_zero
  rw [hpull] at h
  apply hd
  simpa using h.symm

example (α : ℚ) :
    (fullModel ℚ).cycleClass ((doubleTransfer.degree : ℚ)⁻¹ •
      ((2 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) α) = α :=
  normalizedPushforward_cycleClass (fullModel ℚ) LinearMap.id doubleTransfer
    ((2 : ℚ) • LinearMap.id)
    (by apply LinearMap.ext; intro q; simp [fullModel, doubleTransfer]) α α rfl

-- The concrete normalized representative is 3, not its unnormalized trace 6.
example : (doubleTransfer.degree : ℚ)⁻¹ •
    ((2 : ℚ) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) 3 = (3 : ℚ) := by
  norm_num [doubleTransfer]

example : RationalHodgeConjectureAt (fullModel ℚ) :=
  rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy
    (fullModel ℚ) LinearMap.id doubleTransfer ((2 : ℚ) • LinearMap.id)
    (by apply LinearMap.ext; intro q; simp [fullModel, doubleTransfer])
    LinearMap.id (identityGeneration ℚ)

-- Neither pullback nor the recipe need be surjective onto the upstairs space.
example : ¬ Function.Surjective (LinearMap.inl ℚ ℚ ℚ) := by
  intro h
  obtain ⟨q, hq⟩ := h (0, 1)
  have hsecond := congrArg Prod.snd hq
  norm_num at hsecond

example : HodgePullbackGeneratedBy (fullModel ℚ)
    (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ))
    (LinearMap.inl ℚ ℚ ℚ) (LinearMap.inl ℚ ℚ ℚ) := by
  rw [hodgePullbackGeneratedBy_iff]
  intro α _
  exact ⟨α, rfl⟩

example : ((0, 1) : ℚ × ℚ) ∉ LinearMap.range
    ((LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)).comp (LinearMap.inl ℚ ℚ ℚ)) := by
  rintro ⟨q, hq⟩
  have hsecond := congrArg Prod.snd hq
  norm_num at hsecond

example : RationalHodgeConjectureAt (fullModel ℚ) := by
  apply rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy
    (fullModel ℚ) LinearMap.id leftTransfer (LinearMap.fst ℚ ℚ ℚ)
    (by apply LinearMap.ext; intro q; rfl) (LinearMap.inl ℚ ℚ ℚ)
  rw [hodgePullbackGeneratedBy_iff]
  intro α _
  exact ⟨α, rfl⟩

private def boolRecipe (b : Bool) : ℚ →ₗ[ℚ] ℚ :=
  if b then LinearMap.id else 0

example : ClassDependentChowBettiGeneration (fullModel ℚ)
    (fun _ : Bool => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    (fun _ : Bool => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) boolRecipe := by
  apply classDependentChowBettiGeneration_of_fixed _ _ _ _ true
  simpa [boolRecipe] using identityGeneration ℚ

-- Indexed generation does not assert success for every index.
example : ¬ HodgePullbackGeneratedBy (fullModel ℚ)
    LinearMap.id LinearMap.id (boolRecipe false) := by
  intro h
  obtain ⟨c, hc⟩ := (hodgePullbackGeneratedBy_iff _ _ _ _).mp h 1 (by trivial)
  norm_num [boolRecipe] at hc

-- Even the zero Hodge subspace contains a class, so an empty index family
-- cannot satisfy class-dependent generation.
example : ¬ ClassDependentChowBettiGeneration zeroHodgeModel
    (fun _ : Empty => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    (fun _ : Empty => (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    (fun _ : Empty => (LinearMap.id : ℚ →ₗ[ℚ] ℚ)) := by
  intro h
  obtain ⟨i, _⟩ := h 0 (by change (0 : ℚ) ∈ (⊥ : Submodule ℚ ℚ); simp)
  exact Empty.elim i

private def lineRecipe (v : ℚ × ℚ) : ℚ →ₗ[ℚ] (ℚ × ℚ) :=
  LinearMap.toSpanSingleton ℚ (ℚ × ℚ) v

-- Each recipe is fixed before quantification, while its index may be α.
example : ClassDependentChowBettiGeneration (fullModel (ℚ × ℚ))
    (fun _ : ℚ × ℚ => (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)))
    (fun _ : ℚ × ℚ => (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ))) lineRecipe := by
  intro α _
  exact ⟨α, 1, by simp [lineRecipe]⟩

-- No single line recipe covers the full plane, although the indexed family does.
example (v : ℚ × ℚ) : ¬ HodgePullbackGeneratedBy (fullModel (ℚ × ℚ))
    LinearMap.id LinearMap.id (lineRecipe v) := by
  intro h
  obtain ⟨a, ha⟩ := (hodgePullbackGeneratedBy_iff _ _ _ _).mp h (1, 0) (by trivial)
  obtain ⟨b, hb⟩ := (hodgePullbackGeneratedBy_iff _ _ _ _).mp h (0, 1) (by trivial)
  have ha1 : a * v.1 = 1 := congrArg Prod.fst ha
  have ha2 : a * v.2 = 0 := congrArg Prod.snd ha
  have hb2 : b * v.2 = 1 := congrArg Prod.snd hb
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz] at ha1
  have hv2 : v.2 = 0 := (mul_eq_zero.mp ha2).resolve_left ha0
  simp [hv2] at hb2

example : RationalHodgeConjectureAt (fullModel (ℚ × ℚ)) := by
  apply rationalHodgeConjectureAt_of_classDependentChowBettiGeneration
    (fullModel (ℚ × ℚ))
    (fun _ : ℚ × ℚ => (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)))
    (fun _ : ℚ × ℚ => identityTransfer (ℚ × ℚ))
    (fun _ : ℚ × ℚ => (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)))
    (by intro i; rfl) lineRecipe
  intro α _
  exact ⟨α, 1, by simp [lineRecipe, identityTransfer]⟩

end UpstairsGenerationVerification

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.HodgePullbackGeneratedBy,
    `HodgeConjecture.hodgePullbackGeneratedBy_iff,
    `HodgeConjecture.normalizedPushforward_cycleClass,
    `HodgeConjecture.rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy,
    `HodgeConjecture.ClassDependentChowBettiGeneration,
    `HodgeConjecture.classDependentChowBettiGeneration_of_fixed,
    `HodgeConjecture.rationalHodgeConjectureAt_of_classDependentChowBettiGeneration]
  unless declarations.length == 7 && declarations.eraseDups.length == 7 do
    throwError "Expected exactly seven distinct SP94 declarations"
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
  logInfo "PASS SP94 audit registry: seven distinct public declarations"
  let endpoints := [
    `HodgeConjecture.rationalHodgeConjectureAt_of_hodgePullbackGeneratedBy,
    `HodgeConjecture.rationalHodgeConjectureAt_of_classDependentChowBettiGeneration]
  let excludedModules := [
    `HodgeConjecture.LinearAlgebra,
    `HodgeConjecture.Boundary,
    `HodgeConjecture.Correspondence]
  for endpoint in endpoints do
    let dependencies := HodgeConjecture.Research.declarationDependencies env endpoint
    for declaration in dependencies.toList do
      if let some idx := env.getModuleIdxFor? declaration then
        let origin := env.header.moduleNames[idx]!
        unless !excludedModules.any (fun modulePrefix => modulePrefix.isPrefixOf origin) do
          throwError "Unexpected branch dependency {declaration} from {origin} in {endpoint}"
      if declaration == `HodgeConjecture.RationalDegreeTransfer.normalizedProjector then
        throwError "Normalized projector unexpectedly consumed by {endpoint}"
    unless dependencies.contains `HodgeConjecture.RationalDegreeTransfer.push_comp_pull do
      throwError "Expected positive-degree transfer law not consumed by {endpoint}"
    logInfo m!"PASS direct-descent dependency boundary: {endpoint}; consumes degree law, no projector or excluded branch"
