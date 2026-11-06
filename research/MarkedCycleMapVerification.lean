module

import HodgeConjecture.Realization.Chow.MarkedCycleMap
import HodgeConjecture.Realization.Chow.UpstairsGeneration
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP109: actual Chow-valued marked cycle recipes, in arbitrary dimension.
Run with `lake env lean research/MarkedCycleMapVerification.lean`.

Checks use the existing scheme Chow quotient: the marked support disappears,
a nonmarked support contributes with the required sign and rational weight,
and actual principal relations preserve the map. The generic-degree fixture
proves that the output can be nonzero without selecting a dimension. The
existing generation predicate is then reduced to the exact cycle-class span;
this does not discharge generation. All new public declarations receive an
enforced standard-three axiom audit.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory HodgeConjecture HodgeConjecture.SchemeCycles
open HodgeConjecture.MarkedSheetChow

noncomputable section

universe u v

variable {G : Type u} [Group G] [Finite G] (H : Subgroup G)
variable {X : Scheme.{v}} [IsNoetherian X] (δ : DimensionFunction X) (n : ℤ)

local instance : DecidableEq (CollisionFoundations.GaloisSheets H) := Classical.decEq _

-- Marked-only families contribute nothing, even for nonzero cycles.
example (c : cyclesOfDegree ℚ δ n) : chowMap H δ n (Pi.single (baseSheet H) c) = 0 := by
  apply LinearMap.ext
  intro x
  rw [chowMap_single]
  have hx : x.val (baseSheet H) = 0 := x.property
  simp [hx]

-- Negative rational coefficients in a supplied cycle give the intended sign.
example (s : CollisionFoundations.GaloisSheets H) (hs : s ≠ baseSheet H)
    (c : cyclesOfDegree ℚ δ n) :
    chowMap H δ n (Pi.single s (-(2 : ℚ) • c))
        (MarkedSheetProjector.residualClass H) = (2 : ℚ) • rationalClassMap δ n c := by
  rw [chowMap_single]
  simp [MarkedSheetProjector.residualClass, MarkedSheetProjector.selector,
    genericSheetSelector, hs, smul_smul]

-- This is the actual principal-relation family, not a substituted quotient.
example (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n)
    (d : CollisionFoundations.GaloisSheets H → PrincipalRelationData δ n) :
    chowMap H δ n (fun s ↦ C s +
      cyclesOfDegreeRationalize δ n (principalRelation δ n (d s))) = chowMap H δ n C := by
  apply chowMap_congr
  intro s
  simp only [add_sub_cancel_left]
  exact Submodule.subset_span (Set.mem_range_self (d s))

-- A fundamental support at generic degree has nonzero class on every
-- integral Noetherian X with a supplied dimension function.
example [IsIntegral X]
    (s : CollisionFoundations.GaloisSheets H) (hs : s ≠ baseSheet H) :
    ∃ C : CollisionFoundations.GaloisSheets H →
        cyclesOfDegree ℚ δ (δ (genericPoint X)),
      chowMap H δ (δ (genericPoint X)) C (MarkedSheetProjector.residualClass H) ≠ 0 := by
  let W := pointSupport X (genericPoint X)
  let c : cyclesOfDegree ℚ δ (δ (genericPoint X)) :=
    ⟨fundamentalCycle ℚ W, fundamentalCycle_mem_cyclesOfDegree ℚ δ _ W
      (by simp [W, supportDegree])⟩
  have hc : rationalClassMap δ (δ (genericPoint X)) c ≠ 0 := by
    rw [ne_eq, rationalClassMap_eq_zero_iff, rationalPrincipalRelations_genericDegree_eq_bot]
    intro h
    have hz : c = 0 := h
    have he := congrArg (fun z : cyclesOfDegree ℚ δ (δ (genericPoint X)) ↦ z.val W) hz
    simp [c] at he
  refine ⟨Pi.single s c, ?_⟩
  rw [chowMap_single]
  simpa [MarkedSheetProjector.residualClass, MarkedSheetProjector.selector,
    genericSheetSelector, hs] using hc

-- Existing target input: generation is exactly containment in this span.
example {CX HX HY : Type*} [AddCommGroup CX] [Module ℚ CX]
    [AddCommGroup HX] [Module ℚ HX] [AddCommGroup HY] [Module ℚ HY]
    (M : RationalHodgeCycleClassModel CX HX)
    (cl : RationalChowGroup δ n →ₗ[ℚ] HY) (pull : HX →ₗ[ℚ] HY)
    (C : CollisionFoundations.GaloisSheets H → cyclesOfDegree ℚ δ n) :
    HodgePullbackGeneratedBy M cl pull (chowMap H δ n C) ↔
      Submodule.map pull M.hodgeClasses ≤ Submodule.span ℚ
        (Set.range (fun s : {s : CollisionFoundations.GaloisSheets H // s ≠ baseSheet H} ↦
          cl (rationalClassMap δ n (C s.val)))) := by
  rw [HodgePullbackGeneratedBy, range_cycleClass_chowMap]

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.MarkedSheetChow.cycleMap,
    `HodgeConjecture.MarkedSheetChow.chowMap,
    `HodgeConjecture.MarkedSheetChow.chowMap_apply,
    `HodgeConjecture.MarkedSheetChow.chowMap_single,
    `HodgeConjecture.MarkedSheetChow.chowMap_residualClass,
    `HodgeConjecture.MarkedSheetChow.chowMap_congr,
    `HodgeConjecture.MarkedSheetChow.range_chowMap,
    `HodgeConjecture.MarkedSheetChow.range_cycleClass_chowMap,
    `HodgeConjecture.MarkedSheetChow.cycleClass_chowMap_residualClass,
    `HodgeConjecture.MarkedSheetChow.chowMap_residualClass_reweight,
    `HodgeConjecture.MarkedSheetChow.openRestriction_chowMap,
    `HodgeConjecture.MarkedSheetChow.finitePushforward_chowMap]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
