module

import HodgeConjecture.Realization.Chow.BoundaryCorrection
import HodgeConjecture.Realization.Chow.UpstairsGeneration
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP108: conditional boundary correction on the existing Chow groups.
Run with `lake env lean research/BoundaryCorrectionVerification.lean`.

Rational linear fixtures test a nonzero correction, a noninjective boundary
map, and the necessity of boundary algebraicity. A separate consumer composes
the correction with existing positive-degree descent. These fixtures are not
new geometric realizations. The three production theorems, including the
actual scheme-Chow specialization, receive a standard-three axiom audit.
-/

set_option autoImplicit false

open HodgeConjecture HodgeConjecture.BoundaryCorrection

noncomputable section

namespace BoundaryCorrectionVerification

private def fullModel (H : Type*) [AddCommGroup H] [Module ℚ H] :
    RationalHodgeCycleClassModel H H where
  hodgeClasses := ⊤
  cycleClass := LinearMap.id
  cycleClass_lands := le_top

-- The second boundary coordinate lies in the kernel; no Gysin injectivity
-- is needed to lift a supported Hodge class.
private def boundaryMap : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) :=
  (LinearMap.inr ℚ ℚ ℚ).comp (LinearMap.fst ℚ ℚ ℚ)

private theorem supportedLift (δ : ℚ × ℚ)
    (_ : IsRationalHodgeClass (fullModel (ℚ × ℚ)) δ)
    (h : (LinearMap.fst ℚ ℚ ℚ) δ = 0) :
    ∃ γ : ℚ × ℚ, IsRationalHodgeClass (fullModel (ℚ × ℚ)) γ ∧
      boundaryMap γ = δ := by
  refine ⟨(δ.2, 0), by trivial, ?_⟩
  exact Prod.ext h.symm rfl

private theorem fullAlgebraicity (H : Type*) [AddCommGroup H] [Module ℚ H] :
    RationalHodgeConjectureAt (fullModel H) := by
  intro α _
  exact ⟨α, rfl⟩

example : ¬ Function.Injective boundaryMap := by
  intro h
  have heq := h (show boundaryMap (0, 0) = boundaryMap (0, 1) from rfl)
  have := congrArg Prod.snd heq
  norm_num at this

-- Every correction supplied here has nonzero first boundary coordinate.
example : ∃ b : ℚ × ℚ,
    (fullModel (ℚ × ℚ)).cycleClass ((3, 0) + boundaryMap b) = (3, 5) ∧
      b.1 = 5 := by
  obtain ⟨b, hb⟩ := exists_boundary_correction
    (fullModel (ℚ × ℚ)) (fullModel (ℚ × ℚ)) boundaryMap boundaryMap
    (LinearMap.fst ℚ ℚ ℚ) (by apply LinearMap.ext; intro x; rfl) supportedLift
    (fullAlgebraicity _) (3, 5) (by trivial) (3, 0) rfl
  refine ⟨b, hb, ?_⟩
  simpa [fullModel, boundaryMap] using congrArg Prod.snd hb

-- Open restriction and both cycle-class squares are actually instantiated.
example (a b : ℚ) : IsAlgebraicHodgeClass (fullModel (ℚ × ℚ)) (a, b) := by
  apply isAlgebraicHodgeClass_of_openRestriction
    (fullModel (ℚ × ℚ)) (fullModel (ℚ × ℚ)) LinearMap.id
    (LinearMap.fst ℚ ℚ ℚ) (LinearMap.fst ℚ ℚ ℚ) boundaryMap boundaryMap
    (by apply LinearMap.ext; intro x; rfl) (fun q ↦ ⟨(q, 0), rfl⟩)
    (by apply LinearMap.ext; intro x; rfl)
    supportedLift (fullAlgebraicity _) (a, b) (by trivial) a
  rfl

private def deficientModel : RationalHodgeCycleClassModel ℚ (ℚ × ℚ) where
  hodgeClasses := ⊤
  cycleClass := LinearMap.inl ℚ ℚ ℚ
  cycleClass_lands := le_top

private def deficientBoundary : RationalHodgeCycleClassModel ℚ ℚ where
  hodgeClasses := ⊤
  cycleClass := 0
  cycleClass_lands := le_top

-- Supported classes still lift as Hodge classes, and Chow restriction is
-- surjective with both squares commuting, but boundary algebraicity fails.
example :
    Function.Surjective (LinearMap.id : ℚ →ₗ[ℚ] ℚ) ∧
    (LinearMap.id : ℚ →ₗ[ℚ] ℚ).comp LinearMap.id =
      (LinearMap.fst ℚ ℚ ℚ).comp deficientModel.cycleClass ∧
    deficientModel.cycleClass.comp (0 : ℚ →ₗ[ℚ] ℚ) =
      (LinearMap.inr ℚ ℚ ℚ).comp deficientBoundary.cycleClass ∧
    (∀ δ : ℚ × ℚ, IsRationalHodgeClass deficientModel δ →
      (LinearMap.fst ℚ ℚ ℚ) δ = 0 →
      ∃ γ : ℚ, IsRationalHodgeClass deficientBoundary γ ∧
        (LinearMap.inr ℚ ℚ ℚ) γ = δ) := by
  refine ⟨Function.surjective_id, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro q
    rfl
  · apply LinearMap.ext
    intro q
    simp [deficientModel, deficientBoundary]
  · intro δ _ h
    exact ⟨δ.2, by trivial, Prod.ext h.symm rfl⟩

example : ∃ zU : ℚ,
    (LinearMap.id : ℚ →ₗ[ℚ] ℚ) zU = (LinearMap.fst ℚ ℚ ℚ) (0, 1) :=
  ⟨0, rfl⟩

example : ¬ IsAlgebraicHodgeClass deficientModel (0, 1) := by
  rintro ⟨z, hz⟩
  have h := congrArg Prod.snd hz
  norm_num [deficientModel] at h

example : ¬ RationalHodgeConjectureAt deficientBoundary := by
  intro h
  obtain ⟨b, hb⟩ := h (show IsRationalHodgeClass deficientBoundary 1 by trivial)
  norm_num [deficientBoundary] at hb

end BoundaryCorrectionVerification

-- A corrected upstairs cycle feeds directly into normalized descent.
section Descent

variable {CX CY CD HX HY HD HU : Type*}
variable [AddCommGroup CX] [Module ℚ CX] [AddCommGroup CY] [Module ℚ CY]
variable [AddCommGroup CD] [Module ℚ CD] [AddCommGroup HX] [Module ℚ HX]
variable [AddCommGroup HY] [Module ℚ HY] [AddCommGroup HD] [Module ℚ HD]
variable [AddCommGroup HU] [Module ℚ HU]

example (M : RationalHodgeCycleClassModel CX HX)
    (MY : RationalHodgeCycleClassModel CY HY)
    (MD : RationalHodgeCycleClassModel CD HD)
    (T : RationalDegreeTransfer HY HX) (pushCH : CY →ₗ[ℚ] CX)
    (iCH : CD →ₗ[ℚ] CY) (iH : HD →ₗ[ℚ] HY) (rH : HY →ₗ[ℚ] HU)
    (hPush : M.cycleClass.comp pushCH = T.push.comp MY.cycleClass)
    (hBoundaryPush : MY.cycleClass.comp iCH = iH.comp MD.cycleClass)
    (hLift : ∀ δ : HY, IsRationalHodgeClass MY δ → rH δ = 0 →
      ∃ γ : HD, IsRationalHodgeClass MD γ ∧ iH γ = δ)
    (hBoundary : RationalHodgeConjectureAt MD)
    (α : HX) (hα : IsRationalHodgeClass MY (T.pull α)) (z : CY)
    (hOpen : rH (MY.cycleClass z) = rH (T.pull α)) :
    ∃ b : CD, M.cycleClass ((T.degree : ℚ)⁻¹ • pushCH (z + iCH b)) = α := by
  obtain ⟨b, hb⟩ := exists_boundary_correction MY MD iCH iH rH
    hBoundaryPush hLift hBoundary (T.pull α) hα z hOpen
  exact ⟨b, normalizedPushforward_cycleClass M MY.cycleClass T pushCH hPush _ α hb⟩

end Descent

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.BoundaryCorrection.exists_boundary_correction,
    `HodgeConjecture.BoundaryCorrection.isAlgebraicHodgeClass_of_openRestriction,
    `HodgeConjecture.BoundaryCorrection.isAlgebraicHodgeClass_of_schemeOpenRestriction]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
