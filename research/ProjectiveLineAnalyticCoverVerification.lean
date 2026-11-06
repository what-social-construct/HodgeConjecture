module

import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineAnalyticCover
import Lean.Util.CollectAxioms

/-!
Actual affine chart ranges, original finite coordinate on their intersection,
and native radial projection with the original unit-circle section.
These checks concern topology and homotopy, without a cohomology dimension premise.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture HodgeConjecture.ProjectiveLineComplexPoints
open HodgeConjecture.ProjectiveLineAnalyticCover
open HodgeConjecture.PuncturedComplexCircle

example : IsOpen finiteOpen ∧ IsOpen reciprocalOpen :=
  ⟨isOpen_finiteOpen, isOpen_reciprocalOpen⟩

example : finiteOpen ∪ reciprocalOpen = Set.univ := cover

example : ContractibleSpace finiteOpen ∧ ContractibleSpace reciprocalOpen :=
  ⟨inferInstance, inferInstance⟩

-- The first chart excludes infinity while the reciprocal zero is exactly infinity.
example : (reciprocalHomeomorph 0 : Point) = infinity := rfl

example : finite 0 ∉ reciprocalOpen := by
  rw [finite_mem_reciprocal_iff]
  simp

example : finite Complex.I ∈ finiteOpen ∩ reciprocalOpen := by
  exact ⟨⟨Complex.I, rfl⟩, (finite_mem_reciprocal_iff _).mpr Complex.I_ne_zero⟩

example : (overlapHomeomorph ⟨Complex.I, Complex.I_ne_zero⟩ : Point) = finite Complex.I := rfl

example (p : ↥(finiteOpen ∩ reciprocalOpen)) :
    finite (overlapHomeomorph.symm p : ℂ) = (p : Point) := by
  exact congrArg Subtype.val (overlapHomeomorph.apply_symm_apply p)

example (z : Plane) : (radial z : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) := radial_coe z

example (z : Circle) : radial (inclusion z) = z := radial_inclusion z

example (z : Circle) : homotopyEquiv.symm z = inclusion z := homotopyEquiv_symm_apply z

example (z : Plane) :
    overlapCircleHomotopyEquiv (overlapHomeomorph z) = radial z :=
  overlapCircleHomotopyEquiv_finite z

-- At the actual unit-circle point i, native radial normalization retains the coordinate.
example : radial ⟨Complex.I, Complex.I_ne_zero⟩ =
    (⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩ : Circle) := by
  apply Circle.ext
  simp

run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.PuncturedComplexCircle.polarHomeomorph,
    `HodgeConjecture.PuncturedComplexCircle.inclusion,
    `HodgeConjecture.PuncturedComplexCircle.radial,
    `HodgeConjecture.PuncturedComplexCircle.radial_coe,
    `HodgeConjecture.PuncturedComplexCircle.productHomotopy,
    `HodgeConjecture.PuncturedComplexCircle.productEquiv,
    `HodgeConjecture.PuncturedComplexCircle.homotopyEquiv,
    `HodgeConjecture.PuncturedComplexCircle.homotopyEquiv_symm_apply,
    `HodgeConjecture.PuncturedComplexCircle.radial_inclusion,
    `HodgeConjecture.ProjectiveLineAnalyticCover.isOpen_finiteOpen,
    `HodgeConjecture.ProjectiveLineAnalyticCover.isOpen_reciprocalOpen,
    `HodgeConjecture.ProjectiveLineAnalyticCover.cover,
    `HodgeConjecture.ProjectiveLineAnalyticCover.finiteHomeomorph,
    `HodgeConjecture.ProjectiveLineAnalyticCover.reciprocalHomeomorph,
    `HodgeConjecture.ProjectiveLineAnalyticCover.finiteOpenContractibleSpace,
    `HodgeConjecture.ProjectiveLineAnalyticCover.reciprocalOpenContractibleSpace,
    `HodgeConjecture.ProjectiveLineAnalyticCover.finite_mem_reciprocal_iff,
    `HodgeConjecture.ProjectiveLineAnalyticCover.finiteOverlap_surjective,
    `HodgeConjecture.ProjectiveLineAnalyticCover.isEmbedding_finiteOverlap,
    `HodgeConjecture.ProjectiveLineAnalyticCover.overlapHomeomorph,
    `HodgeConjecture.ProjectiveLineAnalyticCover.overlapCircleHomotopyEquiv,
    `HodgeConjecture.ProjectiveLineAnalyticCover.overlapCircleHomotopyEquiv_finite]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    Lean.logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {axioms.toList}"
