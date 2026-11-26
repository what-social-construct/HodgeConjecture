module

import HodgeConjecture.Realization.Chow.HarmonicWitness
import HodgeConjecture.Realization.Betti.ProjectiveLineProductHarmonicWitness
import Lean.Util.CollectAxioms

/-!
Focused integrity checks for the attributed finite harmonic core, its native
closed-cochain quotient criterion, the existing upstairs descent consumer,
and the actual product Betti/fiber-cycle coordinate control.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture

-- A nonclosed observation cannot acquire an exact residual merely by projecting it.
example {V E T : Type*} [Fintype V] [Fintype E] [Fintype T]
    {X : Harmonic.OrientedTwoComplex V E T} (F : Harmonic.CellularSheaf X)
    {c : F.C1} (hc : ¬ F.IsOneCocycle c) :
    ¬ F.IsExactOneCochain (c - F.harmonicOneProjection c) := by
  intro hexact
  apply hc
  have hclosed := F.isOneCocycle_of_isExactOneCochain hexact
  have hh := (F.isHarmonicOneCochain_iff_coclosed_and_cocycle _).mp
    (F.harmonicOneProjection_isHarmonic c)
  have heq : c = (c - F.harmonicOneProjection c) + F.harmonicOneProjection c := by abel
  change F.delta1 c = 0
  rw [heq, map_add, hclosed, hh.2, add_zero]

open ProjectiveLineProductHarmonicWitness ProjectiveLineProductBetti
open ProjectiveLineProductSpanning

-- Actual Betti coordinates retain signed rational coefficients in the harmonic model.
example :
    (witness (coordinateSection (2, -3))).1 ⟨(), (0 : Fin 2)⟩ = 2 ∧
    (witness (coordinateSection (2, -3))).1 ⟨(), (1 : Fin 2)⟩ = -3 := by
  change ((coordinateEquiv (coordinateSection (2, -3))).1 : ℝ) = 2 ∧
    ((coordinateEquiv (coordinateSection (2, -3))).2 : ℝ) = -3
  have h : coordinateEquiv (coordinateSection (2, -3)) = (2, -3) :=
    coordinateProbe_section (2, -3)
  rw [h]
  norm_num

-- The two original geometric fiber classes cannot be accepted as the same target.
example : ¬ coordinateSheaf.IsExactOneCochain
    ((witness firstClass : coordinateSheaf.C1) - (witness secondClass : coordinateSheaf.C1)) := by
  intro certificate
  have h := coordinateSheaf.eq_of_exact_harmonicWitness_sub witness witness_injective certificate
  have hsum : (1 : ℚ) • firstClass + (-1 : ℚ) • secondClass = 0 := by
    simpa only [one_smul, neg_smul, one_smul, sub_eq_add_neg] using sub_eq_zero.mpr h
  have hbad := (classes_independent 1 (-1) hsum).1
  norm_num at hbad

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.Harmonic.CellularSheaf.delta1_comp_delta0,
      `HodgeConjecture.Harmonic.CellularSheaf.degreeOneLaplacian_isPositive,
      `HodgeConjecture.Harmonic.CellularSheaf.degreeOneLaplacian_energy,
      `HodgeConjecture.Harmonic.CellularSheaf.degreeOneLaplacian_apply_eq_zero_iff,
      `HodgeConjecture.Harmonic.CellularSheaf.ker_degreeOneLaplacian,
      `HodgeConjecture.Harmonic.CellularSheaf.IsometricCochainEquiv.degreeOneLaplacian_naturality,
      `HodgeConjecture.Harmonic.CellularSheaf.IsometricCochainEquiv.isHarmonicOneCochain_iff,
      `HodgeConjecture.Harmonic.CellularSheaf.harmonicOneProjection_isHarmonic,
      `HodgeConjecture.Harmonic.CellularSheaf.harmonicOneProjection_of_harmonic,
      `HodgeConjecture.Harmonic.CellularSheaf.harmonicOneProjection_delta0,
      `HodgeConjecture.Harmonic.CellularSheaf.harmonicOneProjection_of_exact,
      `HodgeConjecture.Harmonic.CellularSheaf.sub_harmonicOneProjection_exact,
      `HodgeConjecture.Harmonic.CellularSheaf.existsUnique_harmonic_representative,
      `HodgeConjecture.Harmonic.CellularSheaf.harmonicOneProjection_eq_iff_exact_sub,
      `HodgeConjecture.Harmonic.CellularSheaf.quotient_class_eq_iff_harmonicOneProjection_eq,
      `HodgeConjecture.Harmonic.CellularSheaf.eq_of_exact_harmonicWitness_sub,
      `HodgeConjecture.normalizedPushforward_cycleClass_of_harmonicWitness,
      `HodgeConjecture.ProjectiveLineProductHarmonicWitness.coordinate_delta0,
      `HodgeConjecture.ProjectiveLineProductHarmonicWitness.coordinate_delta1,
      `HodgeConjecture.ProjectiveLineProductHarmonicWitness.coordinate_isHarmonic,
      `HodgeConjecture.ProjectiveLineProductHarmonicWitness.witness_injective,
      `HodgeConjecture.ProjectiveLineProductHarmonicWitness.ordinaryChowCycleClass_eq_iff_exact_witness_sub,
      `HodgeConjecture.ProjectiveLineProductHarmonicWitness.fiberChowClass_harmonic_certificate] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS harmonic standard-three axiom boundary: {declaration}; {axioms.toList}"

end
