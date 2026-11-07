module

public import HodgeConjecture.Realization.Betti.ProjectiveLineHodgeStructure
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The type-(1,1) rational Hodge structure uses the actual Betti group and
actual tensor complexification. The tests retain the original pure tensor
and distinguish its canonical conjugation from raw analytic-period scaling.
The geometric degree-filtration comparison is tested in a separate suite.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture TensorProduct
open ProjectiveLineBettiComplexification ProjectiveLineHodgeStructure
open scoped ComplexConjugate

namespace ProjectiveLineHodgeStructureVerification

example : Module.finrank ℚ Betti = 1 := finrank_betti

example : Module.finrank ℂ Complexification = 1 := finrank_complexification

example (z : Betti) : conjugation (rationalEmbedding z) = rationalEmbedding z :=
  conjugation_rationalEmbedding z

example (c : ℂ) (z : Betti) : conjugation (c ⊗ₜ[ℚ] z) = conj c ⊗ₜ[ℚ] z :=
  conjugation_tmul c z

example (z : Complexification) : conjugation (conjugation z) = z :=
  conjugation_involutive z

/-- The raw analytic period is anti-real under the rational tensor real structure. -/
theorem conjugation_raw_period (z : Betti) :
    conjugation ((2 * Real.pi * Complex.I) ⊗ₜ[ℚ] z) =
      -((2 * Real.pi * Complex.I) ⊗ₜ[ℚ] z) := by
  apply coordinates.injective
  simp [mul_assoc, map_ofNat]

example : bigrading 0 2 = ⊥ := bigrading_eq_bot 0 2 (by decide)

example : bigrading 2 0 = ⊥ := bigrading_eq_bot 2 0 (by decide)

example : bigrading (-3) 5 = ⊥ := bigrading_eq_bot (-3) 5 (by decide)

example : bigrading 1 1 = ⊤ := bigrading_one_one

example : (⨆ pq : ℤ × ℤ, bigrading pq.1 pq.2) = ⊤ := bigrading_exhaustive

example : iSupIndep (fun pq : ℤ × ℤ ↦ bigrading pq.1 pq.2) := bigrading_direct

example : filtration (-3) = ⊤ := filtration_eq_top (-3) (by decide)

example : filtration 1 = ⊤ := filtration_one

example : filtration 2 = ⊥ := filtration_two

example : filtration 17 = ⊥ := filtration_eq_bot 17 (by decide)

example : bigrading (-3) 5 = filtration (-3) ⊓ conjugateSubmodule (filtration 5) :=
  bigrading_eq_filtration_inf_conjugate (-3) 5 (by norm_num)

example : IsCompl (filtration 1) (conjugateSubmodule (filtration 2)) := by
  simpa using filtration_opposed 1

example (z : Betti) : z ∈ rationalHodgeClasses := all_hodge z

example : rationalHodgeClasses = ⊤ := rationalHodgeClasses_eq_top

example (z : Betti) : z ∈ rationalHodgeClasses ↔
    rationalEmbedding z ∈ filtration 1 ∧ conjugation (rationalEmbedding z) ∈ filtration 1 :=
  mem_rationalHodgeClasses_filtration z

end ProjectiveLineHodgeStructureVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ProjectiveLineHodgeStructure.bettiFiniteDimensional,
      `HodgeConjecture.ProjectiveLineHodgeStructure.complexificationFiniteDimensional,
      `HodgeConjecture.ProjectiveLineHodgeStructure.finrank_betti,
      `HodgeConjecture.ProjectiveLineHodgeStructure.finrank_complexification,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation,
      `HodgeConjecture.ProjectiveLineHodgeStructure.coordinates_conjugation,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_zero,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_add,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_smul,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_involutive,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_eq_zero_iff,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_tmul,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_rationalEmbedding,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugateSubmodule,
      `HodgeConjecture.ProjectiveLineHodgeStructure.mem_conjugateSubmodule,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugateSubmodule_top,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugateSubmodule_bot,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugateSubmodule_involutive,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_one_one,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_eq_bot,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_pure_weight_two,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_effective,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_exhaustive,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_direct,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugation_bigrading,
      `HodgeConjecture.ProjectiveLineHodgeStructure.conjugateSubmodule_bigrading,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_antitone,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_eq_top,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_eq_bot,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_one,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_two,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_zero,
      `HodgeConjecture.ProjectiveLineHodgeStructure.bigrading_eq_filtration_inf_conjugate,
      `HodgeConjecture.ProjectiveLineHodgeStructure.filtration_opposed,
      `HodgeConjecture.ProjectiveLineHodgeStructure.rationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineHodgeStructure.mem_rationalHodgeClasses,
      `HodgeConjecture.ProjectiveLineHodgeStructure.all_hodge,
      `HodgeConjecture.ProjectiveLineHodgeStructure.rationalHodgeClasses_eq_top,
      `HodgeConjecture.ProjectiveLineHodgeStructure.mem_rationalHodgeClasses_filtration,
      `ProjectiveLineHodgeStructureVerification.conjugation_raw_period] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
