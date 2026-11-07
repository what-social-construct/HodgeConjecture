module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeFiltration
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Complex.Basic
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
The actual derived image filtration is checked in characteristic zero and
characteristic two, including a nonzero Chern class whose filtration degree
is exactly one. The original derived inclusion is itself invertible.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry HodgeConjecture ProjectiveLineDeRham

namespace ProjectiveLineHodgeFiltrationVerification

example : hodgeFiltration ℚ 0 = ⊤ := hodgeFiltration_zero ℚ
example : hodgeFiltration ℚ 1 = ⊤ := hodgeFiltration_one ℚ
example : hodgeFiltration ℚ 2 = ⊥ := hodgeFiltration_two ℚ
example : hodgeFiltration ℚ (-7) = ⊤ := hodgeFiltration_eq_top ℚ _ (by decide)
example : hodgeFiltration ℚ 9 = ⊥ := hodgeFiltration_eq_bot ℚ _ (by decide)

example : Antitone (hodgeFiltration ℚ) := hodgeFiltration_antitone ℚ

example (z : SchemeH2 ℚ) : z ∈ hodgeFiltration ℚ 1 := by
  rw [hodgeFiltration_one]
  trivial

example (z : SchemeH2 ℚ) : z ∈ hodgeFiltration ℚ 2 ↔ z = 0 := by
  rw [hodgeFiltration_two, Submodule.mem_bot]

example : schemeChernCoordinate ℚ ∈ hodgeFiltration ℚ 1 :=
  chernCoordinate_mem_hodgeFiltration_one ℚ

example : schemeChernCoordinate ℚ ∉ hodgeFiltration ℚ 2 :=
  chernCoordinate_not_mem_hodgeFiltration_two ℚ

example : IsIso (SchemeDeRham.hodgeFiltrationMap ℚ (projectiveLine ℚ)
    (projectiveLine ℚ ↘ Spec (.of ℚ)) 2 1) := hodgeFiltrationOne_isIso ℚ

example (z : SchemeH2 ℚ) :
    z ∈ hodgeFiltration ℚ 1 ↔ ∃ x, SchemeDeRham.hodgeFiltrationMap ℚ (projectiveLine ℚ)
      (projectiveLine ℚ ↘ Spec (.of ℚ)) 2 1 x = z :=
  SchemeDeRham.mem_hodgeFiltration ℚ _ _ 2 1 z

example : hodgeFiltration ℂ 1 = ⊤ := hodgeFiltration_one ℂ
example : hodgeFiltration ℂ 2 = ⊥ := hodgeFiltration_two ℂ

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example : hodgeFiltration (ZMod 2) 1 = ⊤ := hodgeFiltration_one (ZMod 2)
example : hodgeFiltration (ZMod 2) 2 = ⊥ := hodgeFiltration_two (ZMod 2)

theorem characteristicTwo_chern_nonzero : schemeChernCoordinate (ZMod 2) ≠ 0 :=
  schemeChernCoordinate_ne_zero (ZMod 2)

theorem characteristicTwo_chern_filtration_degree :
    schemeChernCoordinate (ZMod 2) ∈ hodgeFiltration (ZMod 2) 1 ∧
      schemeChernCoordinate (ZMod 2) ∉ hodgeFiltration (ZMod 2) 2 :=
  ⟨chernCoordinate_mem_hodgeFiltration_one (ZMod 2),
    chernCoordinate_not_mem_hodgeFiltration_two (ZMod 2)⟩

end ProjectiveLineHodgeFiltrationVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.HypercohomologyFiltration.nonnegativeFunctor,
      `HodgeConjecture.HypercohomologyFiltration.functor,
      `HodgeConjecture.HypercohomologyFiltration.functor_map,
      `HodgeConjecture.HypercohomologyFiltration.image,
      `HodgeConjecture.HypercohomologyFiltration.image_comp_le,
      `HodgeConjecture.HypercohomologyFiltration.image_le_of_factorization,
      `HodgeConjecture.HypercohomologyFiltration.image_eq_top_of_epi,
      `HodgeConjecture.HypercohomologyFiltration.image_eq_top_of_isIso,
      `HodgeConjecture.HypercohomologyFiltration.image_zero,
      `HodgeConjecture.HypercohomologyFiltration.image_eq_bot_of_isZero,
      `HodgeConjecture.HypercohomologyFiltration.filtration,
      `HodgeConjecture.HypercohomologyFiltration.filtration_antitone,
      `HodgeConjecture.HypercohomologyFiltration.filtration_zero,
      `HodgeConjecture.HypercohomologyFiltration.filtration_eq_bot_of_twoTerm,
      `HodgeConjecture.HypercohomologyFiltration.degreeOne_inclusion_map_isIso,
      `HodgeConjecture.HypercohomologyFiltration.filtration_one_map_isIso,
      `HodgeConjecture.HypercohomologyFiltration.filtration_one_of_twoTerm,
      `HodgeConjecture.HypercohomologyFiltration.sheaf_functor_obj,
      `HodgeConjecture.HypercohomologyFiltration.sheaf_functor_map,
      `HodgeConjecture.SchemeDeRham.hodgeFiltrationComplex,
      `HodgeConjecture.SchemeDeRham.hodgeFiltrationInclusion,
      `HodgeConjecture.SchemeDeRham.hodgeFiltrationMap,
      `HodgeConjecture.SchemeDeRham.hodgeFiltration,
      `HodgeConjecture.SchemeDeRham.mem_hodgeFiltration,
      `HodgeConjecture.SchemeDeRham.hodgeFiltration_eq_generic,
      `HodgeConjecture.SchemeDeRham.hodgeFiltration_antitone,
      `HodgeConjecture.SchemeDeRham.hodgeFiltration_eq_top_of_nonpos,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_antitone,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltrationOne_isIso,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_one,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_eq_top_of_nonpos,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_eq_top,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_eq_bot,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_zero,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_two,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltration_eq,
      `HodgeConjecture.ProjectiveLineDeRham.chernCoordinate_mem_hodgeFiltration_one,
      `HodgeConjecture.ProjectiveLineDeRham.chernCoordinate_not_mem_hodgeFiltration_two,
      `HodgeConjecture.ProjectiveLineDeRham.hodgeFiltrationOne_comparison,
      `ProjectiveLineHodgeFiltrationVerification.characteristicTwo_chern_nonzero,
      `ProjectiveLineHodgeFiltrationVerification.characteristicTwo_chern_filtration_degree] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
