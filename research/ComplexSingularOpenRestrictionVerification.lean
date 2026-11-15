module

public import HodgeConjecture.Realization.Betti.ComplexSingularOpenRestriction
public import Mathlib.Analysis.Complex.Basic
public import Lean.Util.CollectAxioms

@[expose] public noncomputable section

/-!
Complex zero extension is checked against the original open pullback, and
the actual complex cochain sheaf is checked on a noncompact complex line.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory TopologicalSpace Opposite HodgeConjecture

namespace ComplexSingularOpenRestrictionVerification

example (X : TopCat.{0}) (U : Opens X) (n : ℕ)
    (φ : (SingularCoefficientChange.complexCochains ((Opens.toTopCat X).obj U)).X n) :
    (SingularCoefficientChange.pullback (Opens.inclusion' U)).f n
      (SingularCoefficientChange.openExtension X U n φ) = φ :=
  SingularCoefficientChange.pullback_openExtension X U n φ

/-- A section on any open of the complex plane lifts to an actual global cochain. -/
theorem complex_plane_open_section_lifts (U : Opens (TopCat.of ℂ)) (n : ℕ)
    (s : (SingularCoefficientChange.cochainSheaf (TopCat.of ℂ) n).obj.obj (op U)) :
    ∃ φ : (SingularCoefficientChange.complexCochains (TopCat.of ℂ)).X n,
      (SingularCoefficientChange.cochainSheaf (TopCat.of ℂ) n).obj.map
          (homOfLE (show U ≤ ⊤ from le_top)).op
          ((SingularCoefficientChange.globalCochainsToSheaf (TopCat.of ℂ)).f n φ) = s := by
  let : LocallyCompactSpace U := U.isOpenEmbedding.locallyCompactSpace
  exact SingularCoefficientChange.exists_global_cochain_open_lift (TopCat.of ℂ) U n s

/-- The original complex cochain sheaf is flasque on the actual noncompact complex plane. -/
theorem complex_plane_cochainSheaf_flasque (n : ℕ) :
    (SingularCoefficientChange.cochainSheaf (TopCat.of ℂ) n).IsFlasque :=
  SingularCoefficientChange.cochainSheaf_isFlasque_of_locallyCompact_secondCountable
    (TopCat.of ℂ) n

end ComplexSingularOpenRestrictionVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularCoefficientChange.openExtension,
      `HodgeConjecture.SingularCoefficientChange.pullback_openExtension,
      `HodgeConjecture.SingularCoefficientChange.openPresheafIso,
      `HodgeConjecture.SingularCoefficientChange.toSheafify_open_surjective,
      `HodgeConjecture.SingularCoefficientChange.exists_global_cochain_open_lift,
      `HodgeConjecture.SingularCoefficientChange.cochainSheaf_restriction_surjective,
      `HodgeConjecture.SingularCoefficientChange.cochainSheaf_isFlasque,
      `HodgeConjecture.SingularCoefficientChange.cochainSheaf_isFlasque_of_locallyCompact_secondCountable,
      `ComplexSingularOpenRestrictionVerification.complex_plane_open_section_lifts,
      `ComplexSingularOpenRestrictionVerification.complex_plane_cochainSheaf_flasque] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
