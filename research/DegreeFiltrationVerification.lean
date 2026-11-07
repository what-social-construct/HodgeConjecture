module

public import HodgeConjecture.Realization.DeRham.TwoTermDegreeFiltration
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
An original identity differential is nonzero, while brutal filtration
level one retains its full degree-one term and removes degree zero.
This checks degree truncation rather than homology truncation. The
actual two-term inclusion comparison and high-level zero pieces are
checked on this same original native double complex.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex HodgeConjecture

namespace DegreeFiltrationVerification

abbrev M := ModuleCat.of ℚ ℚ

/-- The actual native two-term identity complex, with zero terms outside degrees zero and one. -/
def identityPair : CochainComplex (ModuleCat ℚ) ℕ :=
  HomologicalComplex.double (𝟙 M) (show (ComplexShape.up ℕ).Rel 0 1 from rfl)

theorem identityPair_twoTerm (n : ℕ) (hn : 2 ≤ n) : IsZero (identityPair.X n) :=
  HomologicalComplex.isZero_double_X _ _ n (by omega) (by omega)

theorem original_differential_isIso : IsIso (identityPair.d 0 1) := by
  rw [identityPair, HomologicalComplex.double_d _ _ (by decide)]
  infer_instance

theorem original_differential_nonzero : identityPair.d 0 1 ≠ 0 := by
  intro h
  have hzero : IsZero (identityPair.X 1) := by
    have := original_differential_isIso
    exact IsZero.of_epi_eq_zero _ h
  have hM : IsZero M := hzero.of_iso
    (HomologicalComplex.doubleXIso₁ (𝟙 M)
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (by decide)).symm
  have hs := ModuleCat.isZero_iff_subsingleton.mp hM
  have he : (1 : ℚ) = 0 := hs.elim 1 0
  norm_num at he

example : IsZero ((DegreeFiltration.complex identityPair 1).X 0) :=
  DegreeFiltration.isZero_X_of_lt _ 1 0 (by decide)

/-- Brutal level one retains all of the original rational degree-one term. -/
def retainedDegreeOne : (DegreeFiltration.complex identityPair 1).X 1 ≅ M :=
  DegreeFiltration.xIso identityPair 1 1 (by decide) ≪≫
    HomologicalComplex.doubleXIso₁ (𝟙 M)
      (show (ComplexShape.up ℕ).Rel 0 1 from rfl) (by decide)

theorem retainedDegreeOne_nonzero : ¬ IsZero ((DegreeFiltration.complex identityPair 1).X 1) := by
  intro h
  have hM : IsZero M := h.of_iso retainedDegreeOne.symm
  have hs := ModuleCat.isZero_iff_subsingleton.mp hM
  have he : (1 : ℚ) = 0 := hs.elim 1 0
  norm_num at he

example : IsIso (DegreeFiltration.inclusion identityPair 0) := inferInstance

example : DegreeFiltration.complex identityPair 1 ≅ TwoTermComplex.degreeOne identityPair :=
  DegreeFiltration.degreeOneIso identityPair identityPair_twoTerm

example : (DegreeFiltration.degreeOneIso identityPair identityPair_twoTerm).hom ≫
    TwoTermComplex.inclusion identityPair identityPair_twoTerm =
      DegreeFiltration.inclusion identityPair 1 :=
  DegreeFiltration.degreeOneIso_hom_inclusion _ _

example : IsZero (DegreeFiltration.complex identityPair 2) :=
  DegreeFiltration.complex_isZero_of_twoTerm _ identityPair_twoTerm 2 (by decide)

example (p : ℕ) (hp : 2 ≤ p) : IsZero (DegreeFiltration.complex identityPair p) :=
  DegreeFiltration.complex_isZero_of_twoTerm _ identityPair_twoTerm p hp

example (p q : ℕ) (hpq : p ≤ q) :
    DegreeFiltration.transition identityPair p q hpq ≫ DegreeFiltration.inclusion identityPair p =
      DegreeFiltration.inclusion identityPair q :=
  DegreeFiltration.transition_inclusion _ _ _ _

end DegreeFiltrationVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.DegreeFiltration.embedding,
      `HodgeConjecture.DegreeFiltration.complex,
      `HodgeConjecture.DegreeFiltration.xIso,
      `HodgeConjecture.DegreeFiltration.isZero_X_of_lt,
      `HodgeConjecture.DegreeFiltration.d_eq,
      `HodgeConjecture.DegreeFiltration.inclusion,
      `HodgeConjecture.DegreeFiltration.inclusion_f,
      `HodgeConjecture.DegreeFiltration.transition,
      `HodgeConjecture.DegreeFiltration.transition_inclusion,
      `HodgeConjecture.DegreeFiltration.inclusion_zero_isIso,
      `HodgeConjecture.DegreeFiltration.zeroIso,
      `HodgeConjecture.DegreeFiltration.isZero_X_of_twoTerm,
      `HodgeConjecture.DegreeFiltration.complex_isZero_of_twoTerm,
      `HodgeConjecture.DegreeFiltration.degreeOneToComplex,
      `HodgeConjecture.DegreeFiltration.degreeOneToComplex_isIso,
      `HodgeConjecture.DegreeFiltration.degreeOneToComplex_inclusion,
      `HodgeConjecture.DegreeFiltration.degreeOneIso,
      `HodgeConjecture.DegreeFiltration.degreeOneIso_hom_inclusion,
      `DegreeFiltrationVerification.identityPair_twoTerm,
      `DegreeFiltrationVerification.original_differential_isIso,
      `DegreeFiltrationVerification.original_differential_nonzero,
      `DegreeFiltrationVerification.retainedDegreeOne,
      `DegreeFiltrationVerification.retainedDegreeOne_nonzero] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
