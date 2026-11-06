module

public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality
public import Mathlib.Analysis.Convex.Contractible
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
Actual point, interval, and real-plane cohomology calculations verify that
native topological contractions reach the original singular cohomology objects.
The degree-zero tests retain the original constant cocycles and evaluations.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HodgeConjecture

namespace SingularHomotopyVerification

theorem point_allPositive (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularCochains.Cohomology (TopCat.of Unit) n) :=
  SingularContractible.isZero_point_cohomology n hn

theorem realPlane_allPositive (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularCochains.Cohomology (TopCat.of (ℝ × ℝ)) n) :=
  SingularContractible.isZero_cohomology (ℝ × ℝ) n hn

theorem interval_allPositive (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularCochains.Cohomology (TopCat.of (Set.Ioo (-1 : ℝ) 1)) n) := by
  let : ContractibleSpace (Set.Ioo (-1 : ℝ) 1) :=
    (convex_Ioo (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  exact SingularContractible.isZero_cohomology _ n hn

theorem real_cohomology_element_zero (n : ℕ) (hn : n ≠ 0)
    (z : SingularCochains.Cohomology (TopCat.of ℝ) n) : z = 0 :=
  SingularContractible.cohomology_eq_zero ℝ n hn z

theorem contraction_induces_identity (n : ℕ) :
    ∃ x : ℝ, SingularCochains.cohomologyPullback
        (TopCat.ofHom (ContinuousMap.const ℝ x)) n =
      𝟙 (SingularCochains.Cohomology (TopCat.of ℝ) n) := by
  obtain ⟨x, hx⟩ := id_nullhomotopic ℝ
  refine ⟨x, ?_⟩
  have h := SingularHomotopy.cohomologyPullback_eq_of_homotopic hx n
  simpa using h.symm

theorem original_constants_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (q : ℚ) :
    SingularCochains.cohomologyPullback (TopCat.ofHom f) 0
        ((SingularCochains.cohomologyZeroIso Y).inv (SingularDegreeZero.constantClass Y q)) =
      (SingularCochains.cohomologyZeroIso X).inv (SingularDegreeZero.constantClass X q) :=
  SingularDegreeZeroNaturality.pullback_constantClass f q

theorem original_degreeZero_evaluation (q : ℚ) :
    SingularContractible.cohomologyZeroEquiv ℝ 0
        ((SingularCochains.cohomologyZeroIso ℝ).inv (SingularDegreeZero.constantClass ℝ q)) = q := by
  change SingularDegreeZero.equivConstants ℝ 0
    ((SingularCochains.cohomologyZeroIso ℝ).hom
      ((SingularCochains.cohomologyZeroIso ℝ).inv (SingularDegreeZero.constantClass ℝ q))) = q
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  rfl

end SingularHomotopyVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularHomotopy.dualHomotopy,
      `HodgeConjecture.SingularHomotopy.cochainHomotopy,
      `HodgeConjecture.SingularHomotopy.cohomologyPullback_eq_of_homotopy,
      `HodgeConjecture.SingularHomotopy.cohomologyPullback_eq_of_homotopic,
      `HodgeConjecture.SingularHomotopy.homotopyEquivIso,
      `HodgeConjecture.SingularHomotopy.homeomorphIso,
      `HodgeConjecture.SingularContractible.isZero_cohomology_of_totallyDisconnected,
      `HodgeConjecture.SingularContractible.isZero_point_cohomology,
      `HodgeConjecture.SingularContractible.isZero_cohomology,
      `HodgeConjecture.SingularContractible.cohomology_eq_zero,
      `HodgeConjecture.SingularContractible.cohomologyZeroEquiv,
      `HodgeConjecture.SingularDegreeZeroNaturality.representative,
      `HodgeConjecture.SingularDegreeZeroNaturality.cohomologyZeroIso_apply,
      `HodgeConjecture.SingularDegreeZeroNaturality.representative_pullback,
      `HodgeConjecture.SingularDegreeZeroNaturality.cohomologyZeroIso_pullback,
      `HodgeConjecture.SingularDegreeZeroNaturality.cohomologyZeroIso_inv_pullback,
      `HodgeConjecture.SingularDegreeZeroNaturality.constantClass,
      `HodgeConjecture.SingularDegreeZeroNaturality.pullback_constantClass,
      `SingularHomotopyVerification.point_allPositive,
      `SingularHomotopyVerification.realPlane_allPositive,
      `SingularHomotopyVerification.interval_allPositive,
      `SingularHomotopyVerification.real_cohomology_element_zero,
      `SingularHomotopyVerification.contraction_induces_identity,
      `SingularHomotopyVerification.original_constants_natural,
      `SingularHomotopyVerification.original_degreeZero_evaluation] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
