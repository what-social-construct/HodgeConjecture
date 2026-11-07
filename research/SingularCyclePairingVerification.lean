module

public import HodgeConjecture.Realization.Betti.SingularCyclePairing
public import HodgeConjecture.Realization.Betti.CochainDualComparison
public import Lean.Util.CollectAxioms

@[expose] public section

/-! Original finite-chain evaluation, Stokes and actual small/full compatibility. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex Opposite Simplicial HodgeConjecture
open SingularCyclePairing

namespace SingularCyclePairingVerification

example (S : SSet.{0}) (n : ℕ) (σ τ : S.obj (op ⦋n⦌))
    (φ : SubcomplexCochains.Cochain S n) :
    evaluation S n (SingularChainCoordinates.coordinates S n
      ((3 : ℚ) • Finsupp.single σ 1 - (2 : ℚ) • Finsupp.single τ 1)) φ =
        3 * φ σ - 2 * φ τ := by
  rw [evaluation_coordinates, map_sub, map_smul, map_smul]
  simp [Finsupp.llift_apply, Finsupp.lift_apply]

example (S : SSet.{0}) (n : ℕ)
    (b : (SingularChainCoordinates.complex S).X (n + 1))
    (φ : SubcomplexCochains.Cochain S n)
    (hφ : SubcomplexCochains.differential S n φ = 0) :
    evaluation S n ((SingularChainCoordinates.complex S).d (n + 1) n b) φ = 0 :=
  evaluation_boundary_eq_zero S n b φ hφ

example (S : SSet.{0}) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0)
    (φ : SubcomplexCochains.Cochain S n) :
    evaluation S (n + 1) c (SubcomplexCochains.differential S n φ) = 0 :=
  evaluation_differential_eq_zero S n c hc φ

example {S T : SSet.{0}} (f : S ⟶ T) (n : ℕ)
    (c : (SingularChainCoordinates.complex S).X (n + 1))
    (hc : (SingularChainCoordinates.complex S).d (n + 1) n c = 0) :
    homologyMap (SubcomplexCochains.pullback f) (n + 1) ≫ pairing S n c hc =
      pairing T n ((SSet.chainComplexMap f (ModuleCat.of ℚ ℚ)).f (n + 1) c)
        (chainMap_closed f n c hc) := pairing_pullback f n c hc _

/-- The actual full-to-small restriction pairs with exactly the original native inclusion. -/
theorem actual_cover_pairing (X : TopCat.{0}) (U V : Set X) (n : ℕ)
    (c : (SingularChainCoordinates.complex
      (SingularSubcomplexes.smallSingular X U V).toSSet).X (n + 1))
    (hc : (SingularChainCoordinates.complex
      (SingularSubcomplexes.smallSingular X U V).toSSet).d (n + 1) n c = 0) :
    homologyMap (CochainDualComparison.smallRestriction X U V) (n + 1) ≫
      pairing (SingularSubcomplexes.smallSingular X U V).toSSet n c hc =
        pairing (TopCat.toSSet.obj X) n
          ((SubcomplexChainCoordinates.inclusion
            (SingularSubcomplexes.smallSingular X U V)).f (n + 1) c)
          (chainMap_closed (SingularSubcomplexes.smallSingular X U V).ι n c hc) :=
  pairing_pullback (SingularSubcomplexes.smallSingular X U V).ι n c hc _

end SingularCyclePairingVerification

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularCyclePairing.evaluation,
      `HodgeConjecture.SingularCyclePairing.evaluation_add,
      `HodgeConjecture.SingularCyclePairing.evaluation_smul,
      `HodgeConjecture.SingularCyclePairing.evaluation_coordinates,
      `HodgeConjecture.SingularCyclePairing.evaluation_single,
      `HodgeConjecture.SingularCyclePairing.evaluation_differential,
      `HodgeConjecture.SingularCyclePairing.evaluation_differential_eq_zero,
      `HodgeConjecture.SingularCyclePairing.evaluation_boundary_eq_zero,
      `HodgeConjecture.SingularCyclePairing.evaluation_pullback,
      `HodgeConjecture.SingularCyclePairing.toCycles_evaluation_eq_zero,
      `HodgeConjecture.SingularCyclePairing.pairing,
      `HodgeConjecture.SingularCyclePairing.pairing_homologyπ,
      `HodgeConjecture.SingularCyclePairing.pairing_cocycleClass,
      `HodgeConjecture.SingularCyclePairing.chainMap_closed,
      `HodgeConjecture.SingularCyclePairing.pairing_pullback,
      `SingularCyclePairingVerification.actual_cover_pairing] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
