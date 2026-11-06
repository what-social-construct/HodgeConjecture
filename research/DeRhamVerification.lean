module

import HodgeConjecture.Realization.DeRham
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Actual de Rham differentials, algebra trace, geometric degree and
Chow–Betti compatibility. Nonuniform and empty fibers test the trace separately from a
constant-degree assumption. The affine-core examples are checked independently
in `DeRhamCoreVerification.lean`. -/

open HodgeConjecture CategoryTheory KaehlerDifferential
open scoped Polynomial BigOperators TensorProduct

noncomputable section

private def nonuniform : Fin 3 → Fin 3 := fun s ↦ if s = 2 then 1 else 0

private def thirdPoint : SplitZeroCycles.Chow ℂ (Fin 3) ℚ :=
  SplitZeroCycles.classMap ℂ (Fin 3) ℚ (SplitZeroCycles.pointCycle ℂ (Fin 3) ℚ 2)

/-- A point contributes one to its actual image component. -/
example : SplitDeRham.coordinates ℂ (Fin 3)
    (SplitDeRham.pushforward ℂ nonuniform (SplitDeRham.cycleClass (Fin 3) thirdPoint)) 1 = 1 := by
  simp only [SplitDeRham.coordinates_pushforward, thirdPoint,
    SplitDeRham.cycleClass_pointCycle]
  norm_num [Fin.sum_univ_succ, nonuniform]

/-- The same nonuniform map has a genuinely empty third fiber. -/
example : SplitDeRham.coordinates ℂ (Fin 3)
    (SplitDeRham.pushforward ℂ nonuniform (SplitDeRham.cycleClass (Fin 3) thirdPoint)) 2 = 0 := by
  simp only [SplitDeRham.coordinates_pushforward, thirdPoint,
    SplitDeRham.cycleClass_pointCycle]
  norm_num [Fin.sum_univ_succ, nonuniform]

/-- Actual two-sheet projection gives degree two on the de Rham kernel. -/
example (a : SplitDeRham.Cohomology ℂ (Fin 2)) :
    SplitDeRham.pushforward ℂ (Prod.fst : Fin 2 × Fin 2 → Fin 2)
      (SplitDeRham.pullback ℂ Prod.fst a) = 2 • a := by
  apply SplitDeRham.pushforward_pullback ℂ _ 2 _ a
  intro i
  classical
  calc
    _ = (Finset.product {i} (Finset.univ : Finset (Fin 2))).card := by
      congr 1
      ext s
      rcases s with ⟨s, t⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.product_eq_sprod,
        Finset.mem_product,
        Finset.mem_singleton, and_true]
    _ = 2 := by simp

/-- The comparison handles arbitrary complex coefficients, beyond the rational image. -/
example : SplitHodgeStructure.complexCoordinates (Fin 3)
    (SplitDeRham.bettiComparison (Fin 3)
      (SplitDeRham.pushforward ℂ nonuniform
        ((SplitDeRham.coordinates ℂ (Fin 3)).symm ![Complex.I, 1, 0]))) 0 = Complex.I + 1 := by
  simp only [SplitDeRham.complexCoordinates_bettiComparison,
    SplitDeRham.coordinates_pushforward, AlgEquiv.apply_symm_apply]
  norm_num [Fin.sum_univ_succ, nonuniform]

/-- Empty-source transfer remains the zero map. -/
example (a : SplitDeRham.Cohomology ℂ (Fin 0)) :
    SplitDeRham.pushforward ℂ (Fin.elim0 : Fin 0 → Fin 2) a = 0 := by
  apply (SplitDeRham.coordinates ℂ (Fin 2)).injective
  ext i
  simp [SplitDeRham.coordinates_pushforward]

end

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `KaehlerDifferential.deRhamDifferential,
      `KaehlerDifferential.deRhamDifferential_unique,
      `KaehlerDifferential.deRhamDifferential_comp_deRhamDifferential,
      `KaehlerDifferential.deRhamComplex,
      `HodgeConjecture.AffineDeRham.kernelCoordinates,
      `HodgeConjecture.AffineDeRham.cohomologyZeroIso,
      `HodgeConjecture.AffineDeRham.map,
      `HodgeConjecture.AffineDeRham.finiteTrace,
      `HodgeConjecture.AffineDeRham.finiteTrace_finitePullback_of_basis,
      `HodgeConjecture.AffineDeRham.finiteTrace_finitePullback_eq_geometricRank,
      `HodgeConjecture.AffineDeRham.finiteTrace_finitePullback_eq_cycleDegree,
      `HodgeConjecture.RationalAffineDeRham.finiteFreeTransfer,
      `HodgeConjecture.RationalAffineDeRham.finitePullback_injective,
      `HodgeConjecture.finiteFiberSum,
      `HodgeConjecture.SplitDeRham.pushforward_projection_eq_algebraTrace,
      `HodgeConjecture.SplitDeRham.pushforward_pullback,
      `HodgeConjecture.SplitDeRham.cycleClass,
      `HodgeConjecture.SplitDeRham.bettiComparison,
      `HodgeConjecture.SplitDeRham.bettiComparison_cycleClass,
      `HodgeConjecture.SplitDeRham.cycleClass_pullback,
      `HodgeConjecture.SplitDeRham.cycleClass_pushforward,
      `HodgeConjecture.SplitDeRham.bettiComparison_pullback,
      `HodgeConjecture.SplitDeRham.bettiComparison_pushforward,
      `HodgeConjecture.SplitDeRham.cycleClass_intersection,
      `HodgeConjecture.SplitDeRham.cycleClass_pointCycle] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
