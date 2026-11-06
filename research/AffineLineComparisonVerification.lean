module

import HodgeConjecture.Realization.DeRham.AffineLineComparison
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Actual affine-line topology, singular cocycles, tensor coefficients and
polynomial pullback compatibility. The disconnected example guards the
path-connectedness hypothesis independently of the affine-line instance. -/

open HodgeConjecture AffineLineComplexPoints
open scoped Polynomial TensorProduct

noncomputable section

/-- The point map is actual nonlinear polynomial evaluation. -/
example : coordinateHomeomorph
    (map (Polynomial.X ^ 2 + Polynomial.C Complex.I) (evalPoint 2)) = 4 + Complex.I := by
  norm_num

/-- Actual singular cocycles have equal evaluations along the complex line. -/
example (h : AffineLineDeRham.Betti) :
    SingularDegreeZero.eval Point h (evalPoint 0) =
      SingularDegreeZero.eval Point h (evalPoint Complex.I) :=
  SingularDegreeZero.eval_eq Point h _ _

/-- A zero-cochain separating two points fails the actual cocycle equation. -/
example : (fun σ : SingularDegreeZero.Simplex Point 0 ↦
      if coordinateHomeomorph (σ default) = 0 then (0 : ℚ) else 1) ∉
    SingularDegreeZero.cocycles Point := by
  intro hc
  let h : AffineLineDeRham.Betti := ⟨_, hc⟩
  have he := SingularDegreeZero.eval_eq Point h (evalPoint 0) (evalPoint 1)
  norm_num [h, SingularDegreeZero.eval_apply] at he

private abbrev TwoPoints := Fin 2
private instance : TopologicalSpace TwoPoints := ⊥
private instance : DiscreteTopology TwoPoints := ⟨rfl⟩

private def componentLabel : C(ℂ ⊕ ℂ, TwoPoints) :=
  ⟨Sum.elim (fun _ ↦ 0) (fun _ ↦ 1), continuous_const.sumElim continuous_const⟩

private def separateComponents : SingularDegreeZero.H0 (ℂ ⊕ ℂ) :=
  SingularDegreeZero.pullback componentLabel
    (SingularDegreeZero.ofFunctions TwoPoints (fun i ↦ (i.val : ℚ)))

/-- Different path components retain independent cohomology values. -/
example :
    SingularDegreeZero.eval (ℂ ⊕ ℂ) separateComponents (Sum.inl 0) = 0 ∧
      SingularDegreeZero.eval (ℂ ⊕ ℂ) separateComponents (Sum.inr 0) = 1 := by
  constructor <;> rfl

/-- A genuinely complex tensor recovers the original closed polynomial. -/
example :
    (AffineLineDeRham.bettiComparison.symm
      (Complex.I ⊗ₜ[ℚ] SingularDegreeZero.constantClass Point 1)).val =
        Polynomial.C Complex.I := by
  rw [← AffineLineDeRham.bettiComparison_constant, AlgEquiv.symm_apply_apply]
  exact AffineDeRham.affineLineCoordinates_symm_coe ℂ _

/-- Complexification contains classes outside the canonical rational image. -/
example : AffineLineDeRham.bettiComparison (AffineLineDeRham.deRhamCoordinates.symm Complex.I) ∉
    Set.range AffineLineDeRham.rationalEmbedding := by
  simpa only [AffineLineDeRham.bettiComparison, AlgEquiv.trans_apply,
    AlgEquiv.apply_symm_apply] using AffineLineDeRham.imaginaryClass_not_rational

/-- Naturality includes nonlinear and constant self-maps, neither needing an inverse. -/
example (a : AffineLineDeRham.DeRham) :
    AffineLineDeRham.bettiComparison
        (AffineLineDeRham.deRhamPullback (Polynomial.X ^ 2 + Polynomial.C Complex.I) a) =
      AffineLineDeRham.complexPullback (Polynomial.X ^ 2 + Polynomial.C Complex.I)
        (AffineLineDeRham.bettiComparison a) ∧
    AffineLineDeRham.bettiComparison
        (AffineLineDeRham.deRhamPullback (Polynomial.C Complex.I) a) =
      AffineLineDeRham.complexPullback (Polynomial.C Complex.I)
        (AffineLineDeRham.bettiComparison a) :=
  ⟨AffineLineDeRham.bettiComparison_pullback _ a,
    AffineLineDeRham.bettiComparison_pullback _ a⟩

/-- Scalar-extended evaluation is evaluated on the actual point and cocycle. -/
example : AffineLineDeRham.complexEvaluation (evalPoint Complex.I)
    (Complex.I ⊗ₜ[ℚ] SingularDegreeZero.constantClass Point 3) = 3 * Complex.I := by
  simp [mul_comm]

end

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularDegreeZero.face_pathSimplex_zero,
      `HodgeConjecture.SingularDegreeZero.face_pathSimplex_one,
      `HodgeConjecture.SingularDegreeZero.eval_eq_of_joined,
      `HodgeConjecture.SingularDegreeZero.equivConstants,
      `HodgeConjecture.SingularDegreeZero.equivConstants_pullback,
      `HodgeConjecture.AffineLineComplexPoints.coordinateHomeomorph,
      `HodgeConjecture.AffineLineComplexPoints.pointPathConnectedSpace,
      `HodgeConjecture.AffineLineComplexPoints.schemeMorphism_map,
      `HodgeConjecture.AffineLineDeRham.bettiCoordinates,
      `HodgeConjecture.AffineLineDeRham.complexCoordinates,
      `HodgeConjecture.AffineLineDeRham.complexEvaluation,
      `HodgeConjecture.AffineLineDeRham.complexEvaluation_eq_coordinates,
      `HodgeConjecture.AffineLineDeRham.rationalEmbedding_injective,
      `HodgeConjecture.AffineLineDeRham.bettiComparison,
      `HodgeConjecture.AffineLineDeRham.bettiComparison_evaluation,
      `HodgeConjecture.AffineLineDeRham.bettiComparison_constant,
      `HodgeConjecture.AffineLineDeRham.bettiComparison_rational,
      `HodgeConjecture.AffineLineDeRham.bettiComparison_mul,
      `HodgeConjecture.AffineLineDeRham.cohomologyZeroComparison,
      `HodgeConjecture.AffineLineDeRham.deRhamPullback,
      `HodgeConjecture.AffineLineDeRham.bettiPullback,
      `HodgeConjecture.AffineLineDeRham.bettiComparison_pullback,
      `HodgeConjecture.AffineLineDeRham.imaginaryClass_not_rational] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
