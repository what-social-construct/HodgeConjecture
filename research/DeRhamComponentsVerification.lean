module

import HodgeConjecture.Realization.DeRham.AffineComponents
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Positive-dimensional degree-zero calculations and the additive-torsion boundary. -/

open HodgeConjecture KaehlerDifferential
open scoped Polynomial

noncomputable section

/-- Polynomial invariance does not require the coefficient algebra to be reduced. -/
example (A : Type) [CommRing A] [Algebra ℚ A] :
    AffineDeRham.H0 ℚ A[X] ≃ₐ[ℚ] AffineDeRham.H0 ℚ A := by
  letI : HasUniqueDiv A := .of_module_rat A
  exact AffineDeRham.polynomialCoordinates ℚ A

/-- Repeating the same original-coordinate calculation computes the affine plane. -/
example : AffineDeRham.H0 ℚ (ℚ[X])[X] ≃ₐ[ℚ] ℚ :=
  (AffineDeRham.polynomialCoordinates ℚ ℚ[X]).trans (AffineDeRham.affineLineCoordinates ℚ)

/-- The basis is genuinely componentwise, rather than the single global constant. -/
example :
    (AffineDeRham.affineLinesBasis ℚ (Fin 3) 1).val 0 = 0 ∧
      (AffineDeRham.affineLinesBasis ℚ (Fin 3) 1).val 1 = 1 := by
  simp

/-- Three affine components have three independent closed-function classes. -/
example : Module.finrank ℚ (AffineDeRham.H0 ℚ (Fin 3 → ℚ[X])) = 3 := by
  rw [AffineDeRham.affineLines_finrank]
  rfl

/-- Empty products retain the zero-dimensional cohomology vector space. -/
example : Module.finrank ℚ (AffineDeRham.H0 ℚ (Fin 0 → ℚ[X])) = 0 := by
  rw [AffineDeRham.affineLines_finrank]
  rfl

/-- Changing evaluation points on an affine component does not change a closed class. -/
example (p : AffineDeRham.H0 ℚ (Fin 3 → ℚ[X])) :
    Polynomial.aeval (2 : ℚ) (p.val 1) = Polynomial.aeval (7 : ℚ) (p.val 1) := by
  rw [AffineDeRham.affineLines_eval_closed, AffineDeRham.affineLines_eval_closed]

/-- In characteristic two a nonconstant square is closed: torsion-freeness is essential. -/
example :
    D (ZMod 2) (ZMod 2)[X] (Polynomial.X ^ 2) = 0 ∧
      (Polynomial.X ^ 2 : (ZMod 2)[X]) ≠ Polynomial.C ((Polynomial.X ^ 2).coeff 0) := by
  constructor
  · rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_self]
    simp only [zero_smul]
  · intro h
    have h' := congrArg (fun p : (ZMod 2)[X] ↦ p.coeff 2) h
    norm_num at h'

end

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.AffineDeRham.derivative_eq_zero_of_closed,
      `HodgeConjecture.AffineDeRham.closed_C_iff,
      `HodgeConjecture.AffineDeRham.eq_C_of_closed,
      `HodgeConjecture.AffineDeRham.closed_polynomial_iff,
      `HodgeConjecture.AffineDeRham.polynomialCoordinates,
      `HodgeConjecture.AffineDeRham.polynomialCohomologyZeroIso,
      `HodgeConjecture.AffineDeRham.eval_closed,
      `HodgeConjecture.AffineDeRham.affineLineCoordinates,
      `HodgeConjecture.AffineDeRham.idempotent_closed,
      `HodgeConjecture.AffineDeRham.closed_affineLines_iff,
      `HodgeConjecture.AffineDeRham.affineLinesCoordinates,
      `HodgeConjecture.AffineDeRham.affineLinesCohomologyZeroIso,
      `HodgeConjecture.AffineDeRham.affineLinesBasis,
      `HodgeConjecture.AffineDeRham.affineLinesBasis_isIdempotent,
      `HodgeConjecture.AffineDeRham.affineLines_finrank] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
