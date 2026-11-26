module
import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate
public meta import HodgeConjecture.LinearAlgebra.ModularRankCertificate
public meta import Mathlib.Algebra.Field.ZMod
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace HodgeConjecture.FiniteCoverageCertificateVerification

open ModularRankCertificate

def good : Certificate (Fin 2) where
  denominator := 1
  integerMatrix := 1
  modulus := 3
  modularInverse := 1

-- All gates pass on an exact identity profile.
example : check (1 : Matrix (Fin 2) (Fin 2) ℚ) good = true := by decide +kernel

-- A finite field is required, even if the inverse equation holds in a composite residue ring.
example : check (1 : Matrix (Fin 2) (Fin 2) ℚ)
    { good with modulus := 4, modularInverse := 1 } = false := by decide +kernel

-- A wrong inverse fails independently of the model's rational data.
example : check (1 : Matrix (Fin 2) (Fin 2) ℚ)
    { good with modularInverse := 0 } = false := by decide +kernel

-- Modulo three, 4I and I agree. The exact rational binding gate still rejects substitution.
example : check ((4 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) good = false := by decide +kernel

-- Correctly bound large coefficients are allowed: nonzero modular rank lifts without a size bound.
example : check ((4 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
    { good with integerMatrix := (4 : ℤ) • 1 } = true := by decide +kernel

-- Rational denominators are checked in characteristic zero before modular reduction of B.
example : check ((1 / 2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
    { good with denominator := 2 } = true := by decide +kernel

-- The denominator may share the prime because the checker reduces B, not a nonexistent map ℚ → Fp.
example : check ((1 / 3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ))
    { good with denominator := 3 } = true := by decide +kernel

-- A singular candidate family fails the rank gate.
example : check (0 : Matrix (Fin 2) (Fin 2) ℚ)
    { good with integerMatrix := 0 } = false := by decide +kernel

-- A zero-dimensional target still cannot bypass the explicit denominator gate.
example : check (1 : Matrix (Fin 0) (Fin 0) ℚ)
    { denominator := 0, integerMatrix := 1, modulus := 3, modularInverse := 1 } = false := by decide +kernel

-- Kernel reduction and the executable evaluator agree on the accepted and forged profiles.
#eval (check (1 : Matrix (Fin 2) (Fin 2) ℚ) good,
  check ((4 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) good)

noncomputable section

open ProjectiveLineCoverageCertificate

-- Arithmetic acceptance cannot replace the mandatory geometric column proofs.
example (C : FiniteCoverageCertificate.Certificate model basis)
    (zeroCycles : ∀ i, C.cycles i = 0) (identityColumns : C.coordinates = 1) : False := by
  have h := congrArg basis.equivFun (C.column_binding ())
  simp only [zeroCycles, map_zero, basis.equivFun.apply_symm_apply] at h
  have hval := congrFun h ()
  simp [identityColumns] at hval

open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.ModularRankCertificate.check_eq_true_iff,
      `HodgeConjecture.ModularRankCertificate.integer_det_ne_zero_of_check,
      `HodgeConjecture.ModularRankCertificate.rational_det_ne_zero_of_check,
      `HodgeConjecture.ModularRankCertificate.mulVec_surjective_of_check,
      `HodgeConjecture.FiniteCoverageCertificate.coordinate_combination,
      `HodgeConjecture.FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check,
      `HodgeConjecture.FiniteCoverageCertificate.exists_cycle_of_check,
      `HodgeConjecture.FiniteCoverageCertificate.of_harmonic,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.targetEquiv,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.basis_coordinates,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.basis_vector,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.harmonicRealization_injective,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.certificate,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.accepted,
      `HodgeConjecture.ProjectiveLineCoverageCertificate.model_satisfies_from_aggregate] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS aggregate axiom boundary: {declaration}; {axioms.toList}"

end
end HodgeConjecture.FiniteCoverageCertificateVerification
