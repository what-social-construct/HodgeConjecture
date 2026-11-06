module

import HodgeConjecture.Realization.DeRham.Core
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Unramified.Field
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! Affine de Rham and algebra-trace checks without importing project
scheme cycles, Chow models or Betti realization. -/

open HodgeConjecture CategoryTheory KaehlerDifferential
open scoped Polynomial BigOperators TensorProduct

noncomputable section

/-- The constructed complex has a nonzero first arrow on the affine line. -/
example :
    ((deRhamComplex ℚ ℚ[X]).d 0 1).hom
      ((exteriorPower.zeroEquiv ℚ[X] Ω[ℚ[X]⁄ℚ]).symm Polynomial.X) ≠ 0 := by
  intro h
  rw [show (1 : ℕ) = 0 + 1 from rfl, deRhamComplex_d] at h
  change deRhamDifferential (A := ℚ) 0
    ((exteriorPower.zeroEquiv ℚ[X] Ω[ℚ[X]⁄ℚ]).symm Polynomial.X) = 0 at h
  have h' := congrArg (exteriorPower.oneEquiv ℚ[X] Ω[ℚ[X]⁄ℚ]) h
  rw [AffineDeRham.differential_zero, map_zero] at h'
  have h'' := congrArg (KaehlerDifferential.polynomialEquiv ℚ) h'
  simpa [KaehlerDifferential.polynomialEquiv_D] using h''

/-- Finite extensions of ℚ need no chosen splitting or supplied degree law. -/
example (L : Type) [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L] :
    ∃ T : RationalDegreeTransfer (AffineDeRham.H0 ℚ L) (AffineDeRham.H0 ℚ ℚ),
      T.degree = Module.finrank ℚ L ∧ Function.Injective T.pull ∧
        IsIdempotentElem T.normalizedProjector := by
  let : Algebra.FormallyUnramified ℚ L := Algebra.FormallyUnramified.of_isSeparable ℚ L
  let T := RationalAffineDeRham.finiteFreeTransfer ℚ L (Module.finrank ℚ L)
    (Module.finrank_pos_iff.mpr inferInstance).ne' (Module.finBasis ℚ L)
  exact ⟨T, rfl, T.pull_injective, T.normalizedProjector_isIdempotent⟩

/-- The trace is the ordinary multiplication-operator trace of nonconstant coefficients. -/
example : Algebra.trace ℚ (Fin 3 → ℚ) ![1, 3, 2] = 6 := by
  rw [AffineDeRham.algebraTrace_pi]
  norm_num [Fin.sum_univ_succ]

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
      `HodgeConjecture.AffineDeRham.algebraTrace_pi,
      `HodgeConjecture.RationalAffineDeRham.finiteFreeTransfer,
      `HodgeConjecture.RationalAffineDeRham.finitePullback_injective] do
    let axioms ← Lean.collectAxioms declaration
    for name in axioms do
      unless permitted.contains name do
        throwError "Unexpected axiom {name} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
