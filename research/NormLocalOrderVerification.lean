import HodgeConjecture.Cycles.LocalOrderNormFormula
import HodgeConjecture.Cycles.Examples.LocalOrder
import Lean.Util.CollectAxioms

/-!
SP106: the full weighted norm--order identity of Stacks 02MJ.
Run with `lake env lean research/NormLocalOrderVerification.lean`.

Checks include a nonlocal finite algebra and the signed norm-order sum
at the prime `(2)` of `ℤ`.
The final test uses an inverse fraction, so its value is negative.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles
open scoped HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField

attribute [local instance] finiteAlgebra_maximal_liesOver atPrime_krullDimLE_one

-- Semilocality is derived even when the finite algebra is not local or a domain.
example : Finite (MaximalSpectrum (ℚ × ℚ)) :=
  finiteAlgebra_maximalSpectrum_finite ℚ (ℚ × ℚ)

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2

private abbrev A := Localization.AtPrime (Ideal.span {(2 : ℤ)})

private theorem two_localized_order :
    localOrder A (Units.mk0 (2 : ℚ) two_ne_zero) = 1 := by
  have hJ : Ideal.span {algebraMap ℤ A 2} = IsLocalRing.maximalIdeal A := by
    simpa only [Ideal.map_span, Set.image_singleton] using
      (Localization.AtPrime.map_eq_maximalIdeal (I := Ideal.span {(2 : ℤ)}))
  letI : (Ideal.span {algebraMap ℤ A 2}).IsMaximal :=
    hJ.symm ▸ IsLocalRing.maximalIdeal.isMaximal A
  letI : IsSimpleModule A (A ⧸ Ideal.span {algebraMap ℤ A 2}) :=
    isSimpleModule_iff_isCoatom.mpr (inferInstance : (Ideal.span {algebraMap ℤ A 2}).IsMaximal).1
  have h := localOrder_atPrime_algebraMap_eq_localized_length ℤ ℚ
    (Ideal.span {(2 : ℤ)}) 2 two_ne_zero
  rw [length_localized_principalQuotient, Module.length_eq_one] at h
  simpa using h

-- The complete formula applies without supplied semilocal or residue-finiteness data.
example : (∑ᶠ q : MaximalSpectrum A,
    (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (A ⧸ q.asIdeal) : ℤ) *
      localOrder (Localization.AtPrime q.asIdeal) (Units.mk0 (2 : ℚ) two_ne_zero)) = 1 := by
  rw [← localOrder_norm_eq_sum A ℚ ℚ A, Algebra.norm_self]
  simpa using two_localized_order

-- Arbitrary units include denominators: the weighted sum can be strictly negative.
example : (∑ᶠ q : MaximalSpectrum A,
    (Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (A ⧸ q.asIdeal) : ℤ) *
      localOrder (Localization.AtPrime q.asIdeal) (Units.mk0 (2 : ℚ) two_ne_zero)⁻¹) = -1 := by
  rw [← localOrder_norm_eq_sum A ℚ ℚ A, Algebra.norm_self]
  simpa [localOrder_inv] using congrArg Neg.neg two_localized_order

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CommutativeAlgebra.finiteAlgebra_maximal_liesOver,
    `HodgeConjecture.CommutativeAlgebra.finiteAlgebra_residue_finite,
    `HodgeConjecture.CommutativeAlgebra.finiteAlgebra_maximalSpectrum_finite,
    `HodgeConjecture.CommutativeAlgebra.integralAlgebra_krullDimLE_one,
    `HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField.algebra,
    `HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField.scalarTower,
    `HodgeConjecture.CommutativeAlgebra.AtPrimeFractionField.isFractionRing,
    `HodgeConjecture.CommutativeAlgebra.atPrime_krullDimLE_one,
    `HodgeConjecture.SchemeCycles.localOrder_norm_eq_sum]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    let actual := state.axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
