import HodgeConjecture.Cycles.LocalOrderLocalization
import HodgeConjecture.Cycles.Examples.LocalOrder
import Lean.Util.CollectAxioms

/-!
SP105: actual localized principal quotients and their local-order consumer.
Run with `lake env lean research/LocalizedPrincipalQuotientVerification.lean`.

The checks cover an actual denominator, localization of a ring with
nilpotents, and a nonzero localized quotient length at the prime `(2)`.
-/

set_option autoImplicit false

noncomputable section

open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

-- The representative formula respects the denominator, as well as the numerator.
example : localizedPrincipalQuotientEquiv ℤ (Submonoid.powers (3 : ℤ)) 2
    (LocalizedModule.mk (Ideal.Quotient.mk (Ideal.span {(2 : ℤ)}) 1)
      ⟨3, Submonoid.mem_powers 3⟩) =
      Ideal.Quotient.mk _ (IsLocalization.mk' (Localization (Submonoid.powers (3 : ℤ)))
        (1 : ℤ) ⟨3, Submonoid.mem_powers 3⟩) :=
  localizedPrincipalQuotientEquiv_fraction ℤ _ 2 1 _

-- Inverting a nilpotent is allowed: the comparison also covers a zero localization.
example : Module.length (Localization (Submonoid.powers (2 : ZMod 4)))
    (LocalizedModule (Submonoid.powers (2 : ZMod 4)) (ZMod 4 ⧸ Ideal.span {(2 : ZMod 4)})) = 0 :=
  length_localized_principalQuotient_eq_zero (ZMod 4) _ 2 (Submonoid.mem_powers 2)

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2

-- Localization at `(2)` retains the simple principal quotient, with length one.
example : Module.length (Localization.AtPrime (Ideal.span {(2 : ℤ)}))
    (LocalizedModule (Ideal.span {(2 : ℤ)}).primeCompl (ℤ ⧸ Ideal.span {(2 : ℤ)})) = 1 := by
  let A := Localization.AtPrime (Ideal.span {(2 : ℤ)})
  have hJ : Ideal.span {algebraMap ℤ A 2} = IsLocalRing.maximalIdeal A := by
    simpa only [Ideal.map_span, Set.image_singleton] using
      (Localization.AtPrime.map_eq_maximalIdeal (I := Ideal.span {(2 : ℤ)}))
  letI : (Ideal.span {algebraMap ℤ A 2}).IsMaximal :=
    hJ.symm ▸ IsLocalRing.maximalIdeal.isMaximal A
  letI : IsSimpleModule A (A ⧸ Ideal.span {algebraMap ℤ A 2}) :=
    isSimpleModule_iff_isCoatom.mpr (inferInstance : (Ideal.span {algebraMap ℤ A 2}).IsMaximal).1
  rw [length_localized_principalQuotient]
  exact Module.length_eq_one _ _

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CommutativeAlgebra.localizedPrincipalQuotientEquiv,
    `HodgeConjecture.CommutativeAlgebra.localizedPrincipalQuotientEquiv_mk,
    `HodgeConjecture.CommutativeAlgebra.localizedPrincipalQuotientEquiv_fraction,
    `HodgeConjecture.CommutativeAlgebra.length_localized_principalQuotient,
    `HodgeConjecture.CommutativeAlgebra.length_localized_principalQuotient_eq_zero,
    `HodgeConjecture.SchemeCycles.localOrder_atPrime_algebraMap_eq_localized_length,
    `HodgeConjecture.SchemeCycles.localOrder_atPrime_fraction_eq_localized_length,
    `HodgeConjecture.SchemeCycles.localOrder_atPrime_eq_zero_of_not_mem]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let (_, state) := ((CollectAxioms.collect declaration).run env).run {}
    let actual := state.axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
