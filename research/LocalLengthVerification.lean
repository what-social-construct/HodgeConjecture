module

import HodgeConjecture.Cycles.LocalOrderLength
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP103: local length comparison, its actual principal-quotient consumer,
and agreement with dimension over fields. Run with
`lake env lean research/LocalLengthVerification.lean`.

These checks use finite algebras to supply the residue-degree finiteness
automatically, retain the sign of inverse orders, and compare the canonical
residue-field degree with the original field-extension degree. The axiom
audit covers all six public declarations in the two new modules.
-/

set_option autoImplicit false

open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

noncomputable section

section FiniteLocalAlgebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]

-- Finiteness of the algebra supplies the residue extension; no domain or
-- Noetherian assumption is needed for restriction of finite length.
example (M : Type*) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hM : IsFiniteLength B M) :
    IsFiniteLength A M ∧
      Module.length A M =
        (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) : ℕ∞) *
          Module.length B M :=
  ⟨isFiniteLength_restrictScalars_of_localHom A B M hM,
    length_restrictScalars_of_localHom A B M hM⟩

variable [IsDomain B] [IsNoetherianRing B] [Ring.KrullDimLE 1 B]

-- The existing principal-quotient theorem supplies finite length upstairs.
-- There is still no normality assumption on the relation carrier.
example (b : B) (hb : b ≠ 0) :
    Module.length A (B ⧸ Ideal.span {b}) ≠ ⊤ := by
  apply Module.length_ne_top_iff.mpr
  exact isFiniteLength_restrictScalars_of_localHom A B _
    (Module.length_ne_top_iff.mp (principalQuotient_length_ne_top B b hb))

example {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
    (b : B) (hb : b ≠ 0) :
    (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) : ℤ) *
      localOrder B (Units.mk0 (algebraMap B L b)
        (by simpa only [map_zero] using (IsFractionRing.injective B L).ne hb))⁻¹ =
      -((Module.length A (B ⧸ Ideal.span {b})).toNat : ℤ) := by
  rw [localOrder_inv, mul_neg, localOrder_algebraMap_length_restrictScalars A B b hb]

end FiniteLocalAlgebra

section Fields

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Module.Finite K L]

-- The canonical residue action gives the original field degree, rather
-- than the degree of a separately supplied scalar structure.
example :
    Module.finrank (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField L) =
      Module.finrank K L := by
  have h := length_residueField K L
  change Module.length K (L ⧸ IsLocalRing.maximalIdeal L) = _ at h
  rw [IsLocalRing.maximalIdeal_eq_bot,
    (AlgEquiv.quotientBot K L).toLinearEquiv.length_eq,
    Module.length_eq_finrank] at h
  exact_mod_cast h.symm

example (M : Type*) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
    [Module.Finite L M] :
    Module.finrank K M =
      Module.finrank (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField L) *
        Module.finrank L M := by
  letI : Module.Finite K M := Module.Finite.trans L M
  have hM : IsFiniteLength L M := Module.length_ne_top_iff.mp (by
    rw [Module.length_eq_finrank]; exact ENat.coe_ne_top _)
  have h := length_restrictScalars_of_localHom K L M hM
  rw [Module.length_eq_finrank, Module.length_eq_finrank] at h
  exact_mod_cast h

end Fields

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CommutativeAlgebra.length_restrictScalars_of_isLocalRing,
    `HodgeConjecture.CommutativeAlgebra.length_residueField,
    `HodgeConjecture.CommutativeAlgebra.length_restrictScalars_of_localHom,
    `HodgeConjecture.CommutativeAlgebra.isFiniteLength_restrictScalars_of_localHom,
    `HodgeConjecture.SchemeCycles.localOrder_algebraMap_length_restrictScalars,
    `HodgeConjecture.SchemeCycles.localOrder_fraction_length_restrictScalars]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
