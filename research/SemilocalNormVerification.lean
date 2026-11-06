module

import HodgeConjecture.Cycles.LocalOrderNorm
import HodgeConjecture.Cycles.Examples.LocalOrder
import Lean.Util.CollectAxioms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
SP104: semilocal length sums and the determinant/norm comparison.
Run with `lake env lean research/SemilocalNormVerification.lean`.

The checks include a ring with two maximal ideals, signed norm orders over
the actual integers/rationals, and a determinant calculation with an arbitrary
lattice (no free-module instance). The axiom audit covers the public API of
all four new modules.
-/

set_option autoImplicit false
noncomputable section

open HodgeConjecture.CommutativeAlgebra HodgeConjecture.SchemeCycles

section Product

variable (K : Type*) [Field K]

local instance : IsArtinianRing (K × K) := isArtinian_of_tower K inferInstance
local instance : Fintype (MaximalSpectrum (K × K)) := Fintype.ofFinite _

-- This is semilocal with two components; no local-ring assumption upstairs.
example : (∑ q : MaximalSpectrum (K × K),
    Module.length K ((K × K) ⧸ q.asIdeal) *
      Module.length (Localization q.asIdeal.primeCompl)
        (LocalizedModule q.asIdeal.primeCompl (K × K))) = 2 := by
  have hM : IsFiniteLength (K × K) (K × K) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower K inferInstance, inferInstance⟩
  rw [← length_restrictScalars_eq_sum_localized (K × K) K (K × K) hM,
    Module.length_prod]
  norm_num

end Product

section GeneralLattice

variable (R K V : Type*) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [FiniteDimensional K V] (M : Submodule R V) [Submodule.IsLattice K M]

-- The inverse sign follows for every lattice, without an R-basis.
example (f : V ≃ₗ[K] V) :
    latticeIndex M (M.map (f.symm.restrictScalars R).toLinearMap) =
      -latticeIndex M (M.map (f.restrictScalars R).toLinearMap) := by
  rw [latticeIndex_eq_localOrder_det R K V M f.symm,
    latticeIndex_eq_localOrder_det R K V M f, LinearEquiv.det_symm, map_inv, localOrder_inv]

-- Restriction to a stable lattice identifies the actual cokernel length.
example (f : V ≃ₗ[K] V) (hf : M.map (f.restrictScalars R).toLinearMap ≤ M) :
    ((Module.length R (M ⧸
      (M.map (f.restrictScalars R).toLinearMap).comap M.subtype)).toNat : ℤ) =
        localOrder R (LinearEquiv.det f) :=
  (localOrder_det_eq_quotient_length R K V M f hf).symm

end GeneralLattice

-- Concrete nonzero order and inverse sign: this tests the norm specialization
-- beyond the zero-order field-base case.
example : localOrder ℤ (Units.map (Algebra.norm ℚ) (Units.mk0 (2 : ℚ) two_ne_zero)) = 1 := by
  have h := localOrder_norm_algebraMap_eq_length ℤ ℚ ℚ ℤ 2 (by norm_num)
  simpa [HodgeConjecture.SchemeCycles.Examples.int_two_quotient_length] using h

example : localOrder ℤ
    (Units.map (Algebra.norm ℚ) ((Units.mk0 (2 : ℚ) two_ne_zero)⁻¹)) = -1 := by
  have h := localOrder_norm_fraction_eq_length ℤ ℚ ℚ ℤ 1 2 one_ne_zero (by norm_num)
  have hz : Module.length ℤ (ℤ ⧸ Ideal.span {(1 : ℤ)}) = 0 := by
    letI : Subsingleton (ℤ ⧸ Ideal.span {(1 : ℤ)}) :=
      Submodule.Quotient.subsingleton_iff.mpr (by
        change Ideal.span ({(1 : ℤ)} : Set ℤ) = ⊤
        exact Ideal.span_singleton_one)
    exact Module.length_eq_zero
  simpa [HodgeConjecture.SchemeCycles.Examples.int_two_quotient_length, hz] using h

end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let declarations := [
    `HodgeConjecture.CommutativeAlgebra.length_restrictScalars_eq_sum_localized,
    `HodgeConjecture.CommutativeAlgebra.length_eq_sum_localized,
    `HodgeConjecture.CommutativeAlgebra.length_localized_atMaximal_ne_top,
    `HodgeConjecture.CommutativeAlgebra.length_restrictScalars_eq_sum_residueDegree,
    `HodgeConjecture.CommutativeAlgebra.length_restrictScalars_toNat_eq_sum_residueDegree,
    `HodgeConjecture.CommutativeAlgebra.isFiniteLength_restrictScalars_of_semilocal,
    `HodgeConjecture.CommutativeAlgebra.lattice_isLocalizedModule,
    `HodgeConjecture.CommutativeAlgebra.lattice_exists_smul_mem,
    `HodgeConjecture.CommutativeAlgebra.finiteLength_of_killed_by_nonzero,
    `HodgeConjecture.CommutativeAlgebra.lattice_quotient_finiteLength,
    `HodgeConjecture.CommutativeAlgebra.submoduleQuotientLength,
    `HodgeConjecture.CommutativeAlgebra.submoduleQuotientLength_range,
    `HodgeConjecture.CommutativeAlgebra.submoduleQuotientLength_add,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_common_upper,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_add,
    `HodgeConjecture.CommutativeAlgebra.submoduleQuotientLength_map,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_map,
    `HodgeConjecture.CommutativeAlgebra.lattice_map_isLattice,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_independent,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_comp,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_common_lower,
    `HodgeConjecture.CommutativeAlgebra.latticeIndex_of_le,
    `HodgeConjecture.CommutativeAlgebra.latticeIndexHom,
    `HodgeConjecture.SchemeCycles.latticeIndex_eq_localOrder_det,
    `HodgeConjecture.SchemeCycles.localOrder_det_eq_quotient_length,
    `HodgeConjecture.SchemeCycles.latticeIndex_eq_localOrder_norm,
    `HodgeConjecture.SchemeCycles.localOrder_norm_algebraMap_eq_length,
    `HodgeConjecture.SchemeCycles.principalQuotient_restrictScalars_length_ne_top,
    `HodgeConjecture.SchemeCycles.localOrder_norm_fraction_eq_length,
    `HodgeConjecture.SchemeCycles.localOrder_norm_algebraMap_eq_sum_localized_length]
  for declaration in declarations do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    let actual := axioms.toList
    for axiomName in actual do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom allowlist: {declaration}; actual {actual}"
