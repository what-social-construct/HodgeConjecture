module

public import HodgeConjecture.LinearAlgebra.ModularRankCertificate
public import HodgeConjecture.Realization.Chow.HarmonicWitness
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

/-!
# Aggregate certificates for a fixed rational Hodge target

The model and a basis of its independently defined Hodge-class subspace are
fixed public parameters. A certificate contains actual Chow classes, rational
columns, proof-checked bindings to those classes, and the finite modular rank
payload. Thus a missing target direction cannot be hidden by choosing a basis
of the cycle image. Geometry is not accepted on the strength of a Boolean label.

The arithmetic check is executable on finite rational/integer matrices. The
geometric and basis bindings are Lean proof gates; arbitrary geometric input
is not claimed to have a generic executable decoder. Harmonic certificates
can construct those bindings through a supplied faithful realization.

The acceptance theorem establishes the existing fixed-model target. There is
no cryptographic backend, random aggregation, or assumed SNARK soundness here.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.FiniteCoverageCertificate

open scoped BigOperators

variable {Chow H ι : Type*}
  [AddCommGroup Chow] [Module ℚ Chow] [AddCommGroup H] [Module ℚ H]
  [Fintype ι] [DecidableEq ι]

/-- The original cycle map with its proved Hodge-subspace codomain. -/
def hodgeCycleClass (M : RationalHodgeCycleClassModel Chow H) :
    Chow →ₗ[ℚ] M.hodgeClasses :=
  M.cycleClass.codRestrict M.hodgeClasses
    (fun z => M.cycleClass_lands ⟨z, rfl⟩)

/-- Data and checked column bindings for the complete, fixed target basis. -/
structure Certificate (M : RationalHodgeCycleClassModel Chow H)
    (b : Module.Basis ι ℚ M.hodgeClasses) where
  cycles : ι → Chow
  coordinates : Matrix ι ι ℚ
  arithmetic : ModularRankCertificate.Certificate ι
  column_binding : ∀ j, hodgeCycleClass M (cycles j) =
    b.equivFun.symm (fun i => coordinates i j)

/-- Arithmetic acceptance for an already proof-bound aggregate. -/
def check {M : RationalHodgeCycleClassModel Chow H}
    {b : Module.Basis ι ℚ M.hodgeClasses} (C : Certificate M b) : Bool :=
  ModularRankCertificate.check C.coordinates C.arithmetic

omit [DecidableEq ι] in
theorem coordinate_combination
    {M : RationalHodgeCycleClassModel Chow H}
    {b : Module.Basis ι ℚ M.hodgeClasses} (C : Certificate M b) (v : ι → ℚ) :
    b.equivFun (hodgeCycleClass M (∑ j, v j • C.cycles j)) = C.coordinates.mulVec v := by
  rw [map_sum, map_sum]
  simp_rw [map_smul, C.column_binding, b.equivFun.apply_symm_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Exact aggregate acceptance implies coverage of every class of the fixed target. -/
theorem rationalHodgeConjectureAt_of_check
    {M : RationalHodgeCycleClassModel Chow H}
    {b : Module.Basis ι ℚ M.hodgeClasses} (C : Certificate M b)
    (accepted : check C = true) : RationalHodgeConjectureAt M := by
  intro α hα
  let target : M.hodgeClasses := ⟨α, hα⟩
  obtain ⟨v, hv⟩ := ModularRankCertificate.mulVec_surjective_of_check
    C.coordinates C.arithmetic accepted (b.equivFun target)
  refine ⟨∑ j, v j • C.cycles j, ?_⟩
  have h := b.equivFun.injective ((coordinate_combination C v).trans hv)
  exact congrArg Subtype.val h

/-- Every class of the fixed target receives an actual finite cycle combination. -/
theorem exists_cycle_of_check
    {M : RationalHodgeCycleClassModel Chow H}
    {b : Module.Basis ι ℚ M.hodgeClasses} (C : Certificate M b)
    (accepted : check C = true) (α : H) (hα : IsRationalHodgeClass M α) :
    ∃ z : Chow, M.cycleClass z = α :=
  rationalHodgeConjectureAt_of_check C accepted hα

/-- Harmonic proof gates bind every supplied column to the actual cycle image. -/
def of_harmonic
    (M : RationalHodgeCycleClassModel Chow H)
    (b : Module.Basis ι ℚ M.hodgeClasses) (cycles : ι → Chow)
    (A : Matrix ι ι ℚ) (arithmetic : ModularRankCertificate.Certificate ι)
    {Vertex Edge Face : Type*} [Fintype Vertex] [Fintype Edge] [Fintype Face]
    {X : Harmonic.OrientedTwoComplex Vertex Edge Face}
    (F : Harmonic.CellularSheaf X)
    (W : H →ₗ[ℚ] F.harmonicOneSubspace) (faithful : Function.Injective W)
    (column_certificates : ∀ j, F.IsExactOneCochain
      ((W (M.cycleClass (cycles j)) : F.C1) -
        (W (b.equivFun.symm (fun i => A i j) : H) : F.C1))) : Certificate M b where
  cycles := cycles
  coordinates := A
  arithmetic := arithmetic
  column_binding j := Subtype.ext (F.eq_of_exact_harmonicWitness_sub W faithful (column_certificates j))

end HodgeConjecture.FiniteCoverageCertificate

end
