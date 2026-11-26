module

public import HodgeConjecture.Realization.Chow.FiniteCoverageCertificate
public import HodgeConjecture.Realization.DeRham.ProjectiveLineHodgeCycleClass
public import HodgeConjecture.Realization.Betti.ProjectiveLineCoverHarmonicComparison
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# An accepted aggregate for the actual P¹ Hodge target

The public basis comes from the original rational Betti coordinate and the
independently computed geometric Hodge subspace. The sole cycle is the actual
ordinary infinity Chow class. Its column binding is supplied through the
proved finite-cover harmonic realization. The rank payload is identity modulo
three, and the aggregate acceptance theorem recovers the existing fixed-model
Hodge target through the new certificate path.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineCoverageCertificate

open ProjectiveLineBettiComplexification ProjectiveLineBettiCohomology

abbrev model := ProjectiveLineHodgeCycleClass.model

/-- The original target is all of the actual rational Betti line. -/
def targetEquiv : model.hodgeClasses ≃ₗ[ℚ] Betti :=
  LinearEquiv.ofBijective model.hodgeClasses.subtype
    ⟨Subtype.val_injective, fun z => ⟨⟨z, by
      change z ∈ ProjectiveLineHodgeComparison.rationalHodgeClasses
      rw [ProjectiveLineHodgeComparison.rationalHodgeClasses_eq_top]
      exact Submodule.mem_top⟩, rfl⟩⟩

def targetCoordinates : model.hodgeClasses ≃ₗ[ℚ] (Unit → ℚ) :=
  (targetEquiv.trans h2Equiv).trans (LinearEquiv.funUnique Unit ℚ ℚ).symm

def basis : Module.Basis Unit ℚ model.hodgeClasses :=
  Module.Basis.ofEquivFun targetCoordinates

theorem basis_coordinates : basis.equivFun = targetCoordinates :=
  Module.Basis.equivFun_ofEquivFun targetCoordinates

theorem basis_vector (j : Unit) : (basis j : Betti) = coverGenerator := by
  apply h2Equiv.injective
  rw [h2Equiv_coverGenerator]
  change targetCoordinates (basis j) j = 1
  rw [← basis_coordinates]
  simp

def arithmetic : ModularRankCertificate.Certificate Unit where
  denominator := 1
  integerMatrix := 1
  modulus := 3
  modularInverse := 1

def harmonicRealization : Betti →ₗ[ℚ]
    CircleCoverHarmonicComparison.coverSheaf.harmonicOneSubspace :=
  ProjectiveLineCoverHarmonicComparison.witness.comp
    ProjectiveLineProductBetti.canonicalBettiEquiv.toLinearMap

theorem harmonicRealization_injective : Function.Injective harmonicRealization :=
  ProjectiveLineCoverHarmonicComparison.witness_injective.comp
    ProjectiveLineProductBetti.canonicalBettiEquiv.injective

/-- The actual cycle, full target basis, harmonic proofs and arithmetic payload. -/
def certificate : FiniteCoverageCertificate.Certificate model basis := by
  refine FiniteCoverageCertificate.of_harmonic model basis
    (fun _ => ProjectiveLineBettiCycleClass.rationalInfinityClass) 1 arithmetic
    CircleCoverHarmonicComparison.coverSheaf harmonicRealization
    harmonicRealization_injective ?_
  intro j
  have htarget :
      (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i j) : Betti) =
        coverGenerator := by
    rw [Module.Basis.equivFun_symm_apply]
    cases j
    simpa using basis_vector ()
  have hcycle : model.cycleClass ProjectiveLineBettiCycleClass.rationalInfinityClass =
      coverGenerator := ProjectiveLineBettiCycleClass.cycleClass_infinity
  refine ⟨0, ?_⟩
  rw [hcycle, htarget, sub_self, map_zero]

theorem accepted : FiniteCoverageCertificate.check certificate = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ) arithmetic = true
  decide +kernel

/-- Coverage follows from the checked aggregate, not from a stored coverage premise. -/
theorem model_satisfies_from_aggregate : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

end HodgeConjecture.ProjectiveLineCoverageCertificate

end
