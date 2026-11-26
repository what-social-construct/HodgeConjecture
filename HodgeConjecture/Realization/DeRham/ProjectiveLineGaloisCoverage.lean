module

public import HodgeConjecture.Realization.Chow.GaloisHarmonicCoverage
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCoverageCertificate
public import HodgeConjecture.LinearAlgebra.GaloisGaussian

@[expose] public section

/-!
# P¹ coverage through Gaussian coefficient descent and harmonic transport

The coefficient extension is the actual quadratic field ℚ(i). The included
infinity Chow class is invariant, descends back to the original infinity
class, and binds the original full Hodge basis. A second aggregate verifies
the descended columns through multiplication by two on the native cellular
cohomology quotient. Both use the unchanged exact modular rank payload.

Conjugation moves an imaginary multiple of the infinity class, so that
candidate cannot supply the fixedness gate. The zero cellular endomorphism
cannot supply the faithfulness gate. No geometric Chow base-change or
finite-field harmonic comparison is used.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineGaloisCoverage

open scoped TensorProduct
open ProjectiveLineCoverageCertificate ProjectiveLineBettiComplexification
open ProjectiveLineBettiCohomology

abbrev Coefficients := GaloisDescent.Gaussian.Coefficients
abbrev Chow := SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0

/-- The original infinity cycle with coefficients extended to ℚ(i). -/
def upstairsCycles (_ : Unit) : Coefficients ⊗[ℚ] Chow :=
  GaloisDescent.tensorInclude (N := Coefficients)
    ProjectiveLineBettiCycleClass.rationalInfinityClass

theorem upstairsCycles_fixed (j : Unit) (g : Coefficients ≃ₐ[ℚ] Coefficients) :
    GaloisDescent.scalarAction g (upstairsCycles j) = upstairsCycles j := by
  simp [upstairsCycles]

@[simp]
theorem descendedCycles_infinity (j : Unit) :
    FiniteCoverageCertificate.descendedCycles upstairsCycles upstairsCycles_fixed j =
      ProjectiveLineBettiCycleClass.rationalInfinityClass := by
  apply GaloisDescent.tensorInclude_injective (K := ℚ) (N := Coefficients)
  exact FiniteCoverageCertificate.include_descendedCycles upstairsCycles upstairsCycles_fixed j

/-- The original geometric normalization fixes the target column. -/
theorem class_column (j : Unit) :
    model.cycleClass ProjectiveLineBettiCycleClass.rationalInfinityClass =
      (basis.equivFun.symm (fun i => (1 : Matrix Unit Unit ℚ) i j) : Betti) :=
  congrArg Subtype.val (ProjectiveLineCoverageCertificate.certificate.column_binding j)

/-- The first aggregate binds columns after exact scalar-extension descent. -/
def certificate : FiniteCoverageCertificate.Certificate model basis := by
  refine FiniteCoverageCertificate.of_galois_fixed model basis
    upstairsCycles upstairsCycles_fixed 1 arithmetic ?_
  intro j
  rw [upstairsCycles, FiniteCoverageCertificate.extendedCycleClass_tensorInclude, class_column]

theorem accepted : FiniteCoverageCertificate.check certificate = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ) arithmetic = true
  decide +kernel

/-- A genuine nonisometric cellular endomorphism on the existing geometric cover. -/
def doubleMorphism : Harmonic.CellularSheaf.Morphism
    CircleCoverHarmonicComparison.coverSheaf CircleCoverHarmonicComparison.coverSheaf :=
  Harmonic.CellularSheaf.Morphism.scalar CircleCoverHarmonicComparison.coverSheaf 2

theorem doubled_witness_injective :
    Function.Injective (doubleMorphism.transportHarmonicWitness harmonicRealization) := by
  apply Harmonic.CellularSheaf.Morphism.transportHarmonicWitness_scalar_injective
    CircleCoverHarmonicComparison.coverSheaf (by norm_num) harmonicRealization
    harmonicRealization_injective

/-- Both Galois descent and the quotient-defined harmonic transport are used. -/
def transportedCertificate : FiniteCoverageCertificate.Certificate model basis := by
  refine FiniteCoverageCertificate.of_galois_transported_harmonic model basis
    upstairsCycles upstairsCycles_fixed 1 arithmetic
    CircleCoverHarmonicComparison.coverSheaf doubleMorphism
    (Harmonic.CellularSheaf.Morphism.scalar_mapC1_isSymmetric _ 2)
    harmonicRealization doubled_witness_injective ?_
  intro j
  refine ⟨0, ?_⟩
  rw [descendedCycles_infinity, class_column, sub_self, map_zero]

theorem transported_accepted : FiniteCoverageCertificate.check transportedCertificate = true := by
  change ModularRankCertificate.check (1 : Matrix Unit Unit ℚ) arithmetic = true
  decide +kernel

theorem model_satisfies_from_galois_aggregate : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check certificate accepted

theorem model_satisfies_from_transported_aggregate : RationalHodgeConjectureAt model :=
  FiniteCoverageCertificate.rationalHodgeConjectureAt_of_check
    transportedCertificate transported_accepted

/-- A coefficient moved by conjugation on an actual nonzero Chow class. -/
def imaginaryCycle : Coefficients ⊗[ℚ] Chow :=
  GaloisDescent.Gaussian.omega ⊗ₜ[ℚ] ProjectiveLineBettiCycleClass.rationalInfinityClass

theorem imaginaryCycle_not_fixed :
    ¬ ∀ g : Coefficients ≃ₐ[ℚ] Coefficients,
      GaloisDescent.scalarAction g imaginaryCycle = imaginaryCycle := by
  intro fixed
  let evaluate : Coefficients ⊗[ℚ] Chow →ₗ[ℚ] Coefficients :=
    (TensorProduct.rid ℚ Coefficients).toLinearMap.comp
      (TensorProduct.map LinearMap.id (ProjectiveLineCycles.rationalChowDegree ℂ))
  have h := congrArg evaluate (fixed GaloisDescent.Gaussian.conjugation)
  apply GaloisDescent.Gaussian.conjugation_omega_ne
  simpa [evaluate, imaginaryCycle] using h

/-- The zero cellular endomorphism is the degenerate transport control. -/
abbrev zeroMorphism :=
  Harmonic.CellularSheaf.Morphism.scalar CircleCoverHarmonicComparison.coverSheaf 0

/-- Killing every witness does not satisfy the transported faithfulness gate. -/
theorem zero_transport_not_injective :
    ¬ Function.Injective (zeroMorphism.transportHarmonicWitness harmonicRealization) := by
  intro faithful
  have hmap :
      zeroMorphism.transportHarmonicWitness harmonicRealization coverGenerator =
        zeroMorphism.transportHarmonicWitness harmonicRealization (0 : Betti) := by
    simp [zeroMorphism]
  exact coverGenerator_ne_zero (faithful hmap)

end HodgeConjecture.ProjectiveLineGaloisCoverage

end
