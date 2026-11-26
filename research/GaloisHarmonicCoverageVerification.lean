module

public import HodgeConjecture.Realization.DeRham.ProjectiveLineGaloisCoverage
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

@[expose] public section

/-!
Controls for scalar-extension descent and quotient-defined harmonic transport.

These controls deliberately retain the original ordinary Chow group and the
original independent rational Hodge target. No additional geometric base-change
or finite-field Chow interpretation is introduced.
-/

set_option autoImplicit false

namespace HodgeConjecture.GaloisHarmonicCoverageVerification

open scoped TensorProduct

noncomputable section

section VectorSpaceControls

variable {K N V : Type*}
  [Field K] [Field N] [Algebra K N] [AddCommGroup V] [Module K V]

-- Neither inclusion nor its injectivity requires an algebra structure on V.
example (v w : V) :
    GaloisDescent.tensorInclude (K := K) (N := N) v = GaloisDescent.tensorInclude (K := K) (N := N) w ↔
      v = w := by
  constructor
  · intro h
    exact GaloisDescent.tensorInclude_injective (K := K) (N := N) (V := V) h
  · rintro rfl
    rfl

example (v : V) (g : N ≃ₐ[K] N) :
    GaloisDescent.scalarAction g (GaloisDescent.tensorInclude (K := K) (N := N) v) =
      GaloisDescent.tensorInclude (K := K) (N := N) v := by
  simp

variable [FiniteDimensional K N] [IsGalois K N]

-- An included vector survives the actual noncomputable descent construction.
example (v : V) :
    GaloisDescent.descendFixed (GaloisDescent.tensorInclude (K := K) (N := N) v)
      (fun g => GaloisDescent.scalarAction_tensorInclude g v) = v := by
  exact GaloisDescent.descendFixed_tensorInclude (K := K) (N := N) v
    (fun g => GaloisDescent.scalarAction_tensorInclude g v)

-- A fixed tensor has exactly one original vector, including when V has no multiplication.
example (z : N ⊗[K] V)
    (hz : ∀ g : N ≃ₐ[K] N, GaloisDescent.scalarAction g z = z) :
    ∃! v : V, GaloisDescent.tensorInclude (K := K) (N := N) v = z := by
  refine ⟨GaloisDescent.descendFixed z hz, GaloisDescent.include_descendFixed z hz, ?_⟩
  intro v hv
  exact GaloisDescent.descendFixed_unique z hz v hv

end VectorSpaceControls

abbrev Coefficients := GaloisDescent.Gaussian.Coefficients

-- The concrete coefficient extension has degree two.
example : Module.finrank ℚ Coefficients = 2 := GaloisDescent.Gaussian.finrank_eq_two

-- A visibly nonrational coefficient cannot pass either form of the descent gate.
example :
    ¬ ∀ g : Coefficients ≃ₐ[ℚ] Coefficients,
      GaloisDescent.scalarAction g GaloisDescent.Gaussian.imaginaryTensor =
        GaloisDescent.Gaussian.imaginaryTensor :=
  GaloisDescent.Gaussian.imaginaryTensor_not_fixed

example :
    ¬ ∃ q : ℚ, GaloisDescent.tensorInclude (K := ℚ) (N := Coefficients) q =
      GaloisDescent.Gaussian.imaginaryTensor :=
  GaloisDescent.Gaussian.imaginaryTensor_not_in_range

open ProjectiveLineCoverageCertificate
open ProjectiveLineBettiComplexification ProjectiveLineBettiCohomology

example (j : Unit) (g : Coefficients ≃ₐ[ℚ] Coefficients) :
    GaloisDescent.scalarAction g (ProjectiveLineGaloisCoverage.upstairsCycles j) =
      ProjectiveLineGaloisCoverage.upstairsCycles j :=
  ProjectiveLineGaloisCoverage.upstairsCycles_fixed j g

-- Descent recovers the actual ordinary infinity Chow class.
example (j : Unit) :
    FiniteCoverageCertificate.descendedCycles ProjectiveLineGaloisCoverage.upstairsCycles
      ProjectiveLineGaloisCoverage.upstairsCycles_fixed j =
        ProjectiveLineBettiCycleClass.rationalInfinityClass :=
  ProjectiveLineGaloisCoverage.descendedCycles_infinity j

-- Both constructors retain that original cycle as their certified column witness.
example (j : Unit) :
    ProjectiveLineGaloisCoverage.certificate.cycles j =
      ProjectiveLineBettiCycleClass.rationalInfinityClass :=
  ProjectiveLineGaloisCoverage.descendedCycles_infinity j

example (j : Unit) :
    ProjectiveLineGaloisCoverage.transportedCertificate.cycles j =
      ProjectiveLineBettiCycleClass.rationalInfinityClass :=
  ProjectiveLineGaloisCoverage.descendedCycles_infinity j

-- Conjugation also rejects an imaginary multiple of the actual infinity Chow class.
theorem imaginary_cycle_cannot_descend :
    ProjectiveLineGaloisCoverage.imaginaryCycle ∉
      Set.range (GaloisDescent.tensorInclude
        (K := ℚ) (N := Coefficients) (V := ProjectiveLineGaloisCoverage.Chow)) := by
  intro hin
  exact ProjectiveLineGaloisCoverage.imaginaryCycle_not_fixed
    ((GaloisDescent.mem_range_tensorInclude_iff_fixed _).mp hin)

-- Fixed zero tensors still cannot bind the actual nonzero target generator.
theorem zero_tensor_cannot_bind_generator :
    FiniteCoverageCertificate.extendedCycleClass model
        (0 : Coefficients ⊗[ℚ] ProjectiveLineHodgeCycleClass.Source) ≠
      GaloisDescent.tensorInclude (K := ℚ) (N := Coefficients) coverGenerator := by
  intro h
  have hzero : GaloisDescent.tensorInclude (K := ℚ) (N := Coefficients) (0 : Betti) =
      GaloisDescent.tensorInclude (K := ℚ) (N := Coefficients) coverGenerator := by
    simpa using h
  have hgenerator : (0 : Betti) = coverGenerator :=
    GaloisDescent.tensorInclude_injective (K := ℚ) (N := Coefficients) hzero
  exact coverGenerator_ne_zero hgenerator.symm

-- The accepted transport runs through actual cellular cohomology and doubles W.
example (x : Betti) :
    (Harmonic.CellularSheaf.Morphism.scalar CircleCoverHarmonicComparison.coverSheaf 2).transportHarmonicWitness
       harmonicRealization x =
      (2 : ℝ) • harmonicRealization x := by
  simp

example : Function.Injective
    ((Harmonic.CellularSheaf.Morphism.scalar CircleCoverHarmonicComparison.coverSheaf 2).transportHarmonicWitness
       harmonicRealization) :=
  Harmonic.CellularSheaf.Morphism.transportHarmonicWitness_scalar_injective
    CircleCoverHarmonicComparison.coverSheaf (by norm_num)
      harmonicRealization harmonicRealization_injective

-- The nontrivial accepted endomorphism is not an isometry on the actual witness.
theorem scalar_two_changes_witness_norm :
    ‖((Harmonic.CellularSheaf.Morphism.scalar CircleCoverHarmonicComparison.coverSheaf 2).transportHarmonicWitness
       harmonicRealization) coverGenerator‖ ≠
      ‖harmonicRealization coverGenerator‖ := by
  intro h
  have hw : harmonicRealization coverGenerator ≠ 0 := by
    intro hz
    apply coverGenerator_ne_zero
    apply harmonicRealization_injective
    simpa using hz
  have hnorm : ‖(2 : ℝ)‖ * ‖harmonicRealization coverGenerator‖ =
      ‖harmonicRealization coverGenerator‖ := by
    simpa only [Harmonic.CellularSheaf.Morphism.transportHarmonicWitness_scalar_apply,
      norm_smul] using h
  norm_num at hnorm
  change (2 : ℝ) * ‖harmonicRealization coverGenerator‖ =
    ‖harmonicRealization coverGenerator‖ at hnorm
  have hpos : 0 < ‖harmonicRealization coverGenerator‖ := norm_pos_iff.mpr hw
  linarith

-- Symmetry and exactness of the zero transport cannot replace the faithful-map gate.
example : ¬ Function.Injective
    ((Harmonic.CellularSheaf.Morphism.scalar CircleCoverHarmonicComparison.coverSheaf 0).transportHarmonicWitness
       harmonicRealization) :=
  ProjectiveLineGaloisCoverage.zero_transport_not_injective

-- Fail immediately on a missing declaration or any axiom beyond the standard three.
open Lean Elab Command in
run_cmd do
  let env ← Lean.getEnv
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.GaloisDescent.tensorInclude_injective,
      `HodgeConjecture.GaloisDescent.mem_range_tensorInclude_iff_fixed,
      `HodgeConjecture.GaloisDescent.descendFixed,
      `HodgeConjecture.GaloisDescent.include_descendFixed,
      `HodgeConjecture.GaloisDescent.descendFixed_unique,
      `HodgeConjecture.GaloisDescent.Gaussian.finrank_eq_two,
      `HodgeConjecture.GaloisDescent.Gaussian.conjugation_omega_ne,
      `HodgeConjecture.GaloisDescent.Gaussian.imaginaryTensor_not_fixed,
      `HodgeConjecture.GaloisDescent.Gaussian.imaginaryTensor_not_in_range,
      `HodgeConjecture.Harmonic.CellularSheaf.cohomologyOneEquivExactClosedQuotient,
      `HodgeConjecture.Harmonic.CellularSheaf.cohomologyOneEquivHarmonic,
      `HodgeConjecture.Harmonic.CellularSheaf.Morphism.mapCohomologyOne,
      `HodgeConjecture.Harmonic.CellularSheaf.Morphism.mapHarmonicOne,
      `HodgeConjecture.Harmonic.CellularSheaf.Morphism.cohomologyOneEquivHarmonic_naturality,
      `HodgeConjecture.Harmonic.CellularSheaf.Morphism.transportHarmonicWitness,
      `HodgeConjecture.Harmonic.CellularSheaf.Morphism.transportHarmonicWitness_apply,
      `HodgeConjecture.Harmonic.CellularSheaf.Morphism.transportHarmonicWitness_scalar_injective,
      `HodgeConjecture.FiniteCoverageCertificate.extendedCycleClass,
      `HodgeConjecture.FiniteCoverageCertificate.descendedCycles,
      `HodgeConjecture.FiniteCoverageCertificate.of_galois_fixed,
      `HodgeConjecture.FiniteCoverageCertificate.of_transported_harmonic,
      `HodgeConjecture.FiniteCoverageCertificate.of_galois_transported_harmonic,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.upstairsCycles_fixed,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.descendedCycles_infinity,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.class_column,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.certificate,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.accepted,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.transportedCertificate,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.transported_accepted,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.model_satisfies_from_galois_aggregate,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.model_satisfies_from_transported_aggregate,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.imaginaryCycle_not_fixed,
      `HodgeConjecture.ProjectiveLineGaloisCoverage.zero_transport_not_injective,
      `HodgeConjecture.GaloisHarmonicCoverageVerification.zero_tensor_cannot_bind_generator,
      `HodgeConjecture.GaloisHarmonicCoverageVerification.scalar_two_changes_witness_norm] do
    unless (env.find? declaration).isSome do
      throwError "Missing declaration {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms.toList do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS Galois/harmonic axiom boundary: {declaration}; {axioms.toList}"

end
end HodgeConjecture.GaloisHarmonicCoverageVerification
