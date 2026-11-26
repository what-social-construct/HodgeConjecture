module

public import HodgeConjecture.Realization.Betti.CircleCoverHarmonicComparison
public import HodgeConjecture.Realization.Betti.ProjectiveLineCohomology
public import HodgeConjecture.Realization.Betti.ProjectiveLineProductClasses

@[expose] public section

/-!
# The finite cover model on canonical projective-line Betti cohomology

The finite quotient comparison follows the original circle Mayer–Vietoris
boundary, actual radial pullback, original projective-line boundary, and
the canonical scheme-point homeomorphism. The ordinary cycle comparison
uses the existing degree-normalized Chow map, without defining the Betti
comparison from that map.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineCoverHarmonicComparison

open CircleCoverHarmonicComparison ProjectiveLineProductBetti
open ProjectiveLineBettiCohomology

/-- Original radial pullback and native connecting map, with canonical scheme points. -/
def circleBettiEquiv :
    SingularCochains.Cohomology CircleCohomology.space 1 ≃ₗ[ℚ] LineH2 :=
  ProjectiveLineSingularCohomology.circleIso.toLinearEquiv.trans canonicalBettiEquiv

/-- A native finite quotient computes canonical projective-line singular H². -/
def quotientBettiEquiv :
    ((Bool → ℚ) ⧸ LinearMap.range rationalCoboundary) ≃ₗ[ℚ] LineH2 :=
  quotientCircleEquiv.trans circleBettiEquiv

theorem quotientBettiEquiv_mk (f : Bool → ℚ) :
    quotientBettiEquiv (Submodule.Quotient.mk f) =
      canonicalBettiEquiv (ProjectiveLineSingularCohomology.circleIso.hom
        (CircleCohomology.componentBoundary f)) := rfl

/-- Faithful harmonic witnesses from the actual cover comparison. -/
def witness : LineH2 →ₗ[ℚ] coverSheaf.harmonicOneSubspace :=
  CircleCoverHarmonicComparison.witness.comp circleBettiEquiv.symm.toLinearMap

theorem witness_injective : Function.Injective witness :=
  CircleCoverHarmonicComparison.witness_injective.comp circleBettiEquiv.symm.injective

/-- The finite harmonic projection commutes with the two original geometric boundaries. -/
theorem witness_original_boundaries (f : Bool → ℚ) :
    witness (quotientBettiEquiv (Submodule.Quotient.mk f)) = projectedRealization f := by
  change CircleCoverHarmonicComparison.witness
    (circleBettiEquiv.symm (circleBettiEquiv (quotientCircleEquiv (Submodule.Quotient.mk f)))) = _
  rw [LinearEquiv.symm_apply_apply, quotientCircleEquiv_mk,
    CircleCoverHarmonicComparison.witness_componentBoundary]

/-- The existing canonical generator is the original boundary of the component step. -/
theorem quotientBettiEquiv_step (q : ℚ) :
    quotientBettiEquiv (Submodule.Quotient.mk (TwoComponentBoundary.step q)) =
      q • lineGenerator := by
  have hstep : TwoComponentBoundary.step q = q • TwoComponentBoundary.step 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [hstep, Submodule.Quotient.mk_smul, map_smul]
  rfl

/-- The original ordinary Chow map agrees with the actual cover-to-harmonic comparison. -/
theorem witness_canonicalCycleClass
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0) :
    witness (canonicalCycleClass z) =
      projectedRealization (TwoComponentBoundary.step
        (ProjectiveLineCycles.rationalChowDegree ℂ z)) := by
  rw [← witness_original_boundaries]
  congr 1
  rw [quotientBettiEquiv_step]
  change canonicalBettiEquiv
      ((ProjectiveLineCycles.rationalChowDegree ℂ z) • coverGenerator) =
    (ProjectiveLineCycles.rationalChowDegree ℂ z) • canonicalBettiEquiv coverGenerator
  exact map_smul _ _ _

theorem canonicalCycleClass_eq_iff_exact_witness_sub
    (z : SchemeCycles.RationalChowGroup (ProjectiveLineCycles.dimensionFunction ℂ) 0)
    (α : LineH2) :
    canonicalCycleClass z = α ↔
      coverSheaf.IsExactOneCochain
        ((witness (canonicalCycleClass z) : coverSheaf.C1) - (witness α : coverSheaf.C1)) := by
  constructor
  · intro h
    exact ⟨0, by simp [h]⟩
  · exact coverSheaf.eq_of_exact_harmonicWitness_sub witness witness_injective

end HodgeConjecture.ProjectiveLineCoverHarmonicComparison

end
