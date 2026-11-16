module

public import HodgeConjecture.Cycles.ProjectiveLineProductZeroBoundaryGenerators

/-!
# Restriction of the two zero-fiber cycles to the opposite affine chart

Both named zero fibers lie in the reduced complement of the second
affine product chart. Their actual rational cycles therefore restrict to
zero on that open chart. This is a statement about cycle restriction,
before passing to the Chow quotient.
-/

@[expose] public section

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineProductZeroFiberRestriction

open AlgebraicGeometry CategoryTheory SchemeCycles
open HodgeConjecture.ProjectiveLineProductChow
open HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization
open HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators

noncomputable section

universe u

variable (k : Type u) [Field k]

private theorem generic_outside_chart
    (W : IntegralClosedSubscheme (projectiveLineProduct k))
    (h : ambientGenericPoint W ∈ (openComplementIdeal (chart k)).support) :
    ambientGenericPoint W ∉ Set.range (chart k).base := by
  change ambientGenericPoint W ∈
    ((openComplementIdeal (chart k)).support : Set (projectiveLineProduct k)) at h
  rw [← Scheme.IdealSheafData.range_subschemeι, range_openComplement] at h
  exact h

private theorem first_generic_outside_chart :
    ambientGenericPoint (projectiveLineProductZeroFirstCarrier k) ∉
      Set.range (chart k).base := by
  apply generic_outside_chart k
  change ambientGenericPoint (projectiveLineProductZeroFirstCarrier k) ∈
    ((openComplementIdeal (chart k)).support : Set (projectiveLineProduct k))
  rw [boundary_support_eq_zero_fibers]
  left
  have hval : (projectiveLineProductZeroFirstCarrier k).val =
      ProjectiveLineProductFibers.firstFiberIdeal k (projectiveLineZero k) := by
    simpa only [zeroSectionPoint_eq_projectiveLineZero] using
      projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal k
  rw [← hval]
  exact (ambientGenericPoint_isGenericPoint
    (projectiveLineProductZeroFirstCarrier k)).mem

private theorem second_generic_outside_chart :
    ambientGenericPoint (projectiveLineProductZeroSecondCarrier k) ∉
      Set.range (chart k).base := by
  apply generic_outside_chart k
  change ambientGenericPoint (projectiveLineProductZeroSecondCarrier k) ∈
    ((openComplementIdeal (chart k)).support : Set (projectiveLineProduct k))
  rw [boundary_support_eq_zero_fibers]
  right
  have hval : (projectiveLineProductZeroSecondCarrier k).val =
      ProjectiveLineProductFibers.secondFiberIdeal k (projectiveLineZero k) := by
    simpa only [zeroSectionPoint_eq_projectiveLineZero] using
      projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal k
  rw [← hval]
  exact (ambientGenericPoint_isGenericPoint
    (projectiveLineProductZeroSecondCarrier k)).mem

private theorem openRestriction_fundamentalCycle_zero
    (W : IntegralClosedSubscheme (projectiveLineProduct k))
    (hout : ambientGenericPoint W ∉ Set.range (chart k).base) :
    openRestriction ℚ (chart k) (fundamentalCycle ℚ W) = 0 := by
  have hc : fundamentalCycle ℚ W ∈
      Finsupp.supported ℚ ℚ
        {V | ambientGenericPoint V ∉ Set.range (chart k).base} := by
    rw [Finsupp.mem_supported]
    intro V hV
    have hVW : V = W := by simpa [fundamentalCycle] using hV
    subst V
    change ambientGenericPoint W ∉ Set.range (chart k).base
    exact hout
  have hker : fundamentalCycle ℚ W ∈
      LinearMap.ker (openRestriction ℚ (chart k)) := by
    rw [ker_openRestriction]
    exact hc
  exact LinearMap.mem_ker.mp hker

/-- The first actual zero-fiber cycle restricts to zero on the opposite
affine product chart. -/
theorem firstZeroCycle_restrict_zero :
    openRestriction ℚ (chart k)
      (cyclesOfDegreeRationalize (dimensionFunction k) 1 (firstZeroCycle k)).val = 0 := by
  rw [firstZeroCycle_rationalized_val]
  exact openRestriction_fundamentalCycle_zero k _ (first_generic_outside_chart k)

/-- The second actual zero-fiber cycle has the same geometric vanishing. -/
theorem secondZeroCycle_restrict_zero :
    openRestriction ℚ (chart k)
      (cyclesOfDegreeRationalize (dimensionFunction k) 1 (secondZeroCycle k)).val = 0 := by
  rw [secondZeroCycle_rationalized_val]
  exact openRestriction_fundamentalCycle_zero k _ (second_generic_outside_chart k)

end

end HodgeConjecture.ProjectiveLineProductZeroFiberRestriction

end
