module

public import HodgeConjecture.Cycles.ProjectiveLineProductZeroBoundaryGenerators

/-! The two actual coordinate-zero integral carriers are distinct. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators

open AlgebraicGeometry CategoryTheory TopologicalSpace SchemeCycles
open HodgeConjecture.ProjectiveLineProductIntegralCandidates
open HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization
open HodgeConjecture.ProjectiveLineProductFibers

universe u

variable (k : Type u) [Field k]

/-- The first coordinate of the first zero-fiber carrier's generic point
is the actual zero point. -/
theorem firstZeroCarrier_generic_fst :
    (projectiveLineProductFst k).base
      (ambientGenericPoint (projectiveLineProductZeroFirstCarrier k)) =
        projectiveLineZero k := by
  have hmem : ambientGenericPoint (projectiveLineProductZeroFirstCarrier k) ∈
      (projectiveLineProductZeroFirstCarrier k).val.support :=
    (ambientGenericPoint_isGenericPoint _).mem
  have hcarrier : (projectiveLineProductZeroFirstCarrier k).val =
      firstFiberIdeal k (projectiveLineZero k) := by
    simpa only [zeroSectionPoint_eq_projectiveLineZero] using
      projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal k
  have hmem' : ambientGenericPoint (projectiveLineProductZeroFirstCarrier k) ∈
      (firstFiberIdeal k (projectiveLineZero k)).support := by
    rw [← hcarrier]
    exact hmem
  have hproj := (mem_firstFiber_support k (projectiveLineZero k) _).mp hmem'
  rw [(zero_isClosed k).closure_eq] at hproj
  simpa only [Set.mem_singleton_iff] using hproj

/-- Zero is not the generic point of the projective line. -/
theorem projectiveLineZero_ne_genericPoint :
    projectiveLineZero k ≠ genericPoint (projectiveLine k) := by
  intro h
  have hrange : genericPoint (projectiveLine k) ∈
      Set.range (projectiveLineYChart k).base := by
    refine ⟨genericPoint (Spec (.of (Polynomial k))), ?_⟩
    exact genericPoint_eq_of_isOpenImmersion (projectiveLineYChart k)
  exact projectiveLineZero_notMem_range_YChart k (by simpa only [h] using hrange)

/-- The two coordinate-zero fiber carriers have different generic points. -/
theorem firstZeroCarrier_ne_secondZeroCarrier :
    projectiveLineProductZeroFirstCarrier k ≠
      projectiveLineProductZeroSecondCarrier k := by
  intro h
  have hfst := congrArg
    (fun W : IntegralClosedSubscheme (projectiveLineProduct k) ↦
      (projectiveLineProductFst k).base (ambientGenericPoint W)) h
  rw [firstZeroCarrier_generic_fst,
    projectiveLineProductZeroSecondCarrier_eq_candidate,
    secondZeroCarrier_generic_fst] at hfst
  exact projectiveLineZero_ne_genericPoint k hfst

end HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators

end
