module

public import HodgeConjecture.Realization.Betti.SingularCochains
public import Lean.Util.CollectAxioms

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
Focused checks for the actual rational singular complex. The point-space
calculations use its alternating coboundary, including its nonzero degree-one
arrow, and the proved identification of categorical cohomology with the actual
cocycle/coboundary quotient.
-/

open CategoryTheory HodgeConjecture
open SingularCochains

namespace SingularCochainsVerification

noncomputable section

abbrev point : TopCat := TopCat.of PUnit

def pointSimplex (n : ℕ) : Simplex point n :=
  (simplexEquivContinuous point n).symm (ContinuousMap.const _ PUnit.unit)

instance (n : ℕ) : Subsingleton (Simplex point n) where
  allEq _σ _τ := (simplexEquivContinuous point n).injective (Subsingleton.elim _ _)

/-- The actual first positive differential on a point is evaluation, hence is not zero. -/
theorem point_differential_one (φ : Cochain point 1) (σ : Simplex point 2) :
    differential point 1 φ σ = φ (pointSimplex 1) := by
  rw [differential_apply]
  have h (i : Fin 3) : face point σ i = pointSimplex 1 := Subsingleton.elim _ _
  simp only [h]
  simp [Fin.sum_univ_succ]

/-- There are no nonzero singular one-cocycles on a point. -/
theorem point_one_cocycle_eq_zero (φ : Cocycle point 1) : φ = 0 := by
  apply Subtype.ext
  funext σ
  have hclosed := congrFun (LinearMap.mem_ker.mp φ.property) (pointSimplex 2)
  rw [point_differential_one] at hclosed
  rw [Subsingleton.elim σ (pointSimplex 1)]
  exact hclosed

/-- Categorical rational singular H¹ of a point vanishes, calculated from the actual complex. -/
theorem point_h1_eq_zero (z : Cohomology point 1) : z = 0 := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective point 1 z
  rw [point_one_cocycle_eq_zero φ, map_zero]

/-- Every degree-two cocycle on a point is the coboundary of an actual one-cochain. -/
theorem point_two_cocycle_is_boundary (φ : Cocycle point 2) :
    φ ∈ coboundaries point 2 := by
  refine ⟨fun _ ↦ φ.val (pointSimplex 2), Subtype.ext ?_⟩
  funext σ
  change differential point 1 (fun _ ↦ φ.val (pointSimplex 2)) σ = φ.val σ
  rw [point_differential_one]
  exact congrArg φ.val (Subsingleton.elim _ _)

/-- Categorical rational singular H² of a point vanishes, calculated from actual primitives. -/
theorem point_h2_eq_zero (z : Cohomology point 2) : z = 0 := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective point 2 z
  exact (cohomologyClass_eq_zero_iff point 2 φ).mpr (point_two_cocycle_is_boundary φ)

example (σ : Simplex point 2) : differential point 1 (fun _ ↦ 1) σ = 1 :=
  point_differential_one _ _

/-- Three actual singular faces occur with signs +, -, +. -/
example (X : TopCat) (φ : Cochain X 1) (σ : Simplex X 2) :
    differential X 1 φ σ = φ (face X σ 0) - φ (face X σ 1) + φ (face X σ 2) := by
  rw [differential_apply]
  simp [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

/-- This degree-zero bridge has the existing endpoint orientation. -/
example (X : Type) [TopologicalSpace X] (φ : Cochain (TopCat.of X) 0)
    (σ : SingularDegreeZero.Simplex X 1) :
    differential (TopCat.of X) 0 φ (SingularDegreeZero.simplexEquivSingularSet X 1 σ) =
      continuousCochainEquiv X 0 φ (SingularDegreeZero.face X σ 0) -
        continuousCochainEquiv X 0 φ (SingularDegreeZero.face X σ 1) := by
  exact congrFun (differential_zero_coordinates X φ) σ

/-- Pullback acts on actual degree-two representatives in the quotient. -/
example (X Y : TopCat) (f : X ⟶ Y) (φ : Cocycle Y 2) :
    quotientPullback f 2 (quotientClass Y 2 φ) =
      quotientClass X 2 (cocyclePullback f 2 φ) := quotientPullback_class f 2 φ

/-- Pulling back an actual degree-two coboundary gives a zero class. -/
example (X Y : TopCat) (f : X ⟶ Y) (ψ : Cochain Y 1) :
    quotientPullback f 2 (quotientClass Y 2 (differentialToCocycles Y 1 ψ)) = 0 := by
  rw [quotientPullback_class, cocyclePullback_differentialToCocycles]
  exact (quotientClass_eq_zero_iff X 2 _).mpr ⟨(pullback f).f 1 ψ, rfl⟩

end

end SingularCochainsVerification

open Lean Elab Command in
run_cmd do
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  for declaration in [
      `HodgeConjecture.SingularCochains.functionModule,
      `HodgeConjecture.SingularCochains.Simplex,
      `HodgeConjecture.SingularCochains.simplexEquivContinuous,
      `HodgeConjecture.SingularCochains.Cochain,
      `HodgeConjecture.SingularCochains.cosimplicial,
      `HodgeConjecture.SingularCochains.complex,
      `HodgeConjecture.SingularCochains.face,
      `HodgeConjecture.SingularCochains.differential,
      `HodgeConjecture.SingularCochains.complex_d,
      `HodgeConjecture.SingularCochains.differential_apply,
      `HodgeConjecture.SingularCochains.differential_squared,
      `HodgeConjecture.SingularCochains.cosimplicialPullback,
      `HodgeConjecture.SingularCochains.pullback,
      `HodgeConjecture.SingularCochains.pullback_apply,
      `HodgeConjecture.SingularCochains.pullback_id,
      `HodgeConjecture.SingularCochains.pullback_comp,
      `HodgeConjecture.SingularCochains.differential_pullback,
      `HodgeConjecture.SingularCochains.Cohomology,
      `HodgeConjecture.SingularCochains.cohomologyPullback,
      `HodgeConjecture.SingularCochains.cohomologyPullback_id,
      `HodgeConjecture.SingularCochains.cohomologyPullback_comp,
      `HodgeConjecture.SingularCochains.continuousCochainEquiv,
      `HodgeConjecture.SingularCochains.continuousCochainEquiv_pullback,
      `HodgeConjecture.SingularCochains.differential_zero_coordinates,
      `HodgeConjecture.SingularCochains.kernelZeroCoordinates,
      `HodgeConjecture.SingularCochains.cohomologyZeroIso,
      `HodgeConjecture.SingularCochains.Cocycle,
      `HodgeConjecture.SingularCochains.differentialToCocycles,
      `HodgeConjecture.SingularCochains.coboundaries,
      `HodgeConjecture.SingularCochains.QuotientCohomology,
      `HodgeConjecture.SingularCochains.quotientClass,
      `HodgeConjecture.SingularCochains.quotientClass_eq_zero_iff,
      `HodgeConjecture.SingularCochains.quotientClass_succ_eq_zero_iff,
      `HodgeConjecture.SingularCochains.differentialShortComplex,
      `HodgeConjecture.SingularCochains.differentialShortComplexIso,
      `HodgeConjecture.SingularCochains.cohomologyQuotientIso,
      `HodgeConjecture.SingularCochains.cohomologyClass,
      `HodgeConjecture.SingularCochains.cohomologyClass_surjective,
      `HodgeConjecture.SingularCochains.cohomologyClass_eq_zero_iff,
      `HodgeConjecture.SingularCochains.cocyclePullback,
      `HodgeConjecture.SingularCochains.cocyclePullback_differentialToCocycles,
      `HodgeConjecture.SingularCochains.quotientPullback,
      `HodgeConjecture.SingularCochains.quotientPullback_class,
      `SingularCochainsVerification.point_differential_one,
      `SingularCochainsVerification.point_one_cocycle_eq_zero,
      `SingularCochainsVerification.point_h1_eq_zero,
      `SingularCochainsVerification.point_two_cocycle_is_boundary,
      `SingularCochainsVerification.point_h2_eq_zero] do
    unless (← getEnv).contains declaration do
      throwError "Missing declaration in axiom audit: {declaration}"
    let axioms ← Lean.collectAxioms declaration
    for axiomName in axioms do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {declaration}"
    logInfo m!"PASS standard-three axiom boundary: {declaration}; {axioms.toList}"
