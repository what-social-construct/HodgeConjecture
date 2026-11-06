module

public import HodgeConjecture.Realization.Betti.Examples.CircleTopology
public import HodgeConjecture.Realization.Betti.SingularComponents
public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.Realization.Betti.SingularDegreeZeroNaturality
public import HodgeConjecture.Realization.Betti.SingularMayerVietorisMaps
public import HodgeConjecture.Realization.Betti.TwoComponentBoundary

@[expose] public section

/-!
# The actual rational singular H¹ of the circle

The two punctured-circle charts are contractible and their actual overlap
has two path components. Original continuous pullback makes the H⁰
difference map constant on both components. Exactness of the constructed
singular Mayer–Vietoris sequence therefore identifies H¹ of the original
circle with the quotient of two component values by constant pairs.

The generator is the actual connecting image of the upper-component
indicator. Agreement with a standard oriented loop pairing is a separate
comparison, not a consequence of this rank-one calculation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace HodgeConjecture.CircleCohomology

open CategoryTheory CategoryTheory.Limits CircleTopology

abbrev space : TopCat := TopCat.of Circle

/-- Actual H⁰ coordinates on the two components of the original overlap. -/
def overlapZeroEquiv : SingularCochains.Cohomology (TopCat.of overlap) 0 ≃ₗ[ℚ] (Bool → ℚ) :=
  SingularComponents.cohomologyZeroEquiv overlapLabel overlapPoint overlapLabel_point
    joined_overlapPoint

@[simp]
theorem overlapZeroEquiv_apply (z : SingularCochains.Cohomology (TopCat.of overlap) 0)
    (i : Bool) : overlapZeroEquiv z i =
      SingularDegreeZero.eval overlap ((SingularCochains.cohomologyZeroIso overlap).hom z)
        (overlapPoint i) := rfl

/-- The original first-minus-second map on the actual chart H⁰ groups. -/
def difference := SingularMayerVietoris.difference space firstOpen secondOpen 0

/-- The original Mayer–Vietoris connecting map for the two actual circle charts. -/
def connecting := SingularMayerVietoris.connecting space firstOpen secondOpen
  firstOpen_isOpen secondOpen_isOpen opens_cover 0

/-- Evaluation of the two actual chart classes at one common overlap point. -/
def chartDifference (p : SingularCochains.Cohomology (TopCat.of firstOpen) 0 ×
    SingularCochains.Cohomology (TopCat.of secondOpen) 0) : ℚ :=
  SingularDegreeZero.eval firstOpen ((SingularCochains.cohomologyZeroIso firstOpen).hom p.1)
      (overlapToFirst (overlapPoint false)) -
    SingularDegreeZero.eval secondOpen ((SingularCochains.cohomologyZeroIso secondOpen).hom p.2)
      (overlapToSecond (overlapPoint false))

/-- Original restriction and path connectedness make both component values equal. -/
theorem difference_coordinates (p : SingularCochains.Cohomology (TopCat.of firstOpen) 0 ×
    SingularCochains.Cohomology (TopCat.of secondOpen) 0) :
    overlapZeroEquiv (difference p) = TwoComponentBoundary.diagonal (chartDifference p) := by
  funext i
  rw [difference, SingularMayerVietoris.difference_apply]
  change SingularDegreeZero.eval overlap
    ((SingularCochains.cohomologyZeroIso overlap).hom (_ - _)) (overlapPoint i) = _
  rw [map_sub]
  change SingularDegreeZero.eval overlap
    ((SingularCochains.cohomologyZeroIso overlap).hom
      (SingularCochains.cohomologyPullback
        (TopCat.ofHom ⟨overlapToFirst, continuous_overlapToFirst⟩) 0 p.1)) (overlapPoint i) -
    SingularDegreeZero.eval overlap
    ((SingularCochains.cohomologyZeroIso overlap).hom
      (SingularCochains.cohomologyPullback
        (TopCat.ofHom ⟨overlapToSecond, continuous_overlapToSecond⟩) 0 p.2)) (overlapPoint i) = _
  rw [SingularDegreeZeroNaturality.cohomologyZeroIso_pullback,
    SingularDegreeZeroNaturality.cohomologyZeroIso_pullback]
  rw [SingularDegreeZero.eval_pullback, SingularDegreeZero.eval_pullback]
  change SingularDegreeZero.eval firstOpen _ (overlapToFirst (overlapPoint i)) -
    SingularDegreeZero.eval secondOpen _ (overlapToSecond (overlapPoint i)) = _
  exact congrArg₂ (· - ·)
    (SingularDegreeZero.eval_eq firstOpen _ _ _) (SingularDegreeZero.eval_eq secondOpen _ _ _)

/-- Every constant pair comes from original constant cocycles on the charts. -/
theorem difference_constant (q : ℚ) :
    overlapZeroEquiv (difference
      (SingularDegreeZeroNaturality.constantClass firstOpen q, 0)) =
        TwoComponentBoundary.diagonal q := by
  rw [difference_coordinates]
  congr 1
  simp [chartDifference, SingularDegreeZeroNaturality.constantClass]

/-- The actual boundary is onto because positive cohomology of both actual charts vanishes. -/
theorem connecting_surjective : Function.Surjective connecting := by
  have hzero : SingularMayerVietoris.restriction space firstOpen secondOpen 1 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · exact SingularContractible.cohomology_eq_zero firstOpen 1 (by decide) _
    · exact SingularContractible.cohomology_eq_zero secondOpen 1 (by decide) _
  have he := SingularMayerVietoris.unionSequence_exact space firstOpen secondOpen
    firstOpen_isOpen secondOpen_isOpen opens_cover 0
  have hep := he.epi_f (by simpa using hzero)
  exact (ModuleCat.epi_iff_surjective _).mp hep

/-- The original boundary applied to the proved component coordinates. -/
def componentBoundary : (Bool → ℚ) →ₗ[ℚ] SingularCochains.Cohomology space 1 :=
  connecting.hom.comp overlapZeroEquiv.symm.toLinearMap

theorem componentBoundary_surjective : Function.Surjective componentBoundary := by
  intro z
  obtain ⟨x, hx⟩ := connecting_surjective z
  refine ⟨overlapZeroEquiv x, ?_⟩
  change connecting (overlapZeroEquiv.symm (overlapZeroEquiv x)) = z
  rw [LinearEquiv.symm_apply_apply]
  exact hx

/-- Exactness proves that the actual boundary kernel consists precisely of constant pairs. -/
theorem ker_componentBoundary : LinearMap.ker componentBoundary =
    LinearMap.range TwoComponentBoundary.diagonal := by
  have he := (SingularMayerVietoris.intersectionSequence_exact space firstOpen secondOpen
    firstOpen_isOpen secondOpen_isOpen opens_cover 0).moduleCat_range_eq_ker
  change LinearMap.range difference.hom = LinearMap.ker connecting.hom at he
  ext f
  constructor
  · intro hf
    have hm : overlapZeroEquiv.symm f ∈ LinearMap.range difference.hom := by
      rw [he]
      exact hf
    obtain ⟨p, hp⟩ := hm
    refine ⟨chartDifference p, ?_⟩
    rw [← difference_coordinates, hp, LinearEquiv.apply_symm_apply]
  · rintro ⟨q, rfl⟩
    change connecting (overlapZeroEquiv.symm (TwoComponentBoundary.diagonal q)) = 0
    have hm : overlapZeroEquiv.symm (TwoComponentBoundary.diagonal q) ∈
        LinearMap.range difference.hom := by
      refine ⟨(SingularDegreeZeroNaturality.constantClass firstOpen q, 0), ?_⟩
      apply overlapZeroEquiv.injective
      rw [difference_constant, LinearEquiv.apply_symm_apply]
    rw [he] at hm
    exact hm

/-- Proved rational coordinates on the actual singular H¹ of the circle. -/
def h1Equiv : SingularCochains.Cohomology space 1 ≃ₗ[ℚ] ℚ :=
  TwoComponentBoundary.boundaryEquiv componentBoundary componentBoundary_surjective
    ker_componentBoundary

/-- The coordinate is the upper component value minus the lower component value. -/
theorem h1Equiv_connecting (z : SingularCochains.Cohomology (TopCat.of overlap) 0) :
    h1Equiv (connecting z) = TwoComponentBoundary.jump (overlapZeroEquiv z) := by
  have h := TwoComponentBoundary.boundaryEquiv_apply componentBoundary
    componentBoundary_surjective ker_componentBoundary (overlapZeroEquiv z)
  change h1Equiv (connecting (overlapZeroEquiv.symm (overlapZeroEquiv z))) = _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

/-- The genuine Mayer–Vietoris image of the upper-component indicator. -/
def coverGenerator : SingularCochains.Cohomology space 1 :=
  componentBoundary (TwoComponentBoundary.step 1)

@[simp]
theorem h1Equiv_coverGenerator : h1Equiv coverGenerator = 1 := by
  exact (TwoComponentBoundary.boundaryEquiv_apply componentBoundary
    componentBoundary_surjective ker_componentBoundary (TwoComponentBoundary.step 1)).trans
      (TwoComponentBoundary.jump_step 1)

theorem coverGenerator_ne_zero : coverGenerator ≠ 0 :=
  TwoComponentBoundary.boundary_step_ne_zero componentBoundary componentBoundary_surjective
    ker_componentBoundary

end HodgeConjecture.CircleCohomology
