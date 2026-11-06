module

public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineComplexPoints
public import HodgeConjecture.Realization.Betti.Examples.PuncturedComplexCircle
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

/-!
# The actual analytic projective-line cover and overlap

The original affine evaluation charts are homeomorphic to their actual
open ranges. Their actual intersection has the native punctured-plane
topology, via the original finite coordinate. Native polar coordinates
then give its explicit radial homotopy equivalence with the circle.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineAnalyticCover

open Topology ContinuousMap ProjectiveLineComplexPoints
open scoped Topology

/-- The range of the original finite evaluation chart. -/
def finiteOpen : Set Point := Set.range finite

/-- The range of the original reciprocal evaluation chart. -/
def reciprocalOpen : Set Point := Set.range reciprocal

theorem isOpen_finiteOpen : IsOpen finiteOpen := isOpenEmbedding_finite.isOpen_range

theorem isOpen_reciprocalOpen : IsOpen reciprocalOpen := isOpenEmbedding_reciprocal.isOpen_range

theorem cover : finiteOpen ∪ reciprocalOpen = Set.univ := range_finite_union_reciprocal

/-- The actual finite chart range has the usual complex-plane topology. -/
def finiteHomeomorph : ℂ ≃ₜ finiteOpen := isOpenEmbedding_finite.isEmbedding.toHomeomorph

/-- The actual reciprocal chart range has the usual complex-plane topology. -/
def reciprocalHomeomorph : ℂ ≃ₜ reciprocalOpen := isOpenEmbedding_reciprocal.isEmbedding.toHomeomorph

instance finiteOpenContractibleSpace : ContractibleSpace finiteOpen :=
  finiteHomeomorph.symm.contractibleSpace

instance reciprocalOpenContractibleSpace : ContractibleSpace reciprocalOpen :=
  reciprocalHomeomorph.symm.contractibleSpace

@[simp]
theorem finiteHomeomorph_coe (z : ℂ) : (finiteHomeomorph z : Point) = finite z := rfl

@[simp]
theorem reciprocalHomeomorph_coe (z : ℂ) : (reciprocalHomeomorph z : Point) = reciprocal z := rfl

/-- A finite point lies in the reciprocal chart precisely away from zero. -/
theorem finite_mem_reciprocal_iff (z : ℂ) : finite z ∈ reciprocalOpen ↔ z ≠ 0 := by
  constructor
  · rintro ⟨w, hw⟩ rfl
    by_cases hw0 : w = 0
    · subst w
      exact finite_ne_infinity 0 hw.symm
    · have he : w⁻¹ = 0 :=
        finite_injective ((reciprocal_eq_finite_inv w hw0).symm.trans hw)
      exact inv_ne_zero hw0 he
  · intro hz
    exact ⟨z⁻¹, (finite_eq_reciprocal_inv z hz).symm⟩

/-- Nonzero finite coordinate points in the actual chart intersection. -/
def finiteOverlap (z : PuncturedComplexCircle.Plane) : ↥(finiteOpen ∩ reciprocalOpen) :=
  ⟨finite z, ⟨⟨z, rfl⟩, (finite_mem_reciprocal_iff z).mpr z.property⟩⟩

theorem finiteOverlap_injective : Function.Injective finiteOverlap := by
  intro z w h
  apply Subtype.ext
  exact finite_injective (congrArg Subtype.val h)

theorem finiteOverlap_surjective : Function.Surjective finiteOverlap := by
  intro p
  obtain ⟨z, hz⟩ := p.property.1
  have hright : finite z ∈ reciprocalOpen := by rw [hz]; exact p.property.2
  have hz0 := (finite_mem_reciprocal_iff z).mp hright
  exact ⟨⟨z, hz0⟩, Subtype.ext hz⟩

theorem isEmbedding_finiteOverlap : IsEmbedding finiteOverlap := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  exact isOpenEmbedding_finite.isEmbedding.comp IsEmbedding.subtypeVal

/-- The original overlap, with its actual subspace topology, is the punctured complex plane. -/
def overlapHomeomorph : PuncturedComplexCircle.Plane ≃ₜ ↥(finiteOpen ∩ reciprocalOpen) :=
  isEmbedding_finiteOverlap.toHomeomorphOfSurjective finiteOverlap_surjective

@[simp]
theorem overlapHomeomorph_coe (z : PuncturedComplexCircle.Plane) :
    (overlapHomeomorph z : Point) = finite z := rfl

/-- The actual overlap has the native circle's homotopy type by radial normalization. -/
def overlapCircleHomotopyEquiv : ↥(finiteOpen ∩ reciprocalOpen) ≃ₕ Circle :=
  overlapHomeomorph.symm.toHomotopyEquiv.trans PuncturedComplexCircle.homotopyEquiv

@[simp]
theorem overlapCircleHomotopyEquiv_finite (z : PuncturedComplexCircle.Plane) :
    overlapCircleHomotopyEquiv (overlapHomeomorph z) = PuncturedComplexCircle.radial z := by
  change PuncturedComplexCircle.homotopyEquiv (overlapHomeomorph.symm (overlapHomeomorph z)) = _
  rw [Homeomorph.symm_apply_apply, PuncturedComplexCircle.homotopyEquiv_apply]

end HodgeConjecture.ProjectiveLineAnalyticCover
