import HodgeConjecture.Realization.Betti.Examples.SplitTateBlock
import HodgeConjecture.Realization.Chow.Examples.SplitChowShear

/-!
# The Betti action of an actual Chow shear

The already constructed pull--cup--transfer action sends the geometric
column to its lower-left operator and the invertible Chow shear to the
corresponding change of splitting. The cohomological coordinate change is
therefore realized by an actual invertible Chow correspondence.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitBettiTateBlock

noncomputable section

open Classical SplitBetti

variable (I : Type) [Fintype I] [DecidableEq I]

/-- The actual column acts only from the distinguished point to the complement. -/
theorem realization_column_apply (z : SplitZeroCycles.Chow ℂ I ℚ)
    (v : ℚ × Cohomology I) :
    realization I (SplitChowTateBlock.column I z) v = (0, v.1 • cycleClass I z) := by
  rw [realization_apply]
  apply Prod.ext
  · rw [blockCoordinates_fst, coordinates_action,
      ← SplitChowCorrespondence.matrixAlgEquiv_apply, SplitChowTateBlock.matrix_column]
    simp [Matrix.mulVec, dotProduct]
  · apply (coordinates I).injective
    funext i
    rw [coordinates_blockCoordinates_snd, coordinates_action,
      ← SplitChowCorrespondence.matrixAlgEquiv_apply, SplitChowTateBlock.matrix_column]
    simp [Matrix.mulVec, dotProduct, -coordinates_apply,
      -SplitZeroCycles.coordinates_apply, mul_comm]

set_option synthInstance.maxHeartbeats 60000 in
/-- The cohomological shear is the action of an invertible geometric Chow correspondence. -/
theorem realization_shear (z : SplitZeroCycles.Chow ℂ I ℚ) :
    realization I (SplitChowShear.shear I z) =
      (ClassGraphProjector.shear (cycleClass I z)).toLinearMap := by
  rw [SplitChowShear.shear, map_add, map_one]
  apply LinearMap.ext
  intro v
  change v + realization I (SplitChowTateBlock.column I z) v = _
  rw [realization_column_apply]
  rcases v with ⟨t, h⟩
  simp only [Prod.mk_add_mk, add_zero, LinearEquiv.coe_coe,
    ClassGraphProjector.shear_apply]

end

end HodgeConjecture.SplitBettiTateBlock
