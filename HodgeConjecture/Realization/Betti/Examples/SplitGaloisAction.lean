module

public import HodgeConjecture.Realization.Betti.Examples.SplitGaloisMarkedComparison

@[expose] public section

/-!
# The full marked sheet-algebra action on actual Betti cohomology

Actual diagonal Chow correspondences act on the cohomology of actual sheet
cycles by pointwise multiplication. The invertible Chow shear intertwines
that entire diagonal algebra with the marked embedding. Consequently the
constant-marked comparison respects every sheet function, not only the
distinguished selector.
-/

set_option autoImplicit false

namespace HodgeConjecture.SplitGaloisMarkedComparison

noncomputable section

open Classical SplitBetti

variable {G : Type} [Group G] [Finite G] (D : Subgroup G)

local instance : Fintype (SplitGaloisResidual.Complement D) :=
  Fintype.ofFinite (SplitGaloisResidual.Complement D)

/-- The actual diagonal pushforward acts on actual sheet-cycle cohomology
as multiplication by the original sheet function. -/
theorem diagonal_action_sheetCohomology (f g : GenericSheetAlgebra ℚ D) :
    action
      (SplitChowDiagonal.diagonalAlgHom ℂ (Option (SplitGaloisResidual.Complement D))
        (sheetReindex D f)) (sheetCohomology D g) = sheetCohomology D (f * g) := by
  apply (coordinates (Option (SplitGaloisResidual.Complement D))).injective
  rw [coordinates_action, ← SplitChowCorrespondence.matrixAlgEquiv_apply,
    SplitChowDiagonal.matrix_diagonalAlgHom]
  funext s
  simp only [Matrix.mulVec_diagonal, coordinates_sheetCohomology, Pi.mul_apply]
  rfl

/-- The preceding diagonal action in the fixed point-plus-complement block. -/
theorem diagonal_realization_sheetCohomology (f g : GenericSheetAlgebra ℚ D) :
    SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)
      (SplitChowDiagonal.diagonalAlgHom ℂ (Option (SplitGaloisResidual.Complement D))
        (sheetReindex D f))
      (SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D)
        (sheetCohomology D g)) =
      SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D)
        (sheetCohomology D (f * g)) := by
  rw [SplitBettiTateBlock.realization_apply, LinearEquiv.symm_apply_apply,
    diagonal_action_sheetCohomology]

/-- The geometric marked embedding and the raw diagonal embedding are
intertwined by the actual invertible Chow shear. -/
theorem markedEmbedding_mul_shear (f : GenericSheetAlgebra ℚ D) :
    markedEmbedding D f *
        SplitChowShear.shear (SplitGaloisResidual.Complement D) (generatedChowClass D) =
      SplitChowShear.shear (SplitGaloisResidual.Complement D) (generatedChowClass D) *
        SplitChowDiagonal.diagonalAlgHom ℂ (Option (SplitGaloisResidual.Complement D))
          (sheetReindex D f) := by
  change
    (SplitChowShear.shear (SplitGaloisResidual.Complement D) (generatedChowClass D) *
        SplitChowDiagonal.diagonalAlgHom ℂ (Option (SplitGaloisResidual.Complement D))
          (sheetReindex D f) *
        SplitChowShear.shear (SplitGaloisResidual.Complement D) (-generatedChowClass D)) *
      SplitChowShear.shear (SplitGaloisResidual.Complement D) (generatedChowClass D) = _
  rw [mul_assoc, SplitChowShear.shear_neg_mul_shear, mul_one]

set_option synthInstance.maxHeartbeats 60000 in
/-- The full sheet algebra acts on the actual constant-marked Betti comparison:
all pointwise products, not just multiplication by the selector, intertwine. -/
theorem markedEmbedding_action (f g : GenericSheetAlgebra ℚ D) :
    SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)
      (markedEmbedding D f) (sourceToBlock D g) = sourceToBlock D (f * g) := by
  rw [sourceToBlock_eq_realization_shear D g,
    sourceToBlock_eq_realization_shear D (f * g)]
  change
    (SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D) (markedEmbedding D f) *
      SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)
        (SplitChowShear.shear (SplitGaloisResidual.Complement D) (generatedChowClass D)))
      (SplitBettiTateBlock.blockCoordinates (SplitGaloisResidual.Complement D)
        (sheetCohomology D g)) = _
  rw [← map_mul (SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)),
    markedEmbedding_mul_shear,
    map_mul (SplitBettiTateBlock.realization (SplitGaloisResidual.Complement D)),
    Module.End.mul_apply, diagonal_realization_sheetCohomology]

end

end HodgeConjecture.SplitGaloisMarkedComparison
