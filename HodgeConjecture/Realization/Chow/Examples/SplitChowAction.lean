module

public import HodgeConjecture.Realization.Chow.Examples.SplitChowAlgebra

@[expose] public section

/-!
# The actual Chow action of split correspondences

The action is pullback along the first product projection, intersection
with the correspondence, and pushforward along the second projection.
Its matrix formula is computed from those operations.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u

namespace SplitChowCorrespondence

open SplitZeroCycles Classical
open scoped BigOperators

variable (K : Type u) [Field K]
variable {I J L : Type u} [Finite I] [Finite J] [Finite L]

/-- A correspondence acts on actual Chow classes by pull--intersection--push
along the two projections of the actual split product. -/
def action (c : Correspondence K I J) (z : Chow K I ℚ) : Chow K J ℚ :=
  chowPushforward K ℚ (Prod.snd : I × J → J)
    (chowIntersection K ℚ c (chowPullback K ℚ (Prod.fst : I × J → I) z))

/-- The computed Chow action is multiplication of the Chow coefficient vector
by the correspondence matrix, with rows as outputs and columns as inputs. -/
theorem chowCoordinates_action [Fintype I] [Fintype J]
    (c : Correspondence K I J) (z : Chow K I ℚ) :
    chowCoordinates K J ℚ (action K c z) =
      (matrixCoordinates K I J c).mulVec (chowCoordinates K I ℚ z) := by
  ext j
  simp [action, chowCoordinates_pushforward, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, matrixCoordinates_apply]

/-- The geometrically defined Chow action respects correspondence composition. -/
theorem action_comp [Fintype I] [Fintype J] [Fintype L]
    (b : Correspondence K J L) (a : Correspondence K I J) (z : Chow K I ℚ) :
    action K (comp K b a) z = action K b (action K a z) := by
  apply (chowCoordinates K L ℚ).injective
  simp only [chowCoordinates_action, matrixCoordinates_comp, Matrix.mulVec_mulVec]

/-- The actual diagonal fundamental class acts as the identity on Chow. -/
@[simp]
theorem diagonal_action [Fintype I] (z : Chow K I ℚ) :
    action K (diagonal K) z = z := by
  apply (chowCoordinates K I ℚ).injective
  simp [chowCoordinates_action]

end SplitChowCorrespondence

end

end HodgeConjecture
