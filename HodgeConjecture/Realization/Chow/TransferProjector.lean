module

public import HodgeConjecture.Realization.Transfer
public import HodgeConjecture.Realization.Chow.Model

@[expose] public section

/-!
# Degree transfer as a cohomological projector

The generic transfer API is re-exported from `Realization.Transfer`.
This module adds its conversion to the existing cohomological projector
model. `Chow.FiniteFlatTransfer` supplies an actual finite flat Chow
instance; general Betti transfer remains a separate geometric construction.
-/

set_option autoImplicit false

namespace HodgeConjecture

noncomputable section

universe u v

namespace RationalDegreeTransfer

variable {V : Type u} {W : Type v}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]

/-- Transfer data canonically determines a rational cohomological projector.
The same constructor can be instantiated with rational Chow groups once
their pull--push operations are supplied. -/
def toRationalCohomologicalProjector
    (T : RationalDegreeTransfer V W) :
    RationalCohomologicalProjector V where
  operator := T.normalizedProjector
  operator_isIdempotent := T.normalizedProjector_isIdempotent

@[simp]
theorem toRationalCohomologicalProjector_operator
    (T : RationalDegreeTransfer V W) :
    T.toRationalCohomologicalProjector.operator =
      T.normalizedProjector :=
  rfl

end RationalDegreeTransfer

end

end HodgeConjecture
