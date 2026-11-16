module

public import HodgeConjecture.Cycles.ProjectiveLineProductZeroAffineChowLocalization
public import HodgeConjecture.Geometry.ProjectiveLineProductTopology

/-! The opposite affine product chart is the analytic comparison's `(y,y)` tensor chart. -/

@[expose] public section

namespace HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization

open HodgeConjecture.ProjectiveLineProductComplexPoints

/-- The zero-boundary chart is literally the existing complex tensor chart
with the second coordinate choice in both factors. -/
theorem chart_complex_eq_productTensorChart_true_true :
    chart ℂ = productTensorChart true true := by
  rfl

end HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization

end
