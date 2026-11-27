module

public import HodgeConjecture.Geometry.ProjectiveLineAffineChart
public import HodgeConjecture.Cycles.ProjectiveLineChow

@[expose] public section

/-!
# Original ordinary Chow classes of finite projective-line points

Each class is the original rational class map of the actual reduced
point cycle at the evaluation center of the affine normal chart. The
structural dimension function and Chow quotient are the original ones.
Over an algebraically closed field the existing degree map gives degree
one and detects that this same ordinary class is nonzero.

No Betti realization or Gysin normalization enters the definition.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineFinitePointChow

open AlgebraicGeometry SchemeCycles ProjectiveLineCycles

universe u

variable (k : Type u) [Field k]

abbrev Source := RationalChowGroup (dimensionFunction k) 0

/-- The unchanged reduced point representative at the actual affine center. -/
abbrev pointRepresentative (a : k) : cyclesOfDegree ℚ (dimensionFunction k) 0 :=
  pointCycle k ℚ (ProjectiveLineAffineChart.center k a)
    (ProjectiveLineAffineChart.center_ne_genericPoint k a)

/-- The ordinary class is defined by the original quotient map on that original representative. -/
def pointClass (a : k) : Source k :=
  rationalClassMap (dimensionFunction k) 0 (pointRepresentative k a)

@[simp]
theorem pointClass_classMap (a : k) :
    pointClass k a = rationalClassMap (dimensionFunction k) 0
      (pointCycle k ℚ (ProjectiveLineAffineChart.center k a)
        (ProjectiveLineAffineChart.center_ne_genericPoint k a)) := rfl

@[simp]
theorem pointRepresentative_val (a : k) :
    (pointRepresentative k a).val =
      fundamentalCycle ℚ (pointSupport (projectiveLine k) (ProjectiveLineAffineChart.center k a)) :=
  rfl

variable [hAlgClosed : IsAlgClosed k]

include hAlgClosed in
/-- The existing ordinary Chow degree of the same point class is exactly one. -/
theorem pointClass_degree (a : k) : rationalChowDegree k (pointClass k a) = 1 :=
  rationalChowDegree_pointCycle k _ _

include hAlgClosed in
theorem pointClass_ne_zero (a : k) : pointClass k a ≠ 0 := by
  intro h
  have hd := pointClass_degree k a
  rw [h, map_zero] at hd
  exact zero_ne_one hd

end HodgeConjecture.ProjectiveLineFinitePointChow

end
