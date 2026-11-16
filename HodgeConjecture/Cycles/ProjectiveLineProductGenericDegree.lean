module

public import HodgeConjecture.Geometry.ProjectiveLineProductIntegral

/-! The generic degree of the actual integral projective-line product. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductChow

open AlgebraicGeometry SchemeCycles
open HodgeConjecture.ProjectiveLineProductFiberCodimension

universe u

variable (k : Type u) [Field k]

/-- One actual zero fiber has codimension one and degree one, so the
generic dimension-function degree of the product is two. -/
theorem generic_degree_two :
    dimensionFunction k (genericPoint (projectiveLineProduct k)) = 2 := by
  have h := supportCodimension_add_supportDegree_of_integral_locallyOfFiniteType
    k (projectiveLineProduct k) (projectiveLineProductStructureMorphism k)
    (projectiveLineProductZeroFirstCarrier k)
  change ((supportCodimension (projectiveLineProductZeroFirstCarrier k)).toNat : ℤ) +
      supportDegree (dimensionFunction k) (projectiveLineProductZeroFirstCarrier k) =
        dimensionFunction k (genericPoint (projectiveLineProduct k)) at h
  rw [firstZeroCarrier_codimension_one, firstCarrier_supportDegree_one] at h
  norm_num at h
  exact h.symm

/-- The Chow relation carrier degree for divisors is the generic degree
minus one in the product's actual dimension function. -/
theorem generic_degree_sub_one_eq_one :
    dimensionFunction k (genericPoint (projectiveLineProduct k)) - 1 = 1 := by
  rw [generic_degree_two]
  norm_num

end HodgeConjecture.ProjectiveLineProductChow

end
