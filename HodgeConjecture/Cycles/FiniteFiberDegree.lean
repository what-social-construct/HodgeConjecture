module

public import HodgeConjecture.Cycles.FiniteFiberPullback
public import HodgeConjecture.Cycles.FiberResidueField

@[expose] public section

/-!
# The actual finite-fiber degree formula for cycle push--pull

The finite-scheme length formula is reindexed over the original source
points using the actual residue-field comparison. It proves the pointwise
degree formula for the original finite cycle pushforward and fiber pullback.
The rank function is computed from the actual geometric fiber; no degree
law or residue-degree compatibility is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]

/-- The degree of the actual fiber is its residue-degree-weighted sum of
local lengths, indexed by the original source points. -/
theorem finiteFiberDegree_eq_sum (y : Y) :
    finiteFiberDegree f y = ∑ᶠ x : {x : X // f.base x = y},
      residueFieldDegree f x.val * finiteFiberMultiplicity f x.val := by
  letI : IsFinite (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  change (letI := globalSectionBaseAlgebra (Y.residueField y) (f.fiberToSpecResidueField y)
    Module.finrank (Y.residueField y) Γ(f.fiber y, ⊤)) = _
  rw [finiteScheme_finrank_eq_sum_stalkLength]
  symm
  apply finsum_eq_of_bijective (f.fiberHomeo y).symm (f.fiberHomeo y).symm.bijective
  rintro ⟨x, hx⟩
  cases hx
  letI : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  letI := residueFieldBaseAlgebra (Y.residueField (f.base x))
    (f.fiberToSpecResidueField (f.base x)) (f.asFiber x)
  change Module.finrank (Y.residueField (f.base x)) (X.residueField x) * _ =
    Module.finrank (Y.residueField (f.base x))
      ((f.fiber (f.base x)).residueField (f.asFiber x)) * _
  rw [(fiberResidueFieldAlgEquiv f x).toLinearEquiv.finrank_eq]
  rfl

/-- The existing pushforward after actual finite-fiber pullback multiplies
the coefficient at each target support by the degree of that same fiber. -/
theorem finitePushforward_finiteFiberPullback_apply
    (R : Type v) [CommSemiring R] (c : Cycles Y R) (y : Y) :
    finitePushforward R f (finiteFiberPullback f R c) (pointSupport Y y) =
      (finiteFiberDegree f y : R) * c (pointSupport Y y) := by
  classical
  letI := finiteFiber_finite f y
  letI : Fintype {x : X // f.base x = y} := Fintype.ofFinite _
  rw [finitePushforward_apply_pointSupport, finiteFiberDegree_eq_sum,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [finiteFiberPullback_apply_pointSupport, x.property, Nat.cast_mul]
  ring

/-- Constant geometric fiber degree gives the actual cycle push--pull law.
The premise specifies the computed rank function, not a supplied identity
between pushforward and pullback operators. -/
theorem finitePushforward_finiteFiberPullback_of_degree_eq
    (R : Type v) [CommSemiring R] (d : ℕ)
    (hd : ∀ y : Y, finiteFiberDegree f y = d) (c : Cycles Y R) :
    finitePushforward R f (finiteFiberPullback f R c) = d • c := by
  apply Finsupp.ext
  intro W
  rw [← pointSupport_ambientGenericPoint W, finitePushforward_finiteFiberPullback_apply, hd]
  simp only [Finsupp.smul_apply, nsmul_eq_mul, pointSupport_ambientGenericPoint]

end

end HodgeConjecture.SchemeCycles
