import HodgeConjecture.Cycles.FinitePushforward
import HodgeConjecture.Cycles.FunctionFieldResidue

/-!
# The existing finite pushforward weight is the actual residue degree

The support-to-image function fields identify with the corresponding
ambient residue fields. Compatibility follows from the actual image
factorization and functoriality of residue maps. This is the weight in
the coefficient formula of Stacks 02RT:
https://stacks.math.columbia.edu/tag/02RT
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The old support-to-image field degree equals the actual ambient residue degree. -/
theorem finitePushforwardDegree_eq_residueFieldDegree {X Y : Scheme.{u}}
    (f : X ⟶ Y) (W : IntegralClosedSubscheme X) [IsFinite (W.val.subschemeι ≫ f)] :
    finitePushforwardDegree f W = residueFieldDegree f (ambientGenericPoint W) := by
  letI := W.property
  letI : IsIntegral (W.val.subschemeι ≫ f).image := (imageSubscheme f W).property
  letI : Algebra (W.val.subschemeι ≫ f).image.functionField W.val.subscheme.functionField :=
    (functionFieldMapOfDominant (W.val.subschemeι ≫ f).toImage).hom.toAlgebra
  change Module.finrank (W.val.subschemeι ≫ f).image.functionField W.val.subscheme.functionField = _
  rw [functionField_finrank_eq_residueFieldDegree,
    ← residueFieldDegree_comp_of_target_surjectiveOnStalks
      (W.val.subschemeι ≫ f).toImage (W.val.subschemeι ≫ f).imageι,
    Scheme.Hom.toImage_imageι, residueFieldDegree_comp_of_source_surjectiveOnStalks]
  rfl

end

end HodgeConjecture.SchemeCycles
