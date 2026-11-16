module

public import HodgeConjecture.Cycles.BaseFieldScalarPrincipalDivisor

/-!
# Base scalars through an affine open chart

For an integral open immersion over `Spec k`, the actual contravariant
function-field equivalence sends a scalar from the ambient structure map
to the same scalar from the chart structure map. This uses equality of the
two scheme morphisms over the field, with no chosen fraction-field model.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles.ProjectiveLineDegree

noncomputable section

universe u

theorem baseFieldScalar_openImmersion
    (k : Type u) [Field k]
    {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    (j : U ⟶ X) [IsOpenImmersion j]
    (p : X ⟶ Spec (.of k)) (q : U ⟶ Spec (.of k))
    (h : j ≫ p = q) (c : kˣ) :
    letI : Algebra k (Spec (.of k)).functionField := specFunctionFieldAlgebra (.of k)
    letI : IsDominant p := isDominant_toSpecField k X p
    letI : IsDominant q := isDominant_toSpecField k U q
    Units.map (functionFieldEquivOfOpenImmersion j).toMonoidHom
      (Units.map (functionFieldMapOfDominant p).hom.toMonoidHom
        (Units.map (algebraMap k (Spec (.of k)).functionField).toMonoidHom c)) =
      Units.map (functionFieldMapOfDominant q).hom.toMonoidHom
        (Units.map (algebraMap k (Spec (.of k)).functionField).toMonoidHom c) := by
  letI : Algebra k (Spec (.of k)).functionField := specFunctionFieldAlgebra (.of k)
  letI : IsDominant p := isDominant_toSpecField k X p
  letI : IsDominant q := isDominant_toSpecField k U q
  letI : IsDominant j := isDominant_integralOpenImmersion j
  apply Units.ext
  change (functionFieldEquivOfOpenImmersion j)
    ((functionFieldMapOfDominant p).hom
      (algebraMap k (Spec (.of k)).functionField (c : k))) =
    (functionFieldMapOfDominant q).hom
      (algebraMap k (Spec (.of k)).functionField (c : k))
  have hcomp : functionFieldMapOfDominant q =
      functionFieldMapOfDominant p ≫ functionFieldMapOfDominant j := by
    simpa only [h] using functionFieldMapOfDominant_comp p j
  have hval := congrArg
    (fun f : (Spec (.of k)).functionField ⟶ U.functionField =>
      f.hom (algebraMap k (Spec (.of k)).functionField (c : k))) hcomp
  change (functionFieldMapOfDominant q).hom _ =
    (functionFieldMapOfDominant j).hom
      ((functionFieldMapOfDominant p).hom _) at hval
  exact hval.symm

end

end HodgeConjecture.SchemeCycles

end
