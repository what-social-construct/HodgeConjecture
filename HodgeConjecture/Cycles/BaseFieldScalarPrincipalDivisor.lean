module

public import HodgeConjecture.Cycles.GlobalUnitPrincipalDivisor
public import HodgeConjecture.Cycles.FunctionFieldMap
public import HodgeConjecture.Cycles.ProjectiveLineOrderDictionary

/-!
# Base-field scalars have zero principal divisor

For a dominant integral scheme over a field, every nonzero base scalar
maps to a unit in each local stalk. The dominant function-field map
therefore gives it zero local divisor order and zero principal divisor.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory
open HodgeConjecture.SchemeCycles.ProjectiveLineDegree

noncomputable section

universe u

theorem isDominant_toSpecField (k : Type u) [Field k]
    (X : Scheme.{u}) [IsIntegral X] (p : X ⟶ Spec (.of k)) : IsDominant p := by
  have hp : Function.Surjective p.base := by
    intro y
    exact ⟨genericPoint X, Subsingleton.elim _ _⟩
  exact ⟨hp.denseRange⟩

theorem isDominant_integralOpenImmersion {U X : Scheme.{u}}
    [IsIntegral U] [IsIntegral X] (j : U ⟶ X) [IsOpenImmersion j] :
    IsDominant j := by
  exact ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j.base)⟩

variable (k : Type u) [Field k]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (.of k)) [IsDominant p]

/-- The actual function-field image of a nonzero base scalar has zero
order at every divisor point of the integral scheme. -/
theorem divisorOrder_baseFieldScalar_zero
    (x : DivisorPoint X) (c : kˣ) :
    letI : Algebra k (Spec (.of k)).functionField := specFunctionFieldAlgebra (.of k)
    divisorOrder X x
      (Units.map (functionFieldMapOfDominant p).hom.toMonoidHom
        (Units.map (algebraMap k (Spec (.of k)).functionField).toMonoidHom c)) = 0 := by
  letI : Algebra k (Spec (.of k)).functionField := specFunctionFieldAlgebra (.of k)
  let Y : Scheme.{u} := Spec (.of k)
  let y : Y := p.base x.val
  letI : Algebra k Y.functionField := specFunctionFieldAlgebra (.of k)
  letI : y.asIdeal.IsPrime := y.isPrime
  letI : Algebra k (Y.presheaf.stalk y) := specStalkAlgebra (.of k) y
  letI : IsLocalization.AtPrime (Y.presheaf.stalk y) y.asIdeal :=
    specStalkIsLocalization (.of k) y
  letI : IsScalarTower k (Y.presheaf.stalk y) Y.functionField :=
    spec_stalk_functionField_isScalarTower (.of k) y
  let cy : (Y.presheaf.stalk y)ˣ :=
    Units.map (algebraMap k (Y.presheaf.stalk y)).toMonoidHom c
  let cx : (X.presheaf.stalk x.val)ˣ :=
    Units.map (p.stalkMap x.val).hom.toMonoidHom cy
  have h : Units.map (functionFieldMapOfDominant p).hom.toMonoidHom
        (Units.map (algebraMap k Y.functionField).toMonoidHom c) =
      Units.map (algebraMap (X.presheaf.stalk x.val) X.functionField).toMonoidHom cx := by
    apply Units.ext
    change (functionFieldMapOfDominant p).hom
        (algebraMap k Y.functionField (c : k)) =
      algebraMap (X.presheaf.stalk x.val) X.functionField
        ((p.stalkMap x.val).hom
          (algebraMap k (Y.presheaf.stalk y) (c : k)))
    rw [IsScalarTower.algebraMap_apply k (Y.presheaf.stalk y) Y.functionField]
    exact functionFieldMapOfDominant_algebraMap p x.val _
  change localOrder (X.presheaf.stalk x.val) _ = 0
  rw [h, localOrder_map_unit]

/-- The principal divisor of a nonzero base-field scalar is zero. -/
theorem principalDivisor_baseFieldScalar_zero
    [CompactSpace X] (c : kˣ) :
    letI : Algebra k (Spec (.of k)).functionField := specFunctionFieldAlgebra (.of k)
    principalDivisor X
      (Units.map (functionFieldMapOfDominant p).hom.toMonoidHom
        (Units.map (algebraMap k (Spec (.of k)).functionField).toMonoidHom c)) = 0 := by
  letI : Algebra k (Spec (.of k)).functionField := specFunctionFieldAlgebra (.of k)
  apply (principalDivisor_eq_zero_iff X _).mpr
  intro Z
  exact divisorOrder_baseFieldScalar_zero k X p
    ((divisorPointEquivPrimeDivisor X).symm Z) c

end

end HodgeConjecture.SchemeCycles

end
