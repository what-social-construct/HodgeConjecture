module

public import HodgeConjecture.Cycles.PrincipalDivisor
public import HodgeConjecture.Cycles.RationalFunctionPresentation

/-!
# Global units have zero principal divisor

A unit among global sections remains a unit in every stalk. Its image in
the function field therefore has zero local order at every divisor point
and zero principal divisor. In particular, any nonzero base-field scalar
has zero principal divisor once its structure-map image is identified as
a global unit.
-/

@[expose] public section

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry

noncomputable section

universe u

private instance nonempty_topOpen_of_integral (X : Scheme.{u}) [IsIntegral X] :
    Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩

/-- The image of a global unit has zero order at every divisor point. -/
theorem divisorOrder_globalUnit_zero (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [Nonempty (⊤ : X.Opens)]
    (x : DivisorPoint X) (a : Γ(X, ⊤)ˣ) :
    divisorOrder X x
      (Units.map (algebraMap Γ(X, ⊤) X.functionField).toMonoidHom a) = 0 := by
  let ax : (X.presheaf.stalk x.val)ˣ :=
    Units.map (X.presheaf.germ ⊤ x.val (by trivial)).hom.toMonoidHom a
  have h : Units.map (algebraMap Γ(X, ⊤) X.functionField).toMonoidHom a =
      Units.map (algebraMap (X.presheaf.stalk x.val) X.functionField).toMonoidHom ax := by
    apply Units.ext
    change algebraMap Γ(X, ⊤) X.functionField (a : Γ(X, ⊤)) =
      algebraMap (X.presheaf.stalk x.val) X.functionField
        ((X.presheaf.germ ⊤ x.val (by trivial)).hom (a : Γ(X, ⊤)))
    exact (sectionToFunctionField_through_stalk X ⊤
      ⟨x.val, by trivial⟩ (a : Γ(X, ⊤))).symm
  change localOrder (X.presheaf.stalk x.val)
    (Units.map (algebraMap Γ(X, ⊤) X.functionField).toMonoidHom a) = 0
  rw [h, localOrder_map_unit]

/-- The principal divisor of a global unit is the zero cycle. -/
theorem principalDivisor_globalUnit_zero (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [Nonempty (⊤ : X.Opens)]
    (a : Γ(X, ⊤)ˣ) :
    principalDivisor X
      (Units.map (algebraMap Γ(X, ⊤) X.functionField).toMonoidHom a) = 0 := by
  apply (principalDivisor_eq_zero_iff X _).mpr
  intro Z
  exact divisorOrder_globalUnit_zero X
    ((divisorPointEquivPrimeDivisor X).symm Z) a

end

end HodgeConjecture.SchemeCycles

end
