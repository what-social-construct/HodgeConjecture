import HodgeConjecture.Cycles.FiniteAffineLocalOrder
import HodgeConjecture.Cycles.FinitePushforwardCoefficients
import HodgeConjecture.Cycles.PrincipalDivisor

/-!
# Finite pushforward of the existing principal divisor

For a finite dominant morphism of integral schemes locally of finite type
over a field, the pushforward of the existing principal divisor is the
principal divisor of the norm in the original function fields. Local
Noetherianity and quasi-compactness are the hypotheses used by the existing
finite-cycle construction. No new cycle module or order function is introduced.

This is the finite case of Stacks 02RT, using the local identity 02MJ:
https://stacks.math.columbia.edu/tag/02RT
https://stacks.math.columbia.edu/tag/02MJ
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The coefficient on a divisor point's reduced closure is its original stalk order. -/
theorem principalDivisor_apply_point (X : Scheme.{u})
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (g : X.functionFieldˣ) (x : DivisorPoint X) :
    principalDivisor X g (pointSupport X x.val) = divisorOrder X x g := by
  exact (principalDivisor_apply_prime X g (divisorPointEquivPrimeDivisor X x)).trans
    (primeDivisorOrder_pointSupport x g)

/-- Finite pushforward commutes with principal divisors through the actual field norm.
The codimension comparison is the existing finite-type dimension formula. -/
theorem finitePushforward_principalDivisor
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [CompactSpace X] [CompactSpace Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] (g : X.functionFieldˣ) :
    finitePushforward ℤ f (principalDivisor X g) =
      principalDivisor Y (functionFieldNorm f g) := by
  classical
  ext W
  rw [← pointSupport_ambientGenericPoint W]
  let y := ambientGenericPoint W
  by_cases hy : ringKrullDim (Y.presheaf.stalk y) = 1
  · let y₁ : DivisorPoint Y := ⟨y, hy⟩
    rw [finitePushforward_apply_pointSupport,
      principalDivisor_apply_point Y (functionFieldNorm f g) y₁,
      divisorOrder_norm_eq_sum_fiber f y₁ k pY g]
    apply finsum_congr
    intro x
    exact congrArg (fun a : ℤ ↦ (residueFieldDegree f x.val : ℤ) * a)
      (principalDivisor_apply_point X g (divisorPointOfFiniteFiber k pY f y₁ x))
  · have hY : supportCodimension (pointSupport Y y) ≠ 1 := by
      intro h
      apply hy
      exact (congrArg (fun z : Y ↦ ringKrullDim (Y.presheaf.stalk z))
        (ambientGenericPoint_pointSupport Y y)).symm.trans
          ((supportCodimension_eq_one_iff (pointSupport Y y)).mp h)
    rw [principalDivisor_apply_of_not_prime Y (functionFieldNorm f g) _ hY,
      finitePushforward_apply_pointSupport]
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    have hX : supportCodimension (pointSupport X x.val) ≠ 1 := by
      intro h
      apply hy
      have hd := (supportCodimension_eq_one_iff (pointSupport X x.val)).mp h
      have he := (congrArg (fun z : X ↦ ringKrullDim (X.presheaf.stalk z))
        (ambientGenericPoint_pointSupport X x.val)).trans
          ((stalkDimension_finite_dominant k pY f x.val).trans
            (congrArg (fun z : Y ↦ ringKrullDim (Y.presheaf.stalk z)) x.property))
      exact he.symm.trans hd
    rw [principalDivisor_apply_of_not_prime X g _ hX, mul_zero]

end

end HodgeConjecture.SchemeCycles
