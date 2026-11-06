module

public import HodgeConjecture.Cycles.ProjectiveLineCycleDegree
public import HodgeConjecture.Cycles.ProjectiveLineDivisorPoints
public import HodgeConjecture.Cycles.ProjectiveLineGlobalOrder

@[expose] public section

/-!
# Actual principal-divisor degree zero on the glued projective line

The original principal-divisor cycle is summed over its actual divisor
points. The genuine finite-chart/infinity decomposition and polynomial
prime dictionary reindex that sum, and the original stalk orders agree
with the polynomial factor orders and the geometric inversion at infinity.
Over an algebraically closed field all irreducible polynomial degrees are
one, so the arithmetic product formula kills the actual coefficient sum.
No rational-equivalence invariance or degree-zero premise is supplied.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineCycles

open AlgebraicGeometry CategoryTheory SchemeCycles
open SchemeCycles.ProjectiveLineDegree
open scoped Classical

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The original finite-chart divisor-point sum is exactly the arithmetic factor-order sum. -/
theorem finsum_chartDivisorOrder_eq_finiteOrder (f : (projectiveLine k).functionFieldˣ) :
    (∑ᶠ x : DivisorPoint (Spec (.of (Polynomial k))),
      divisorOrder (projectiveLine k) (chartDivisorPointEmbedding k x) f) =
      ∑ᶠ p : Polynomial k,
        finiteOrder p (projectiveLineFunctionFieldEquiv k (f : (projectiveLine k).functionField)) := by
  classical
  let g := projectiveLineFunctionFieldEquiv k (f : (projectiveLine k).functionField)
  calc
    _ = ∑ᶠ p : MonicIrreducibles k,
        divisorOrder (projectiveLine k)
          (chartDivisorPointEmbedding k ((polynomialDivisorPointEquiv k).symm p)) f :=
      (finsum_comp_equiv (polynomialDivisorPointEquiv k).symm
        (f := fun x ↦ divisorOrder (projectiveLine k) (chartDivisorPointEmbedding k x) f)).symm
    _ = ∑ᶠ p : MonicIrreducibles k, finiteOrder p.val g := by
      apply finsum_congr
      intro p
      rw [polynomialDivisorPointEquiv_symm]
      exact finiteDivisorPoint_order k p.property.2 p.property.1 f
    _ = ∑ᶠ p : Polynomial k, finiteOrder p g := by
      refine finsum_monicIrreducibles_of_zero_outside k (fun p ↦ finiteOrder p g) ?_
      intro p hp
      by_contra h
      exact hp (finiteOrder_ne_zero_imp_monic_irreducible k h)

/-- The original infinity coefficient is the negative rational-function degree in the first chart. -/
theorem divisorOrder_infinity_eq_infinityOrder (f : (projectiveLine k).functionFieldˣ) :
    divisorOrder (projectiveLine k) (infinityDivisorPoint k) f =
      infinityOrder (projectiveLineFunctionFieldEquiv k (f : (projectiveLine k).functionField)) := by
  classical
  have hx : infinityDivisorPoint k = SchemeCycles.ProjectiveLineDegree.infinityDivisorPoint k :=
    Subtype.ext rfl
  rw [hx, SchemeCycles.ProjectiveLineDegree.infinityDivisorPoint_order]
  rfl

/-- The actual principal-divisor coefficient degree is zero, with invariance fully derived. -/
theorem coefficientSum_principalDivisor_eq_zero [IsAlgClosed k]
    (f : (projectiveLine k).functionFieldˣ) :
    coefficientSum k ℤ (principalDivisor (projectiveLine k) f) = 0 := by
  classical
  rw [coefficientSum_principalDivisor, finsum_divisorOrder,
    finsum_chartDivisorOrder_eq_finiteOrder, divisorOrder_infinity_eq_infinityOrder]
  apply unweightedPrincipalDegree_eq_zero
  exact (map_ne_zero_iff _ (projectiveLineFunctionFieldEquiv k).injective).mpr f.ne_zero

end

end HodgeConjecture.ProjectiveLineCycles
