module

public import HodgeConjecture.Cycles.ProjectiveLineOrderDictionary
public import HodgeConjecture.Cycles.ProjectiveLineInversionOrder
public import HodgeConjecture.Cycles.ProjectiveLineFunctionField
public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-!
# The actual chart and infinity coefficients of a projective-line principal divisor

Actual open-immersion transport compares the existing signed divisor
orders with the polynomial factor-count dictionary. The genuine inversion
of the two chart function fields computes the order at the actual point
at infinity as minus rational-function degree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeConjecture.SchemeCycles.ProjectiveLineDegree

open AlgebraicGeometry CategoryTheory Polynomial UniqueFactorizationMonoid

noncomputable section

universe u

variable (k : Type u) [Field k] [DecidableEq k]

/-- The actual finite-chart prime divisor, with its original stalk and function-field maps. -/
def finiteDivisorPoint {p : Polynomial k} (hp : Irreducible p) : DivisorPoint (projectiveLine k) :=
  divisorPointEmbedding (projectiveLineXChart k)
    (irreducibleDivisorPoint (.of (Polynomial k)) (Polynomial.not_isField k) hp)

/-- Actual finite-chart orders are the normalized polynomial-factor orders. -/
theorem finiteDivisorPoint_order {p : Polynomial k} (hp : Irreducible p) (hpm : p.Monic)
    (f : (projectiveLine k).functionFieldˣ) :
    divisorOrder (projectiveLine k) (finiteDivisorPoint k hp) f =
      finiteOrder p (projectiveLineFunctionFieldEquiv k (f : (projectiveLine k).functionField)) := by
  rw [finiteDivisorPoint, ← divisorOrder_openImmersion]
  exact polynomialDivisorOrder_eq_finiteOrder k hp hpm _

/-- Infinity is the actual divisor point given by the origin of the second chart. -/
def infinityDivisorPoint : DivisorPoint (projectiveLine k) :=
  divisorPointEmbedding (projectiveLineYChart k)
    (irreducibleDivisorPoint (.of (Polynomial k)) (Polynomial.not_isField k) irreducible_X)

omit [DecidableEq k] in
@[simp]
theorem infinityDivisorPoint_val : (infinityDivisorPoint k).val = projectiveLineInfinity k := rfl

/-- Reading the actual infinity coefficient in the second chart gives order at its origin. -/
theorem infinityDivisorPoint_order_secondChart (f : (projectiveLine k).functionFieldˣ) :
    divisorOrder (projectiveLine k) (infinityDivisorPoint k) f =
      finiteOrder (Polynomial.X : Polynomial k)
        (affineLineFunctionFieldEquiv k
          (projectiveLineFunctionFieldEquivY k (f : (projectiveLine k).functionField))) := by
  rw [infinityDivisorPoint, ← divisorOrder_openImmersion]
  exact polynomialDivisorOrder_eq_finiteOrder k irreducible_X monic_X _

/-- The order at the actual infinity point is minus the integer degree in the first chart. -/
theorem infinityDivisorPoint_order (f : (projectiveLine k).functionFieldˣ) :
    divisorOrder (projectiveLine k) (infinityDivisorPoint k) f =
      -(projectiveLineFunctionFieldEquiv k (f : (projectiveLine k).functionField)).intDegree := by
  rw [infinityDivisorPoint_order_secondChart, ← projectiveLineChartInversion_apply]
  refine finiteOrder_X_inversion (projectiveLineChartInversion k).toRingHom ?_ ?_ _ ?_
  · intro a
    simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      projectiveLineChartInversion_C k a
  · simpa only [RatFunc.algebraMap_X, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] using
      projectiveLineChartInversion_X k
  · simpa only [map_zero] using
      (projectiveLineFunctionFieldEquiv k).injective.ne f.ne_zero

/-- Only actual monic irreducible polynomial points can contribute to the factor-count order. -/
theorem finiteOrder_ne_zero_imp_monic_irreducible {p : Polynomial k} {g : RatFunc k}
    (hp : finiteOrder p g ≠ 0) : p.Monic ∧ Irreducible p := by
  have hmem : p ∈ normalizedFactors g.num ∨ p ∈ normalizedFactors g.denom := by
    by_contra h
    simp only [not_or] at h
    exact hp (by simp [finiteOrder, Multiset.count_eq_zero_of_notMem h.1,
      Multiset.count_eq_zero_of_notMem h.2])
  have hin {a : Polynomial k} (hpa : p ∈ normalizedFactors a) : p.Monic ∧ Irreducible p := by
    have hi := irreducible_of_normalized_factor _ hpa
    exact ⟨(normalize_eq_self_iff_monic hi.ne_zero).mp (normalize_normalized_factor p hpa), hi⟩
  exact hmem.elim hin hin

/-- Over an algebraically closed field the actual finite closed-point weights are one. -/
theorem finiteOrder_mul_natDegree_eq [IsAlgClosed k] (p : Polynomial k) (g : RatFunc k) :
    finiteOrder p g * (p.natDegree : ℤ) = finiteOrder p g := by
  by_cases h : finiteOrder p g = 0
  · simp only [h, zero_mul]
  · have hp := (finiteOrder_ne_zero_imp_monic_irreducible k h).2
    have hd : p.natDegree = 1 :=
      natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible k hp)
    rw [hd, Nat.cast_one, mul_one]

/-- The unweighted finite-point arithmetic sum plus infinity vanishes over an algebraically closed field. -/
theorem unweightedPrincipalDegree_eq_zero [IsAlgClosed k] (g : RatFunc k) (hg : g ≠ 0) :
    (∑ᶠ p : Polynomial k, finiteOrder p g) + infinityOrder g = 0 := by
  have h := principalDegree_eq_zero g hg
  simpa only [finiteOrder_mul_natDegree_eq] using h

end

end HodgeConjecture.SchemeCycles.ProjectiveLineDegree
