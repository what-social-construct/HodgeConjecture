module

public import HodgeConjecture.Cycles.LocalOrderTransport
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

@[expose] public section

/-!
# Polynomial orders and the degree of a principal divisor on the line

The normalized irreducible factors of a rational function give its finite
orders. Their degree-weighted sum is numerator degree minus denominator
degree; the order at infinity cancels it. The localization computation
below identifies the factor counts with the existing length-based local
order, rather than postulating an equality with geometric coefficients.

Selected proof adaptations from AxiomMath/Stacks, revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/AlgebraicGeometry/Chow/ProperPushforwardDivisor.lean`
and `ProjectiveLineDivisorDegree/SpecOrder.lean`, Apache-2.0.
See `third_party/axiom-stacks/LICENSE`.

This file constructs the arithmetic and local-ring comparisons. Descent
from all actual projective-line principal relations also needs the global
chart/infinity point and function-field dictionary.
-/

set_option autoImplicit false

namespace HodgeConjecture.SchemeCycles.ProjectiveLineDegree

open Polynomial UniqueFactorizationMonoid

noncomputable section

universe u

variable {k : Type u} [Field k] [DecidableEq k]

/-- Multiplicities of the normalized irreducible factors recover the actual polynomial degree. -/
theorem sum_map_natDegree_normalizedFactors (q : Polynomial k) (hq : q ≠ 0) :
    ((normalizedFactors q).map natDegree).sum = q.natDegree := by
  rw [← natDegree_multiset_prod _ fun h ↦ (irreducible_of_normalized_factor _ h).ne_zero rfl]
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (prod_normalizedFactors hq))

theorem sum_count_normalizedFactors_mul_natDegree (q : Polynomial k) (hq : q ≠ 0)
    (s : Finset (Polynomial k)) (hs : (normalizedFactors q).toFinset ⊆ s) :
    ∑ p ∈ s, ((normalizedFactors q).count p : ℤ) * p.natDegree = q.natDegree := by
  have key : ∑ p ∈ (normalizedFactors q).toFinset,
      ((normalizedFactors q).count p : ℤ) * p.natDegree = q.natDegree := by
    rw [← sum_map_natDegree_normalizedFactors q hq, Finset.sum_multiset_map_count]
    push_cast
    simp [mul_comm]
  rw [← key, Finset.sum_subset hs]
  intro p _ hp
  have hp' : p ∉ normalizedFactors q := fun hm ↦ hp (Multiset.mem_toFinset.mpr hm)
  rw [Multiset.count_eq_zero_of_notMem hp']
  simp

/-- The finite-place order defined by the original normalized numerator and denominator. -/
def finiteOrder (p : Polynomial k) (g : RatFunc k) : ℤ :=
  ((normalizedFactors g.num).count p : ℤ) - ((normalizedFactors g.denom).count p : ℤ)

/-- The rational-function order at infinity is minus the actual integer degree. -/
def infinityOrder (g : RatFunc k) : ℤ := -g.intDegree

private theorem count_add_count_eq_of_mul_eq (p : Polynomial k) {x y z w : Polynomial k}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) (h : x * y = z * w) :
    (normalizedFactors x).count p + (normalizedFactors y).count p =
      (normalizedFactors z).count p + (normalizedFactors w).count p := by
  simpa [normalizedFactors_mul hx hy, normalizedFactors_mul hz hw] using
    congrArg (fun r ↦ (normalizedFactors r).count p) h

/-- The count difference is independent of the chosen numerator/denominator presentation. -/
theorem finiteOrder_div (p : Polynomial k) {a b : Polynomial k} (ha : a ≠ 0) (hb : b ≠ 0) :
    finiteOrder p (algebraMap (Polynomial k) (RatFunc k) a /
        algebraMap (Polynomial k) (RatFunc k) b) =
      ((normalizedFactors a).count p : ℤ) - ((normalizedFactors b).count p : ℤ) := by
  have hinj := RatFunc.algebraMap_injective k
  set g : RatFunc k := algebraMap (Polynomial k) (RatFunc k) a /
    algebraMap (Polynomial k) (RatFunc k) b with hgdef
  have hg : g ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ hinj).mpr ha) ((map_ne_zero_iff _ hinj).mpr hb)
  have hcount := count_add_count_eq_of_mul_eq p (RatFunc.num_ne_zero hg) hb ha
    (RatFunc.denom_ne_zero g) ((RatFunc.num_mul_eq_mul_denom_iff hb).mpr hgdef)
  simp only [finiteOrder]
  omega

@[simp]
theorem finiteOrder_one (p : Polynomial k) : finiteOrder p (1 : RatFunc k) = 0 := by
  simp [finiteOrder]

theorem finiteOrder_mul (p : Polynomial k) {g h : RatFunc k} (hg : g ≠ 0) (hh : h ≠ 0) :
    finiteOrder p (g * h) = finiteOrder p g + finiteOrder p h := by
  have hgn := RatFunc.num_ne_zero hg
  have hhn := RatFunc.num_ne_zero hh
  have hgd := RatFunc.denom_ne_zero g
  have hhd := RatFunc.denom_ne_zero h
  have hcount := count_add_count_eq_of_mul_eq p (RatFunc.num_ne_zero (mul_ne_zero hg hh))
    (mul_ne_zero hgd hhd) (mul_ne_zero hgn hhn) (RatFunc.denom_ne_zero (g * h))
    (RatFunc.num_denom_mul g h)
  simp only [normalizedFactors_mul hgd hhd, normalizedFactors_mul hgn hhn,
    Multiset.count_add] at hcount
  simp only [finiteOrder]
  omega

theorem finiteOrder_eq_multiplicity_sub_multiplicity {p : Polynomial k}
    (hp : Irreducible p) (hpm : p.Monic) {g : RatFunc k} (hg : g ≠ 0) :
    finiteOrder p g = (multiplicity p g.num : ℤ) - (multiplicity p g.denom : ℤ) := by
  rw [finiteOrder, multiplicity_eq_count_normalizedFactors hp (RatFunc.num_ne_zero hg),
    multiplicity_eq_count_normalizedFactors hp (RatFunc.denom_ne_zero g), hpm.normalize_eq_self]

theorem finiteOrder_eq_zero_of_notMem {g : RatFunc k} {p : Polynomial k}
    (hnum : p ∉ (normalizedFactors g.num).toFinset)
    (hden : p ∉ (normalizedFactors g.denom).toFinset) : finiteOrder p g = 0 := by
  simp only [Multiset.mem_toFinset] at hnum hden
  simp [finiteOrder, Multiset.count_eq_zero_of_notMem hnum, Multiset.count_eq_zero_of_notMem hden]

/-- The weighted order sum is genuinely finitely supported. -/
theorem weightedFiniteOrder_support_subset (g : RatFunc k) :
    Function.support (fun p : Polynomial k ↦ finiteOrder p g * (p.natDegree : ℤ)) ⊆
      ↑((normalizedFactors g.num).toFinset ∪ (normalizedFactors g.denom).toFinset) := by
  intro p hp
  by_contra hmem
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hmem
  exact hp (by simp [finiteOrder_eq_zero_of_notMem hmem.1 hmem.2])

theorem weightedFiniteOrder_support_finite (g : RatFunc k) :
    (Function.support fun p : Polynomial k ↦ finiteOrder p g * (p.natDegree : ℤ)).Finite :=
  (Finset.finite_toSet _).subset (weightedFiniteOrder_support_subset g)

theorem sum_finiteOrder_mul_natDegree (g : RatFunc k) (hg : g ≠ 0)
    (s : Finset (Polynomial k)) (hnum : (normalizedFactors g.num).toFinset ⊆ s)
    (hden : (normalizedFactors g.denom).toFinset ⊆ s) :
    ∑ p ∈ s, finiteOrder p g * (p.natDegree : ℤ) = g.intDegree := by
  rw [RatFunc.intDegree,
    ← sum_count_normalizedFactors_mul_natDegree g.num (RatFunc.num_ne_zero hg) s hnum,
    ← sum_count_normalizedFactors_mul_natDegree g.denom (RatFunc.denom_ne_zero g) s hden,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ by simp [finiteOrder, sub_mul]

/-- The arithmetic degree of the finite divisor together with the point at infinity is zero. -/
theorem principalDegree_eq_zero (g : RatFunc k) (hg : g ≠ 0) :
    (∑ᶠ p : Polynomial k, finiteOrder p g * (p.natDegree : ℤ)) + infinityOrder g = 0 := by
  rw [finsum_eq_sum_of_support_subset _ (weightedFiniteOrder_support_subset g)]
  rw [sum_finiteOrder_mul_natDegree g hg _ Finset.subset_union_left Finset.subset_union_right,
    infinityOrder, add_neg_cancel]

section Localization

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (P : Ideal R) [P.IsPrime]
variable (L : Type u) [CommRing L] [IsDomain L] [Algebra R L] [IsLocalization.AtPrime L P]

/-- The original length of a principal quotient in a PID localization detects the prime exponent. -/
theorem ord_localization_eq_of_eq_pow_mul {ϖ : R} (hϖ : Irreducible ϖ)
    (hP : P = Ideal.span {ϖ}) {a b : R} (n : ℕ) (hab : a = ϖ ^ n * b) (hb : ¬ϖ ∣ b) :
    Ring.ord L (algebraMap R L a) = n := by
  have hPne : P ≠ ⊥ := by
    rw [hP]
    exact fun h ↦ hϖ.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have : IsDiscreteValuationRing L :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hPne L
  have hmax : IsLocalRing.maximalIdeal L = Ideal.span {algebraMap R L ϖ} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P L, hP, Ideal.map_span, Set.image_singleton]
  have hirr : Irreducible (algebraMap R L ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  have hbnot : b ∉ P := by
    rw [hP]
    exact fun hmem ↦ hb (Ideal.mem_span_singleton.mp hmem)
  have hu : IsUnit (algebraMap R L b) := IsLocalization.map_units L (⟨b, hbnot⟩ : P.primeCompl)
  rw [hab, map_mul, map_pow, Ring.ord_mul_of_isUnit_right hu,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hirr.ne_zero), Ring.ord_of_irreducible hirr,
    nsmul_one]

end Localization

/-- Polynomial-factor counts equal the actual quotient-length order in the corresponding local ring. -/
theorem ord_polynomialLocalization_eq_count {p : Polynomial k} (hp : Irreducible p)
    (hpm : p.Monic) (P : Ideal (Polynomial k)) [P.IsPrime] (hP : P = Ideal.span {p})
    (L : Type u) [CommRing L] [IsDomain L] [Algebra (Polynomial k) L]
    [IsLocalization.AtPrime L P] (a : Polynomial k) (ha : a ≠ 0) :
    Ring.ord L (algebraMap (Polynomial k) L a) = (normalizedFactors a).count p := by
  have hfin : FiniteMultiplicity p a := FiniteMultiplicity.of_not_isUnit hp.not_isUnit ha
  obtain ⟨b, hab, hb⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hcount : multiplicity p a = (normalizedFactors a).count p := by
    rw [multiplicity_eq_count_normalizedFactors hp ha, hpm.normalize_eq_self]
  rw [← hcount]
  exact ord_localization_eq_of_eq_pow_mul P L hp hP (multiplicity p a) hab hb

/-- The same factor count computes the existing signed fraction-field local order. -/
theorem localOrder_polynomialLocalization_eq_count {p : Polynomial k} (hp : Irreducible p)
    (hpm : p.Monic) (P : Ideal (Polynomial k)) [P.IsPrime] (hP : P = Ideal.span {p})
    (L : Type u) [CommRing L] [IsDomain L] [IsNoetherianRing L] [Ring.KrullDimLE 1 L]
    [Algebra (Polynomial k) L] [IsLocalization.AtPrime L P]
    (K : Type u) [Field K] [Algebra (Polynomial k) K] [IsFractionRing (Polynomial k) K]
    [Algebra L K] [IsFractionRing L K] [IsScalarTower (Polynomial k) L K]
    (a : Polynomial k) (ha : a ≠ 0) :
    localOrder L (Units.mk0 (algebraMap (Polynomial k) K a)
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) K)).mpr ha)) =
        ((normalizedFactors a).count p : ℤ) := by
  have haL : algebraMap (Polynomial k) L a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective L P.primeCompl_le_nonZeroDivisors)).mpr ha
  have h := localOrder_algebraMap (K := K) L (algebraMap (Polynomial k) L a) haL
  have hord := ord_polynomialLocalization_eq_count hp hpm P hP L a ha
  change Ring.ord L (algebraMap (Polynomial k) L a) = _ at hord
  change _ = ((Ring.ord L (algebraMap (Polynomial k) L a)).toNat : ℤ) at h
  rw [hord] at h
  simpa only [← IsScalarTower.algebraMap_apply, ENat.toNat_natCast] using h

/-- The actual local-order dictionary for every nonzero rational function at a polynomial prime. -/
theorem localOrder_polynomialLocalization_eq_finiteOrder {p : Polynomial k}
    (hp : Irreducible p) (hpm : p.Monic) (P : Ideal (Polynomial k)) [P.IsPrime]
    (hP : P = Ideal.span {p})
    (L : Type u) [CommRing L] [IsDomain L] [IsNoetherianRing L] [Ring.KrullDimLE 1 L]
    [Algebra (Polynomial k) L] [IsLocalization.AtPrime L P]
    (K : Type u) [Field K] [Algebra (Polynomial k) K] [IsFractionRing (Polynomial k) K]
    [Algebra L K] [IsFractionRing L K] [IsScalarTower (Polynomial k) L K] (f : Kˣ) :
    localOrder L f = finiteOrder p
      (IsLocalization.algEquiv (nonZeroDivisors (Polynomial k)) K (RatFunc k) (f : K)) := by
  let e := IsLocalization.algEquiv (nonZeroDivisors (Polynomial k)) K (RatFunc k)
  let g : RatFunc k := e (f : K)
  have hg : g ≠ 0 := by simpa only [g, map_zero] using e.injective.ne f.ne_zero
  let a : Kˣ := Units.mk0 (algebraMap (Polynomial k) K g.num)
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) K)).mpr (RatFunc.num_ne_zero hg))
  let b : Kˣ := Units.mk0 (algebraMap (Polynomial k) K g.denom)
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) K)).mpr (RatFunc.denom_ne_zero g))
  have hf : f = a / b := by
    apply Units.ext
    apply e.injective
    simp only [Units.val_div_eq_div_val, a, b, Units.val_mk0, map_div₀, e.commutes]
    exact (RatFunc.num_div_denom g).symm
  calc
    _ = localOrder L (a / b) := congrArg (localOrder L) hf
    _ = ((normalizedFactors g.num).count p : ℤ) - ((normalizedFactors g.denom).count p : ℤ) := by
      rw [localOrder_div,
        localOrder_polynomialLocalization_eq_count hp hpm P hP L K g.num (RatFunc.num_ne_zero hg),
        localOrder_polynomialLocalization_eq_count hp hpm P hP L K g.denom (RatFunc.denom_ne_zero g)]
    _ = _ := rfl

end

end HodgeConjecture.SchemeCycles.ProjectiveLineDegree
