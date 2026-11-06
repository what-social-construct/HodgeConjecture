module

public import HodgeConjecture.Geometry.ProjectiveLinePoints
public import HodgeConjecture.Cycles.ProjectiveLineOrderDictionary
public import HodgeConjecture.Cycles.DivisorFiniteness
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Logic.Equiv.Set

@[expose] public section

/-!
# Actual projective-line divisor points, including infinity

The original open-immersion maps identify the finite divisor points with
those in the first affine chart. The remaining divisor point is the actual
origin of the second chart. The resulting equivalence and finite-sum
splitting retain those literal point maps. Affine divisor points are also
identified with their original monic irreducible polynomial generators.
No replacement point or divisor-order model is introduced.
-/

set_option autoImplicit false

namespace HodgeConjecture.ProjectiveLineCycles

open AlgebraicGeometry CategoryTheory SchemeCycles
open SchemeCycles.ProjectiveLineDegree

noncomputable section

universe u v

variable (k : Type u) [Field k]

/-- The actual infinity point, with its one-dimensional stalk proved in the second chart. -/
def infinityDivisorPoint : DivisorPoint (projectiveLine k) := by
  classical
  exact divisorPointEmbedding (projectiveLineYChart k)
    (irreducibleDivisorPoint (.of (Polynomial k)) (Polynomial.not_isField k)
      Polynomial.irreducible_X)

@[simp]
theorem infinityDivisorPoint_val : (infinityDivisorPoint k).val = projectiveLineInfinity k := rfl

/-- The original embedding of finite-chart divisor points. -/
def chartDivisorPointEmbedding :
    DivisorPoint (Spec (.of (Polynomial k))) ↪ DivisorPoint (projectiveLine k) :=
  divisorPointEmbedding (projectiveLineXChart k)

@[simp]
theorem chartDivisorPointEmbedding_val (x : DivisorPoint (Spec (.of (Polynomial k)))) :
    (chartDivisorPointEmbedding k x).val = (projectiveLineXChart k).base x.val := rfl

/-- The chart divisor points are exactly all actual divisor points other than infinity. -/
theorem mem_range_chartDivisorPointEmbedding_iff (x : DivisorPoint (projectiveLine k)) :
    x ∈ Set.range (chartDivisorPointEmbedding k) ↔ x ≠ infinityDivisorPoint k := by
  rw [chartDivisorPointEmbedding, mem_range_divisorPointEmbedding_iff,
    mem_range_projectiveLineXChart_iff_ne_infinity]
  constructor
  · intro hx heq
    exact hx (congrArg Subtype.val heq)
  · intro hx heq
    exact hx (Subtype.ext heq)

@[simp]
theorem chartDivisorPointEmbedding_ne_infinity
    (x : DivisorPoint (Spec (.of (Polynomial k)))) :
    chartDivisorPointEmbedding k x ≠ infinityDivisorPoint k :=
  (mem_range_chartDivisorPointEmbedding_iff k _).mp ⟨x, rfl⟩

/-- The finite chart and the actual infinity divisor point form an exhaustive disjoint sum. -/
def divisorPointEquiv :
    (DivisorPoint (Spec (.of (Polynomial k))) ⊕ Unit) ≃ DivisorPoint (projectiveLine k) := by
  classical
  refine Equiv.ofBijective
    (Sum.elim (chartDivisorPointEmbedding k) (fun _ : Unit ↦ infinityDivisorPoint k)) ⟨?_, ?_⟩
  · intro a b h
    rcases a with x | x <;> rcases b with y | y
    · exact congrArg Sum.inl ((chartDivisorPointEmbedding k).injective h)
    · exact ((chartDivisorPointEmbedding_ne_infinity k x) h).elim
    · exact ((chartDivisorPointEmbedding_ne_infinity k y) h.symm).elim
    · exact congrArg Sum.inr (Subsingleton.elim x y)
  · intro x
    by_cases hx : x = infinityDivisorPoint k
    · exact ⟨Sum.inr (), hx.symm⟩
    · obtain ⟨y, hy⟩ := (mem_range_chartDivisorPointEmbedding_iff k x).mpr hx
      exact ⟨Sum.inl y, hy⟩

@[simp]
theorem divisorPointEquiv_inl (x : DivisorPoint (Spec (.of (Polynomial k)))) :
    divisorPointEquiv k (Sum.inl x) = chartDivisorPointEmbedding k x := rfl

@[simp]
theorem divisorPointEquiv_inr (x : Unit) :
    divisorPointEquiv k (Sum.inr x) = infinityDivisorPoint k := rfl

/-- Finite-support sums split along the genuine finite chart and the one point at infinity. -/
theorem finsum_divisorPoints {M : Type v} [AddCommMonoid M]
    (f : DivisorPoint (projectiveLine k) → M) (hf : Function.HasFiniteSupport f) :
    (∑ᶠ x, f x) =
      (∑ᶠ x : DivisorPoint (Spec (.of (Polynomial k))), f (chartDivisorPointEmbedding k x)) +
        f (infinityDivisorPoint k) := by
  classical
  let s : Set (DivisorPoint (projectiveLine k)) := Set.range (chartDivisorPointEmbedding k)
  have hinf : infinityDivisorPoint k ∉ s := by
    rw [mem_range_chartDivisorPointEmbedding_iff]
    exact not_not_intro rfl
  have hcover : s ∪ {infinityDivisorPoint k} = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hx : x = infinityDivisorPoint k
    · exact Or.inr hx
    · exact Or.inl ((mem_range_chartDivisorPointEmbedding_iff k x).mpr hx)
  have hs : (s ∩ Function.support f).Finite := hf.subset Set.inter_subset_right
  have ht : ({infinityDivisorPoint k} ∩ Function.support f).Finite :=
    (Set.finite_singleton _).inter_of_left _
  have hsplit := finsum_mem_union' (f := f)
    (Set.disjoint_singleton_right.mpr hinf) hs ht
  rw [hcover, finsum_mem_univ, finsum_mem_range (chartDivisorPointEmbedding k).injective,
    finsum_mem_singleton] at hsplit
  exact hsplit

/-- The actual existing divisor-order sum has the corresponding chart/infinity splitting. -/
theorem finsum_divisorOrder (f : (projectiveLine k).functionFieldˣ) :
    (∑ᶠ x : DivisorPoint (projectiveLine k), divisorOrder (projectiveLine k) x f) =
      (∑ᶠ x : DivisorPoint (Spec (.of (Polynomial k))),
        divisorOrder (projectiveLine k) (chartDivisorPointEmbedding k x) f) +
      divisorOrder (projectiveLine k) (infinityDivisorPoint k) f :=
  finsum_divisorPoints k _ (finite_divisorOrder_support (projectiveLine k) f)

/-- An actual one-dimensional affine-line stalk cannot lie over the zero prime. -/
theorem polynomialDivisorPoint_asIdeal_ne_bot (x : DivisorPoint (Spec (.of (Polynomial k)))) :
    x.val.asIdeal ≠ ⊥ := by
  classical
  let : Algebra (Polynomial k) ((Spec (.of (Polynomial k))).presheaf.stalk x.val) :=
    specStalkAlgebra (.of (Polynomial k)) x.val
  have : IsLocalization.AtPrime ((Spec (.of (Polynomial k))).presheaf.stalk x.val)
      x.val.asIdeal := specStalkIsLocalization (.of (Polynomial k)) x.val
  have hdim := x.property
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.val.asIdeal] at hdim
  intro hx
  rw [hx, Ideal.height_bot] at hdim
  norm_num at hdim

/-- Every actual nonzero prime of the affine line is a divisor point, by its original stalk. -/
def polynomialPrimeDivisorPoint (x : Spec (.of (Polynomial k))) (hx : x.asIdeal ≠ ⊥) :
    DivisorPoint (Spec (.of (Polynomial k))) := by
  classical
  let : Algebra (Polynomial k) ((Spec (.of (Polynomial k))).presheaf.stalk x) :=
    specStalkAlgebra (.of (Polynomial k)) x
  have : IsLocalization.AtPrime ((Spec (.of (Polynomial k))).presheaf.stalk x)
      x.asIdeal := specStalkIsLocalization (.of (Polynomial k)) x
  refine ⟨x, ?_⟩
  have : x.asIdeal.IsMaximal := IsPrime.to_maximal_ideal hx
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal,
    IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField k)]
  rfl

/-- Divisor points are the actual nonzero polynomial-spectrum primes. -/
def polynomialDivisorPointNonzeroPrimeEquiv :
    DivisorPoint (Spec (.of (Polynomial k))) ≃
      {x : Spec (.of (Polynomial k)) // x.asIdeal ≠ ⊥} where
  toFun x := ⟨x.val, polynomialDivisorPoint_asIdeal_ne_bot k x⟩
  invFun x := polynomialPrimeDivisorPoint k x.val x.property
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The original polynomial generators, with monicity removing the unit ambiguity. -/
abbrev MonicIrreducibles := {p : Polynomial k // p.Monic ∧ Irreducible p}

/-- The actual affine divisor-point dictionary with monic irreducible polynomial generators. -/
def polynomialDivisorPointEquiv :
    DivisorPoint (Spec (.of (Polynomial k))) ≃ MonicIrreducibles k :=
  (polynomialDivisorPointNonzeroPrimeEquiv k).trans
    (Set.BijOn.equiv (affineLineGenerator (k := k)) (bijOn_affineLineGenerator (k := k)))

@[simp]
theorem polynomialDivisorPointEquiv_val (x : DivisorPoint (Spec (.of (Polynomial k)))) :
    (polynomialDivisorPointEquiv k x).val = affineLineGenerator x.val := rfl

/-- The inverse dictionary retains the literal irreducible polynomial point and actual stalk. -/
@[simp]
theorem polynomialDivisorPointEquiv_symm (p : MonicIrreducibles k) :
    (polynomialDivisorPointEquiv k).symm p =
      irreducibleDivisorPoint (.of (Polynomial k)) (Polynomial.not_isField k) p.property.2 := by
  classical
  apply Subtype.ext
  apply PrimeSpectrum.ext
  change (((polynomialDivisorPointEquiv k).symm p).val).asIdeal =
    (irreduciblePoint (.of (Polynomial k)) p.property.2).asIdeal
  rw [irreduciblePoint_asIdeal]
  have hgen := congrArg Subtype.val ((polynomialDivisorPointEquiv k).apply_symm_apply p)
  change affineLineGenerator ((polynomialDivisorPointEquiv k).symm p).val = p.val at hgen
  simpa only [hgen] using
    (affineLineGenerator_spec ((polynomialDivisorPointEquiv k).symm p).val
      (polynomialDivisorPoint_asIdeal_ne_bot k _)).2.2

/-- Reindexing uses the actual polynomial generators, without any finite-degree premise. -/
theorem finsum_polynomialDivisorPoints {M : Type v} [AddCommMonoid M]
    (f : MonicIrreducibles k → M) :
    (∑ᶠ x : DivisorPoint (Spec (.of (Polynomial k))), f (polynomialDivisorPointEquiv k x)) =
      ∑ᶠ p : MonicIrreducibles k, f p :=
  finsum_comp_equiv (polynomialDivisorPointEquiv k)

open scoped Classical in
/-- The monic-irreducible subtype sum is the zero extension to all polynomials. -/
theorem finsum_monicIrreducibles {M : Type v} [AddCommMonoid M] (f : Polynomial k → M) :
    (∑ᶠ p : MonicIrreducibles k, f p.val) =
      ∑ᶠ p : Polynomial k, if p.Monic ∧ Irreducible p then f p else 0 := by
  classical
  rw [finsum_subtype_eq_finsum_cond]
  simp only [finsum_eq_if]

/-- A function already zero outside monic irreducibles needs no zero-extension wrapper. -/
theorem finsum_monicIrreducibles_of_zero_outside {M : Type v} [AddCommMonoid M]
    (f : Polynomial k → M) (hf : ∀ p, ¬(p.Monic ∧ Irreducible p) → f p = 0) :
    (∑ᶠ p : MonicIrreducibles k, f p.val) = ∑ᶠ p : Polynomial k, f p := by
  classical
  rw [finsum_monicIrreducibles]
  apply finsum_congr
  intro p
  split_ifs with hp
  · rfl
  · exact (hf p hp).symm

end

end HodgeConjecture.ProjectiveLineCycles
