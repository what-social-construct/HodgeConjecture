module

public import HodgeConjecture.Geometry.ProjectiveLineProperties
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public section

/-!
# Actual point dictionary for the two-chart projective line

The actual overlap is D(X) on each chart. Over a field its complement is
just the affine origin; the glued scheme is the first affine chart together
with infinity. Nongeneric finite-chart points correspond bijectively to
monic irreducible polynomials through their actual prime ideals.

Selected proof adaptation from AxiomMath/Stacks, pinned revision
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`,
`StacksFrontier/AlgebraicGeometry/Scheme/Glueing/ProjectiveLinePoints.lean`
and its point-level pullback lemma in `ProjectiveLineSeparated.lean`.
Apache-2.0; see `third_party/axiom-stacks/LICENSE`.
Infinitude and unrelated automorphism results are omitted.
-/

set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The overlap of the two charts -/

section CommRing

variable (k : Type u) [CommRing k]

/-- The overlap `U₁₂` of the two charts of the projective line, seen in the first chart, is
`D(x)`, the locus where the coordinate is invertible. -/
theorem mem_range_projectiveLinePuncturedChart_iff (y : Spec (.of (Polynomial k))) :
    y ∈ Set.range (projectiveLinePuncturedChart k).base ↔
      (Polynomial.X : Polynomial k) ∉ y.asIdeal := by
  have hr := PrimeSpectrum.localization_away_comap_range (R := Polynomial k)
    (LaurentPolynomial k) (Polynomial.X : Polynomial k)
  have hid : y ∈ Set.range (projectiveLinePuncturedChart k).base ↔
      y ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (Polynomial k) (LaurentPolynomial k))) := Iff.rfl
  rw [hid, hr]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- The overlap `U₂₁` of the two charts of the projective line, seen in the second chart, is
`D(y)`, the locus where the coordinate of that chart is invertible. -/
theorem mem_range_projectiveLineOverlapYInclusion_iff (y : Spec (.of (Polynomial k))) :
    y ∈ Set.range (projectiveLineOverlapYInclusion k).base ↔
      (Polynomial.X : Polynomial k) ∉ y.asIdeal := by
  rw [← mem_range_projectiveLinePuncturedChart_iff k y,
    show projectiveLineOverlapYInclusion k =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k from rfl]
  rw [Scheme.Hom.comp_base, TopCat.coe_comp,
    ((projectiveLineInversionIso k).hom.surjective).range_comp]

/-- Two chart points have the same image exactly when they come from the actual Laurent overlap. -/
theorem projectiveLineXChart_base_eq_projectiveLineYChart_base_iff
    (p q : Spec (.of (Polynomial k))) :
    (projectiveLineXChart k).base p = (projectiveLineYChart k).base q ↔
      ∃ w : Spec (.of (LaurentPolynomial k)),
        (projectiveLinePuncturedChart k).base w = p ∧
          (projectiveLineOverlapYInclusion k).base w = q := by
  have hpb := projectiveLineOverlap_isPullback k
  have := hpb.hasPullback
  refine ⟨fun h ↦ ?_, fun ⟨w, hwp, hwq⟩ ↦ ?_⟩
  · obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback p q h
    refine ⟨hpb.isoPullback.inv.base z, ?_, ?_⟩
    · rw [← hz₁, ← hpb.isoPullback_inv_fst]
      rfl
    · rw [← hz₂, ← hpb.isoPullback_inv_snd]
      rfl
  · rw [← hwp, ← hwq]
    exact congrArg (fun φ : Spec (.of (LaurentPolynomial k)) ⟶ projectiveLine k ↦ φ.base w) hpb.w

end CommRing

/-! ### The points of a chart -/

variable {k : Type u} [Field k]

/-- An irreducible polynomial over a field is associated to a monic irreducible polynomial. -/
private theorem exists_monic_irreducible_associated {q : Polynomial k} (hq : Irreducible q) :
    ∃ p : Polynomial k, p.Monic ∧ Irreducible p ∧ Associated p q := by
  classical
  exact ⟨normalize q, Polynomial.monic_normalize hq.ne_zero,
    (normalize_associated q).symm.irreducible hq, normalize_associated q⟩

/-- The complement of the overlap in a chart is the single point `0` of that chart: the only
point of the affine line over a field at which the coordinate vanishes is the origin. -/
theorem eq_affineLineOrigin_of_X_mem (y : Spec (.of (Polynomial k)))
    (hy : (Polynomial.X : Polynomial k) ∈ y.asIdeal) : y = affineLineOrigin k := by
  refine PrimeSpectrum.ext ?_
  have hmax : (Ideal.span {(Polynomial.X : Polynomial k)}).IsMaximal := by
    simpa [← Ideal.submodule_span_eq] using
      PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X
  have hle : Ideal.span {(Polynomial.X : Polynomial k)} ≤ y.asIdeal := by
    rw [Ideal.span_le]
    simpa using hy
  exact (hmax.eq_of_le y.2.ne_top hle).symm

/-- Every point of the affine line over a field other than the generic point is cut out by a
monic irreducible polynomial. -/
theorem exists_monic_irreducible_asIdeal_eq_span (y : Spec (.of (Polynomial k)))
    (hy : y.asIdeal ≠ ⊥) :
    ∃ p : Polynomial k, p.Monic ∧ Irreducible p ∧ y.asIdeal = Ideal.span {p} := by
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal y.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hq
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at hq
    exact hy hq
  obtain ⟨p, hpm, hpi, hpq⟩ := exists_monic_irreducible_associated
    ((Ideal.span_singleton_prime hq0).mp (hq ▸ y.2)).irreducible
  exact ⟨p, hpm, hpi, hq ▸ (Ideal.span_singleton_eq_span_singleton.2 hpq.symm)⟩

open scoped Classical in
/-- The monic irreducible polynomial cutting out a point of the affine line over a field, and
zero at the generic point. -/
noncomputable def affineLineGenerator (y : Spec (.of (Polynomial k))) : Polynomial k :=
  if h : y.asIdeal = ⊥ then 0 else (exists_monic_irreducible_asIdeal_eq_span y h).choose

/-- Away from the generic point, `AlgebraicGeometry.affineLineGenerator` is a monic irreducible
generator of the prime ideal of the point. -/
theorem affineLineGenerator_spec (y : Spec (.of (Polynomial k))) (hy : y.asIdeal ≠ ⊥) :
    (affineLineGenerator y).Monic ∧ Irreducible (affineLineGenerator y) ∧
      y.asIdeal = Ideal.span {affineLineGenerator y} := by
  classical
  rw [affineLineGenerator, dite_eq_right hy]
  exact (exists_monic_irreducible_asIdeal_eq_span y hy).choose_spec

/-- `AlgebraicGeometry.affineLineGenerator` is a bijection from the points of the affine line over
a field other than the generic point onto the monic irreducible polynomials. -/
theorem bijOn_affineLineGenerator :
    Set.BijOn (affineLineGenerator (k := k)) {y | y.asIdeal ≠ ⊥}
      {p : Polynomial k | p.Monic ∧ Irreducible p} := by
  refine ⟨fun y hy ↦ ⟨(affineLineGenerator_spec y hy).1, (affineLineGenerator_spec y hy).2.1⟩,
    fun y hy z hz hyz ↦ ?_, fun p hp ↦ ?_⟩
  · refine PrimeSpectrum.ext ?_
    rw [(affineLineGenerator_spec y hy).2.2, (affineLineGenerator_spec z hz).2.2, hyz]
  · obtain ⟨hpm, hpi⟩ := hp
    refine ⟨⟨Ideal.span {p}, (Ideal.span_singleton_prime hpi.ne_zero).2 hpi.prime⟩, ?_, ?_⟩
    · exact fun h ↦ hpi.ne_zero (Ideal.span_singleton_eq_bot.1 h)
    · have hne : (⟨Ideal.span {p}, (Ideal.span_singleton_prime hpi.ne_zero).2 hpi.prime⟩ :
          Spec (.of (Polynomial k))).asIdeal ≠ ⊥ :=
        fun h ↦ hpi.ne_zero (Ideal.span_singleton_eq_bot.1 h)
      obtain ⟨hgm, -, hgspan⟩ := affineLineGenerator_spec _ hne
      refine Polynomial.eq_of_monic_of_associated hgm hpm (associated_of_dvd_dvd ?_ ?_)
      · exact Ideal.span_singleton_le_span_singleton.1 hgspan.le
      · exact Ideal.span_singleton_le_span_singleton.1 hgspan.ge

/-! ### The points of the projective line -/

/-- Every point of the projective line lies in the first chart or is the point at infinity. -/
theorem mem_range_projectiveLineXChart_or_eq_infinity (x : projectiveLine k) :
    x ∈ Set.range (projectiveLineXChart k).base ∨ x = projectiveLineInfinity k := by
  obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData k).ι_jointly_surjective x
  obtain ⟨i⟩ := i
  cases i
  · exact Or.inl ⟨y, rfl⟩
  · by_cases hy : (Polynomial.X : Polynomial k) ∈ y.asIdeal
    · right
      rw [eq_affineLineOrigin_of_X_mem y hy]
      rfl
    · obtain ⟨w, hw⟩ := (mem_range_projectiveLineOverlapYInclusion_iff k y).2 hy
      refine Or.inl ⟨(projectiveLinePuncturedChart k).base w, ?_⟩
      calc (projectiveLineXChart k).base ((projectiveLinePuncturedChart k).base w)
          = (projectiveLinePuncturedChart k ≫ projectiveLineXChart k).base w := rfl
        _ = (projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k).base w := by
          rw [projectiveLineOverlap_compat]
          simp only [projectiveLineOverlapYInclusion, Category.assoc]
        _ = (projectiveLineYChart k).base y := by rw [← hw]; rfl

/-- The first chart of the projective line sends the generic point of `Spec k[X]` to the generic
point of the projective line. -/
theorem projectiveLineXChart_genericPoint_eq :
    (projectiveLineXChart k).base (genericPoint (Spec (.of (Polynomial k)))) =
      genericPoint (projectiveLine k) :=
  genericPoint_eq_of_isOpenImmersion (projectiveLineXChart k)

/-- A point of the affine line over a field whose prime ideal is zero is its generic point. -/
theorem eq_genericPoint_of_asIdeal_eq_bot (y : Spec (.of (Polynomial k)))
    (hy : y.asIdeal = ⊥) : y = genericPoint (Spec (.of (Polynomial k))) := by
  rw [genericPoint_eq_bot_of_affine]
  exact PrimeSpectrum.ext (by simpa using hy)

/-- The base map of the first chart of the projective line is injective. -/
theorem projectiveLineXChart_base_injective :
    Function.Injective (projectiveLineXChart k).base :=
  (projectiveLineXChart k).isOpenEmbedding.injective

/-- The points `0` and `∞` of the projective line are distinct. -/
theorem projectiveLineZero_ne_projectiveLineInfinity (k : Type u) [Field k] :
    projectiveLineZero k ≠ projectiveLineInfinity k := by
  intro h
  obtain ⟨w, hw, -⟩ := (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k
    (affineLineOrigin k) (affineLineOrigin k)).mp h
  exact (mem_range_projectiveLinePuncturedChart_iff k _).mp ⟨w, hw⟩ (Ideal.subset_span rfl)


/-- Infinity lies outside the first actual affine chart. -/
theorem projectiveLineInfinity_notMem_range_XChart (k : Type u) [Field k] :
    projectiveLineInfinity k ∉ Set.range (projectiveLineXChart k).base := by
  rintro ⟨p, hp⟩
  have hp' : (projectiveLineXChart k).base p =
      (projectiveLineYChart k).base (affineLineOrigin k) := hp
  obtain ⟨w, _, hw⟩ :=
    (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k p (affineLineOrigin k)).mp hp'
  exact (mem_range_projectiveLineOverlapYInclusion_iff k _).mp ⟨w, hw⟩
    (Ideal.subset_span rfl)

/-- The actual first chart is precisely the complement of infinity. -/
theorem mem_range_projectiveLineXChart_iff_ne_infinity (x : projectiveLine k) :
    x ∈ Set.range (projectiveLineXChart k).base ↔ x ≠ projectiveLineInfinity k := by
  constructor
  · intro hx h
    exact projectiveLineInfinity_notMem_range_XChart k (h ▸ hx)
  · intro hx
    rcases mem_range_projectiveLineXChart_or_eq_infinity x with h | h
    · exact h
    · exact (hx h).elim

/-- The complement of the first chart is the single actual closed point at infinity. -/
theorem compl_range_projectiveLineXChart :
    (Set.range (projectiveLineXChart k).base)ᶜ = {projectiveLineInfinity k} := by
  ext x
  change (x ∉ Set.range (projectiveLineXChart k).base) ↔ x = projectiveLineInfinity k
  rw [mem_range_projectiveLineXChart_iff_ne_infinity]
  exact not_not

/-- Every nongeneric point is either a nongeneric finite-chart point or infinity. -/
theorem projectiveLine_nongeneric_chart_or_infinity (x : projectiveLine k)
    (hx : x ≠ genericPoint (projectiveLine k)) :
    (∃ y : Spec (.of (Polynomial k)), y.asIdeal ≠ ⊥ ∧ (projectiveLineXChart k).base y = x) ∨
      x = projectiveLineInfinity k := by
  rcases mem_range_projectiveLineXChart_or_eq_infinity x with ⟨y, rfl⟩ | h
  · left
    refine ⟨y, ?_, rfl⟩
    intro hy
    exact hx ((congrArg (projectiveLineXChart k).base
      (eq_genericPoint_of_asIdeal_eq_bot y hy)).trans projectiveLineXChart_genericPoint_eq)
  · exact Or.inr h

end AlgebraicGeometry
