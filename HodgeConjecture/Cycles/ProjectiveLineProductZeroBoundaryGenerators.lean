module

public import HodgeConjecture.Cycles.ProjectiveLineProductZeroAffineChowLocalization
public import HodgeConjecture.Cycles.ProjectiveLineProductAffineChowVanishing

/-!
# Degree-one carriers on the zero-fiber boundary

The reduced complement of the opposite affine product chart has precisely
two integral components in degree one: the two actual coordinate-zero
fibers. Consequently, rational degree-one cycles supported on this
boundary are spanned by their fundamental cycles.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators

open AlgebraicGeometry CategoryTheory TopologicalSpace SchemeCycles
open HodgeConjecture.ProjectiveLineProductChow
open HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization

universe u

variable (k : Type u) [Field k]

/-- Two integral supports of the same degree coincide if the generic point
of one lies in the support of the other. -/
theorem carrier_eq_of_generic_mem_support_of_same_degree
    {X : Scheme.{u}} (δ : DimensionFunction X)
    (W F : IntegralClosedSubscheme X)
    (hdeg : supportDegree δ W = supportDegree δ F)
    (hmem : ambientGenericPoint W ∈ F.val.support) : W = F := by
  have hle : ambientGenericPoint W ≤ ambientGenericPoint F :=
    Scheme.le_iff_specializes.mpr
      ((ambientGenericPoint_isGenericPoint F).specializes_iff_mem.mpr hmem)
  have hpoint : ambientGenericPoint W = ambientGenericPoint F := by
    by_contra hne
    have hnle : ¬ ambientGenericPoint F ≤ ambientGenericPoint W := by
      intro hback
      exact hne (((Scheme.le_iff_specializes.mp hback).antisymm
        (Scheme.le_iff_specializes.mp hle)).eq)
    have hlt := δ.strictMono (lt_iff_le_not_ge.mpr ⟨hle, hnle⟩)
    exact (ne_of_lt hlt) hdeg
  calc
    W = pointSupport X (ambientGenericPoint W) := (pointSupport_ambientGenericPoint W).symm
    _ = pointSupport X (ambientGenericPoint F) := congrArg (pointSupport X) hpoint
    _ = F := pointSupport_ambientGenericPoint F

/-- An integral degree-one carrier on the chart boundary is literally one
of the two existing zero-fiber carriers. -/
theorem degree_one_boundary_carrier_eq_zero_fiber
    (W : IntegralClosedSubscheme (projectiveLineProduct k))
    (hdeg : supportDegree (dimensionFunction k) W = 1)
    (hboundary : ambientGenericPoint W ∈
      (openComplementIdeal (chart k)).support) :
    W = projectiveLineProductZeroFirstCarrier k ∨
      W = projectiveLineProductZeroSecondCarrier k := by
  have hboundary' : ambientGenericPoint W ∈
      ((ProjectiveLineProductFibers.firstFiberIdeal k
        (projectiveLineZero k)).support : Set (projectiveLineProduct k)) ∪
        ((ProjectiveLineProductFibers.secondFiberIdeal k
          (projectiveLineZero k)).support : Set (projectiveLineProduct k)) := by
    rw [← boundary_support_eq_zero_fibers k]
    exact hboundary
  rcases hboundary' with hfirst | hsecond
  · left
    apply carrier_eq_of_generic_mem_support_of_same_degree
      (dimensionFunction k) W (projectiveLineProductZeroFirstCarrier k)
    · rw [hdeg, firstCarrier_supportDegree_one]
    · have hcarrier : (projectiveLineProductZeroFirstCarrier k).val =
          ProjectiveLineProductFibers.firstFiberIdeal k (projectiveLineZero k) := by
        simpa only [zeroSectionPoint_eq_projectiveLineZero] using
          projectiveLineProductZeroFirstCarrier_val_eq_fiberIdeal k
      rw [hcarrier]
      exact hfirst
  · right
    apply carrier_eq_of_generic_mem_support_of_same_degree
      (dimensionFunction k) W (projectiveLineProductZeroSecondCarrier k)
    · rw [hdeg, secondCarrier_supportDegree_one]
    · have hcarrier : (projectiveLineProductZeroSecondCarrier k).val =
          ProjectiveLineProductFibers.secondFiberIdeal k (projectiveLineZero k) := by
        simpa only [zeroSectionPoint_eq_projectiveLineZero] using
          projectiveLineProductZeroSecondCarrier_val_eq_fiberIdeal k
      rw [hcarrier]
      exact hsecond

/-- Rationalization of the first named cycle is its rational fundamental cycle. -/
theorem firstZeroCycle_rationalized_val :
    (cyclesOfDegreeRationalize (dimensionFunction k) 1 (firstZeroCycle k)).val =
      fundamentalCycle ℚ (projectiveLineProductZeroFirstCarrier k) := by
  ext W
  simp only [cyclesOfDegreeRationalize_apply]
  classical
  by_cases h : W = projectiveLineProductZeroFirstCarrier k <;>
    simp [firstZeroCycle, fundamentalCycle, h]

/-- Rationalization of the second named cycle is its rational fundamental cycle. -/
theorem secondZeroCycle_rationalized_val :
    (cyclesOfDegreeRationalize (dimensionFunction k) 1 (secondZeroCycle k)).val =
      fundamentalCycle ℚ (projectiveLineProductZeroSecondCarrier k) := by
  ext W
  simp only [cyclesOfDegreeRationalize_apply]
  classical
  by_cases h : W = projectiveLineProductZeroSecondCarrier k <;>
    simp [secondZeroCycle, fundamentalCycle, h]

/-- Every rational homogeneous cycle supported on the actual zero boundary
is a linear combination of the two named rationalized fiber cycles. -/
theorem cycle_supported_on_boundary_mem_span
    (c : cyclesOfDegree ℚ (dimensionFunction k) 1)
    (hc : c.val ∈ Finsupp.supported ℚ ℚ
      {W | ambientGenericPoint W ∈ (openComplementIdeal (chart k)).support}) :
    c ∈ Submodule.span ℚ
      ({cyclesOfDegreeRationalize (dimensionFunction k) 1 (firstZeroCycle k),
        cyclesOfDegreeRationalize (dimensionFunction k) 1 (secondZeroCycle k)} :
          Set (cyclesOfDegree ℚ (dimensionFunction k) 1)) := by
  let F₁ := projectiveLineProductZeroFirstCarrier k
  let F₂ := projectiveLineProductZeroSecondCarrier k
  have hpair : c.val ∈ Finsupp.supported ℚ ℚ ({F₁, F₂} : Set _) := by
    rw [Finsupp.mem_supported] at hc ⊢
    intro W hW
    have hWdeg : supportDegree (dimensionFunction k) W = 1 :=
      (mem_cyclesOfDegree_iff ℚ (dimensionFunction k) 1 c.val).mp c.property W
        (Finsupp.mem_support_iff.mp hW)
    have hWbd : ambientGenericPoint W ∈ (openComplementIdeal (chart k)).support :=
      hc hW
    rcases degree_one_boundary_carrier_eq_zero_fiber k W hWdeg hWbd with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (by simpa only [Set.mem_singleton_iff, F₂] using h))
  have hspan : c.val ∈ Submodule.span ℚ
      ({fundamentalCycle ℚ F₁, fundamentalCycle ℚ F₂} : Set (Cycles _ ℚ)) := by
    rw [Finsupp.supported_eq_span_single, Set.image_pair] at hpair
    exact hpair
  obtain ⟨a, b, hsum⟩ := (Submodule.mem_span_pair).mp hspan
  apply (Submodule.mem_span_pair).mpr
  refine ⟨a, b, ?_⟩
  apply Subtype.ext
  change a • (cyclesOfDegreeRationalize (dimensionFunction k) 1 (firstZeroCycle k)).val +
      b • (cyclesOfDegreeRationalize (dimensionFunction k) 1 (secondZeroCycle k)).val =
        c.val
  rw [firstZeroCycle_rationalized_val, secondZeroCycle_rationalized_val]
  exact hsum

/-- A degree-one rational cycle on the two-fiber boundary maps to a class
in the span of the two existing fiber Chow classes. -/
theorem class_of_boundary_cycle_mem_span
    (c : cyclesOfDegree ℚ (dimensionFunction k) 1)
    (hc : c.val ∈ Finsupp.supported ℚ ℚ
      {W | ambientGenericPoint W ∈ (openComplementIdeal (chart k)).support}) :
    rationalClassMap (dimensionFunction k) 1 c ∈
      Submodule.span ℚ
        ({firstZeroRationalChowClass k, secondZeroRationalChowClass k} :
          Set (RationalChowGroup (dimensionFunction k) 1)) := by
  obtain ⟨a, b, hsum⟩ := (Submodule.mem_span_pair).mp
    (cycle_supported_on_boundary_mem_span k c hc)
  have hfirst : rationalClassMap (dimensionFunction k) 1
      (cyclesOfDegreeRationalize (dimensionFunction k) 1 (firstZeroCycle k)) =
        firstZeroRationalChowClass k := by
    simp only [firstZeroRationalChowClass, firstZeroChowClass,
      chowRationalize_classMap]
  have hsecond : rationalClassMap (dimensionFunction k) 1
      (cyclesOfDegreeRationalize (dimensionFunction k) 1 (secondZeroCycle k)) =
        secondZeroRationalChowClass k := by
    simp only [secondZeroRationalChowClass, secondZeroChowClass,
      chowRationalize_classMap]
  rw [← hsum, map_add, map_smul, map_smul, hfirst, hsecond]
  exact (Submodule.mem_span_pair).mpr ⟨a, b, rfl⟩

/-- Every boundary Chow class pushed to the product is in the span of the
two named zero-fiber classes. -/
theorem boundary_pushforward_class_mem_span
    (c : cyclesOfDegree ℚ
      ((dimensionFunction k).comapClosedImmersion
        (openComplementIdeal (chart k)).subschemeι) 1) :
    letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
    rationalChowClosedImmersionPushforward
      ((dimensionFunction k).comapClosedImmersion
        (openComplementIdeal (chart k)).subschemeι)
      (dimensionFunction k) (openComplementIdeal (chart k)).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion (dimensionFunction k)
        (openComplementIdeal (chart k)).subschemeι W).symm) 1
      (rationalClassMap _ 1 c) ∈
      Submodule.span ℚ
        ({firstZeroRationalChowClass k, secondZeroRationalChowClass k} :
          Set (RationalChowGroup (dimensionFunction k) 1)) := by
  letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
  rw [rationalChowClosedImmersionPushforward_classMap]
  apply class_of_boundary_cycle_mem_span k
  have hrange : closedImmersionPushforward ℚ
      (openComplementIdeal (chart k)).subschemeι c.val ∈
      LinearMap.range (closedImmersionPushforward ℚ
        (openComplementIdeal (chart k)).subschemeι) := ⟨c.val, rfl⟩
  rw [range_closedImmersionPushforward] at hrange
  change closedImmersionPushforward ℚ
    (openComplementIdeal (chart k)).subschemeι c.val ∈ _
  rw [Finsupp.mem_supported] at hrange ⊢
  intro W hW
  have h := hrange hW
  rw [Scheme.IdealSheafData.range_subschemeι] at h
  exact h

/-- Vanishing of the actual affine-plane Chow group makes the two existing
fiber classes span the ordinary rational Chow group of the product. -/
theorem rationalChowGroup_span_zero_fibers_of_affine_zero
    (hzero : ∀ q : RationalChowGroup
      ((dimensionFunction k).comapOpenImmersion (chart k)) 1, q = 0) :
    Submodule.span ℚ
      ({firstZeroRationalChowClass k, secondZeroRationalChowClass k} :
        Set (RationalChowGroup (dimensionFunction k) 1)) = ⊤ := by
  letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
  apply Submodule.eq_top_iff'.mpr
  intro q
  obtain ⟨b, hb⟩ := boundaryPushforward_surjective_of_affine_zero k hzero q
  obtain ⟨c, rfl⟩ := rationalClassMap_surjective
    ((dimensionFunction k).comapClosedImmersion
      (openComplementIdeal (chart k)).subschemeι) 1 b
  rw [← hb]
  exact boundary_pushforward_class_mem_span k c

/-- The two actual zero-fiber classes span the product's ordinary rational
degree-one Chow group. -/
theorem rationalChowGroup_span_zero_fibers :
    Submodule.span ℚ
      ({firstZeroRationalChowClass k, secondZeroRationalChowClass k} :
        Set (RationalChowGroup (dimensionFunction k) 1)) = ⊤ := by
  apply rationalChowGroup_span_zero_fibers_of_affine_zero k
  intro q
  exact ProjectiveLineProductAffineChowVanishing.chart_restricted_rationalChowGroup_one_eq_zero
    k (chart k) q

end HodgeConjecture.ProjectiveLineProductZeroBoundaryGenerators

end
