module

public import HodgeConjecture.Cycles.ProjectiveLineProductAffineChowLocalization

/-!
# The zero-fiber boundary of the opposite affine product chart

Using the second affine chart in both projective-line coordinates makes the
closed complement the union of the two named zero fibers. Rational Chow
localization for this actual open immersion places its boundary classes in
the kernel of restriction. The classification of all boundary components
and the vanishing of affine-plane CH₁ are separate steps.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization

open AlgebraicGeometry CategoryTheory SchemeCycles TensorProduct
open HodgeConjecture.ProjectiveLineProductChow

universe u

variable (k : Type u) [Field k]

/-- Every point lies in the second affine chart or is the distinguished
zero point of the first chart. -/
theorem mem_range_projectiveLineYChart_or_eq_zero (x : projectiveLine k) :
    x ∈ Set.range (projectiveLineYChart k).base ∨ x = projectiveLineZero k := by
  obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData k).ι_jointly_surjective x
  obtain ⟨i⟩ := i
  cases i
  · by_cases hy : (Polynomial.X : Polynomial k) ∈ y.asIdeal
    · right
      rw [eq_affineLineOrigin_of_X_mem y hy]
      rfl
    · obtain ⟨w, hw⟩ := (mem_range_projectiveLinePuncturedChart_iff k y).2 hy
      refine Or.inl ⟨(projectiveLineOverlapYInclusion k).base w, ?_⟩
      calc
        (projectiveLineYChart k).base
            ((projectiveLineOverlapYInclusion k).base w) =
            (projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k).base w := rfl
        _ = (projectiveLinePuncturedChart k ≫ projectiveLineXChart k).base w := by
          rw [projectiveLineOverlap_compat]
          simp only [projectiveLineOverlapYInclusion, Category.assoc]
        _ = (projectiveLineXChart k).base y := by rw [← hw]; rfl
  · exact Or.inl ⟨y, rfl⟩

/-- Zero lies outside the second affine chart. -/
theorem projectiveLineZero_notMem_range_YChart :
    projectiveLineZero k ∉ Set.range (projectiveLineYChart k).base := by
  rintro ⟨p, hp⟩
  have hp' : (projectiveLineXChart k).base (affineLineOrigin k) =
      (projectiveLineYChart k).base p := hp.symm
  obtain ⟨w, hw, -⟩ :=
    (projectiveLineXChart_base_eq_projectiveLineYChart_base_iff k
      (affineLineOrigin k) p).mp hp'
  exact (mem_range_projectiveLinePuncturedChart_iff k _).mp ⟨w, hw⟩
    (Ideal.subset_span rfl)

/-- The second projective-line affine chart is exactly the complement of zero. -/
theorem mem_range_projectiveLineYChart_iff_ne_zero (x : projectiveLine k) :
    x ∈ Set.range (projectiveLineYChart k).base ↔ x ≠ projectiveLineZero k := by
  constructor
  · intro hx h
    exact projectiveLineZero_notMem_range_YChart k (h ▸ hx)
  · intro hx
    rcases mem_range_projectiveLineYChart_or_eq_zero k x with h | h
    · exact h
    · exact (hx h).elim

/-- The distinguished zero point is closed as the complement of the second chart. -/
theorem zero_isClosed :
    IsClosed ({projectiveLineZero k} : Set (projectiveLine k)) := by
  have h : ({projectiveLineZero k} : Set (projectiveLine k)) =
      (Set.range (projectiveLineYChart k).base)ᶜ := by
    ext x
    change x = projectiveLineZero k ↔
      x ∉ Set.range (projectiveLineYChart k).base
    rw [mem_range_projectiveLineYChart_iff_ne_zero]
    exact not_not.symm
  rw [h]
  exact (projectiveLineYChart k).isOpenEmbedding.isOpen_range.isClosed_compl

/-- The two second-coordinate affine charts over the same base. -/
def affineProductMap : projectiveLineAffineProduct k ⟶ projectiveLineProduct k :=
  Limits.pullback.map
    (projectiveLineAffineStructureMorphism k)
    (projectiveLineAffineStructureMorphism k)
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLineYChart k) (projectiveLineYChart k)
    (𝟙 (Spec (.of k))) (by simp) (by simp)

instance affineProductMap_isOpenImmersion : IsOpenImmersion (affineProductMap k) := by
  unfold affineProductMap
  infer_instance

/-- The second-coordinate affine chart in the same polynomial tensor ring. -/
def chart :
    Spec (.of (Polynomial k ⊗[k] Polynomial k)) ⟶ projectiveLineProduct k :=
  (projectiveLineAffineProductIso k).inv ≫ affineProductMap k

instance chart_isOpenImmersion : IsOpenImmersion (chart k) := by
  unfold chart
  infer_instance

instance chart_isNoetherian : IsNoetherian (Spec (.of (Polynomial k ⊗[k] Polynomial k))) :=
  openImmersion_isNoetherian (chart k)

/-- The second-coordinate affine product chart consists of points where
neither coordinate is zero. -/
theorem range_chart :
    Set.range (chart k).base =
      (projectiveLineProductFst k).base ⁻¹'
          Set.range (projectiveLineYChart k).base ∩
        (projectiveLineProductSnd k).base ⁻¹'
          Set.range (projectiveLineYChart k).base := by
  unfold chart
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hs : Set.range (projectiveLineAffineProductIso k).inv.base = Set.univ :=
    Set.range_eq_univ.mpr (projectiveLineAffineProductIso k).inv.homeomorph.surjective
  rw [hs, Set.image_univ]
  change Set.range (Limits.pullback.map
    (projectiveLineAffineStructureMorphism k)
    (projectiveLineAffineStructureMorphism k)
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLineYChart k) (projectiveLineYChart k)
    (𝟙 (Spec (.of k))) (by simp) (by simp)).base = _
  exact Scheme.Pullback.range_map
    (projectiveLineAffineStructureMorphism k)
    (projectiveLineAffineStructureMorphism k)
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLine k ↘ Spec (.of k))
    (projectiveLineYChart k) (projectiveLineYChart k)
    (𝟙 (Spec (.of k))) (by simp) (by simp)

/-- The reduced boundary of this chart is exactly the union of the two
scheme-theoretic zero-fiber supports. -/
theorem boundary_support_eq_zero_fibers :
    ((openComplementIdeal (chart k)).support : Set (projectiveLineProduct k)) =
      ((ProjectiveLineProductFibers.firstFiberIdeal k
        (projectiveLineZero k)).support : Set (projectiveLineProduct k)) ∪
        ((ProjectiveLineProductFibers.secondFiberIdeal k
          (projectiveLineZero k)).support : Set (projectiveLineProduct k)) := by
  ext y
  rw [← Scheme.IdealSheafData.range_subschemeι, range_openComplement, range_chart]
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, not_and_or]
  rw [mem_range_projectiveLineYChart_iff_ne_zero,
    mem_range_projectiveLineYChart_iff_ne_zero]
  simp only [not_not, Set.mem_union]
  have hfirst : y ∈ (ProjectiveLineProductFibers.firstFiberIdeal k
      (projectiveLineZero k)).support ↔
      (projectiveLineProductFst k).base y = projectiveLineZero k := by
    simpa only [(zero_isClosed k).closure_eq, Set.mem_singleton_iff] using
      (ProjectiveLineProductFibers.mem_firstFiber_support k
        (projectiveLineZero k) y)
  have hsecond : y ∈ (ProjectiveLineProductFibers.secondFiberIdeal k
      (projectiveLineZero k)).support ↔
      (projectiveLineProductSnd k).base y = projectiveLineZero k := by
    simpa only [(zero_isClosed k).closure_eq, Set.mem_singleton_iff] using
      (ProjectiveLineProductFibers.mem_secondFiber_support k
        (projectiveLineZero k) y)
  exact or_congr hfirst.symm hsecond.symm

/-- Rational Chow localization for the actual open chart whose boundary is
the two named zero fibers. -/
theorem range_boundaryPushforward_eq_ker_restrict :
    letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
    LinearMap.range (rationalChowClosedImmersionPushforward
      ((dimensionFunction k).comapClosedImmersion
        (openComplementIdeal (chart k)).subschemeι)
      (dimensionFunction k) (openComplementIdeal (chart k)).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion (dimensionFunction k)
        (openComplementIdeal (chart k)).subschemeι W).symm) 1) =
      LinearMap.ker (rationalChowOpenRestriction (dimensionFunction k) (chart k) 1) := by
  letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
  exact range_rationalChowOpenComplementPushforward_eq_ker
    (dimensionFunction k) (chart k) 1

/-- If the actual affine product chart has vanishing degree-one rational
Chow group, every product class comes from the reduced boundary whose
support is the union of the two named zero fibers. -/
theorem boundaryPushforward_surjective_of_affine_zero
    (hzero : ∀ q : RationalChowGroup
      ((dimensionFunction k).comapOpenImmersion (chart k)) 1, q = 0) :
    letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
    Function.Surjective (rationalChowClosedImmersionPushforward
      ((dimensionFunction k).comapClosedImmersion
        (openComplementIdeal (chart k)).subschemeι)
      (dimensionFunction k) (openComplementIdeal (chart k)).subschemeι
      (fun W ↦ (supportDegree_comapClosedImmersion (dimensionFunction k)
        (openComplementIdeal (chart k)).subschemeι W).symm) 1) := by
  letI := closedImmersion_isNoetherian (openComplementIdeal (chart k)).subschemeι
  intro z
  have hz : z ∈ LinearMap.ker
      (rationalChowOpenRestriction (dimensionFunction k) (chart k) 1) := by
    change rationalChowOpenRestriction (dimensionFunction k) (chart k) 1 z = 0
    exact hzero _
  rw [← range_boundaryPushforward_eq_ker_restrict k] at hz
  exact hz

end HodgeConjecture.ProjectiveLineProductZeroAffineChowLocalization

end
