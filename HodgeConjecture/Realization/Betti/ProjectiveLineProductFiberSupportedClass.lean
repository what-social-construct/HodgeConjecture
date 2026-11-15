module

public import HodgeConjecture.Realization.Betti.ProjectiveLineProductFiberClassInputs
public import HodgeConjecture.Realization.Betti.RelativeCochains

/-!
# Supported Betti classes of the two product zero fibers

The point's existing oriented relative Thom class pulls back along each
actual projection of the product scheme. These are genuine relative
singular-cohomology classes supported over the corresponding coordinate
fiber. Forgetting support recovers the two previously computed absolute
Betti classes. The construction is independent of a product Chow cycle-class
map, which remains a separate comparison theorem.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductFiberSupportedClass

open AlgebraicGeometry CategoryTheory HomologicalComplex
open HodgeConjecture.ProjectiveLineProductBetti
open HodgeConjecture.ProjectiveLinePointGysin
open HodgeConjecture.ProjectiveLineComplexPoints
open HodgeConjecture.ProjectiveLineProductFibers

/-- Canonical complex points of the actual product scheme. -/
abbrev ProductSpace : TopCat :=
  SchemeBetti.space (projectiveLineProductStructureMorphism ℂ)

/-- The original point model of the projective line, reached from canonical
complex points by the proved homeomorphism. -/
def lineComparison : SchemeBetti.space lineStructure ⟶ space :=
  TopCat.ofHom ⟨canonicalHomeomorph.symm, canonicalHomeomorph.symm.continuous⟩

def firstMap : ProductSpace ⟶ space :=
  SchemeBetti.map (projectiveLineProductFst ℂ)
    (projectiveLineProductFst_comp_structureMorphism ℂ) ≫ lineComparison

def secondMap : ProductSpace ⟶ space :=
  SchemeBetti.map (projectiveLineProductSnd ℂ)
    (projectiveLineProductSnd_comp_structureMorphism ℂ) ≫ lineComparison

/-- The actual simplicial complement of the first-coordinate zero fiber. -/
abbrev firstComplement : (TopCat.toSSet.obj ProductSpace).Subcomplex :=
  complementSubcomplex.preimage (TopCat.toSSet.map firstMap)

/-- The actual simplicial complement of the second-coordinate zero fiber. -/
abbrev secondComplement : (TopCat.toSSet.obj ProductSpace).Subcomplex :=
  complementSubcomplex.preimage (TopCat.toSSet.map secondMap)

/-- The simplicial complement is exactly the singular simplices contained
in the inverse image of the point's punctured open set. -/
theorem firstComplement_eq_subsetSingular :
    firstComplement =
      SingularSubcomplexes.subsetSingular ProductSpace
        (firstMap ⁻¹' ProjectiveLinePointSupport.puncturedOpen) := by
  rw [← ProjectiveLinePointSupport.reciprocalOpen_eq_puncturedOpen]
  rfl

theorem secondComplement_eq_subsetSingular :
    secondComplement =
      SingularSubcomplexes.subsetSingular ProductSpace
        (secondMap ⁻¹' ProjectiveLinePointSupport.puncturedOpen) := by
  rw [← ProjectiveLinePointSupport.reciprocalOpen_eq_puncturedOpen]
  rfl

/-- The original rational zero point is closed in the underlying scheme. -/
private theorem lineZero_isClosed :
    IsClosed ({projectiveLineZero ℂ} : Set (projectiveLine ℂ)) := by
  have hrange : Set.range (projectiveLineZeroSection ℂ).base =
      {projectiveLineZero ℂ} := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      rw [show q = (default : Spec (.of ℂ)) from Subsingleton.elim _ _]
      exact projectiveLineZeroSection_apply_unique ℂ
    · intro hx
      exact ⟨default, (projectiveLineZeroSection_apply_unique ℂ).trans
        (Set.mem_singleton_iff.mp hx).symm⟩
  simpa only [hrange] using
    (projectiveLineZeroSection ℂ).isClosedEmbedding.isClosed_range

/-- On the original projective-line point model, the analytic zero point
is exactly the complex point above the scheme-theoretic zero point. -/
private theorem linePoint_eq_zero_iff_base (p : Point) :
    p = ProjectiveLinePointSupport.zeroPoint ↔
      (schemeMorphism p).base (default : Spec (.of ℂ)) = projectiveLineZero ℂ := by
  constructor
  · rintro rfl
    exact ProjectiveLinePointSupport.zeroPoint_scheme_base default
  · intro h
    rcases finite_or_infinity p with ⟨z, hz⟩ | hp
    · rw [← hz] at h ⊢
      have ha : affineMorphism (AffineLineComplexPoints.evalPoint z)
          (default : Spec (.of ℂ)) = affineLineOrigin ℂ := by
        apply projectiveLineXChart_base_injective
        simpa only [finite, xChart, schemeMorphism, projectiveLineZero,
          Scheme.Hom.comp_apply] using h
      have hx : (Polynomial.X : Polynomial ℂ) ∈
          (affineMorphism (AffineLineComplexPoints.evalPoint z) default).asIdeal := by
        rw [ha]
        exact Ideal.subset_span rfl
      have hz0 : z = 0 := by
        have h' : AffineLineComplexPoints.evalPoint z Polynomial.X = 0 := by
          change AffineLineComplexPoints.evalPoint z Polynomial.X = 0 at hx
          exact hx
        simpa using h'
      rw [hz0]
      rfl
    · exfalso
      rw [hp] at h
      have hi : projectiveLineInfinity ℂ = projectiveLineZero ℂ :=
        (infinity_base default).symm.trans h
      exact projectiveLineZero_ne_projectiveLineInfinity ℂ hi.symm

/-- A complex product point lies in the first punctured inverse image
precisely when its scheme base lies outside the actual first zero-fiber
ideal's support. -/
theorem firstPunctured_eq_outside_fiber :
    firstMap ⁻¹' ProjectiveLinePointSupport.puncturedOpen =
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉
          (firstFiberIdeal ℂ (projectiveLineZero ℂ)).support} := by
  ext p
  change firstMap p ≠ ProjectiveLinePointSupport.zeroPoint ↔ _
  have hb : (schemeMorphism (firstMap p)).base (default : Spec (.of ℂ)) =
      (projectiveLineProductFst ℂ).base
        (p.hom.base (default : Spec (.of ℂ))) := by
    rfl
  have hs := mem_firstFiber_support ℂ (projectiveLineZero ℂ)
    (p.hom.base (default : Spec (.of ℂ)))
  rw [lineZero_isClosed.closure_eq] at hs
  calc
    firstMap p ≠ ProjectiveLinePointSupport.zeroPoint ↔
        (schemeMorphism (firstMap p)).base (default : Spec (.of ℂ)) ≠
          projectiveLineZero ℂ :=
      not_congr (linePoint_eq_zero_iff_base _)
    _ ↔ _ := by
      rw [hb]
      exact (not_congr hs).symm

/-- The same identification holds for the second coordinate fiber. -/
theorem secondPunctured_eq_outside_fiber :
    secondMap ⁻¹' ProjectiveLinePointSupport.puncturedOpen =
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉
          (secondFiberIdeal ℂ (projectiveLineZero ℂ)).support} := by
  ext p
  change secondMap p ≠ ProjectiveLinePointSupport.zeroPoint ↔ _
  have hb : (schemeMorphism (secondMap p)).base (default : Spec (.of ℂ)) =
      (projectiveLineProductSnd ℂ).base
        (p.hom.base (default : Spec (.of ℂ))) := by
    rfl
  have hs := mem_secondFiber_support ℂ (projectiveLineZero ℂ)
    (p.hom.base (default : Spec (.of ℂ)))
  rw [lineZero_isClosed.closure_eq] at hs
  calc
    secondMap p ≠ ProjectiveLinePointSupport.zeroPoint ↔
        (schemeMorphism (secondMap p)).base (default : Spec (.of ℂ)) ≠
          projectiveLineZero ℂ :=
      not_congr (linePoint_eq_zero_iff_base _)
    _ ↔ _ := by
      rw [hb]
      exact (not_congr hs).symm

/-- The first relative cochain group really vanishes on the singular
simplices of the complement of the first scheme-theoretic zero fiber. -/
theorem firstComplement_eq_outside_fiber :
    firstComplement = SingularSubcomplexes.subsetSingular ProductSpace
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉
          (firstFiberIdeal ℂ (projectiveLineZero ℂ)).support} := by
  rw [firstComplement_eq_subsetSingular, firstPunctured_eq_outside_fiber]

theorem secondComplement_eq_outside_fiber :
    secondComplement = SingularSubcomplexes.subsetSingular ProductSpace
      {p : ProductSpace |
        p.hom.base (default : Spec (.of ℂ)) ∉
          (secondFiberIdeal ℂ (projectiveLineZero ℂ)).support} := by
  rw [secondComplement_eq_subsetSingular, secondPunctured_eq_outside_fiber]

/-- Pull the oriented point Thom class back along the genuine first map of
simplicial pairs. -/
def firstSupportedClass : RelativeCochains.Cohomology firstComplement 2 :=
  homologyMap (RelativeCochains.pullback
    (TopCat.toSSet.map firstMap) le_rfl) 2 supportedThomClass

/-- Pull the same point Thom class back along the second projection. -/
def secondSupportedClass : RelativeCochains.Cohomology secondComplement 2 :=
  homologyMap (RelativeCochains.pullback
    (TopCat.toSSet.map secondMap) le_rfl) 2 supportedThomClass

/-- Relative pullback followed by forgetting support is the original
absolute singular pullback. -/
private theorem forget_pullback (f : ProductSpace ⟶ space)
    (z : SupportedH2) :
    RelativeCochains.forget
        (complementSubcomplex.preimage (TopCat.toSSet.map f)) 2
        (homologyMap (RelativeCochains.pullback
          (TopCat.toSSet.map f) le_rfl) 2 z) =
      SingularCochains.cohomologyPullback f 2
        (RelativeCochains.forget complementSubcomplex 2 z) := by
  change (homologyMap (RelativeCochains.pullback
      (TopCat.toSSet.map f) le_rfl) 2 ≫
      homologyMap (RelativeCochains.inclusion
        (complementSubcomplex.preimage (TopCat.toSSet.map f))) 2) z =
    (homologyMap (RelativeCochains.inclusion complementSubcomplex) 2 ≫
      homologyMap (SubcomplexCochains.pullback (TopCat.toSSet.map f)) 2) z
  rw [← homologyMap_comp, ← homologyMap_comp]
  rw [RelativeCochains.pullback_inclusion]

theorem lineComparison_pullback_coverGenerator :
    SingularCochains.cohomologyPullback lineComparison 2
      ProjectiveLineBettiCohomology.coverGenerator = lineGenerator := by
  rfl

/-- Forgetting support on the pulled-back first-fiber Thom class gives the
actual first product Betti basis class. -/
theorem forget_firstSupportedClass :
    RelativeCochains.forget firstComplement 2 firstSupportedClass = firstClass := by
  rw [firstSupportedClass, forget_pullback, forget_supportedThomClass]
  change SingularCochains.cohomologyPullback
      (SchemeBetti.map (projectiveLineProductFst ℂ)
        (projectiveLineProductFst_comp_structureMorphism ℂ) ≫ lineComparison) 2
      ProjectiveLineBettiCohomology.coverGenerator = firstClass
  rw [SingularCochains.cohomologyPullback_comp]
  change SingularCochains.cohomologyPullback
    (SchemeBetti.map (projectiveLineProductFst ℂ)
      (projectiveLineProductFst_comp_structureMorphism ℂ)) 2
    (SingularCochains.cohomologyPullback lineComparison 2
      ProjectiveLineBettiCohomology.coverGenerator) = firstClass
  rw [lineComparison_pullback_coverGenerator]
  rfl

/-- The corresponding second-fiber supported class forgets to the second
product Betti basis class. -/
theorem forget_secondSupportedClass :
    RelativeCochains.forget secondComplement 2 secondSupportedClass = secondClass := by
  rw [secondSupportedClass, forget_pullback, forget_supportedThomClass]
  change SingularCochains.cohomologyPullback
      (SchemeBetti.map (projectiveLineProductSnd ℂ)
        (projectiveLineProductSnd_comp_structureMorphism ℂ) ≫ lineComparison) 2
      ProjectiveLineBettiCohomology.coverGenerator = secondClass
  rw [SingularCochains.cohomologyPullback_comp]
  change SingularCochains.cohomologyPullback
    (SchemeBetti.map (projectiveLineProductSnd ℂ)
      (projectiveLineProductSnd_comp_structureMorphism ℂ)) 2
    (SingularCochains.cohomologyPullback lineComparison 2
      ProjectiveLineBettiCohomology.coverGenerator) = secondClass
  rw [lineComparison_pullback_coverGenerator]
  rfl

end HodgeConjecture.ProjectiveLineProductFiberSupportedClass

end
