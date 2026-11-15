module

public import HodgeConjecture.Geometry.ProjectiveLineProductSections
public import HodgeConjecture.Realization.Betti.Examples.ProjectiveLineCanonicalPoints
public import HodgeConjecture.Realization.Betti.ProjectiveLineCycleClass
public import HodgeConjecture.Realization.Betti.Scheme
public import HodgeConjecture.Realization.Betti.SingularContractible
public import HodgeConjecture.Realization.Betti.SingularHomotopy

/-!
# Two singular classes on the actual product of projective lines

Each class is the pullback of the proved degree-two class of the canonical
complex point space of `P¹_ℂ` along an actual scheme projection. Their
construction uses the existing singular cohomology functor on complex
schemes. The two coordinate-fiber sections detect their independence.
The full degree-two calculation is a separate statement.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HodgeConjecture.ProjectiveLineProductBetti

open AlgebraicGeometry CategoryTheory

abbrev baseScheme := Spec (.of ℂ)

abbrev lineStructure : projectiveLine ℂ ⟶ baseScheme :=
  projectiveLine ℂ ↘ baseScheme

theorem zeroFirst_over :
    projectiveLineProductZeroFirst ℂ ≫
      projectiveLineProductStructureMorphism ℂ = lineStructure := by
  change projectiveLineProductZeroFirst ℂ ≫
    (projectiveLineProductFst ℂ ≫ lineStructure) = lineStructure
  rw [← Category.assoc, projectiveLineProductZeroFirst_fst, Category.assoc,
    projectiveLineZeroSection_comp_structureMorphism, Category.comp_id]

theorem zeroSecond_over :
    projectiveLineProductZeroSecond ℂ ≫
      projectiveLineProductStructureMorphism ℂ = lineStructure := by
  change projectiveLineProductZeroSecond ℂ ≫
    (projectiveLineProductFst ℂ ≫ lineStructure) = lineStructure
  rw [← Category.assoc, projectiveLineProductZeroSecond_fst, Category.id_comp]

theorem lineConstant_over :
    (lineStructure ≫ projectiveLineZeroSection ℂ) ≫ lineStructure =
      lineStructure := by
  rw [Category.assoc, projectiveLineZeroSection_comp_structureMorphism,
    Category.comp_id]

private theorem basePoint_subsingleton :
    Subsingleton (Scheme.ComplexPoints (𝟙 baseScheme)) := by
  constructor
  intro p q
  apply Scheme.ComplexPoints.ext
  simpa only [Category.comp_id] using p.hom_comp.trans q.hom_comp.symm

private theorem baseH2_eq_zero
    (z : SchemeBetti.Cohomology (𝟙 baseScheme) 2) : z = 0 := by
  letI : Subsingleton (Scheme.ComplexPoints (𝟙 baseScheme)) :=
    basePoint_subsingleton
  letI : TotallyDisconnectedSpace (Scheme.ComplexPoints (𝟙 baseScheme)) :=
    ⟨fun _ _ _ x _ y _ ↦ Subsingleton.elim x y⟩
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (SingularContractible.isZero_cohomology_of_totallyDisconnected
      (SchemeBetti.space (𝟙 baseScheme)) 2 (by decide))).elim z 0

/-- Actual rational singular H² of the canonical projective-line point space. -/
abbrev LineH2 := SchemeBetti.Cohomology (projectiveLine ℂ ↘ Spec (.of ℂ)) 2

/-- Actual rational singular H² of the scheme fiber product's complex points. -/
abbrev ProductH2 := SchemeBetti.Cohomology
  (projectiveLineProductStructureMorphism ℂ) 2

/-- The proved identity-on-sections homeomorphism induces the canonical Betti equivalence. -/
def canonicalBettiEquiv :
    SingularCochains.Cohomology
      (TopCat.of ProjectiveLineComplexPoints.Point) 2 ≃ₗ[ℚ] LineH2 :=
  (SingularHomotopy.homeomorphIso
    ProjectiveLineComplexPoints.canonicalHomeomorph 2).toLinearEquiv.symm

/-- The original ordinary P¹ cycle map, transported to canonical complex points. -/
def canonicalCycleClass :
    SchemeCycles.RationalChowGroup
      (ProjectiveLineCycles.dimensionFunction ℂ) 0 →ₗ[ℚ] LineH2 :=
  canonicalBettiEquiv.toLinearMap.comp ProjectiveLineBettiCycleClass.cycleClass

/-- The proved projective-line cover generator, transported to canonical complex points. -/
def lineGenerator : LineH2 :=
  canonicalBettiEquiv ProjectiveLineBettiCohomology.coverGenerator

theorem lineGenerator_ne_zero : lineGenerator ≠ 0 := by
  intro h
  change canonicalBettiEquiv ProjectiveLineBettiCohomology.coverGenerator = 0 at h
  apply ProjectiveLineBettiCohomology.coverGenerator_ne_zero
  exact canonicalBettiEquiv.injective
    (by simpa only [map_zero] using h)

/-- The generator is the established cycle class of the actual infinity Chow point. -/
theorem lineGenerator_eq_cycleClass_infinity :
    lineGenerator =
      canonicalCycleClass
        ProjectiveLineBettiCycleClass.rationalInfinityClass := by
  change canonicalBettiEquiv ProjectiveLineBettiCohomology.coverGenerator =
    canonicalBettiEquiv
      (ProjectiveLineBettiCycleClass.cycleClass
        ProjectiveLineBettiCycleClass.rationalInfinityClass)
  rw [ProjectiveLineBettiCycleClass.cycleClass_infinity]

/-- Pullback of the projective-line class along the first actual scheme projection. -/
def firstClass : ProductH2 :=
  SchemeBetti.pullback (projectiveLineProductFst ℂ)
    (projectiveLineProductFst_comp_structureMorphism ℂ) 2 lineGenerator

/-- Pullback of the projective-line class along the second actual scheme projection. -/
def secondClass : ProductH2 :=
  SchemeBetti.pullback (projectiveLineProductSnd ℂ)
    (projectiveLineProductSnd_comp_structureMorphism ℂ) 2 lineGenerator

private theorem pullback_comp_apply
    {X Y Z : Scheme.{0}}
    {x : X ⟶ baseScheme} {y : Y ⟶ baseScheme} {z : Z ⟶ baseScheme}
    (f : X ⟶ Y) (hf : f ≫ y = x)
    (g : Y ⟶ Z) (hg : g ≫ z = y)
    (a : SchemeBetti.Cohomology z 2) :
    SchemeBetti.pullback (f ≫ g) (by rw [Category.assoc, hg, hf]) 2 a =
      SchemeBetti.pullback f hf 2 (SchemeBetti.pullback g hg 2 a) := by
  exact congrArg
    (fun m : SchemeBetti.Cohomology z 2 ⟶ SchemeBetti.Cohomology x 2 ↦ m a)
    (SchemeBetti.pullback_comp f hf g hg 2)

theorem constant_pullback_lineGenerator_eq_zero :
    SchemeBetti.pullback (lineStructure ≫ projectiveLineZeroSection ℂ)
      lineConstant_over 2 lineGenerator = 0 := by
  have hf : lineStructure ≫ (𝟙 baseScheme) = lineStructure := Category.comp_id _
  rw [pullback_comp_apply (x := lineStructure) (y := 𝟙 baseScheme)
    (z := lineStructure) lineStructure hf (projectiveLineZeroSection ℂ)
    (projectiveLineZeroSection_comp_structureMorphism ℂ)]
  rw [baseH2_eq_zero (SchemeBetti.pullback (projectiveLineZeroSection ℂ)
    (projectiveLineZeroSection_comp_structureMorphism ℂ) 2 lineGenerator), map_zero]

/-- Restriction to the second-coordinate-zero fiber detects the first class. -/
def firstProbe : ProductH2 ⟶ LineH2 :=
  SchemeBetti.pullback (projectiveLineProductZeroSecond ℂ) zeroSecond_over 2

/-- Restriction to the first-coordinate-zero fiber detects the second class. -/
def secondProbe : ProductH2 ⟶ LineH2 :=
  SchemeBetti.pullback (projectiveLineProductZeroFirst ℂ) zeroFirst_over 2

@[simp] theorem firstProbe_firstClass : firstProbe firstClass = lineGenerator := by
  unfold firstProbe firstClass
  rw [← pullback_comp_apply (projectiveLineProductZeroSecond ℂ) zeroSecond_over
    (projectiveLineProductFst ℂ)
    (projectiveLineProductFst_comp_structureMorphism ℂ)]
  simp

@[simp] theorem firstProbe_secondClass : firstProbe secondClass = 0 := by
  unfold firstProbe secondClass
  rw [← pullback_comp_apply (projectiveLineProductZeroSecond ℂ) zeroSecond_over
    (projectiveLineProductSnd ℂ)
    (projectiveLineProductSnd_comp_structureMorphism ℂ)]
  simpa only [projectiveLineProductZeroSecond_snd] using
    constant_pullback_lineGenerator_eq_zero

@[simp] theorem secondProbe_firstClass : secondProbe firstClass = 0 := by
  unfold secondProbe firstClass
  rw [← pullback_comp_apply (projectiveLineProductZeroFirst ℂ) zeroFirst_over
    (projectiveLineProductFst ℂ)
    (projectiveLineProductFst_comp_structureMorphism ℂ)]
  simpa only [projectiveLineProductZeroFirst_fst] using
    constant_pullback_lineGenerator_eq_zero

@[simp] theorem secondProbe_secondClass : secondProbe secondClass = lineGenerator := by
  unfold secondProbe secondClass
  rw [← pullback_comp_apply (projectiveLineProductZeroFirst ℂ) zeroFirst_over
    (projectiveLineProductSnd ℂ)
    (projectiveLineProductSnd_comp_structureMorphism ℂ)]
  simp

/-- The two actual projection pullbacks are linearly independent in singular H². -/
theorem classes_independent (a b : ℚ)
    (h : a • firstClass + b • secondClass = 0) : a = 0 ∧ b = 0 := by
  have h₁ := congrArg firstProbe h
  have h₂ := congrArg secondProbe h
  simp only [map_add, map_smul, firstProbe_firstClass, firstProbe_secondClass,
    secondProbe_firstClass, secondProbe_secondClass, smul_zero, zero_add, add_zero,
    map_zero] at h₁ h₂
  exact ⟨(smul_eq_zero.mp h₁).resolve_right lineGenerator_ne_zero,
    (smul_eq_zero.mp h₂).resolve_right lineGenerator_ne_zero⟩

end HodgeConjecture.ProjectiveLineProductBetti

end
