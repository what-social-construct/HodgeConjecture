module

public import HodgeConjecture.Geometry.Holomorphic.AtlasCoordinates
public import HodgeConjecture.Realization.DeRham.HolomorphicComplex
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

@[expose] public section

/-! # The descended holomorphic de Rham sheaf complex

The sheaf property glues the original coordinate sections and proves
their overlap equations locally. Thus descent does not introduce a new
gluing assumption. The arrows are the same descended exterior derivatives.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace HodgeConjecture.HolomorphicAtlas

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff
open HolomorphicForms

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

omit [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem domain_iSup (e : Chart E M) {ι : Type} (U : ι → Opens M) :
    (⨆ i, domain e (U i)) = domain e (⨆ i, U i) := by
  apply Opens.ext
  apply Set.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz
    exact ⟨hi.1, Opens.mem_iSup.mpr ⟨i, hi.2⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hz.2
    exact Opens.mem_iSup.mpr ⟨i, hz.1, hi⟩

/-- The presheaf obtained from the actual atlas descent modules. -/
def formsPresheaf (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    (n : ℕ) : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of M) where
  obj U := ModuleCat.of ℂ (Forms E U.unop n)
  map i := ModuleCat.ofHom (restrict (leOfHom i.unop) n)
  map_id _ := rfl
  map_comp _ _ := rfl

theorem formsPresheaf_isSheaf (n : ℕ) : (formsPresheaf E M n).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U a ha
  have hc : ∀ e : Chart E M, ∃ g : Sections (domain e (iSup U)) n,
      ∀ i, HolomorphicForms.restrict (domain_mono e (le_iSup U i)) n g = (a i).1 e := by
    intro e
    have hnative := (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
      (HolomorphicDeRham.formsPresheaf E n)).mp (HolomorphicDeRham.formsSheaf E n).property
    have hcompat : (HolomorphicDeRham.formsPresheaf E n).IsCompatible
        (fun i ↦ domain e (U i)) (fun i ↦ (a i).1 e) := by
      intro i j
      apply ContMDiffMap.ext
      intro z
      exact congrArg (fun b : Forms E (U i ⊓ U j) n ↦ b.1 e
        ⟨z.1, ⟨z.2.1.1, z.2.1.2, z.2.2.2⟩⟩) (ha i j)
    obtain ⟨g, hg, -⟩ := hnative (fun i ↦ domain e (U i)) (fun i ↦ (a i).1 e) hcompat
    have heq := domain_iSup e U
    refine ⟨HolomorphicForms.restrict (le_of_eq heq.symm) n g, ?_⟩
    intro i
    apply ContMDiffMap.ext
    intro z
    exact congrArg (fun b : Sections (domain e (U i)) n ↦ b z) (hg i)
  choose g hg using hc
  have hgpt (e : Chart E M) (i : ι) (z : domain e (U i)) :
      g e ⟨z.1, domain_mono e (le_iSup U i) z.2⟩ = (a i).1 e z :=
    congrArg (fun b : Sections (domain e (U i)) n ↦ b z) (hg e i)
  have hdesc : g ∈ compatibleSubmodule (E := E) (iSup U) n := by
    intro e e'
    apply ContMDiffMap.ext
    intro z
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp z.2.2.1
    have hz : z.1 ∈ overlap e e' (U i) := ⟨z.2.1, hi, z.2.2.2⟩
    have htrans := transition_mapsTo e e' (U i) hz
    change g e ⟨z.1, _⟩ =
      (g e' ⟨transition e e' z, _⟩).compContinuousLinearMap
        (fderiv ℂ (transition e e') z)
    rw [hgpt e i ⟨z.1, overlap_le e e' (U i) hz⟩,
      hgpt e' i ⟨transition e e' z, htrans⟩]
    exact congrArg (fun b : Sections (overlap e e' (U i)) n ↦ b ⟨z.1, hz⟩)
      ((a i).2 e e')
  refine ⟨⟨g, hdesc⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    funext e
    exact hg e i
  · intro b hb
    apply Subtype.ext
    funext e
    apply ContMDiffMap.ext
    intro z
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp z.2.2
    have hz : z.1 ∈ domain e (U i) := ⟨z.2.1, hi⟩
    exact (congrArg (fun c : Forms E (U i) n ↦ c.1 e ⟨z.1, hz⟩) (hb i)).trans
      (hgpt e i ⟨z.1, hz⟩).symm

/-- Intrinsic holomorphic forms are a proved sheaf on the original manifold topology. -/
def formsSheaf (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
    (n : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M) :=
  ⟨formsPresheaf E M n, formsPresheaf_isSheaf n⟩

def sheafDifferential (n : ℕ) : formsSheaf E M n ⟶ formsSheaf E M (n + 1) :=
  ObjectProperty.homMk {
    app U := ModuleCat.ofHom (differential U.unop n)
    naturality _ _ i := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact (restrict_differential (leOfHom i.unop) n a).symm }

theorem sheafDifferential_comp (n : ℕ) :
    sheafDifferential (E := E) (M := M) n ≫ sheafDifferential (n + 1) = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact ModuleCat.hom_ext (differential_comp U.unop n)

/-- The all-degree holomorphic de Rham complex descended through the native atlas. -/
def complex (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) ℕ :=
  CochainComplex.of (formsSheaf E M) (sheafDifferential) (sheafDifferential_comp)

@[simp]
theorem complex_X (n : ℕ) : (complex E M).X n = formsSheaf E M n := rfl

@[simp]
theorem complex_d (n : ℕ) :
    (complex E M).d n (n + 1) = sheafDifferential (E := E) (M := M) n := by
  apply CochainComplex.of_d

/-- Sections of the same intrinsic complex, with the same differential. -/
def sectionComplex (U : Opens M) : CochainComplex (ModuleCat.{0} ℂ) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of ℂ (Forms E U n))
    (fun n ↦ ModuleCat.ofHom (differential U n))
    (fun n ↦ ModuleCat.hom_ext (differential_comp U n))

/-- The actual complex on a chart source is isomorphic to the coordinate complex. -/
def chartComplexIso {U : Opens M} (e : Chart E M) (hU : U ≤ source e) :
    sectionComplex (E := E) U ≅ HolomorphicDeRham.sectionComplex E (domain e U) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ (chartEquiv e hU n).toModuleIso) (by
    intro i j hij
    change i + 1 = j at hij
    subst j
    simp only [sectionComplex, HolomorphicDeRham.sectionComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (inChart_differential U i e a).symm)

end HodgeConjecture.HolomorphicAtlas
