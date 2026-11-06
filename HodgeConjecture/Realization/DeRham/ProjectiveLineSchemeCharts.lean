module

public import HodgeConjecture.Geometry.ProjectiveLineOpenCover
public import HodgeConjecture.Realization.DeRham.AffineSectionCoordinates
public import HodgeConjecture.Realization.DeRham.ProjectiveLineCech

@[expose] public section

/-!
# Scheme-section coordinates for the original projective-line complex

The two polynomial algebras and Laurent overlap are identified, over the
original base, with sections of the actual structure sheaf on their open
images. Both actual restriction maps become the original coordinate maps.
The induced maps on forms and their differentials therefore retain the
geometric content of the existing Čech calculation.
-/

set_option autoImplicit false

noncomputable section

namespace HodgeConjecture.ProjectiveLineDeRham

open AlgebraicGeometry CategoryTheory SchemeDeRham KaehlerDifferential

universe u

variable (k : Type u) [CommRing k]

/-- The original structural morphism also gives the expected constants on the overlap. -/
theorem overlapChart_comp_structureMorphism :
    projectiveLineOverlapChart k ≫ (projectiveLine k ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))) := by
  rw [projectiveLineOverlapChart, Category.assoc,
    projectiveLineXChart_comp_structureMorphism]
  change Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C (R := k))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact Polynomial.toLaurent_C (R := k) a

/-- The zero-chart structure-sheaf sections have their original polynomial coordinates. -/
def zeroSectionCoordinates :
    letI := sectionAlgebra k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) (projectiveLineXOpen k)
    Γ(projectiveLine k, projectiveLineXOpen k) ≃ₐ[k] Polynomial k :=
  affineSectionAlgEquiv k (projectiveLine k ↘ Spec (.of k))
    (projectiveLineXChart k) (projectiveLineXChart_comp_structureMorphism k)

/-- The infinity-chart structure-sheaf sections have their original polynomial coordinates. -/
def infinitySectionCoordinates :
    letI := sectionAlgebra k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) (projectiveLineYOpen k)
    Γ(projectiveLine k, projectiveLineYOpen k) ≃ₐ[k] Polynomial k :=
  affineSectionAlgEquiv k (projectiveLine k ↘ Spec (.of k))
    (projectiveLineYChart k) (projectiveLineYChart_comp_structureMorphism k)

/-- The actual overlap section ring, with its original Laurent coordinates. Its open
range is proved equal to the intersection of the two chart opens. -/
def overlapSectionCoordinates :
    letI := sectionAlgebra k (projectiveLine k)
      (projectiveLine k ↘ Spec (.of k)) (projectiveLineOverlapChart k).opensRange
    Γ(projectiveLine k, (projectiveLineOverlapChart k).opensRange) ≃ₐ[k]
      LaurentPolynomial k :=
  affineSectionAlgEquiv k (projectiveLine k ↘ Spec (.of k))
    (projectiveLineOverlapChart k) (overlapChart_comp_structureMorphism k)

/-- The actual overlap inclusion into the zero-coordinate open. -/
theorem overlapOpen_le_zeroOpen :
    (projectiveLineOverlapChart k).opensRange ≤ projectiveLineXOpen k :=
  affineRange_le (projectiveLineXChart k) (projectiveLineOverlapChart k)
    (CommRingCat.ofHom (chartZeroRingMap k).toRingHom) rfl

/-- The actual overlap inclusion into the infinity-coordinate open. -/
theorem overlapOpen_le_infinityOpen :
    (projectiveLineOverlapChart k).opensRange ≤ projectiveLineYOpen k :=
  affineRange_le (projectiveLineYChart k) (projectiveLineOverlapChart k)
    (CommRingCat.ofHom (chartInfinityRingMap k).toRingHom)
    (cechChartRingMaps_isPullback k).w.symm

/-- Zero-chart restriction is the original polynomial-to-Laurent map, on actual sections. -/
theorem zeroSectionCoordinates_restriction
    (a : Γ(projectiveLine k, projectiveLineXOpen k)) :
    overlapSectionCoordinates k
      ((projectiveLine k).presheaf.map (homOfLE (overlapOpen_le_zeroOpen k)).op a) =
        chartZeroRingMap k (zeroSectionCoordinates k a) := by
  exact congrArg (fun ψ : Γ(projectiveLine k, projectiveLineXOpen k) ⟶
      CommRingCat.of (LaurentPolynomial k) ↦ ψ a)
    (affineSectionIso_restriction (projectiveLineXChart k)
      (projectiveLineOverlapChart k)
      (CommRingCat.ofHom (chartZeroRingMap k).toRingHom) rfl)

/-- Infinity-chart restriction retains the coordinate inversion, on actual sections. -/
theorem infinitySectionCoordinates_restriction
    (a : Γ(projectiveLine k, projectiveLineYOpen k)) :
    overlapSectionCoordinates k
      ((projectiveLine k).presheaf.map (homOfLE (overlapOpen_le_infinityOpen k)).op a) =
        chartInfinityRingMap k (infinitySectionCoordinates k a) := by
  exact congrArg (fun ψ : Γ(projectiveLine k, projectiveLineYOpen k) ⟶
      CommRingCat.of (LaurentPolynomial k) ↦ ψ a)
    (affineSectionIso_restriction (projectiveLineYChart k)
      (projectiveLineOverlapChart k)
      (CommRingCat.ofHom (chartInfinityRingMap k).toRingHom)
      (cechChartRingMaps_isPullback k).w.symm)

section Forms

local instance (U : (projectiveLine k).Opens) : Algebra k Γ(projectiveLine k, U) :=
  sectionAlgebra k (projectiveLine k) (projectiveLine k ↘ Spec (.of k)) U

/-- Degreewise coordinates on the actual zero-chart sectionwise forms. -/
def zeroFormsCoordinates (n : ℕ) :
    ⋀[Γ(projectiveLine k, projectiveLineXOpen k)]^n
        Ω[Γ(projectiveLine k, projectiveLineXOpen k)⁄k] ≃ₗ[k]
      ⋀[Polynomial k]^n Ω[Polynomial k⁄k] :=
  AlgebraDeRham.formsEquiv k (zeroSectionCoordinates k) n

/-- Degreewise coordinates on the actual infinity-chart sectionwise forms. -/
def infinityFormsCoordinates (n : ℕ) :
    ⋀[Γ(projectiveLine k, projectiveLineYOpen k)]^n
        Ω[Γ(projectiveLine k, projectiveLineYOpen k)⁄k] ≃ₗ[k]
      ⋀[Polynomial k]^n Ω[Polynomial k⁄k] :=
  AlgebraDeRham.formsEquiv k (infinitySectionCoordinates k) n

/-- Degreewise coordinates on actual overlap sectionwise forms. -/
def overlapFormsCoordinates (n : ℕ) :
    ⋀[Γ(projectiveLine k, (projectiveLineOverlapChart k).opensRange)]^n
        Ω[Γ(projectiveLine k, (projectiveLineOverlapChart k).opensRange)⁄k]
        ≃ₗ[k] ⋀[LaurentPolynomial k]^n Ω[LaurentPolynomial k⁄k] :=
  AlgebraDeRham.formsEquiv k (overlapSectionCoordinates k) n

/-- These are isomorphisms of the actual de Rham complexes, including their differentials. -/
def zeroSectionDeRhamIso :
    KaehlerDifferential.deRhamComplex k Γ(projectiveLine k, projectiveLineXOpen k) ≅
      KaehlerDifferential.deRhamComplex k (Polynomial k) :=
  AlgebraDeRham.deRhamComplexIso k (zeroSectionCoordinates k)

/-- The infinity-chart coordinate comparison also preserves the original differential. -/
def infinitySectionDeRhamIso :
    KaehlerDifferential.deRhamComplex k Γ(projectiveLine k, projectiveLineYOpen k) ≅
      KaehlerDifferential.deRhamComplex k (Polynomial k) :=
  AlgebraDeRham.deRhamComplexIso k (infinitySectionCoordinates k)

/-- The Laurent coordinate comparison is a complex isomorphism on actual overlap sections. -/
def overlapSectionDeRhamIso :
    KaehlerDifferential.deRhamComplex k
        Γ(projectiveLine k, (projectiveLineOverlapChart k).opensRange) ≅
      KaehlerDifferential.deRhamComplex k (LaurentPolynomial k) :=
  AlgebraDeRham.deRhamComplexIso k (overlapSectionCoordinates k)

/-- In every form degree, actual zero-chart restriction is the original coordinate pullback. -/
theorem zeroFormsCoordinates_restriction (n : ℕ)
    (ω : ⋀[Γ(projectiveLine k, projectiveLineXOpen k)]^n
      Ω[Γ(projectiveLine k, projectiveLineXOpen k)⁄k]) :
    overlapFormsCoordinates k n
      (AlgebraDeRham.formsMap k
        (sectionMap k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
          (homOfLE (overlapOpen_le_zeroOpen k))) n ω) =
      AlgebraDeRham.formsMap k (chartZeroRingMap k) n (zeroFormsCoordinates k n ω) := by
  have he : (overlapSectionCoordinates k).toAlgHom.comp
      (sectionMap k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
        (homOfLE (overlapOpen_le_zeroOpen k))) =
      (chartZeroRingMap k).comp (zeroSectionCoordinates k).toAlgHom := by
    apply AlgHom.ext
    intro a
    exact zeroSectionCoordinates_restriction k a
  have hm := congrArg (fun φ ↦ AlgebraDeRham.formsMap k φ n) he
  simp only [AlgebraDeRham.formsMap_comp] at hm
  exact LinearMap.congr_fun hm ω

/-- In every form degree, infinity-chart restriction retains the original inversion map. -/
theorem infinityFormsCoordinates_restriction (n : ℕ)
    (ω : ⋀[Γ(projectiveLine k, projectiveLineYOpen k)]^n
      Ω[Γ(projectiveLine k, projectiveLineYOpen k)⁄k]) :
    overlapFormsCoordinates k n
      (AlgebraDeRham.formsMap k
        (sectionMap k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
          (homOfLE (overlapOpen_le_infinityOpen k))) n ω) =
      AlgebraDeRham.formsMap k (chartInfinityRingMap k) n
        (infinityFormsCoordinates k n ω) := by
  have he : (overlapSectionCoordinates k).toAlgHom.comp
      (sectionMap k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
        (homOfLE (overlapOpen_le_infinityOpen k))) =
      (chartInfinityRingMap k).comp (infinitySectionCoordinates k).toAlgHom := by
    apply AlgHom.ext
    intro a
    exact infinitySectionCoordinates_restriction k a
  have hm := congrArg (fun φ ↦ AlgebraDeRham.formsMap k φ n) he
  simp only [AlgebraDeRham.formsMap_comp] at hm
  exact LinearMap.congr_fun hm ω

end Forms

end HodgeConjecture.ProjectiveLineDeRham
