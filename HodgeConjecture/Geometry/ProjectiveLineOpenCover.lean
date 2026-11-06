module

public import HodgeConjecture.Geometry.ProjectiveLine
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# The actual open subsets of the projective-line cover

The two named affine charts define open subsets of the original glued scheme.
They cover the whole scheme, and the original Laurent overlap has precisely
their intersection as its open image. The associated Mayer–Vietoris square
therefore uses the actual scheme opens, rather than a second abstract cover.
No cohomological acyclicity or de Rham comparison is assumed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The actual open image of the zero-coordinate chart. -/
abbrev projectiveLineXOpen : (projectiveLine k).Opens :=
  (projectiveLineXChart k).opensRange

/-- The actual open image of the infinity-coordinate chart. -/
abbrev projectiveLineYOpen : (projectiveLine k).Opens :=
  (projectiveLineYChart k).opensRange

/-- The actual Laurent overlap mapped into the original projective line. -/
abbrev projectiveLineOverlapChart :
    Spec (.of (LaurentPolynomial k)) ⟶ projectiveLine k :=
  projectiveLinePuncturedChart k ≫ projectiveLineXChart k

instance : IsOpenImmersion (projectiveLineOverlapChart k) := by
  dsimp [projectiveLineOverlapChart]
  infer_instance

/-- The two chart images cover the entire original scheme. -/
theorem projectiveLineXOpen_sup_YOpen :
    projectiveLineXOpen k ⊔ projectiveLineYOpen k = ⊤ := by
  apply top_unique
  intro x _
  exact projectiveLine_charts_cover k x

/-- The open image of the original Laurent overlap is the intersection of chart images. -/
theorem projectiveLineOverlapChart_opensRange :
    (projectiveLineOverlapChart k).opensRange =
      projectiveLineXOpen k ⊓ projectiveLineYOpen k := by
  let h := projectiveLineOverlap_isPullback k
  apply Opens.ext
  change Set.range (projectiveLineOverlapChart k) =
    Set.range (projectiveLineXChart k) ∩ Set.range (projectiveLineYChart k)
  rw [← IsOpenImmersion.range_pullback_to_base_of_left
    (projectiveLineXChart k) (projectiveLineYChart k)]
  unfold projectiveLineOverlapChart
  rw [← h.isoPullback_hom_fst_assoc]
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hs : Set.range h.isoPullback.hom = Set.univ :=
    Set.range_eq_univ.mpr h.isoPullback.hom.homeomorph.surjective
  rw [hs, Set.image_univ, Set.range_comp]

/-- The original zero-coordinate affine scheme is isomorphic to its open subscheme. -/
def projectiveLineXOpenIso :
    Spec (.of (Polynomial k)) ≅ (projectiveLineXOpen k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (projectiveLineXChart k) (projectiveLineXOpen k).ι
    (by rw [Scheme.Opens.range_ι]; rfl)

/-- The original infinity-coordinate affine scheme is isomorphic to its open subscheme. -/
def projectiveLineYOpenIso :
    Spec (.of (Polynomial k)) ≅ (projectiveLineYOpen k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (projectiveLineYChart k) (projectiveLineYOpen k).ι
    (by rw [Scheme.Opens.range_ι]; rfl)

/-- The original Laurent scheme is isomorphic to the actual intersection open subscheme. -/
def projectiveLineOverlapOpenIso :
    Spec (.of (LaurentPolynomial k)) ≅
      (projectiveLineXOpen k ⊓ projectiveLineYOpen k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (projectiveLineOverlapChart k)
    (projectiveLineXOpen k ⊓ projectiveLineYOpen k).ι
    (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (projectiveLineOverlapChart_opensRange k))

@[reassoc (attr := simp)]
theorem projectiveLineXOpenIso_hom_ι :
    (projectiveLineXOpenIso k).hom ≫ (projectiveLineXOpen k).ι =
      projectiveLineXChart k :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem projectiveLineYOpenIso_hom_ι :
    (projectiveLineYOpenIso k).hom ≫ (projectiveLineYOpen k).ι =
      projectiveLineYChart k :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
theorem projectiveLineOverlapOpenIso_hom_ι :
    (projectiveLineOverlapOpenIso k).hom ≫
        (projectiveLineXOpen k ⊓ projectiveLineYOpen k).ι =
      projectiveLineOverlapChart k :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Restriction of the overlap into the zero-chart open retains the original punctured chart. -/
@[reassoc (attr := simp)]
theorem projectiveLineOverlapOpenIso_hom_X :
    (projectiveLineOverlapOpenIso k).hom ≫
        (projectiveLine k).homOfLE (show projectiveLineXOpen k ⊓
          projectiveLineYOpen k ≤ projectiveLineXOpen k from inf_le_left) =
      projectiveLinePuncturedChart k ≫ (projectiveLineXOpenIso k).hom := by
  rw [← cancel_mono (projectiveLineXOpen k).ι]
  simp [projectiveLineOverlapChart]

/-- Restriction of the overlap into the infinity-chart open retains coordinate inversion. -/
@[reassoc (attr := simp)]
theorem projectiveLineOverlapOpenIso_hom_Y :
    (projectiveLineOverlapOpenIso k).hom ≫
        (projectiveLine k).homOfLE (show projectiveLineXOpen k ⊓
          projectiveLineYOpen k ≤ projectiveLineYOpen k from inf_le_right) =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k ≫
        (projectiveLineYOpenIso k).hom := by
  rw [← cancel_mono (projectiveLineYOpen k).ι]
  simp [projectiveLineOverlapChart, projectiveLineOverlap_compat]

/-- The actual zero-chart image is an affine open of the original scheme. -/
theorem projectiveLineXOpen_isAffine : IsAffineOpen (projectiveLineXOpen k) := by
  unfold projectiveLineXOpen
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact (isAffineOpen_top _).image_of_isOpenImmersion (projectiveLineXChart k)

/-- The actual infinity-chart image is an affine open of the original scheme. -/
theorem projectiveLineYOpen_isAffine : IsAffineOpen (projectiveLineYOpen k) := by
  unfold projectiveLineYOpen
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact (isAffineOpen_top _).image_of_isOpenImmersion (projectiveLineYChart k)

/-- The actual intersection of the chart images is affine, with the original Laurent scheme. -/
theorem projectiveLineOverlapOpen_isAffine :
    IsAffineOpen (projectiveLineXOpen k ⊓ projectiveLineYOpen k) := by
  rw [← projectiveLineOverlapChart_opensRange, ← Scheme.Hom.image_top_eq_opensRange]
  exact (isAffineOpen_top _).image_of_isOpenImmersion (projectiveLineOverlapChart k)

/-- The polynomial zero-chart coordinates are actual sections of the structure sheaf. -/
def projectiveLineXOpenSectionsIso :
    CommRingCat.of (Polynomial k) ≅ Γ(projectiveLine k, projectiveLineXOpen k) :=
  (Scheme.ΓSpecIso (.of (Polynomial k))).symm ≪≫
    IsOpenImmersion.ΓIsoTop (projectiveLineXChart k)

/-- The polynomial infinity-chart coordinates are actual sections of the structure sheaf. -/
def projectiveLineYOpenSectionsIso :
    CommRingCat.of (Polynomial k) ≅ Γ(projectiveLine k, projectiveLineYOpen k) :=
  (Scheme.ΓSpecIso (.of (Polynomial k))).symm ≪≫
    IsOpenImmersion.ΓIsoTop (projectiveLineYChart k)

/-- The Laurent overlap coordinates are actual sections of the structure sheaf. -/
def projectiveLineOverlapOpenSectionsIso :
    CommRingCat.of (LaurentPolynomial k) ≅
      Γ(projectiveLine k, projectiveLineXOpen k ⊓ projectiveLineYOpen k) :=
  (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).symm ≪≫
    IsOpenImmersion.ΓIsoTop (projectiveLineOverlapChart k) ≪≫
    (projectiveLine k).presheaf.mapIso
      (eqToIso (projectiveLineOverlapChart_opensRange k)).symm.op

/-- The sheaf-theoretic Mayer–Vietoris square of the actual affine cover, with top vertex
literally the whole original projective line. -/
def projectiveLineMayerVietorisSquare :
    (Opens.grothendieckTopology (projectiveLine k)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := projectiveLineXOpen k ⊓ projectiveLineYOpen k
      X₂ := projectiveLineXOpen k
      X₃ := projectiveLineYOpen k
      X₄ := ⊤
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ }
    (projectiveLineXOpen_sup_YOpen k).symm rfl

end AlgebraicGeometry

end
