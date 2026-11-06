module

public import HodgeConjecture.Realization.DeRham.AffineSheafAcyclicity
public import HodgeConjecture.Realization.DeRham.ProjectiveLineFormsSheaf
public import HodgeConjecture.Realization.DeRham.OpenImmersionTrivialization

@[expose] public section

/-!
# Actual chart acyclicity for the projective-line differential sheaves

The original fixed-ring sheaf category and its actual right-derived
sections functors are retained. The two affine charts and their Laurent
overlap have vanishing positive cohomology for zero- and one-forms.
One-form acyclicity follows from restriction-compatible local bases on
every open below the chart, through the localized affine criterion.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open KaehlerDifferential

namespace HodgeConjecture.SchemeDeRham

noncomputable section

universe u

/-- A proved local basis on an affine open immersion gives actual ambient
cohomology vanishing for the original one-form sheaf. -/
theorem isZero_oneFormsCohomology_of_affineTrivialization
    (k : Type u) [CommRing k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : Y ⟶ X) [IsOpenImmersion i] [IsAffine Y]
    (e : formsPresheaf k Y (i ≫ f) 1 ≅ functionsPresheaf k Y (i ≫ f))
    (n : ℕ) (hn : 0 < n) :
    IsZero (SheafCohomology.TwoOpenModules.Hobj k (𝟭 _) i.opensRange n
      (formsSheaf k X f 1)) := by
  apply isZero_moduleCohomology_of_localFunctions k X _ i.opensRange
    (isAffineOpen_opensRange i) (underRangeOneFormsAddEquiv k f i e)
    (fun {V W} hVW hWU s => ?_) n hn
  exact underRangeOneFormsAddEquiv_naturality k f i e (hVW.trans hWU) hWU (homOfLE hVW) s

end

end HodgeConjecture.SchemeDeRham

namespace HodgeConjecture.ProjectiveLineDeRham

open SchemeDeRham SheafCohomology

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The actual polynomial differential basis on the zero-coordinate chart. -/
def zeroChartOneFormsTrivialization :
    formsPresheaf k (Spec (.of (Polynomial k)))
        (projectiveLineXChart k ≫ (projectiveLine k ↘ Spec (.of k))) 1 ≅
      functionsPresheaf k (Spec (.of (Polynomial k)))
        (projectiveLineXChart k ≫ (projectiveLine k ↘ Spec (.of k))) := by
  rw [projectiveLineXChart_comp_structureMorphism]
  exact affineOneFormsIsoFunctions k (Polynomial k) (polynomialEquiv k) Polynomial.X (by simp)

/-- The actual polynomial differential basis on the infinity-coordinate chart. -/
def infinityChartOneFormsTrivialization :
    formsPresheaf k (Spec (.of (Polynomial k)))
        (projectiveLineYChart k ≫ (projectiveLine k ↘ Spec (.of k))) 1 ≅
      functionsPresheaf k (Spec (.of (Polynomial k)))
        (projectiveLineYChart k ≫ (projectiveLine k ↘ Spec (.of k))) := by
  rw [projectiveLineYChart_comp_structureMorphism]
  exact affineOneFormsIsoFunctions k (Polynomial k) (polynomialEquiv k) Polynomial.X (by simp)

/-- The actual ordinary `dT` basis on the Laurent overlap. -/
def overlapOneFormsTrivialization :
    formsPresheaf k (Spec (.of (LaurentPolynomial k)))
        (projectiveLineOverlapChart k ≫ (projectiveLine k ↘ Spec (.of k))) 1 ≅
      functionsPresheaf k (Spec (.of (LaurentPolynomial k)))
        (projectiveLineOverlapChart k ≫ (projectiveLine k ↘ Spec (.of k))) := by
  rw [overlapChart_comp_structureMorphism]
  exact affineOneFormsIsoFunctions k (LaurentPolynomial k)
    (laurentOrdinaryKaehlerCoordinates k) (LaurentPolynomial.T 1)
    (laurentOrdinaryKaehlerCoordinates_D_T k)

/-- The original zero-form sheaf is acyclic on the actual zero-coordinate chart. -/
theorem zeroChart_zeroFormsCohomology_isZero (j : ℕ) (hj : 0 < j) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) (projectiveLineXOpen k) j (schemeFormsSheaf k 0)) :=
  isZero_zeroFormsCohomology k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
    (projectiveLineXOpen k) (isAffineOpen_opensRange (projectiveLineXChart k)) j hj

/-- The original zero-form sheaf is acyclic on the actual infinity-coordinate chart. -/
theorem infinityChart_zeroFormsCohomology_isZero (j : ℕ) (hj : 0 < j) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) (projectiveLineYOpen k) j (schemeFormsSheaf k 0)) :=
  isZero_zeroFormsCohomology k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
    (projectiveLineYOpen k) (isAffineOpen_opensRange (projectiveLineYChart k)) j hj

/-- The original one-form sheaf is acyclic on the actual zero-coordinate chart. -/
theorem zeroChart_oneFormsCohomology_isZero (j : ℕ) (hj : 0 < j) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) (projectiveLineXOpen k) j (schemeFormsSheaf k 1)) :=
  isZero_oneFormsCohomology_of_affineTrivialization k (projectiveLine k ↘ Spec (.of k))
    (projectiveLineXChart k) (zeroChartOneFormsTrivialization k) j hj

/-- The original one-form sheaf is acyclic on the actual infinity-coordinate chart. -/
theorem infinityChart_oneFormsCohomology_isZero (j : ℕ) (hj : 0 < j) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) (projectiveLineYOpen k) j (schemeFormsSheaf k 1)) :=
  isZero_oneFormsCohomology_of_affineTrivialization k (projectiveLine k ↘ Spec (.of k))
    (projectiveLineYChart k) (infinityChartOneFormsTrivialization k) j hj

/-- The original zero-form sheaf is acyclic on the actual chart intersection. -/
theorem overlap_zeroFormsCohomology_isZero (j : ℕ) (hj : 0 < j) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) (projectiveLineXOpen k ⊓ projectiveLineYOpen k) j
      (schemeFormsSheaf k 0)) := by
  rw [← projectiveLineOverlapChart_opensRange]
  exact isZero_zeroFormsCohomology k (projectiveLine k) (projectiveLine k ↘ Spec (.of k))
    (projectiveLineOverlapChart k).opensRange
    (isAffineOpen_opensRange (projectiveLineOverlapChart k)) j hj

/-- The original one-form sheaf is acyclic on the actual chart intersection. -/
theorem overlap_oneFormsCohomology_isZero (j : ℕ) (hj : 0 < j) :
    IsZero (TwoOpenModules.Hobj k (𝟭 _) (projectiveLineXOpen k ⊓ projectiveLineYOpen k) j
      (schemeFormsSheaf k 1)) := by
  rw [← projectiveLineOverlapChart_opensRange]
  exact isZero_oneFormsCohomology_of_affineTrivialization k
    (projectiveLine k ↘ Spec (.of k)) (projectiveLineOverlapChart k)
    (overlapOneFormsTrivialization k) j hj

end

end HodgeConjecture.ProjectiveLineDeRham
